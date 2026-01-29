#!/usr/bin/env python3

# =============================================================================
# Amazon FPGA Hardware Development Kit
#
# Copyright 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Amazon Software License (the "License"). You may not use
# this file except in compliance with the License. A copy of the License is
# located at
#
#    http://aws.amazon.com/asl/
#
# or in the "license" file accompanying this file. This file is distributed on
# an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
# implied. See the License for the specific language governing permissions and
# limitations under the License.
# =============================================================================

"""
AFI Creation Helper Script

Interactive tool to create Amazon FPGA Images (AFIs) from Design Checkpoint (DCP) files.
Guides users through region selection, S3 setup, DCP selection, and AFI creation.
"""

import argparse
import glob
import json
import os
import re
import subprocess
import sys
import tarfile
import time
import traceback
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import boto3
from mypy_boto3_ec2.client import EC2Client
from mypy_boto3_ec2.type_defs import CreateFpgaImageResultTypeDef
from mypy_boto3_s3.client import S3Client
from mypy_boto3_s3.type_defs import ListObjectsV2OutputTypeDef
from pydantic import BaseModel, Field, field_validator


DEFAULT_POLL_INTERVAL = 300


class AfiMetadata(BaseModel):
    name: str = Field(..., min_length=1, max_length=255)
    description: str = Field(..., min_length=1, max_length=255)
    dcp_path: str = Field(...)
    bucket: str = Field(...)
    dcp_s3_path: str = Field(...)
    logs_s3_path: str = Field(...)
    region: str = Field(...)

    @field_validator("bucket")
    @classmethod
    def validate_bucket_name(cls, v: str) -> str:
        if not re.match(r"^[a-z0-9][a-z0-9\-]*[a-z0-9]$", v) or not (3 <= len(v) <= 63):
            raise ValueError("Invalid S3 bucket name format")
        return v

    @field_validator("dcp_path")
    @classmethod
    def validate_dcp_file(cls, v: str) -> str:
        print(f"🔎 Validating DCP file is a proper tar archive: {v}")
        if not v.lower().endswith(".tar"):
            raise ValueError("DCP file must have .tar extension")

        try:
            file_size = os.path.getsize(v)
            if file_size == 0:
                raise ValueError("DCP file is empty")

            with tarfile.open(v, "r") as tar:
                if not tar.getnames():
                    raise ValueError("DCP tar file contains no files")

        except (OSError, tarfile.TarError) as e:
            raise ValueError(f"Invalid DCP file: {e}")

        print(f"✓ DCP file validation passed: {v} ({file_size / (1024 * 1024):.1f}MB)")
        return v

    def get_create_args(self) -> Dict[str, Any]:
        return {
            "InputStorageLocation": {"Bucket": self.bucket, "Key": self.dcp_s3_path},
            "LogsStorageLocation": {"Bucket": self.bucket, "Key": self.logs_s3_path},
            "Name": self.name,
            "Description": self.description,
        }


class RegionManager:
    CACHE_FILE = Path.home() / ".aws" / "fpga_regions_cache.json"
    CACHE_TTL = 24 * 60 * 60  # 24 hours
    KNOWN_F2_REGIONS = ["us-east-1", "us-west-2", "ap-southeast-2", "eu-west-2"]
    F2_INSTANCE_TYPES = ["f2.6xlarge", "f2.12xlarge", "f2.48xlarge"]

    @staticmethod
    def get_supported_regions() -> List[str]:
        # Get the regions from the cache if it's less than 24 hours old
        try:
            if (
                RegionManager.CACHE_FILE.exists()
                and (time.time() - RegionManager.CACHE_FILE.stat().st_mtime) < RegionManager.CACHE_TTL
            ):
                with RegionManager.CACHE_FILE.open("r") as f:
                    regions = json.load(f)["regions"]
                    if regions:
                        return regions
        except Exception:
            pass

        # Get regions from AWS or fallback to known list
        regions = (
            RegionManager._get_current_f2_region_list()
            if boto3.Session().get_credentials()
            else RegionManager.KNOWN_F2_REGIONS
        )

        # Save the latest regions in the cache
        try:
            RegionManager.CACHE_FILE.parent.mkdir(parents=True, exist_ok=True)
            with RegionManager.CACHE_FILE.open("w") as f:
                json.dump({"regions": regions, "timestamp": time.time()}, f)
        except Exception:
            pass

        return regions

    @staticmethod
    def _get_current_f2_region_list() -> List[str]:
        print("🔍 Discovering F2 instance supported regions via AWS API...")
        regions: List[str] = []
        for region in boto3.Session().get_available_regions("ec2"):
            try:
                ec2 = boto3.client("ec2", region_name=region)
                if ec2.describe_instance_type_offerings(
                    Filters=[{"Name": "instance-type", "Values": RegionManager.F2_INSTANCE_TYPES}]
                )["InstanceTypeOfferings"]:
                    regions.append(region)
                    print(f"  ✓ Found F2 support in {region}")
            except Exception:
                continue
        return regions

    @staticmethod
    def validate_region_supports_f2(region: str) -> None:
        if region not in RegionManager.get_supported_regions():
            raise ValueError(
                f"Region '{region}' does not support F2 instances.\n"
                f"Supported regions: {', '.join(RegionManager.get_supported_regions())}"
            )


class UserInterface:
    @staticmethod
    def get_choice_from_options(prompt: str, options: List[str], default: int = 0) -> int:
        print(f"\n{prompt}")
        [print(f"{i + 1}) {opt}") for i, opt in enumerate(options)]

        while True:
            try:
                choice = input(f"Choice [{default + 1}]: ").strip() or str(default + 1)
                idx = int(choice) - 1
                if 0 <= idx < len(options):
                    return idx
                print("Invalid choice.")
            except ValueError:
                print("Enter a number.")

    @staticmethod
    def get_input(prompt: str) -> str:
        while True:
            value = input(f"\n{prompt}").strip()
            if value:
                return value
            print("Input cannot be empty.")

    @staticmethod
    def confirm(message: str) -> bool:
        return UserInterface.get_choice_from_options(message, ["Yes", "No"], default=1) == 0


class DCPDiscovery:
    @staticmethod
    def find_hdk_dir() -> Optional[str]:
        if os.environ.get("HDK_DIR"):
            return os.environ.get("HDK_DIR")

        try:
            result = subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True, check=True)
            hdk_path = os.path.join(result.stdout.strip(), "hdk")
            if os.path.isdir(hdk_path):
                print(f"✓ Found HDK directory: {hdk_path}")
                return hdk_path
        except (subprocess.CalledProcessError, FileNotFoundError):
            pass

        return DCPDiscovery.search_for_repo_root_from_current_script_dir()

    @staticmethod
    def search_for_repo_root_from_current_script_dir() -> Optional[str]:
        current_path = Path(__file__).resolve().parent
        while current_path != current_path.parent:
            hdk_dir = current_path / "hdk"
            if (current_path / "hdk_setup.sh").is_file() and (hdk_dir).is_dir():
                print(f"✓ Found HDK directory via repo root: {hdk_dir}")
                return str(hdk_dir)
            current_path = current_path.parent
        print("⚠️  Could not find an HDK directory", file=sys.stderr)
        return None

    def find_dcp_files_in_hdk_workspace(self) -> List[Tuple[str, str]]:
        hdk_dir = DCPDiscovery.find_hdk_dir()
        if not hdk_dir:
            return []

        dcp_paths = glob.glob(os.path.join(hdk_dir, "cl", "examples", "*", "build", "checkpoints", "*.tar"))
        return [(path, self._create_display_name(path)) for path in sorted(dcp_paths)]

    def _create_display_name(self, path: str) -> str:
        name = os.path.basename(path)
        info = [name]

        date_match = re.search(r"(\d{4}_\d{2}_\d{2}-\d{6})", name)
        if date_match:
            try:
                build_date = datetime.strptime(date_match.group(1), "%Y_%m_%d-%H%M%S")
                info.append(f"Built: {build_date.strftime('%b %d, %Y at %H:%M')}")
            except ValueError:
                pass

        if os.path.exists(path):
            size_mb = os.path.getsize(path) / (1024 * 1024)
            info.append(f"Size: {size_mb:.1f}MB")

        return f"{info[0]} ({', '.join(info[1:])})" if len(info) > 1 else info[0]

    def get_dcp_path_interactive(self) -> str:
        if (
            UserInterface.get_choice_from_options(
                "Would you like to scan for DCP files in your HDK workspace?",
                ["Yes, scan automatically", "No, I'll provide the path manually"],
            )
            != 0
        ):
            return UserInterface.get_input("Please enter the path to your DCP file: ")

        dcp_files = self.find_dcp_files_in_hdk_workspace()
        if not dcp_files:
            return UserInterface.get_input("No DCP files found. Please enter the path: ")

        options = [f"{display}\n   Path: {path}" for path, display in dcp_files]
        options.append("Other path (specify manually)")

        idx = UserInterface.get_choice_from_options("Select DCP file from your HDK workspace:", options)
        return dcp_files[idx][0] if idx < len(dcp_files) else UserInterface.get_input("Enter DCP file path: ")


class S3Manager:
    def __init__(self, region: str):
        self.region = region
        self.s3_client: S3Client = boto3.client("s3")

    def get_regional_buckets(self) -> List[str]:
        buckets: List[str] = []
        for bucket_name in [b.get("Name", "") for b in self.s3_client.list_buckets()["Buckets"]]:
            try:
                location = self.s3_client.get_bucket_location(Bucket=bucket_name).get("LocationConstraint")
                if location == self.region or (location is None and self.region == "us-east-1"):
                    buckets.append(bucket_name)
            except Exception:
                continue
        return buckets

    def create_bucket(self, bucket_name: str) -> None:
        kwargs: Dict[str, Any] = {"Bucket": bucket_name}
        if self.region != "us-east-1":
            kwargs["CreateBucketConfiguration"] = {"LocationConstraint": self.region}
        self.s3_client.create_bucket(**kwargs)
        print(f"✓ Created S3 bucket: {bucket_name}")

    def ensure_folder_exists(self, bucket: str, folder_path: str) -> None:
        folder_path = folder_path.rstrip("/") + "/"
        if not self.s3_client.list_objects_v2(Bucket=bucket, Prefix=folder_path).get("Contents"):
            self.s3_client.put_object(Bucket=bucket, Key=folder_path)
            print(f"✓ Created S3 folder: s3://{bucket}/{folder_path}")

    def upload_file(self, local_path: str, bucket: str, key: str) -> None:
        print(f"Uploading: {local_path} -> s3://{bucket}/{key}")
        self.s3_client.upload_file(local_path, bucket, key)
        print("✓ Upload completed")

    def get_bucket_interactive(self) -> str:
        buckets = self.get_regional_buckets()
        options = buckets + ["Create new bucket"]
        idx = UserInterface.get_choice_from_options(f"Select {self.region} S3 bucket:", options, default=len(buckets))

        if idx < len(buckets):
            return buckets[idx]

        bucket_name = UserInterface.get_input("Enter new bucket name: ")
        self.create_bucket(bucket_name)
        return bucket_name

    def get_s3_paths_interactive(self, bucket: str) -> Tuple[str, str]:
        msg = "Store DCP file and logs in the same directory?"
        same_dir = UserInterface.get_choice_from_options(msg, ["Yes, same directory", "No, separate directories"]) == 0

        if same_dir:
            base_path = self._get_s3_base_path(bucket)
            return base_path, base_path

        print("\nConfiguring DCP storage path:")
        dcp_path = self._get_s3_base_path(bucket)
        print("\nConfiguring logs storage path:")
        logs_path = self._get_s3_base_path(bucket)
        return dcp_path, logs_path

    def _get_s3_base_path(self, bucket: str) -> str:
        response: ListObjectsV2OutputTypeDef = self.s3_client.list_objects_v2(Bucket=bucket, Delimiter="/", MaxKeys=10)
        folders = [p.get("Prefix", "").rstrip("/") for p in response.get("CommonPrefixes", [])]

        if folders:
            options = folders + ["Enter custom path"]
            idx = UserInterface.get_choice_from_options(
                f"Select folder in bucket '{bucket}':", options, default=len(folders)
            )
            if idx < len(folders):
                return folders[idx]

        return UserInterface.get_input("Enter S3 path (without leading/trailing slashes): ").strip("/")


class AFICreator:
    def __init__(self, region: str, interactive: bool = True):
        self.region = region
        self.interactive = interactive
        self.s3_manager = S3Manager(region)
        self.dcp_discovery = DCPDiscovery()
        self.ec2_client: EC2Client = boto3.client("ec2", region_name=region)

    def create_afi(
        self, afi_data: Dict[str, str], create_bucket: bool = False, poll_interval: Optional[int] = None
    ) -> CreateFpgaImageResultTypeDef:
        complete_data = self._complete_afi_data(afi_data)
        afi_metadata = AfiMetadata(**complete_data)

        self._prepare_s3_resources(afi_metadata, create_bucket)

        if self.interactive:
            self._confirm_operations(afi_metadata)

        result = self.ec2_client.create_fpga_image(**afi_metadata.get_create_args())
        print("✓ AFI creation started successfully!")
        print(f"  AFI ID: {result['FpgaImageId']}")
        print(f"  AGFI ID: {result['FpgaImageGlobalId']}")

        if poll_interval:
            self._handle_polling(result["FpgaImageId"], poll_interval)
        return result

    def _complete_afi_data(self, data: Dict[str, str]) -> Dict[str, str]:
        if not data.get("name") and self.interactive:
            data["name"] = UserInterface.get_input("Enter AFI name: ")

        if not data.get("description") and self.interactive:
            data["description"] = UserInterface.get_input("Enter AFI description: ")

        if not data.get("dcp_path") and self.interactive:
            data["dcp_path"] = self.dcp_discovery.get_dcp_path_interactive()

        if not data.get("bucket") and self.interactive:
            data["bucket"] = self.s3_manager.get_bucket_interactive()

        if not data.get("dcp_s3_path") or not data.get("logs_s3_path") and self.interactive:
            data["dcp_s3_path"], data["logs_s3_path"] = self.s3_manager.get_s3_paths_interactive(data["bucket"])

        data["region"] = self.region
        return data

    def _prepare_s3_resources(self, afi: AfiMetadata, create_bucket: bool) -> None:
        if create_bucket:
            self.s3_manager.create_bucket(afi.bucket)

        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        afi_folder = f"{afi.name}_{timestamp}"

        final_dcp_path = f"{afi.dcp_s3_path}/{afi_folder}/"
        final_logs_path = f"{afi.logs_s3_path}/{afi_folder}/logs/"

        self.s3_manager.ensure_folder_exists(afi.bucket, final_dcp_path)
        self.s3_manager.ensure_folder_exists(afi.bucket, final_logs_path)

        dcp_key = f"{final_dcp_path}{os.path.basename(afi.dcp_path)}"
        self.s3_manager.upload_file(afi.dcp_path, afi.bucket, dcp_key)

        afi.dcp_s3_path = dcp_key
        afi.logs_s3_path = final_logs_path

    def _confirm_operations(self, afi: AfiMetadata) -> None:
        print(f"""
Operations to execute:
1. Upload DCP: {afi.dcp_path} -> s3://{afi.bucket}/{afi.dcp_s3_path}
2. Create AFI: '{afi.name}' - '{afi.description}' in {self.region}""")

        if not UserInterface.confirm("Proceed with these operations?"):
            raise KeyboardInterrupt("Operation cancelled by user")

    def _handle_polling(self, afi_id: str, interval: int) -> None:
        should_poll = not self.interactive or UserInterface.confirm(
            f"Poll AFI status every {interval} seconds until completion?"
        )

        if should_poll:
            self._poll_afi_status(afi_id, interval)

    def _poll_afi_status(self, afi_id: str, interval: int) -> None:
        print(f"\nPolling AFI status every {interval // 60} minutes...")

        while True:
            try:
                state = self.ec2_client.describe_fpga_images(FpgaImageIds=[afi_id])["FpgaImages"][0]["State"]
                status_code = state["Code"]

                print(f"[{datetime.now():%Y-%m-%d %H:%M:%S}] AFI Status: {status_code}")

                if status_code == "available":
                    print("\n🎉 AFI creation completed successfully!")
                    break
                if status_code in ["failed", "unavailable"]:
                    print(f"\n❌ AFI creation failed: {status_code}")
                    print(f"Error: {state.get('Message', 'MISSING')}")
                    break

                time.sleep(interval)

            except KeyboardInterrupt:
                print(f"\nPolling stopped. Check status with: aws ec2 describe-fpga-images --fpga-image-ids {afi_id}")
                break
            except Exception as e:
                print(f"Error polling AFI status: {e}")
                break

    def provide_next_steps(self, agfi_id: str) -> None:
        hdk_dir = DCPDiscovery.find_hdk_dir()
        repo_root_str = "$AWS_FPGA_REPO_DIR" if not hdk_dir else os.path.dirname(hdk_dir)
        # TODO: Insert documentation pointing to the AMI's
        # TODO: Insert documentation pointing to the tools

        print(f"""
{"=" * 80}
🚀 NEXT STEPS: Load Your FPGA Image
{"=" * 80}

Your AFI is now ready! Here's how to load it on an F2 instance:

📋 STEP 1: Launch an Amazon EC2 F2 instance (f2.6xlarge, f2.12xlarge, or f2.48xlarge)
   Make sure to use an FPGA Runtime AMI or the FPGA Developer AMI for the best experience

📋 STEP 2: Set Up Your Environment from the aws-fpga repository root
   cd {repo_root_str}
   source sdk_setup.sh

📋 STEP 3: Load Your FPGA Image with the AGFI ID
   sudo fpga-load-local-image -S 0 -I {agfi_id}

📋 STEP 4: Check that your AFI has 'loaded' successfully with your AGFI ID
   sudo fpga-describe-local-image -S 0 -H

{"=" * 80}""")


parser = argparse.ArgumentParser(
    description="Create Amazon FPGA Images (AFIs) from Design Checkpoint files",
    formatter_class=argparse.RawDescriptionHelpFormatter,
    epilog=f"""
Examples:
# Interactive mode (default)
python3 create_afi.py

# Non-interactive mode
python3 create_afi.py --region us-east-1 --name "my-design" \\
--description "Custom FPGA logic" --dcp-path /path/to/dcp.tar \\
--bucket my-afi-bucket --create-bucket --poll-interval {DEFAULT_POLL_INTERVAL}
    """,
)

supported_regions = RegionManager.get_supported_regions()
parser.add_argument("--interactive", action="store_true", default=True, help="Run in interactive mode (default)")
parser.add_argument("--non-interactive", dest="interactive", action="store_false", help="Run in non-interactive mode")
parser.add_argument("--region", choices=supported_regions, help="AWS region for AFI creation")
parser.add_argument("--name", help="AFI name")
parser.add_argument("--description", help="AFI description")
parser.add_argument("--dcp-path", help="Path to DCP tarball file")
parser.add_argument("--bucket", help="S3 bucket name for DCP and logs")
parser.add_argument("--dcp-s3-path", help="S3 path for DCP")
parser.add_argument("--logs-s3-path", help="S3 path for logs")
parser.add_argument("--create-bucket", action="store_true", help="Create S3 bucket if it doesn't exist")
parser.add_argument(
    "--poll-interval",
    type=int,
    default=DEFAULT_POLL_INTERVAL,
    help=f"Polling interval in seconds (default: {DEFAULT_POLL_INTERVAL})",
)


class AFIManager:
    def handle_interactive_mode(self, args: argparse.Namespace) -> str:
        if args.interactive and not args.region:
            idx = UserInterface.get_choice_from_options("Select AWS region:", supported_regions)
            return supported_regions[idx]
        return args.region

    def create_afi_request(self, args: argparse.Namespace, region: str):
        creator = AFICreator(region=region, interactive=args.interactive)
        result = creator.create_afi(
            afi_data=vars(args),
            create_bucket=args.create_bucket,
            poll_interval=args.poll_interval,
        )

        self.print_success(result, region, args.interactive)
        creator.provide_next_steps(result["FpgaImageGlobalId"])
        return result

    @staticmethod
    def print_success(result: CreateFpgaImageResultTypeDef, region: str, interactive: bool):
        print("\n✅ AFI creation request submitted successfully!")
        print(f"AFI ID: {result['FpgaImageId']}")
        print(f"AGFI ID: {result['FpgaImageGlobalId']}")

        if not interactive:
            print("\nMonitor progress with:")
            print(f"aws ec2 describe-fpga-images --fpga-image-ids {result['FpgaImageId']} --region {region}")


def main():
    try:
        args = parser.parse_args()
    except SystemExit as e:
        return 0 if e.code == 0 else 1

    try:
        afi_manager = AFIManager()
        region = afi_manager.handle_interactive_mode(args)
        RegionManager.validate_region_supports_f2(region)
        afi_manager.create_afi_request(args, region)
        return 0

    except KeyboardInterrupt:
        print("\n⚠️  Operation cancelled by user", file=sys.stderr)
    except Exception as e:
        print(f"❌ Error: {e}", file=sys.stderr)
        traceback.print_exc()
    return 1


if __name__ == "__main__":
    sys.exit(main())
