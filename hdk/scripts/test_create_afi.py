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


if __name__ == "__main__":
    import coverage
    import os

    current_dir = os.path.dirname(os.path.abspath(__file__))
    cov = coverage.Coverage(source=[current_dir], omit=["*test*.py"])
    cov.start()

from pathlib import Path
import shutil
import os
import sys
import subprocess
import tempfile
import unittest
from io import StringIO
from unittest.mock import MagicMock, Mock, patch, mock_open, DEFAULT
from typing import List, Tuple, Optional
import boto3
from moto import mock_s3
from pydantic import ValidationError

# Import the module under test
from create_afi import (
    AFICreator,
    AfiMetadata,
    DCPDiscovery,
    RegionManager,
    S3Manager,
    UserInterface,
    AFIManager,
    main,
)


class TestAfiMetadata(unittest.TestCase):
    def setUp(self):
        self.valid_data = {
            "name": "test-afi",
            "description": "Test AFI",
            "dcp_path": "/path/to/test.tar",
            "bucket": "test-bucket",
            "dcp_s3_path": "dcp/path",
            "logs_s3_path": "logs/path",
            "region": "us-east-1",
        }

    @patch("os.path.getsize")
    @patch("tarfile.open")
    def test_valid_metadata(self, mock_tarfile, mock_getsize):
        mock_getsize.return_value = 1024
        mock_tarfile.return_value.__enter__.return_value.getnames.return_value = ["test.dcp"]

        metadata = AfiMetadata(**self.valid_data)
        self.assertEqual(metadata.name, "test-afi")
        self.assertEqual(metadata.bucket, "test-bucket")

    def test_bucket_validation(self):
        invalid_buckets = ["UPPER", "under_score", "ab", "a" * 64, "-bucket", "bucket-"]
        valid_buckets = ["test-bucket", "my-bucket-123", "abc"]

        for bucket in invalid_buckets:
            with self.subTest(bucket=bucket):
                data = self.valid_data.copy()
                data["bucket"] = bucket
                with self.assertRaises(ValidationError):
                    AfiMetadata(**data)

        for bucket in valid_buckets:
            with self.subTest(bucket=bucket):
                with patch("os.path.getsize", return_value=1024), patch("tarfile.open") as mock_tar:
                    mock_tar.return_value.__enter__.return_value.getnames.return_value = ["test.dcp"]
                    data = self.valid_data.copy()
                    data["bucket"] = bucket
                    metadata = AfiMetadata(**data)
                    self.assertEqual(metadata.bucket, bucket)

    @patch("os.path.getsize")
    @patch("tarfile.open")
    def test_dcp_validation(self, mock_tarfile, mock_getsize):
        mock_getsize.return_value = 1024
        mock_tarfile.return_value.__enter__.return_value.getnames.return_value = ["test.dcp"]

        # Test invalid extension
        data = self.valid_data.copy()
        data["dcp_path"] = "test.zip"
        with self.assertRaises(ValidationError):
            AfiMetadata(**data)

        # Test empty file
        mock_getsize.return_value = 0
        with self.assertRaises(ValidationError):
            AfiMetadata(**self.valid_data)

        # Test empty tar
        mock_getsize.return_value = 1024
        mock_tarfile.return_value.__enter__.return_value.getnames.return_value = []
        with self.assertRaises(ValidationError):
            AfiMetadata(**self.valid_data)

    def test_get_create_args(self):
        with patch("os.path.getsize", return_value=1024), patch("tarfile.open") as mock_tar:
            mock_tar.return_value.__enter__.return_value.getnames.return_value = ["test.dcp"]
            metadata = AfiMetadata(**self.valid_data)
            args = metadata.get_create_args()

            expected = {
                "InputStorageLocation": {"Bucket": "test-bucket", "Key": "dcp/path"},
                "LogsStorageLocation": {"Bucket": "test-bucket", "Key": "logs/path"},
                "Name": "test-afi",
                "Description": "Test AFI",
            }
            self.assertEqual(args, expected)


class TestRegionManager(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.test_regions = ["us-east-1", "us-west-2", "eu-west-1"]
        cls.temp_dir = tempfile.mkdtemp()
        cls.cache_file = Path(cls.temp_dir) / ".aws" / "fpga_regions_cache.json"
        cls.cache_file.parent.mkdir(parents=True)

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.temp_dir)

    def setUp(self):
        if self.cache_file.exists():
            self.cache_file.unlink()

    def setup_cache_mock(self, mock_cache_file, mock_time, exists=True, mtime=999000):
        """Helper to set up common cache mocking."""
        mock_time.return_value = 1000000
        mock_cache_file.exists.return_value = exists
        mock_cache_file.stat.return_value.st_mtime = mtime
        return mock_open()

    @patch("create_afi.RegionManager.CACHE_FILE")
    @patch("time.time")
    def test_cache_operations(self, mock_time, mock_cache_file):
        """Test all cache-related scenarios."""
        test_cases: List[Tuple[str, bool, Optional[str], List[str], bool]] = [
            ("read valid", True, '{"regions": ["us-east-1"], "timestamp": 1000000}', ["us-east-1"], False),
            ("read invalid json", True, "invalid json", self.test_regions, False),
            ("read missing regions", True, '{"timestamp": 1000000}', self.test_regions, False),
            ("write error", False, None, self.test_regions, False),
            ("json dump error", False, None, self.test_regions, True),
        ]

        for scenario, exists, content, expected, json_error in test_cases:
            with self.subTest(scenario=scenario):
                mock_file = self.setup_cache_mock(mock_cache_file, mock_time, exists)
                if content:
                    mock_file.return_value.__enter__.return_value.read.return_value = content
                mock_cache_file.open = mock_file

                with patch("boto3.Session") as mock_session:
                    mock_session.return_value.get_credentials.return_value = MagicMock()
                    with patch.object(RegionManager, "_get_current_f2_region_list", return_value=self.test_regions):
                        if json_error:
                            # Make json.dump raise an exception
                            with patch("json.dump", side_effect=TypeError("JSON serialization error")):
                                regions = RegionManager.get_supported_regions()
                        else:
                            regions = RegionManager.get_supported_regions()
                        self.assertEqual(regions, expected)

    @patch("boto3.Session")
    @patch("boto3.client")
    def test_region_discovery(self, mock_client, mock_session):
        """Test region discovery scenarios."""
        mock_session.return_value.get_available_regions.return_value = ["us-east-1", "us-west-2", "eu-west-1"]

        # Create mock EC2 clients with different behaviors
        mock_ec2_clients = {
            "us-east-1": MagicMock(
                **{
                    "describe_instance_type_offerings.return_value": {
                        "InstanceTypeOfferings": [{"InstanceType": "f2.6xlarge"}]
                    }
                }
            ),
            "us-west-2": MagicMock(**{"describe_instance_type_offerings.return_value": {"InstanceTypeOfferings": []}}),
            "eu-west-1": MagicMock(**{"describe_instance_type_offerings.side_effect": Exception("API Error")}),
        }

        def mock_ec2_client(service, region_name):
            return mock_ec2_clients[region_name]

        mock_client.side_effect = mock_ec2_client

        regions = RegionManager._get_current_f2_region_list()
        self.assertEqual(regions, ["us-east-1"])

        # Verify each region was checked with correct parameters
        for region, mock_ec2 in mock_ec2_clients.items():
            if region != "eu-west-1":  # Skip error case
                mock_ec2.describe_instance_type_offerings.assert_called_once_with(
                    Filters=[{"Name": "instance-type", "Values": RegionManager.F2_INSTANCE_TYPES}]
                )

    def test_region_validation(self):
        """Test region validation."""
        with patch.object(RegionManager, "get_supported_regions", return_value=self.test_regions):
            RegionManager.validate_region_supports_f2("us-east-1")  # Should not raise
            with self.assertRaisesRegex(ValueError, "does not support F2 instances"):
                RegionManager.validate_region_supports_f2("invalid-region")


class TestUserInterface(unittest.TestCase):
    def setUp(self):
        self.options = ["Option 1", "Option 2"]
        self.prompt = "Select option:"

    @patch("builtins.input", return_value="")
    def test_get_choice_default(self, mock_input):
        self.assertEqual(UserInterface.get_choice_from_options(self.prompt, self.options, default=1), 1)

    @patch("builtins.input", return_value="2")
    def test_get_choice_valid(self, mock_input):
        self.assertEqual(UserInterface.get_choice_from_options(self.prompt, self.options), 1)

    @patch("builtins.input", side_effect=["invalid", "0", "2"])
    def test_get_choice_invalid_then_valid(self, mock_input):
        result = UserInterface.get_choice_from_options(self.prompt, self.options)
        self.assertEqual(result, 1)
        self.assertEqual(mock_input.call_count, 3)

    @patch("builtins.input", side_effect=["5", "1"])
    def test_get_choice_out_of_range(self, mock_input):
        result = UserInterface.get_choice_from_options(self.prompt, self.options)
        self.assertEqual(result, 0)
        self.assertEqual(mock_input.call_count, 2)

    @patch("builtins.input", side_effect=["", "  ", "valid"])
    def test_get_input(self, mock_input):
        self.assertEqual(UserInterface.get_input("Prompt:"), "valid")
        self.assertEqual(mock_input.call_count, 3)

    @patch.object(UserInterface, "get_choice_from_options")
    def test_confirm(self, mock_get_choice_from_options):
        mock_get_choice_from_options.return_value = 0
        self.assertTrue(UserInterface.confirm("Confirm?"))
        mock_get_choice_from_options.return_value = 1
        self.assertFalse(UserInterface.confirm("Confirm?"))


class TestDCPDiscovery(unittest.TestCase):
    def setUp(self):
        self.dcp_discovery = DCPDiscovery()

    def test_find_hdk_dir_scenarios(self):
        # From environment variable
        with patch.dict(os.environ, {"HDK_DIR": "/test/hdk"}):
            self.assertEqual(DCPDiscovery.find_hdk_dir(), "/test/hdk")

        # From git
        with patch.dict(os.environ, {}, clear=True):
            with patch("subprocess.run") as mock_run:
                with patch("os.path.isdir", return_value=True):
                    mock_run.return_value.stdout = "/repo/root\n"
                    self.assertEqual(DCPDiscovery.find_hdk_dir(), "/repo/root/hdk")

        # Fallback case
        with patch.dict(os.environ, {}, clear=True):
            with patch("subprocess.run", side_effect=subprocess.CalledProcessError(1, "git")):
                with patch.object(
                    DCPDiscovery, "search_for_repo_root_from_current_script_dir", return_value="/fallback/hdk"
                ):
                    self.assertEqual(DCPDiscovery.find_hdk_dir(), "/fallback/hdk")

    @patch("create_afi.Path")
    def test_search_for_repo_root(self, mock_path):
        mock_parent, mock_root = MagicMock(), MagicMock()
        mock_path.return_value.resolve.return_value.parent = mock_parent
        mock_parent.parent = mock_root
        mock_root.parent = mock_root

        # Test HDK not found
        mock_parent.__truediv__.return_value.is_file.return_value = False
        self.assertIsNone(DCPDiscovery.search_for_repo_root_from_current_script_dir())

        # Test HDK found
        mock_hdk_setup, mock_hdk_dir = MagicMock(), MagicMock()
        mock_hdk_setup.is_file.return_value = True
        mock_hdk_dir.is_dir.return_value = True
        mock_hdk_dir.__str__.return_value = "/test/repo/hdk"
        mock_parent.__truediv__ = MagicMock(
            side_effect=lambda p: mock_hdk_setup if p == "hdk_setup.sh" else mock_hdk_dir
        )
        self.assertEqual(DCPDiscovery.search_for_repo_root_from_current_script_dir(), "/test/repo/hdk")

    def test_dcp_operations(self):
        # Test find_dcp_files scenarios
        with patch.object(DCPDiscovery, "find_hdk_dir") as mock_find_hdk, patch("glob.glob") as mock_glob:
            mock_find_hdk.return_value = None
            self.assertEqual(self.dcp_discovery.find_dcp_files_in_hdk_workspace(), [])

            mock_find_hdk.return_value = "/test/hdk"
            mock_glob.return_value = ["/test/path/test.tar"]
            results = self.dcp_discovery.find_dcp_files_in_hdk_workspace()
            self.assertEqual(len(results), 1)

        # Test display name creation
        self.assertEqual(
            self.dcp_discovery._create_display_name("/test/file_2024_13_99-999999.tar"), "file_2024_13_99-999999.tar"
        )

        with patch("os.path.exists", return_value=True), patch("os.path.getsize", return_value=2 * 1024 * 1024):
            self.assertIn(
                "Built: Jan 01, 2024 at 12:00",
                self.dcp_discovery._create_display_name("/test/file_2024_01_01-120000.tar"),
            )

    def test_interactive_path_selection(self):
        with patch.object(DCPDiscovery, "find_dcp_files_in_hdk_workspace") as mock_find:
            with patch.object(UserInterface, "get_choice_from_options") as mock_choice:
                with patch.object(UserInterface, "get_input") as mock_input:
                    # Manual path
                    mock_choice.return_value = 1
                    mock_input.return_value = "/test/path.tar"
                    self.assertEqual(self.dcp_discovery.get_dcp_path_interactive(), "/test/path.tar")

                    # Empty list
                    mock_choice.return_value = 0
                    mock_find.return_value = []
                    self.assertEqual(self.dcp_discovery.get_dcp_path_interactive(), "/test/path.tar")

                    # Choose from list
                    mock_find.return_value = [("/path1.tar", "d1"), ("/path2.tar", "d2")]
                    mock_choice.side_effect = [0, 1]
                    self.assertEqual(self.dcp_discovery.get_dcp_path_interactive(), "/path2.tar")

                    # Choose other path
                    mock_choice.side_effect = [0, 2]
                    self.assertEqual(self.dcp_discovery.get_dcp_path_interactive(), "/test/path.tar")


class TestS3Manager(unittest.TestCase):
    def setUp(self):
        self.region = "us-east-1"
        self.bucket_name = "test-bucket"
        self.test_content = "test content"

    def setup_mock_bucket(self):
        self.s3_client = boto3.client("s3", region_name=self.region)
        S3Manager(self.region).create_bucket(self.bucket_name)
        return S3Manager(self.region)

    @mock_s3
    def test_bucket_operations(self):
        self.s3_client = boto3.client("s3", region_name=self.region)
        s3_manager = S3Manager(self.region)

        # Test bucket creation in different regions
        self.s3_client.create_bucket(Bucket="us-east-1-bucket")

        # Test non-default region bucket creation
        west_manager = S3Manager("us-west-2")
        west_manager.create_bucket("west-bucket")  # This will use LocationConstraint

        location = self.s3_client.get_bucket_location(Bucket="west-bucket")["LocationConstraint"]
        self.assertEqual(location, "us-west-2")

        # Test error handling
        original_get_location = s3_manager.s3_client.get_bucket_location

        def mock_get_location(**kwargs):
            if kwargs["Bucket"] == "error-bucket":
                raise boto3.exceptions.ClientError(
                    {"Error": {"Code": "AccessDenied", "Message": "Access Denied"}}, "GetBucketLocation"
                )
            return original_get_location(**kwargs)

        s3_manager.s3_client.get_bucket_location = mock_get_location
        self.s3_client.create_bucket(Bucket="error-bucket")

        buckets = s3_manager.get_regional_buckets()
        self.assertIn("us-east-1-bucket", buckets)
        self.assertNotIn("west-bucket", buckets)
        self.assertNotIn("error-bucket", buckets)

    @mock_s3
    def test_folder_and_file_operations(self):
        s3_manager = self.setup_mock_bucket()
        folder_path = "test/folder"

        # Test folder operations
        s3_manager.ensure_folder_exists(self.bucket_name, folder_path)
        self.s3_client.put_object(Bucket=self.bucket_name, Key=f"{folder_path}/existing.txt", Body=b"test")
        s3_manager.ensure_folder_exists(self.bucket_name, folder_path)
        objects = self.s3_client.list_objects_v2(Bucket=self.bucket_name, Prefix=f"{folder_path}/")
        self.assertEqual(len(objects.get("Contents", [])), 2)

        # Test file upload
        with tempfile.NamedTemporaryFile(mode="w", delete=False) as f:
            f.write(self.test_content)
            temp_file = f.name
        try:
            s3_manager.upload_file(temp_file, self.bucket_name, "test/file.txt")
            content = self.s3_client.get_object(Bucket=self.bucket_name, Key="test/file.txt")["Body"].read().decode()
            self.assertEqual(content, self.test_content)
        finally:
            os.unlink(temp_file)

    @mock_s3
    @patch.object(UserInterface, "get_choice_from_options")
    @patch.object(UserInterface, "get_input")
    def test_interactive_operations(self, mock_input, mock_choice):
        s3_manager = self.setup_mock_bucket()
        self.s3_client.put_object(Bucket=self.bucket_name, Key="existing_folder1/")

        # Test bucket selection (both existing and new)
        mock_choice.side_effect = [0, 1]  # First select existing, then create new
        mock_input.return_value = "new-test-bucket"
        self.assertEqual(s3_manager.get_bucket_interactive(), self.bucket_name)
        self.assertEqual(s3_manager.get_bucket_interactive(), "new-test-bucket")

        # Test path selection - same directory
        mock_choice.reset_mock()
        mock_input.reset_mock()
        mock_choice.side_effect = [0, 0]  # Same directory, select existing folder
        dcp_path, logs_path = s3_manager.get_s3_paths_interactive(self.bucket_name)
        self.assertEqual(dcp_path, logs_path)
        self.assertEqual(dcp_path, "existing_folder1")

        # Test path selection - separate directories
        mock_choice.reset_mock()
        mock_input.reset_mock()
        mock_choice.side_effect = [1, 0, 2]  # Separate dirs, existing folder, custom path
        mock_input.return_value = "custom/path"
        dcp_path, logs_path = s3_manager.get_s3_paths_interactive(self.bucket_name)
        self.assertEqual(dcp_path, "existing_folder1")
        self.assertEqual(logs_path, "custom/path")


class TestAFICreator(unittest.TestCase):
    def setUp(self):
        self.region = "us-east-1"
        self.afi_creator = AFICreator(self.region, interactive=False)
        self.mock_afi_data = {
            "name": "test-afi",
            "description": "Test description",
            "dcp_path": "/path/to/test.tar",
            "bucket": "test-bucket",
            "dcp_s3_path": "dcp/path",
            "logs_s3_path": "logs/path",
        }
        # Set up string buffer to capture output
        self.output = StringIO()
        self._stdout = sys.stdout
        sys.stdout = self.output

    def tearDown(self):
        sys.stdout = self._stdout
        self.output.close()

    @patch("boto3.client")
    def test_initialization(self, _):
        creator = AFICreator("us-west-2", interactive=True)
        self.assertEqual(creator.region, "us-west-2")
        self.assertTrue(creator.interactive)
        self.assertIsInstance(creator.s3_manager, S3Manager)
        self.assertIsInstance(creator.dcp_discovery, DCPDiscovery)

    @patch.multiple("create_afi.AFICreator", _complete_afi_data=DEFAULT, _poll_afi_status=DEFAULT)
    @patch.multiple("os.path", getsize=DEFAULT)
    @patch("boto3.client")
    @patch("tarfile.open")
    @patch("create_afi.UserInterface.confirm")
    def test_create_afi_workflow(self, mock_confirm, mock_tarfile, mock_client, **mocks):
        # Setup basic mocks
        mock_tarfile.return_value.__enter__.return_value.getnames.return_value = ["test.dcp"]
        mocks["getsize"].return_value = 1024 * 1024
        mocks["_complete_afi_data"].return_value = {**self.mock_afi_data, "region": self.region}

        self.afi_creator.ec2_client = MagicMock()
        self.afi_creator.ec2_client.create_fpga_image.return_value = {
            "FpgaImageId": "afi-12345",
            "FpgaImageGlobalId": "agfi-67890",
        }
        self.afi_creator.s3_manager = MagicMock()
        self.afi_creator.interactive = True

        # Test create_bucket and polling
        mock_confirm.side_effect = [True, True]  # First call
        result = self.afi_creator.create_afi({"name": "test"}, create_bucket=True, poll_interval=300)
        self.afi_creator.s3_manager.create_bucket.assert_called_once()
        mocks["_poll_afi_status"].assert_called_once_with("afi-12345", 300)

        # Reset mocks and set up for cancellation test
        mock_confirm.reset_mock()
        mock_confirm.side_effect = None  # Clear side_effect
        mock_confirm.return_value = False  # Second call
        with self.assertRaises(KeyboardInterrupt) as cm:
            self.afi_creator.create_afi({"name": "test"})
        self.assertEqual(str(cm.exception), "Operation cancelled by user")

    def test_afi_data_completion(self):
        result = self.afi_creator._complete_afi_data(self.mock_afi_data.copy())
        self.assertEqual(result, {**self.mock_afi_data, "region": self.region})

        with patch.multiple(
            "create_afi.UserInterface", get_input=MagicMock(side_effect=["New AFI", "New Description"])
        ):
            with patch.multiple(
                "create_afi.S3Manager",
                get_s3_paths_interactive=MagicMock(return_value=("dcp/path", "logs/path")),
                get_bucket_interactive=MagicMock(return_value="test-bucket"),
            ):
                with patch.multiple(
                    "create_afi.DCPDiscovery", get_dcp_path_interactive=MagicMock(return_value="/path/to/dcp")
                ):
                    result = AFICreator(self.region, interactive=True)._complete_afi_data({})
                    self.assertEqual(result["name"], "New AFI")
                    self.assertEqual(result["description"], "New Description")

    @patch("time.sleep")
    def test_polling_scenarios(self, mock_sleep):
        self.afi_creator.ec2_client = MagicMock()

        test_cases = [
            ({"Code": "available"}, "🎉 AFI creation completed successfully!"),
            ({"Code": "failed"}, "❌ AFI creation failed: failed"),
            ({"Code": "unavailable", "Message": "Error message"}, "Error: Error message"),
        ]

        # Capture all output
        for state, expected_output in test_cases:
            self.afi_creator.ec2_client.describe_fpga_images.return_value = {"FpgaImages": [{"State": state}]}
            self.afi_creator._poll_afi_status("afi-12345", 60)
            self.assertIn(expected_output, self.output.getvalue())
            self.output.truncate(0)
            self.output.seek(0)

        # Test interrupts
        mock_sleep.side_effect = KeyboardInterrupt()
        self.afi_creator.ec2_client.describe_fpga_images.return_value = {"FpgaImages": [{"State": {"Code": "pending"}}]}
        self.afi_creator._poll_afi_status("afi-12345", 60)
        self.assertIn("Polling stopped", self.output.getvalue())
        self.output.truncate(0)
        self.output.seek(0)

        # Test generic exception
        self.afi_creator.ec2_client.describe_fpga_images.side_effect = Exception("Test error")
        self.afi_creator._poll_afi_status("afi-12345", 60)
        self.assertIn("Error polling AFI status: Test error", self.output.getvalue())

    @patch.object(DCPDiscovery, "find_hdk_dir")
    def test_provide_next_steps(self, mock_find_hdk):
        for hdk_dir in ["/path/to/hdk", None]:
            mock_find_hdk.return_value = hdk_dir
            self.afi_creator.provide_next_steps("agfi-12345")


class TestAFIManager(unittest.TestCase):
    def setUp(self):
        self.afi_manager = AFIManager()
        self.mock_args = Mock(interactive=False, region="us-east-1", create_bucket=False, poll_interval=30)
        self.mock_result = {"FpgaImageId": "afi-12345", "FpgaImageGlobalId": "agfi-67890"}

    @patch.object(UserInterface, "get_choice_from_options")
    def test_handle_interactive_mode(self, mock_get_choice):
        # Test non-interactive mode
        result = self.afi_manager.handle_interactive_mode(self.mock_args)
        self.assertEqual(result, "us-east-1")
        mock_get_choice.assert_not_called()

        # Test interactive mode with no region
        self.mock_args.interactive = True
        self.mock_args.region = None
        mock_get_choice.return_value = 0

        with patch("create_afi.supported_regions", ["us-east-1", "us-west-2"]):
            result = self.afi_manager.handle_interactive_mode(self.mock_args)

        self.assertEqual(result, "us-east-1")
        mock_get_choice.assert_called_once()

    @patch.object(AFICreator, "create_afi")
    @patch.object(AFICreator, "provide_next_steps")
    def test_create_afi_request(self, mock_provide_steps, mock_create_afi):
        mock_create_afi.return_value = self.mock_result

        with patch.object(self.afi_manager, "print_success") as mock_print_success:
            result = self.afi_manager.create_afi_request(self.mock_args, "us-east-1")

        self.assertEqual(result, self.mock_result)
        mock_create_afi.assert_called_once_with(
            afi_data=vars(self.mock_args),
            create_bucket=self.mock_args.create_bucket,
            poll_interval=self.mock_args.poll_interval,
        )
        mock_provide_steps.assert_called_once_with("agfi-67890")
        mock_print_success.assert_called_once_with(self.mock_result, "us-east-1", False)

    def test_print_success(self):
        test_cases = [
            (True, 3),  # Interactive mode: 3 prints
            (False, 5),  # Non-interactive mode: 5 prints
        ]

        for interactive, expected_prints in test_cases:
            with self.subTest(interactive=interactive):
                with patch("builtins.print") as mock_print:
                    AFIManager.print_success(self.mock_result, "us-east-1", interactive)
                    self.assertEqual(mock_print.call_count, expected_prints)

                    # Verify the content of print calls
                    calls = [str(call) for call in mock_print.call_args_list]
                    self.assertIn("AFI creation request submitted successfully", calls[0])
                    self.assertIn("afi-12345", calls[1])
                    self.assertIn("agfi-67890", calls[2])

                    if not interactive:
                        self.assertIn("Monitor progress with", calls[3])
                        self.assertIn("describe-fpga-images", calls[4])


class TestMain(unittest.TestCase):
    @patch("create_afi.parser.parse_args")
    def test_parser_exit_scenarios(self, mock_parse_args):
        # Test successful parse
        mock_parse_args.side_effect = SystemExit(0)
        self.assertEqual(main(), 0)

        # Test parser error
        mock_parse_args.side_effect = SystemExit(1)
        self.assertEqual(main(), 1)

    @patch("create_afi.parser.parse_args")
    @patch.object(AFIManager, "handle_interactive_mode")
    @patch.object(RegionManager, "validate_region_supports_f2")
    @patch.object(AFIManager, "create_afi_request")
    def test_main_success(self, mock_create, mock_validate, mock_handle, mock_parse_args):
        mock_args = Mock()
        mock_parse_args.return_value = mock_args
        mock_handle.return_value = "us-east-1"

        self.assertEqual(main(), 0)
        mock_handle.assert_called_once_with(mock_args)
        mock_validate.assert_called_once_with("us-east-1")
        mock_create.assert_called_once_with(mock_args, "us-east-1")

    @patch("create_afi.parser.parse_args")
    @patch.object(AFIManager, "handle_interactive_mode")
    def test_main_keyboard_interrupt(self, mock_handle, mock_parse_args):
        mock_parse_args.return_value = Mock()
        mock_handle.side_effect = KeyboardInterrupt()

        with patch("builtins.print") as mock_print:
            self.assertEqual(main(), 1)
            # Verify error message was printed
            mock_print.assert_any_call("\n⚠️  Operation cancelled by user", file=sys.stderr)

    @patch("create_afi.parser.parse_args")
    @patch.object(AFIManager, "handle_interactive_mode")
    @patch("traceback.print_exc")
    def test_main_generic_exception(self, mock_traceback, mock_handle, mock_parse_args):
        mock_parse_args.return_value = Mock()
        mock_handle.side_effect = Exception("test error")

        with patch("builtins.print") as mock_print:
            self.assertEqual(main(), 1)
            # Verify error message was printed
            mock_print.assert_any_call("❌ Error: test error", file=sys.stderr)
            mock_traceback.assert_called_once()


if __name__ == "__main__":
    try:
        unittest.main(exit=False, buffer=True)
    except SystemExit:
        pass
    cov.stop()
    cov.save()
    cov.report(
        show_missing=True,
        skip_covered=True,  # Only show files that have missing lines
        skip_empty=True,  # Skip files with no executable statements
    )
    # Optional: Generate HTML report
    # cov.html_report()
