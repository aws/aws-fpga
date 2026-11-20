#!/bin/bash

# Amazon FPGA Hardware Development Kit
#
# Copyright 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

set -e

script=${BASH_SOURCE[0]}
full_script=$(readlink -f "$script")
script_name=$(basename "$full_script")
script_dir=$(dirname "$full_script")

# Help and argument errors must work before vitis_setup.sh has been sourced.
if ! source "$script_dir/../../shared/bin/set_common_functions.sh"; then
    echo "ERROR: Couldn't set up common functions!" >&2
    exit 1
fi


function usage {
    info_msg "USAGE: $script_name"
    info_msg "             -h|-help|--help"
    info_msg "             -s3_bucket=<bucket_name>"
    info_msg "             -s3_dcp_key=<S3_folder_of_dcp>"
    info_msg "             -s3_logs_key=<S3_folder_of_logs>"
    info_msg "             -xclbin=<xclbin_filename>"
    info_msg "             -o=<awsxclbin_filename>"
    info_msg "             -aws_profile_name=<aws_profile_name> !!! OPTIONAL !!!"
    info_msg "             -region=<aws_region_name>"
}


function help {
    info_msg "$script_name"
    info_msg " "
    info_msg "Vitis AFI Creation"
    info_msg " "
    info_msg "create_vitis_afi.sh assumes you have:"
    info_msg "  (*) Sourced vitis_setup.sh with Vitis ${MINIMUM_VITIS_TOOL_VER} or later.  AFIs are not supported on earlier tool versions."
    info_msg "  (*) Read the README on Github and understand the Vitis workflow (Vitis/README.md)"
    info_msg "  (*) Generated an XCLBIN using the Vitis Build flow"
    info_msg "  (*) Ready to create an AFI and test on F2.  Your kernel has been validated using HW Emulation."
    info_msg "create_vitis_afi.sh will:"
    info_msg "  (1) Extract three parts from your XCLBIN:  DCP (.dcp) , clocks data(.json) and build metadata (.json)"
    info_msg "  (2) Generate a Manifest file for AFI creation that sets the clocks based on your achieved target freq from your build"
    info_msg "  (3) Prepare tar file for AFI creation process"
    info_msg "  (4) Call aws ec2 create-fpga-image"
    info_msg "  (5) Create new XCLBIN (called AWSXCLBIN) using Metadata and AGFI-ID"
    echo " "
    usage
}


# Vitis rejects the 2024.2-built XDMA platform on earlier tool versions.
MINIMUM_VITIS_TOOL_VER="2024.2"

function preflight_checks {
    if [[ -z $AWS_FPGA_REPO_DIR ]]; then
        err_msg "\$AWS_FPGA_REPO_DIR not set! Please source vitis_setup.sh from this repository's root directory"
        exit 1
    fi

    if [ -z "$VITIS_TOOL_VER" ]; then
        err_msg "Env variable VITIS_TOOL_VER not set, did you source vitis_setup.sh?"
        exit 1
    fi

    if [ -z "$PLATFORM_REPO_PATHS" ]; then
        err_msg "Env variable PLATFORM_REPO_PATHS not set, did you source vitis_setup.sh?"
        exit 1
    fi

    if [[ "$(printf '%s\n' "$MINIMUM_VITIS_TOOL_VER" "$VITIS_TOOL_VER" | sort -V | head -n 1)" != "$MINIMUM_VITIS_TOOL_VER" ]]; then
        err_msg "Vitis AFIs require Vitis ${MINIMUM_VITIS_TOOL_VER} or later, but VITIS_TOOL_VER is ${VITIS_TOOL_VER}!!!"
        exit 1
    fi

    if ! command -v python3 >/dev/null; then
        err_msg "python3 is required to validate the AFI creation response"
        exit 1
    fi

    if [[ -z "${s3_bucket}" ]]; then
        err_msg "S3 Bucket not defined!!!"
        usage
        exit 1
    fi

    if [[ -z "${s3_dcps}" ]]; then
        err_msg "S3 DCP Key not defined!!!"
        usage
        exit 1
    fi

    if [[ -z "${s3_logs}" ]]; then
        err_msg "S3 Logs Key not defined!!!"
        usage
        exit 1
    fi

    if [[ -z "${xclbin}" ]]; then
        err_msg "Input XCLBIN file not defined!!!"
        usage
        exit 1
    fi

    if [[ -z "${awsxclbin}" ]]; then
        err_msg "Output AWS XCLBIN name not defined!!!"
        usage
        exit 1
    fi

    if [[ -z "${region}" ]]; then
        err_msg "Instance region not defined!!!"
        usage
        exit 1
    fi
}


function args_check {
    if [[ ! -e "$xclbin" ]]; then
        err_msg "No XCLBIN file found !!!"
        exit 1
    fi
    info_msg "Found xclbin '$xclbin'"

    stripped_xclbin=$(basename "$xclbin")
    ext_xclbin=${stripped_xclbin##*.}
    stripped_xclbin=${stripped_xclbin%.*}
    description="${stripped_xclbin}_Vitis"

    info_msg "$stripped_xclbin"

    if [ -z "$awsxclbin" ]; then
        awsxclbin=$stripped_xclbin
    fi

    if [ "$awsxclbin" != "$stripped_xclbin" ]; then
        warn_msg "$awsxclbin does not match $stripped_xclbin"
        warn_msg "For github examples, -o <xclbin_filename> must be equal to $stripped_xclbin"
    fi

    if [[ -e "${awsxclbin}.awsxclbin" ]]; then
        err_msg "File '${awsxclbin}.awsxclbin' already exists"
        exit 1
    fi

    if [ ":$s3_bucket" == ":" ]; then
        err_msg "Invalid s3_bucket"
        usage
        exit 1
    fi

    # s3 dcp key and s3 logs key are required
    if [ -z "$s3_dcps" ]; then
        err_msg "Invalid s3_dcps key"
        usage
        exit 1
    fi
}


#Steps
#1. Strip XCLBIN to get DCP for ingestion
#2. Create Manifest file
#3. Prepare ingestion tar file
#4. Call create-fpga-image
#5. Manipulate the AFI ID
#6. Create awsxclbin


#STEP 1
#Strip XCLBIN to get DCP for ingestion
#/opt/xilinx/xrt/bin/xclbinsplit -o ${timestamp} $xclbin
function extract_dcp {
    timestamp=$(date +"%Y_%m_%d-%H%M%S")

    /opt/xilinx/xrt/bin/xclbinutil --dump-section BUILD_METADATA:JSON:${timestamp}_build.json --dump-section CLOCK_FREQ_TOPOLOGY:JSON:${timestamp}_clocks.json --dump-section BITSTREAM:RAW:${timestamp}_SH_CL_routed.dcp -i "$xclbin"

    if [[ ! -e "${timestamp}_SH_CL_routed.dcp" ]]; then
        err_msg "File ${timestamp}_SH_CL_routed.dcp not found"
        exit 1
    fi
    info_msg "Split DCP from xclbin: ${timestamp}_SH_CL_routed.dcp"

    if [[ ! -e "${timestamp}_build.json" ]]; then
        err_msg "File ${timestamp}_build.json not found"
        exit 1
    fi
    info_msg "The build Metadata from xclbin: ${timestamp}_build.json"

    if [[ ! -e "${timestamp}_clocks.json" ]]; then
        err_msg "File ${timestamp}_clocks.json not found"
        exit 1
    fi
    info_msg "The clocks Metadata from xclbin: ${timestamp}_clocks.json"

    # An earlier run that failed after this point leaves to_aws behind. Move it aside instead of failing,
    # and remove it once the tarball for this run is built.
    to_aws_backup=""
    if [[ -d "to_aws" ]]; then
        to_aws_backup="to_aws_backup_${timestamp}"
        warn_msg "Directory to_aws already exists from an earlier run. Moving it to ${to_aws_backup}"
        if ! mv to_aws "${to_aws_backup}"; then
            err_msg "Couldn't move the existing to_aws directory aside"
            exit 1
        fi
    fi

    mkdir to_aws
    cp ${timestamp}_SH_CL_routed.dcp ./to_aws/
}


declare -A valid_shell_versions
valid_shell_versions['2024.2:0x10052623']="true"
valid_shell_versions['2025.1:0x10052623']="true"
valid_shell_versions['2025.2:0x10052623']="true"

declare -A xsa_to_shell_map
xsa_to_shell_map['202420_3']="0x10052623"

# Runs before extract_dcp so that rejecting the platform leaves no to_aws/ behind
# and the rebuild advice below can be followed from the same directory.
function resolve_shell_version {
    export MAJOR_MINOR=$(ls $PLATFORM_REPO_PATHS/*.xpfm | sed -E 's/.*xilinx_aws-vu47p-f2_([0-9]+_[0-9_]+)\.xpfm/\1/')
    shell_version="${xsa_to_shell_map[$MAJOR_MINOR]}"
    if [[ -z "${shell_version}" ]]; then
        err_msg "Platform xilinx_aws-vu47p-f2_${MAJOR_MINOR} is not supported!!!"
        info_msg "Supported platform versions: ${!xsa_to_shell_map[*]}"
        info_msg "Source vitis_setup.sh again to install a supported platform, then rebuild the xclbin."
        exit 1
    fi

    tool_shell_combo="${VITIS_TOOL_VER}:${shell_version}"
    if [[ "${valid_shell_versions[$tool_shell_combo]}" != "true" ]]; then
        err_msg "Shell and tool version: ${shell_version}/${VITIS_TOOL_VER} is not supported!!!"
        exit 1
    fi
}

#STEP 2
# Create Manifest file
function create_manifest {
    tool_version="v${VITIS_TOOL_VER}"
    device_id=0xF010
    vendor_id=0x1D0F
    subsystem_id=0x1D51
    subsystem_vendor_id=0xFEDD

    # Get XSA info from build metadata
    vendor=$(echo $(grep -A 6 dsa ./${timestamp}_build.json | grep vendor | sed 's/.*: "//g' | sed 's/",//'))
    board_id=$(echo $(grep -A 6 dsa ./${timestamp}_build.json | grep board_id | sed 's/.*: "//g' | sed 's/",//'))
    plat_name=$(echo $(grep -A 6 dsa ./${timestamp}_build.json | grep name | sed 's/.*: "//g' | sed 's/",//'))
    major=$(echo $(grep -A 6 dsa ./${timestamp}_build.json | grep major | sed 's/.*: "//g' | sed 's/",//'))
    minor=$(echo $(grep -A 6 dsa ./${timestamp}_build.json | grep minor | sed 's/.*: "//g' | sed 's/",//'))

    # Get clock info from clock metadata
    read -a clock_main_a0 <<<"$(echo $(grep -B 1 SYSTEM ${timestamp}_clocks.json | grep -o -e '[0-9]*'))"
    clock_main_a0=$(echo ${clock_main_a0[0]})
    clock_extra_b0=$(echo $(grep -B 2 KERNEL_CLK ${timestamp}_clocks.json | grep -o -e '[0-9]*'))
    clock_extra_c0=$(echo $(grep -B 2 DATA_CLK ${timestamp}_clocks.json | grep freq | grep -o -e '[0-9]*'))
    clock_hbm_axi=$(echo $(grep -B 2 clk_out1_clk_mmcm_hbm ${timestamp}_clocks.json | grep -o -e '[0-9][0-9][0-9]*'))

    invalid_config=0
    if [[ "$vendor" != "xilinx" ]]; then
        err_msg "Vendor: ${vendor} is not supported!!!"
        invalid_config=1
    fi

    if [[ "$board_id" != "aws-vu47p-f2" ]]; then
        err_msg "Board ID: ${board_id} is not supported!!!"
        invalid_config=1
    fi

    if [[ "$plat_name" != "xdma-shell-v${shell_version:2}" ]]; then
        err_msg "Platform: ${plat_name} is not supported!!!"
        invalid_config=1
    fi

    if [[ $invalid_config -ne 0 ]]; then
        err_msg "Platform ${vendor}_${board_id}_${plat_name}_${major}_${minor} used to create xclbin is invalid!!!"
        info_msg "Supported config for given tool and shell:"
        info_msg "    xilinx_aws-vu47p-f2_xdma-shell-v${shell_version:2}_${MAJOR_MINOR}"
        exit 1
    fi

    # Write Manifest File here
    hash=$(sha256sum to_aws/${timestamp}_SH_CL_routed.dcp | awk '{ print $1 }')
    manifest_file="${timestamp}_manifest.txt"
    exec 3<>$manifest_file
    echo "manifest_format_version=2" >&3
    echo "pci_vendor_id=$vendor_id" >&3
    echo "pci_device_id=$device_id" >&3
    echo "pci_subsystem_id=$subsystem_id" >&3
    echo "pci_subsystem_vendor_id=$subsystem_vendor_id" >&3
    echo "dcp_hash=$hash" >&3
    echo "shell_version=$shell_version" >&3
    echo "dcp_file_name=${timestamp}_SH_CL_routed.dcp" >&3
    echo "tool_version=$tool_version" >&3
    echo "date=$timestamp" >&3
    echo "clock_main_a0=$clock_main_a0" >&3
    echo "clock_extra_b0=$clock_extra_b0" >&3
    echo "clock_extra_c0=$clock_extra_c0" >&3
    echo "clock_hbm_axi=$clock_hbm_axi" >&3
    exec 3>&-

    if [[ ! -e "$manifest_file" ]]; then
        err_msg "File '$manifest_file' not found"
        exit 1
    fi

    info_msg "Generated manifest file '$manifest_file'"
    cp $manifest_file to_aws/$manifest_file
}


#STEP 3
#Prepare ingestion
function ingestion_prep {
    if ! tar -cf ${timestamp}_Developer_Vitis_Kernel.tar to_aws/${timestamp}_SH_CL_routed.dcp to_aws/${timestamp}_manifest.txt; then
        err_msg "Couldn't create ${timestamp}_Developer_Vitis_Kernel.tar"
        exit 1
    fi

    if [[ -n "${to_aws_backup}" ]]; then
        rm -rf "${to_aws_backup}"
    fi
}


#STEP 4
#Call create-fpga-image
function call_create_fpga_image {
    profile_text=""
    if [ "$aws_profile_name" != "" ]; then
        profile_text="--profile ${aws_profile_name}"
    fi

    log_storage_text=""
    if [ "${s3_logs}" != "" ]; then
        log_storage_text="--logs-storage-location Bucket=${s3_bucket},Key=${s3_logs}"
    fi

    if ! aws s3 ${profile_text} --region ${region} cp ${timestamp}_Developer_Vitis_Kernel.tar s3://${s3_bucket}/${s3_dcps}/; then
        err_msg "Couldn't copy files to s3://${s3_bucket}/${s3_dcps}/"
        exit 1
    fi

    if ! aws ec2 ${profile_text} create-fpga-image --name ${stripped_xclbin} --description ${description} --input-storage-location Bucket=${s3_bucket},Key=${s3_dcps}/${timestamp}_Developer_Vitis_Kernel.tar --region ${region} ${log_storage_text} --output json >${timestamp}_afi_id.txt; then
        err_msg "Failed to create AFI from .xclbin file!"
        exit 1
    fi
}


#STEP 5
#Manipulate the AFI ID
function set_afi_id {
    local agfi_id
    if ! agfi_id=$(python3 - "${timestamp}_afi_id.txt" <<'PY'
import json
import re
import sys

try:
    with open(sys.argv[1]) as response_file:
        response = json.load(response_file)
except (OSError, ValueError):
    sys.exit("Invalid JSON in AFI creation response")

agfi = response.get("FpgaImageGlobalId") if isinstance(response, dict) else None
if not isinstance(agfi, str) or not re.fullmatch(r"agfi-[0-9a-f]{17}", agfi):
    sys.exit("Missing or invalid FpgaImageGlobalId in AFI creation response")
print(agfi)
PY
    ); then
        err_msg "Couldn't extract a valid FpgaImageGlobalId from ${timestamp}_afi_id.txt"
        exit 1
    fi
    printf '%s' "$agfi_id" >"${timestamp}_agfi_id.txt"
    echo ${timestamp}_agfi_id.txt
}


#STEP 6
#Create .awsxclbin
function create_awsxclbin {
    if ! /opt/xilinx/xrt/bin/xclbinutil -i "$xclbin" --remove-section PARTITION_METADATA --replace-section BITSTREAM:RAW:${timestamp}_agfi_id.txt -o ${awsxclbin}.awsxclbin; then
        err_msg "Failed to create an AWSXCLBIN!!!"
        exit 1
    fi
}


function main {
    preflight_checks
    args_check
    resolve_shell_version
    extract_dcp
    create_manifest
    ingestion_prep
    call_create_fpga_image
    set_afi_id
    create_awsxclbin
}


while (( $# )); do
    case "${1%%=*}" in
        -h|-help|--help)
            help
            exit
            ;;
        -xclbin|-o|-aws_profile_name|-s3_bucket|-s3_logs_key|-s3_dcp_key|-region)
            if [[ "$1" == *=* ]]; then
                VALUE="${1#*=}"
                PARAM="${1%%=*}"
            elif [[ -n "${2:-}" && "$2" != -* ]]; then
                VALUE="$2"
                PARAM="$1"
                shift
            else
                err_msg "Missing value for parameter \"$1\""
                usage
                exit 1
            fi

            case "$PARAM" in
                -xclbin)           xclbin="$VALUE" ;;
                -o)                awsxclbin="$VALUE" ;;
                -aws_profile_name) aws_profile_name="$VALUE" ;;
                -s3_bucket)        s3_bucket="$VALUE" ;;
                -s3_logs_key)      s3_logs="$VALUE" ;;
                -s3_dcp_key)       s3_dcps="$VALUE" ;;
                -region)           region="$VALUE" ;;
            esac
            ;;
        *)
            err_msg "Unknown parameter \"$1\""
            usage
            exit 1
            ;;
    esac
    shift
done

main
