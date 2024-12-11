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

# Script must be sourced from a bash shell or it will not work
# When being sourced $0 will be the interactive shell and $BASH_SOURCE_ will contain the script being sourced
# When being run $0 and $_ will be the same.

script=${BASH_SOURCE[0]}
if [ $script == $0 ]; then
  echo "ERROR: You must source this script"
  exit 2
fi

full_script=$(readlink -f $script)
script_name=$(basename $full_script)
script_dir=$(dirname $full_script)
current_dir=$(pwd)

debug=0

function usage {
  echo -e "USAGE: source [\$AWS_FPGA_REPO_DIR/]$script_name [-d|-debug] [-h|-help]"
}

function help {
  info_msg "$script_name"
  info_msg " "
  info_msg "Sets up the environment for AWS FPGA HDK tools."
  info_msg " "
  info_msg "hdk_setup.sh script will:"
  info_msg "  (1) Check if Xilinx Vivado is installed,"
  info_msg "  (2) Set up key environment variables HDK_*, and"
  echo " "
  usage
}

function sha256_check {
    sha_file=$1
    xsa_file=$2
    s3_sha=$(awk '{print $1}' $sha_file)
    local_sha=$(sha256sum "$2" | awk '{print $1}')

    if [[ "$s3_sha" != "$local_sha" ]]; then
        err_msg "SHA256 mismatch for $2"
        info_msg "  Expected: $s3_sha"
        info_msg "  Actual:   $local_sha"
        info_msg "Moving existing $2 to $2.back"
        mv $2 $2.back
        err_msg "HDK setup has FAILED!!!"
        return 1
    fi

    return 0
}

# Process command line args
args=("$@")
for ((i = 0; i < ${#args[@]}; i++)); do
  arg=${args[$i]}
  case $arg in
  -d | -debug)
    debug=1
    ;;
  -h | -help)
    help
    return 0
    ;;
  *)
    err_msg "Invalid option: $arg\n"
    usage
    return 1
    ;;
  esac
done

if ! source $script_dir/shared/bin/set_common_functions.sh; then
  err_msg "Couldn't set up common functions for HDK! Exiting!"
  return 1
fi
if ! source $script_dir/shared/bin/set_common_env_vars.sh; then
  err_msg "Couldn't set up env vars for HDK! Exiting!"
  return 1
fi

debug_msg "Checking for Vivado install:"

# before going too far make sure Vivado is available
if ! is_vivado_available; then
  err_msg "Please install/enable Vivado."
  err_msg "  If you are using the FPGA Developer AMI then please open an issue on GitHub."
  return 1
fi

# Searching for Vivado version and comparing it with the list of supported versions
export VIVADO_VER=$(vivado -version | grep -i Vivado | head -1)
info_msg "Using $VIVADO_VER"

VIVADO_VERSION_CHECK=0
check_vivado_version "$VIVADO_VER" $AWS_FPGA_REPO_DIR/supported_vivado_versions.txt 0

if [ $VIVADO_VERSION_CHECK -eq 1 ]; then
  debug_msg "$VIVADO_VER is supported by this HDK release."
else
  err_msg "$VIVADO_VER is not supported by this HDK release."
  err_msg "Supported versions are:"
  cat $AWS_FPGA_REPO_DIR/supported_vivado_versions.txt
  return 1
fi

VIVADO_TOOL_VERSION=$(vivado -version | grep -i Vivado | head -1 | sed 's/[Vv]ivado v//' | sed 's/^\(.\{7\}\).*$/\1/')
export VIVADO_TOOL_VERSION=${VIVADO_TOOL_VERSION:0:7}
info_msg "VIVADO_TOOL_VERSION is $VIVADO_TOOL_VERSION"

debug_msg "Vivado check succeeded"

# The CL_DIR is where the actual Custom Logic design resides. The developer is expected to override this.
# export CL_DIR=$HDK_DIR/cl/developer_designs

debug_msg "Done setting environment variables."

# Shell release version
shell_ver_file=$HDK_SHELL_DIR/shell_version.txt

# Shell files to be downloaded
declare -a s3_hdk_files=("cl_bb_routed.small_shell.dcp")

# Downloading the shell files
for shell_file in "${s3_hdk_files[@]}"; do
  sub_dir="checkpoints"
  hdk_shell_dir=$HDK_SHELL_DIR/build/$sub_dir
  hdk_shell_dir_from_aws=$hdk_shell_dir/from_aws
  hdk_file=$hdk_shell_dir_from_aws/$shell_file
  hdk_file_sha256=$hdk_shell_dir_from_aws/$shell_file.sha256
  shell_file_sha256=$shell_file.sha256

  if [ ! -d $hdk_shell_dir ]; then
    if ! mkdir $hdk_shell_dir; then
      err_msg "Failed to create $hdk_shell_dir"
      return 2
    fi
  fi

  if [ ! -d $hdk_shell_dir_from_aws ]; then
    if ! mkdir $hdk_shell_dir_from_aws; then
      err_msg "Failed to create $hdk_shell_dir_from_aws"
      return 2
    fi
  fi

  shell_type=$(echo $shell_file | cut -d'.' -f2)
  shell_ver=$(cat $shell_ver_file | grep "$shell_type" | cut -d '=' -f2)

  s3_hdk_dir_url=https://aws-fpga-hdk-resources.s3.amazonaws.com/hdk
  s3_shell_dir=${s3_hdk_dir_url}/shell_v${shell_ver:2}

  if ! wget $s3_shell_dir/$shell_file -O $hdk_file -q; then
    err_msg "Failed to download HDK shell $shell_file version $shell_ver"
    return 2
  fi

  if ! wget $s3_shell_dir/$shell_file_sha256 -O $hdk_file_sha256 -q; then
    err_msg "Failed to download HDK shell $shell_file_sha256 version $shell_ver"
    return 2
  fi
  sha256_check $hdk_file_sha256 $hdk_file
  if [ $? -ne 0 ]; then
    return 1
  fi
done

info_msg "HDK shell is up-to-date"

if [[ ":$CL_DIR" == ':' ]]; then
  warn_msg "Don't forget to set the CL_DIR variable for the directory of your Custom Logic."
else
  info_msg "CL_DIR is $CL_DIR"
  if [ ! -d $CL_DIR ]; then
    err_msg "CL_DIR doesn't exist. Set CL_DIR to a valid directory."
    unset CL_DIR
  fi
fi

cd $current_dir

info_msg "AWS HDK setup PASSED."
