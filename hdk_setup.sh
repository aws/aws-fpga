# Amazon FPGA Hardware Development Kit
#
# Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
  info_msg "  (3) Download/update the HDK shell's checkpoint"
  info_msg "  (4) Prepare DRAM controller and PCIe IP modules if they are not already available in your directory."
  echo " "
  usage
}

# Process command line args
args=( "$@" )
for (( i = 0; i < ${#args[@]}; i++ )); do
  arg=${args[$i]}
  case $arg in
    -d|-debug)
      debug=1
    ;;
    -h|-help)
      help
      return 0
    ;;
    *)
      err_msg "Invalid option: $arg\n"
      usage
      return 1
  esac
done

source $script_dir/shared/bin/set_common_functions.sh
source $script_dir/shared/bin/set_common_env_vars.sh

hdk_shell_version=$(readlink $HDK_COMMON_DIR/shell_stable)

debug_msg "Checking for Vivado install:"

# before going too far make sure Vivado is available
if ! exists vivado; then
    err_msg "Please install/enable Vivado."
    err_msg "  If you are using the FPGA Developer AMI then please request support."
    return 1
fi

# Install any patches as required
info_msg "Setting up Vivado patches if required."
setup_patches

#Searching for Vivado version and comparing it with the list of supported versions

export VIVADO_VER=`vivado -version | grep Vivado | head -1`

info_msg "Using $VIVADO_VER"

if grep -Fxq "$VIVADO_VER" $AWS_FPGA_REPO_DIR/supported_vivado_versions.txt
then
    debug_msg "$VIVADO_VER is supported by this HDK release."
else
    err_msg "$VIVADO_VER is not supported by this HDK release."
    err_msg "Supported versions are:"
    cat $AWS_FPGA_REPO_DIR/supported_vivado_versions.txt
    return 1
fi

VIVADO_TOOL_VERSION=`vivado -version | grep Vivado | head -1 | sed 's:Vivado *::' | sed 's: .*$::'`
export VIVADO_TOOL_VERSION=${VIVADO_TOOL_VERSION:0:7}
echo "VIVADO_TOOL_VERSION is $VIVADO_TOOL_VERSION"

debug_msg "Vivado check succeeded"

# The CL_DIR is where the actual Custom Logic design resides. The developer is expected to override this.
# export CL_DIR=$HDK_DIR/cl/developer_designs

debug_msg "Done setting environment variables.";

# Download correct shell DCP
info_msg "Using HDK shell version $hdk_shell_version"
debug_msg "Checking HDK shell's checkpoint version"
hdk_resources_s3_bucket=aws-fpga-hdk-resources

# Shell files to be downloaded
declare -a s3_hdk_files=("SH_CL_BB_routed.dcp"
                         "cl_hello_world.debug_probes.ltx"
                         "cl_dram_dma.debug_probes.ltx"
                        )
# Downloading the shell files
for shell_file in "${s3_hdk_files[@]}"
do
  # Determine if shell or debug probe
  if [ $shell_file == "SH_CL_BB_routed.dcp" ]; then
    sub_dir="checkpoints"
  else
    sub_dir="debug_probes"
  fi
  hdk_shell_dir=$HDK_SHELL_DIR/build/$sub_dir/from_aws
  hdk_file=$hdk_shell_dir/$shell_file
  s3_shell_dir=hdk/$hdk_shell_version/build/$sub_dir/from_aws
  # Download the sha256
  if [ ! -e $hdk_shell_dir ]; then
      mkdir -p $hdk_shell_dir || { err_msg "Failed to create $hdk_shell_dir"; return 2; }
  fi
  # Use curl instead of AWS CLI so that credentials aren't required.
  debug_msg "curl -s https://$hdk_resources_s3_bucket.s3.amazonaws.com/$s3_shell_dir/$shell_file.sha256 -o $hdk_file.sha256"
  curl -s https://$hdk_resources_s3_bucket.s3.amazonaws.com/$s3_shell_dir/$shell_file.sha256 -o $hdk_file.sha256 || { err_msg "Failed to download HDK shell's $shell_file version from $s3_shell_dir/$shell_file.sha256 -o $hdk_file.sha256"; return 2; }
  if grep -q '<?xml version' $hdk_file.sha256; then
    err_msg "Failed to download HDK shell's $shell_file version from $s3_shell_dir/$shell_file.sha256"
    cat $hdk_file.sha256
    return 2
  fi
  exp_sha256=$(cat $hdk_file.sha256)
  debug_msg "  $shell_file latest   version=$exp_sha256"
  # If shell file already downloaded check its sha256
  if [ -e $hdk_file ]; then
    act_sha256=$( sha256sum $hdk_file | awk '{ print $1 }' )
    debug_msg "  $shell_file existing version=$act_sha256"
    if [[ $act_sha256 != $exp_sha256 ]]; then
      info_msg "HDK shell's $shell_file version is incorrect"
      info_msg "  Saving old file to $hdk_file.back"
      mv $hdk_file $hdk_file.back
    fi
  else
    info_msg "HDK shell's $shell_file hasn't been downloaded yet."
  fi
  if [ ! -e $hdk_file ]; then
    info_msg "Downloading latest HDK shell $shell_file from $s3_shell_dir/$shell_file"
    # Use curl instead of AWS CLI so that credentials aren't required.
    curl -s https://$hdk_resources_s3_bucket.s3.amazonaws.com/$s3_shell_dir/$shell_file -o $hdk_file || { err_msg "HDK shell checkpoint download failed"; return 2; }
  fi

  # Check sha256
  act_sha256=$( sha256sum $hdk_file | awk '{ print $1 }' )
  if [[ $act_sha256 != $exp_sha256 ]]; then
    err_msg "Incorrect HDK shell checkpoint version:"
    err_msg "  expected version=$exp_sha256"
    err_msg "  actual   version=$act_sha256"
    err_msg "  There may be an issue with the uploaded checkpoint or the download failed."
    return 2
  fi
  info_msg "HDK shell is up-to-date"
done

# Create DDR and PCIe IP models and patch PCIe
models_dir=$HDK_COMMON_DIR/verif/models
ddr4_model_dir=$models_dir/ddr4_model
if [ -f $ddr4_model_dir/arch_defines.v ]; then
  # Models already built
  # Check to make sure they were built with this version of vivado
  if [[ -f $models_dir/.vivado_version ]]; then
    models_vivado_version=$(cat $models_dir/.vivado_version)
    info_msg "DDR4 model files in $ddr4_model_dir/ were built with $models_vivado_version"
    if [[ $models_vivado_version != $VIVADO_VER ]]; then
      info_msg "  Wrong vivado version so rebuilding with $VIVADO_VER"
    fi
  else
    models_vivado_version=UNKNOWN
    info_msg "DDR4 model files in $ddr4_model_dir/ were built with UNKNOWN Vivado version so rebuilding."
  fi
else
  # Models haven't been built
  models_vivado_version=NOT_BUILT
  info_msg "DDR4 model files in "$ddr4_model_dir/" do NOT exist. Running model creation step.";
fi
if [[ $models_vivado_version != $VIVADO_VER ]] && [ ! -e $models_dir/build.lock ]; then
  rm -rf $HDK_COMMON_DIR/verif/scripts/.done 2>&1 >/dev/null
fi
ddr4_build_dir=$HDK_COMMON_DIR/verif/scripts/tmp
if [ -d $ddr4_build_dir ] && [ ! -e $models_dir/build.lock ]; then rm -rf $ddr4_build_dir; fi
if ! make -s -C $HDK_DIR/common/verif/scripts MODEL_DIR=$models_dir; then
  err_msg "  build dir=$ddr4_build_dir"
  return 2
fi

if [[ ":$CL_DIR" == ':' ]]; then
  info_msg "attention: don't forget to set the CL_DIR variable for the directory of your custom logic.";
else
  info_msg "CL_DIR is $CL_DIR"
  if [ ! -d $CL_DIR ]; then
    err_msg "CL_DIR doesn't exist. set CL_DIR to a valid directory."
    unset CL_DIR
  fi
fi

cd $current_dir

info_msg "AWS HDK setup PASSED.";
