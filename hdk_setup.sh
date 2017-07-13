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

debug=0

# This function checks if an environment module exists
# Returns 0 if it exists, and returns 1 if it doesn't
function does_module_exist() {

    output=`/usr/bin/ls /usr/local/Modules/$MODULE_VERSION/modulefiles | grep $1`

    if [[ $output == "$1" ]]; then
        return 0;
    else
        return 1;
    fi
}


function info_msg {
  echo -e "INFO: $1"
}

function debug_msg {
  if [[ $debug == 0 ]]; then
    return
  fi
  echo -e "DEBUG: $1"
}

function warn_msg {
  echo -e "WARNING: $1"
}

function err_msg {
  echo -e >&2 "ERROR: $1"
}

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

# Make sure that AWS_FPGA_REPO_DIR is set to the location of this script.
if [[ ":$AWS_FPGA_REPO_DIR" == ':' ]]; then
  debug_msg "AWS_FPGA_REPO_DIR not set so setting to $script_dir"
  export AWS_FPGA_REPO_DIR=$script_dir
elif [[ $AWS_FPGA_REPO_DIR != $script_dir ]]; then
  info_msg "Changing AWS_FPGA_REPO_DIR from $AWS_FPGA_REPO_DIR to $script_dir"
  export AWS_FPGA_REPO_DIR=$script_dir
else
  debug_msg "AWS_FPGA_REPO_DIR=$AWS_FPGA_REPO_DIR"
fi

debug_msg "Checking for Vivado install:"

# On the FPGA Developer AMI use module load to use the correct version of Vivado
if [ -e /usr/local/Modules/$MODULE_VERSION/bin/modulecmd ]; then
  # Module command is installed.
  # Load and unload the modules just to make sure have the environment set correctly

    # We want to make sure sdx exists before calling the unload function
    if does_module_exist sdx; then
        module unload sdx
    fi

    if does_module_exist vivado; then
        # First unload and then load it back.
        module unload vivado
        module load vivado
    else
        err_msg "The modulefile to set the environment variables for Vivado does not exist!"
        err_msg "  Please source the hdk_setup script on the correct AMI from the marketplace"
        return 1
    fi
fi

# before going too far make sure Vivado is available
if ! vivado -version > /dev/null 2>&1; then
    err_msg "Please install/enable Vivado."
    err_msg "  If you are using the FPGA Developer AMI then please request support."
    return 1
fi

#Searching for Vivado version and comparing it with the list of supported versions

export VIVADO_VER=`vivado -version | grep Vivado | head -1`

info_msg "Using $VIVADO_VER"

if grep -Fxq "$VIVADO_VER" $AWS_FPGA_REPO_DIR/hdk/supported_vivado_versions.txt
then
    debug_msg "$VIVADO_VER is supported by this HDK release."
else
    err_msg "$VIVADO_VER is not supported by this HDK release."
    err_msg "Supported versions are:"
    cat $AWS_FPGA_REPO_DIR/hdk/supported_vivado_versions.txt
    return 1
fi

debug_msg "Vivado check succeeded"

info_msg "Setting up environment variables"

# Clear environment variables
unset HDK_DIR
unset HDK_COMMON_DIR
unset HDK_SHELL_DIR
unset HDK_SHELL_DESIGN_DIR
# Don't unset CL_DIR if designer has already set it.
#unset CL_DIR

export HDK_DIR=$AWS_FPGA_REPO_DIR/hdk

# The next variable should not be modified and should always point to the /common directory under HDK_DIR
export HDK_COMMON_DIR=$HDK_DIR/common

# Point to the latest version of AWS shell
export HDK_SHELL_DIR=$(readlink -f $HDK_COMMON_DIR/shell_stable)
hdk_shell_version=$(readlink $HDK_COMMON_DIR/shell_stable)

# Set the common shell design dir
export HDK_SHELL_DESIGN_DIR=$HDK_SHELL_DIR/design

export PATH=$(echo $PATH | sed -e 's/\(^\|:\)[^:]\+\/hdk\/common\/scripts\(:\|$\)/:/g; s/^://; s/:$//')
PATH=$AWS_FPGA_REPO_DIR/hdk/common/scripts:$PATH

# The CL_DIR is where the actual Custom Logic design resides. The developer is expected to override this.
# export CL_DIR=$HDK_DIR/cl/developer_designs

debug_msg "Done setting environment variables.";

# Download correct shell DCP
info_msg "Using HDK shell version $hdk_shell_version"
debug_msg "Checking HDK shell's checkpoint version"
hdk_shell_dir=$HDK_SHELL_DIR/build/checkpoints/from_aws
hdk_shell=$hdk_shell_dir/SH_CL_BB_routed.dcp
hdk_shell_s3_bucket=aws-fpga-hdk-resources
s3_hdk_shell=$hdk_shell_s3_bucket/hdk/$hdk_shell_version/build/checkpoints/from_aws/SH_CL_BB_routed.dcp
# Download the sha256
if [ ! -e $hdk_shell_dir ]; then
	mkdir -p $hdk_shell_dir || { err_msg "Failed to create $hdk_shell_dir"; return 2; }
fi
# Use curl instead of AWS CLI so that credentials aren't required.
curl -s https://s3.amazonaws.com/$s3_hdk_shell.sha256 -o $hdk_shell.sha256 || { err_msg "Failed to download HDK shell's checkpoint version from $s3_hdk_shell.sha256 -o $hdk_shell.sha256"; return 2; }
if grep -q '<?xml version' $hdk_shell.sha256; then
  err_msg "Failed to downlonad HDK shell's checkpoint version from $s3_hdk_shell.sha256"
  cat hdk_shell.sha256
  return 2
fi
exp_sha256=$(cat $hdk_shell.sha256)
debug_msg "  latest   version=$exp_sha256"
# If shell already downloaded check its sha256
if [ -e $hdk_shell ]; then
  act_sha256=$( sha256sum $hdk_shell | awk '{ print $1 }' )
  debug_msg "  existing version=$act_sha256"
  if [[ $act_sha256 != $exp_sha256 ]]; then
    info_msg "HDK shell's checkpoint version is incorrect"
    info_msg "  Saving old checkpoint to $hdk_shell.back"
    mv $hdk_shell $hdk_shell.back
  fi
else
  info_msg "HDK shell's checkpoint hasn't been downloaded yet."
fi
if [ ! -e $hdk_shell ]; then
  info_msg "Downloading latest HDK shell checkpoint from $s3_hdk_shell"
  # Use curl instead of AWS CLI so that credentials aren't required.
  curl -s https://s3.amazonaws.com/$s3_hdk_shell -o $hdk_shell || { err_msg "HDK shell checkpoint download failed"; return 2; }
fi
# Check sha256
act_sha256=$( sha256sum $hdk_shell | awk '{ print $1 }' )
if [[ $act_sha256 != $exp_sha256 ]]; then
  err_msg "Incorrect HDK shell checkpoint version:"
  err_msg "  expected version=$exp_sha256"
  err_msg "  actual   version=$act_sha256"
  err_msg "  There may be an issue with the uploaded checkpoint or the download failed."
  return 2
fi
info_msg "HDK shell is up-to-date"

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
if [[ $models_vivado_version != $VIVADO_VER ]]; then
  ddr4_build_dir=$AWS_FPGA_REPO_DIR/ddr4_model_build
  info_msg "  Building in $ddr4_build_dir"
  info_msg "  This could take 5-10 minutes, please be patient!";
  mkdir -p $ddr4_build_dir
  pushd $ddr4_build_dir &> /dev/null
  # Run init.sh then clean-up
  if ! $HDK_DIR/common/verif/scripts/init.sh $models_dir; then
    err_msg "DDR4 model build failed."
    err_msg "  Build dir=$ddr4_build_dir"
    popd &> /dev/null
    return 2
  fi
  info_msg "DDR4 model build passed."
  popd &> /dev/null
  rm -rf $ddr4_build_dir
else
  debug_msg "DDR4 model files exist in "$ddr4_model_dir/". Skipping model creation step.";
fi
if [[ ":$CL_DIR" == ':' ]]; then
  info_msg "ATTENTION: Don't forget to set the CL_DIR variable for the directory of your Custom Logic.";
else
  info_msg "CL_DIR is $CL_DIR"
  if [ ! -d $CL_DIR ]; then
    err_msg "CL_DIR doesn't exist. Set CL_DIR to a valid directory."
    unset CL_DIR
  fi
fi
info_msg "AWS HDK setup PASSED.";
