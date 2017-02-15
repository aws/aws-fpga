# Script must be sourced from a bash shell or it will not work
# When being sourced $0 will be the interactive shell and $BASH_SOURCE_ will contain the script being sourced
# When being run $0 and $_ will be the same.
script=$BASH_SOURCE
if [ $script == $0 ]; then
  echo "ERROR: You must source this script"
  exit 2
fi
full_script=$(readlink -f $script)
script_dir=$(dirname $full_script)
if [[ ':$AWS_FPGA_REPO_DIR' == ':' ]]; then
  export AWS_FPGA_REPO_DIR=$script_dir
fi

echo "AWS FPGA: hdk_setup.sh script will:"
echo "AWS FPGA:   (i) check if Xilinx's vivado is installed,"
echo "AWS FPGA:   (ii) set up key environment variables HDK_*, and"
echo "AWS FPGA:   (iii) prepare DRAM controller and PCIe IP modules if they are not already available in your directory."

echo "AWS FPGA: Checking for vivado install:"
 
# before going too far make sure Vivado is available
vivado -version >/dev/null 2>&1 || { echo >&2 "AWS FPGA: ERROR - Please install/enable Vivado." ; return 1; }

#Searching for Vivado version and comparing it with the list of supported versio

export VIVADO_VER=`vivado -version | grep Vivado | head -1`

echo "AWS FPGA: Found $VIVADO_VER"

if grep -Fxq "$VIVADO_VER" $AWS_FPGA_REPO_DIR/hdk/supported_vivado_versions.txt
then
    echo "AWS FPGA: $VIVADO_VER is supported by this HDK release."
else
    echo "AWS FPGA: ERROR - $VIVADO_VER is not supported by this HDK release."
    return 1
fi

echo "AWS FPGA: Vivado check succeeded"

echo "AWS FPGA: Setting up environment variables"

# Clear environment variables
unset HDK_DIR
unset HDK_COMMON_DIR
unset HDK_SHELL_DIR
# Don't unset CL_DIR if designer has already set it.
#unset CL_DIR

export HDK_DIR=$AWS_FPGA_REPO_DIR/hdk

# The next variable should not be modified and should always point to the /common directory under HDK_DIR
export HDK_COMMON_DIR=$HDK_DIR/common

# Point to the latest version of AWS shell
export HDK_SHELL_DIR=$(readlink -f $HDK_COMMON_DIR/shell_stable)

# The CL_DIR is where the actual Custom Logic design resides. The developer is expected to override this.
# export CL_DIR=$HDK_DIR/cl/developer_designs

echo "AWS FPGA: Done setting environment variables.";

# Create DDR and PCIe IP models and patch PCIe\
models_dir=$HDK_COMMON_DIR/verif/models
ddr4_model_dir=$models_dir/ddr4_model
if [ ! -f $ddr4_model_dir/arch_defines.v ]; then
  ddr4_build_dir=$AWS_FPGA_REPO_DIR/ddr4_model_build
  echo "AWS FPGA: DDR4 model files in "$ddr4_model_dir/" do NOT exist. Running model creation step.";
  echo "AWS FPGA: Building in $ddr4_build_dir"
  echo "AWS FPGA: This could take 5-10 minutes, please be patient!";
  return 2
  mkdir -p $ddr4_build_dir
  pushd $ddr4_build_dir &> /dev/null
  # Run init.sh then clean-up
  if ! $HDK_DIR/common/verif/scripts/init.sh $models_dir; then
    echo "AWS FPGA: ERROR - DDR4 model build failed."
    echo "AWS FPGA: Build dir=$ddr4_build_dir"
    popd &> /dev/null
    return 2
  fi
  echo "AWS FPGA: Done with model creation step. Cleaning up temporary files.";
  popd &> /dev/null
  rm -rf $ddr4_build_dir
else
  echo "AWS FPGA: DDR4 model files exist in "$ddr4_model_dir/". Skipping model creation step.";
fi
echo "AWS FPGA: Done with AWS HDK setup.";
if [[ ":$CL_DIR" == ':' ]]; then
  echo "AWS FPGA: ATTENTION: Don't forget to change the CL_DIR variable for the directory of your Custom Logic.";
else
  echo "AWS FPGA: CL_DIR is $CL_DIR"
  if [ ! -d $CL_DIR ]; then
    echo "AWS FPGA: ERROR - CL_DIR doesn't exist. Set CL_DIR to a valid directory."
    unset CL_DIR
  fi
fi


