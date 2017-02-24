#!/bin/bash

echo "AWS FPGA: hdk_setup.sh script will (i) check if Xilinx's vivado is installed, (ii) set up key environment variables HDK_*, and (iii) prepare DRAM controller and PCIe IP modules if they are not already available in your directory."

echo "AWS FPGA: Checking for vivado install:"
 
# before going too far make sure Vivado is available
vivado -version >/dev/null 2>&1 || { echo >&2 "ERROR - Please install/enable Vivado." ; return 1; }

echo "AWS FPGA: Vivado check successed"

echo "AWS FPGA: Setting up environment variables"

# Clear environment variables
unset HDK_DIR
unset HDK_COMMON_DIR
unset HDK_SHELL_DIR
unset CL_DIR

export HDK_DIR=${HDK_DIR:=$(pwd)/hdk}

# The next variable should not be modified and should always point to the /common directory under HDK_DIR
export HDK_COMMON_DIR=$HDK_DIR/common

# Point to the latest version of AWS shell
export HDK_SHELL_DIR=$HDK_COMMON_DIR/shell_latest

# The CL_DIR is where the actual Custom Logic design resides. The developer is expected to override this.
# export CL_DIR=$HDK_DIR/cl/developer_designs

echo "AWS FPGA: Done setting environment variables.";

# Create DDR and PCIe IP models and patch PCIe
if [ ! -f $HDK_COMMON_DIR/verif/models/ddr4_model/arch_defines.v ]
then
  echo "DDR4 model files in "$HDK_COMMON_DIR/verif/models/ddr4_model/" do NOT exist. Running model creation step.";
  echo "This could take 5-10 minutes, please be patient!";
  # Run init.sh then clean-up
  source $HDK_DIR/common/verif/scripts/init.sh
  echo "Done with model creation step. Cleaning up temporary files.";
  rm -fr tmp
  rm vivado*jou
  rm vivado*log
else
  echo "DDR4 model files exist in "$HDK_COMMON_DIR/verif/models/ddr4_model/". Skipping model creation step.";
fi
echo "AWS FPGA: Done with AWS HDK setup.";
echo "AWS FPGA: ATTENTION: Don't forget to change the CL_DIR variable for the directory of your Custom Logic.";


