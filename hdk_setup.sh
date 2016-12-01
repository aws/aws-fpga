#!/bin/bash

export HDK_DIR=${HDK_DIR:=$(pwd)/hdk}

# The next variable should not be modified and should always point to the /common directory under HDK_DIR
export HDK_COMMON_DIR=$HDK_DIR/common

# Point to the latest version of AWS shell
export HDK_SHELL_DIR=$HDK_COMMON_DIR/shell_latest

# The CL_DIR is where the actual Custom Logic design resides. The developer is expected to override this.
export CL_DIR=$HDK_DIR/cl/developer_designs

echo "Done setting environment variables.";
echo "ATTENTION: Don't forget to change the CL_DIR variable for the directory of your Custom Logic.";

# Create DDR and PCIe IP models and patch PCIe
if [ ! -f $HDK_COMMON_DIR/verif/models/ddr4_model/arch_defines.v ]
then
  echo "DDR4 model files in "$HDK_COMMON_DIR/verif/models/ddr4_model/" do NOT exist. Running model creation step.";
  echo "This could take 5-10 minutes, please be patient!";
  echo "NOTE: This step requires having Xilinx Vivado installed and running Licensing Manager";
  # Run init.sh then clean-up
  source $HDK_DIR/common/verif/scripts/init.sh
  echo "Done with model creation step. Cleaning up temporary files.";
  rm -fr tmp
  rm vivado*jou
  rm vivado*log
else
  echo "DDR4 model files exist in "$HDK_COMMON_DIR/verif/models/ddr4_model/". Skipping model creation step.";
fi
echo "Done with AWS HDK setup.";

