#!/bin/bash

set -e

if [ -z "$SDK_DIR" ]; then
    echo "Error: SDK_DIR environment variable is not set.  Please 'source sdk_setup.sh' from the aws-fpga directory first."
    exit 1
fi  

SDK_MGMT_DIR=$SDK_DIR/management
AFI_MGMT_TOOLS_SRC_DIR=$SDK_MGMT_DIR/fpga_image_tools/src
AFI_MGMT_TOOLS_DST_DIR=/usr/bin

# Build and install the Amazon FPGA Image (AFI) Management Tools
cd $SDK_MGMT_DIR
$SDK_MGMT_DIR/mkall_fpga_image_tools.sh

if [ ! -d "$AFI_MGMT_TOOLS_DST_DIR" ]; then
    mkdir -p $AFI_MGMT_TOOLS_DST_DIR
fi

# /usr/bin requires sudo permissions 
echo "Copying Amazon FPGA Image (AFI) Management Tools to $AFI_MGMT_TOOLS_DST_DIR"
sudo cp -f $AFI_MGMT_TOOLS_SRC_DIR/fpga-* $AFI_MGMT_TOOLS_DST_DIR

echo "Done with Amazon FPGA Image (AFI) Management Tools install."
