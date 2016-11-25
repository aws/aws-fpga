#!/bin/bash

set -e

if [ -z "$SDK_DIR" ]; then
    echo "Error: SDK_DIR environment variable is not set.  Please 'source sdk_setup.sh' from the aws-fpga directory first."
    exit 1
fi  

SDK_MGMT_DIR=$SDK_DIR/management

# Build and install the Amazon FPGA Image (AFI) Management Tools
$SDK_MGMT_DIR/install_fpga_image_tools.sh

echo "Done with SDK install."
