#!/bin/bash

if [ -z "$SDK_DIR" ]; then
    echo "Error: SDK_DIR environment variable is not set.  Please 'source sdk_setup.sh' from the aws-fpga directory first."
    exit 1
fi

gcc --version &> /dev/null
RET=$?
if [ $RET != 0 ]; then
    echo "Error: gcc is not installed."
    echo "    You can install gcc and other useful development tools by using: sudo yum groupinstall \"Development tools\""
    exit $RET 
fi

SDK_MGMT_DIR=$SDK_DIR/management

# Build and install the Amazon FPGA Image (AFI) Management Tools
$SDK_MGMT_DIR/install_fpga_image_tools.sh
RET=$?
if [ $RET != 0 ]; then
    echo "Error: install_fpga_image_tools.sh returned $RET"
    exit $RET 
fi

echo "Done with SDK install."
