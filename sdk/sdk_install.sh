#!/bin/bash

#
# Copyright 2015-2017 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License"). You may
# not use this file except in compliance with the License. A copy of the
# License is located at
#
#     http://aws.amazon.com/apache2.0/
#
# or in the "license" file accompanying this file. This file is distributed
# on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
# express or implied. See the License for the specific language governing
# permissions and limitations under the License.
#

if [ -z "$SDK_DIR" ]; then
    echo "Error: SDK_DIR environment variable is not set.  Please use 'source sdk_setup.sh' from the aws-fpga directory."
    exit 1
fi

gcc --version &> /dev/null
RET=$?
if [ $RET != 0 ]; then
    echo "Error: gcc is not installed."
    echo "    You can install gcc and other useful development tools by using: sudo yum groupinstall \"Development tools\""
    exit $RET 
fi

sudo -V &> /dev/null
RET=$?
if [ $RET != 0 ]; then
    echo "Error: sudo is not in path or not installed. Driver installations will fail "
    echo "    To install drivers please add sudo to your path or install sudo by running \"yum install sudo\" as root "
    #exit $RET 
fi


SDK_USERSPACE_DIR=$SDK_DIR/userspace

# Build the Amazon FPGA Image (AFI) Management Tools
(cd $SDK_USERSPACE_DIR && ./mkall_fpga_mgmt_tools.sh)
RET=$?
if [ $RET != 0 ]; then
    echo "Error: mkall_fpga_mgmt_tools.sh returned $RET"
    exit $RET
fi
echo "Build complete."

# Install the Amazon FPGA Image (AFI) Management Tools
$SDK_USERSPACE_DIR/install_fpga_mgmt_tools.sh
RET=$?
if [ $RET != 0 ]; then
    echo "Error: install_fpga_mgmt_tools.sh returned $RET"
    exit $RET
fi

echo "Done with SDK install."
