#!/bin/bash

#
# Copyright 2015-2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
