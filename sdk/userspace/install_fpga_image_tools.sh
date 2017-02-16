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
