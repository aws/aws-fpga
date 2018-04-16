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

info_msg "Setting up environment variables"

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

# HDK
# Clear environment variables
unset HDK_DIR
unset HDK_COMMON_DIR
unset HDK_SHELL_DIR
unset HDK_SHELL_DESIGN_DIR

export HDK_DIR=$AWS_FPGA_REPO_DIR/hdk

# The next variable should not be modified and should always point to the /common directory under HDK_DIR
export HDK_COMMON_DIR=$HDK_DIR/common

# Point to the latest version of AWS shell
export HDK_SHELL_DIR=$(readlink -f $HDK_COMMON_DIR/shell_stable)

# Set the common shell design dir
export HDK_SHELL_DESIGN_DIR=$HDK_SHELL_DIR/design

export PATH=$(echo $PATH | sed -e 's/\(^\|:\)[^:]\+\/hdk\/common\/scripts\(:\|$\)/:/g; s/^://; s/:$//')
PATH=$AWS_FPGA_REPO_DIR/hdk/common/scripts:$PATH

# SDK
unset SDK_DIR

export SDK_DIR=$AWS_FPGA_REPO_DIR/sdk

export XIL_CHECK_TCL_DEBUG=1

# SDACCEL
# Setup Location of SDACCEL_DIR
export SDACCEL_DIR=$AWS_FPGA_REPO_DIR/SDAccel


# PYTHONPATH
# Update PYTHONPATH with libraries used for unit testing
python_lib=$AWS_FPGA_REPO_DIR/shared/lib
export PYTHONPATH=$(echo $PATH | sed -e 's/\(^\|:\)[^:]\+$python_lib\(:\|$\)/:/g; s/^://; s/:$//')
PYTHONPATH=$python_lib:$PYTHONPATH
