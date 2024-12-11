# Amazon FPGA Hardware Development Kit
#
# Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
unset HDK_IP_SRC_DIR
unset HDK_BD_SRC_DIR
unset HDK_BD_GEN_DIR

export HDK_DIR=$AWS_FPGA_REPO_DIR/hdk

# The next variable should not be modified and should always point to the /common directory under HDK_DIR
export HDK_COMMON_DIR=$HDK_DIR/common

# Point to the latest version of AWS shell
export HDK_SHELL_DIR=$(realpath -s $HDK_COMMON_DIR/shell_stable)

# Set the common shell design dir
export HDK_SHELL_DESIGN_DIR=$HDK_SHELL_DIR/design

# Set CL IP directories
export HDK_IP_SRC_DIR=$(realpath -s $HDK_COMMON_DIR/ip/cl_ip/cl_ip.srcs/sources_1/ip)
export HDK_BD_SRC_DIR=$(realpath -s $HDK_COMMON_DIR/ip/cl_ip/cl_ip.srcs/sources_1/bd)
export HDK_BD_GEN_DIR=$(realpath -s $HDK_COMMON_DIR/ip/cl_ip/cl_ip.gen/sources_1/bd)

# SDK
unset SDK_DIR

export SDK_DIR=$AWS_FPGA_REPO_DIR/sdk
#Vitis
export VITIS_DIR=$AWS_FPGA_REPO_DIR/vitis

# PYTHONPATH
# Update PYTHONPATH with libraries used for unit testing
python_lib=$AWS_FPGA_REPO_DIR/shared/lib
PYTHONPATH=$python_lib:$PYTHONPATH
export PYTHONPATH

# PATH Changes

export PATH=$(echo $PATH | sed -e 's/\(^\|:\)[^:]\+\/shared\/bin\/scripts\(:\|$\)/:/g; s/^://; s/:$//')
PATH=$AWS_FPGA_REPO_DIR/shared/bin/scripts:$PATH
