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

# Script must be sourced from a bash shell or it will not work
# When being sourced $0 will be the interactive shell and $BASH_SOURCE_ will contain the script being sourced
# When being run $0 and $_ will be the same.
script=${BASH_SOURCE[0]}
if [ $script == $0 ]; then
  echo "ERROR: You must source this script"
  exit 2
fi

full_script=$(readlink -f $script)
script_name=$(basename $full_script)
script_dir=$(dirname $full_script)
current_dir=$(pwd)

source $script_dir/shared/bin/set_common_functions.sh
source $script_dir/shared/bin/set_common_env_vars.sh

sudo rm -f /tmp/sdk_root_env.exp
typeset -f allow_non_root > /tmp/sdk_root_env.exp
echo "export AWS_FPGA_SDK_GROUP=${AWS_FPGA_SDK_GROUP}" >> /tmp/sdk_root_env.exp
echo "export SDK_NON_ROOT_USER=${SDK_NON_ROOT_USER}" >> /tmp/sdk_root_env.exp
echo "export AWS_FPGA_SDK_OVERRIDE_GROUP=${AWS_FPGA_SDK_OVERRIDE_GROUP}" >> /tmp/sdk_root_env.exp
sudo chown root:root /tmp/sdk_root_env.exp
sudo chmod 700 /tmp/sdk_root_env.exp

#
# Execute sdk_install.sh inside a subshell so the user's current
# shell does not exit on errors from the install.
#
cd $script_dir
if ! bash $SDK_DIR/sdk_install.sh; then
    echo "Error: AWS SDK install was unsuccessful, sdk_install.sh returned $?"
    return 1
fi

cd $current_dir
info_msg "$script_name PASSED"
