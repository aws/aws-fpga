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
setup_test_env_script_dir=$script_dir

if ! source $script_dir/setup_test_env.sh; then
  return 1
fi

if ! source $WORKSPACE/sdk_setup.sh; then
  return 1
fi

if [ x$1 == "xpy_bindings" ] ; then
  source $WORKSPACE/.virtualenvs/python3/bin/activate
  aws s3 cp s3://aws-fpga-jenkins-testing/python_bindings_dependencies/setup.sh .
  chmod 755 ./setup.sh
  ./setup.sh
  export PYTHONPATH=$PYTHONPATH:$SDK_DIR/apps
  source $WORKSPACE/.virtualenvs/python2/bin/activate
fi