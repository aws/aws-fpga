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
gui_script_dir="/home/centos/src/scripts"

if [ -d $gui_script_dir ]; then
 if [ -e $gui_script_dir/setup_gui.sh ]; then
   #use curl to overwrite AMI default script
   curl https://s3.amazonaws.com/aws-fpga-developer-ami/1.4.0/Scripts/setup_gui.sh -o $gui_script_dir/setup_gui.sh || { err_msg "Failed to download errata gui script from s3 bucket"; return 2; }
   /home/centos/src/scripts/setup_gui.sh
  fi
 fi

python_versions=(2.7 3.4)

python_packages=(\
pytest \
pytest-timeout \
GitPython \
boto3 \
)

for python_version in ${python_versions[@]}; do
    python=python$python_version
    pip=pip$python_version
    yum_python_package=${python/./}
    yum_pip_package=$yum_python_package-pip
    if [ ! -e /usr/bin/$python ]; then
        if ! sudo yum -y install $yum_python_package; then
            echo "error: Install of $yum_python_package failed"
            return 1
        fi
    fi
    if [ ! -e /usr/bin/$pip ]; then
        if ! sudo yum -y install $yum_pip_package; then
            echo "error: Install of $yum_pip_package failed"
            return 1
        fi
        sudo $pip install --upgrade pip
    fi
    
    for p in ${python_packages[@]}; do
        if ! $pip show $p > /dev/null; then
            echo "Installing $p"
            if ! sudo $pip install $p; then
                echo "error: Install of $python $p failed"
                return 1
            fi
        fi
    done
done

if [ ":$WORKSPACE" == ":" ]; then
    export WORKSPACE=$(git rev-parse --show-toplevel)
fi

export PYTHONPATH=$WORKSPACE/shared/lib:$PYTHONPATH

export AWS_DEFAULT_REGION=us-east-1
