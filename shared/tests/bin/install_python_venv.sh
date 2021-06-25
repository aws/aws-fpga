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

os_uname=`uname -r`

script=${BASH_SOURCE[0]}
full_script=$(readlink -f $script)
script_name=$(basename $full_script)
script_dir=$(dirname $full_script)

python_versions=(3.6 2.7)

# First install python if it is not installed.
for python_version in ${python_versions[@]}; do
    if [[ $os_uname =~ (amzn2) ]]; then
        python_version = ${python_version:0:1}
    fi

    python=python$python_version
    pip=pip$python_version
    yum_python_package=${python/./}
    if [ ! -e /usr/bin/$python ]; then
        if ! sudo yum -y install $yum_python_package; then
            echo "Error: Install of $yum_python_package failed"
            exit 1
        fi
    fi
done

# Python2 pip is common between OS's. We can use that to install other
if [ ! -e /usr/bin/pip2 ]; then
    if ! sudo yum -y install python2-pip; then
        echo "Error: Install of $yum_python_package failed"
        exit 1
    fi
    sudo pip install -U 'pip<21'
fi

# Install virtualenv
if [ ! -e /usr/bin/virtualenv ]; then
    if ! sudo pip install virtualenv; then
        echo "Error: Install of virtualenv failed"
        exit 1
    fi
fi

# Install virtualenvwrapper
if [ ! -e ~/.local/bin/virtualenvwrapper.sh ]; then
    if ! pip install --user virtualenvwrapper; then
        echo "Error: Install of virtualenvwrapper failed"
        exit 1
    fi
fi

source ~/.local/bin/virtualenvwrapper.sh

# Create virtualenv environments
for python_version in ${python_versions[@]}; do

    if [[ $os_uname =~ (amzn2) ]]
    then
        site_packages=/usr/lib64/python$python_version/site-packages/

        python=python${python_version:0:1}

        mkvirtualenv -r $script_dir/requirements.txt  -p $(which $python) --system-site-packages python${python_version:0:1}

        # Adding the python bindings site packages to path
        add2virtualenv $site_packages
    else
        python=python$python_version
        mkvirtualenv -r $script_dir/requirements.txt  -p $(which $python) python${python_version:0:1}
    fi
done
