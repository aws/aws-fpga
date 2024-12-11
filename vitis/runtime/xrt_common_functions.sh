# 
# Copyright (C) 2018 Xilinx, Inc
# Xilinx XRT setup functions
#
# Author: ryan.radjabi@xilinx.com
# 
# Licensed under the Apache License, Version 2.0 (the "License"). You may
# not use this file except in compliance with the License. A copy of the
# License is located at
# 
#     http://www.apache.org/licenses/LICENSE-2.0
# 
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
# License for the specific language governing permissions and limitations
# under the License.
#

XRT_PATH="${VITIS_DIR}/runtime/XRT_${RELEASE_VER}"

function get_install_cmd {
    xrt_inst_cmd="install"
    aws_inst_cmd="install"
    if [[ $(lsb_release -si) == "Ubuntu" ]]; then
        dpkg -s xrt
        ret=$?
        if [[ $ret == "0" ]]; then
            xrt_inst_cmd="install --reinstall"
        fi
        dpkg -s xrt-aws
        ret=$?
        if [[ $ret == "0" ]]; then
            aws_inst_cmd="install --reinstall"
        fi
    else
        err_msg "Only Ubuntu 22.04 is supported at this time"
        return 1
    fi
}

function build_xrt {
    info_msg "xrt-path: $XRT_PATH"
    if [ -z "$(ls -A $XRT_PATH)" ]; then
        # XRT_PATH is empty, this is the first run, so call submodule update
        git submodule update --init -- $XRT_PATH
    else
        # XRT_PATH is not empty, only call init, this allows local changes to exist in XRT 
        git submodule init -- $XRT_PATH
    fi
    info_msg "XRT Developer Flow: Building Xilinx runtime XRT..."
    sudo sh -c "cd $XRT_PATH;./src/runtime_src/tools/scripts/xrtdeps.sh;"
    ret=$?
    if [[ $ret -ne 0 ]]; then
        err_msg "XRT Developer Flow: Failed to install dependencies: xrtdeps.sh: {$ret}"
        return $?
    fi
    if [[ $(lsb_release -si) == "Ubuntu" ]]; then
        sudo sh -c "cd ${XRT_PATH}/build/; ./build.sh;"
    fi
    ret=$?
    if [[ $ret != 0 ]]; then
        err_msg "XRT Developer Flow: Failed to build XRT: {$?}"
    fi
    return $?
}

# takes the path to RPM/DEB package as argument
function install_xrt_package {
    get_install_cmd
    if [[ $(lsb_release -si) == "Ubuntu" ]]; then
        sudo sh -c "cd $1; apt ${xrt_inst_cmd} ./xrt_*-xrt.deb; apt ${aws_inst_cmd} ./xrt_*-aws.deb;"
    fi
    ret=$?
    if [[ $ret != 0 ]]; then
        err_msg "XRT Developer Flow: Failed to install XRT: {$?}"
    else
        info_msg "Xilinx runtime installed"
    fi
    return $?
}

function setup_runtime {
    if [ -e /opt/xilinx/xrt ]; then # Check if XRT is installed
        info_msg "XRT Install, non-dev"
        export XILINX_XRT=/opt/xilinx/xrt
        export PATH=$PATH:/opt/xilinx/xrt/bin

        export LD_LIBRARY_PATH=$XILINX_XRT/lib:$LD_LIBRARY_PATH

        if [[ $RELEASE_VER =~ .*2024\.* ]]; then

          # copy libstdc++ from $XILINX_VITIS/lib
          if [[ $(lsb_release -si) == "Ubuntu" ]]; then
                if [[ ! -e /opt/xilinx/xrt/lib ]]; then
                    sudo mkdir /opt/xilinx/xrt/lib
                fi
                sudo cp $XILINX_VITIS/lib/lnx64.o/Ubuntu/libstdc++.so* /opt/xilinx/xrt/lib/
          else
              info_msg "Unsupported OS."
              return 1
          fi
        fi
        info_msg "Xilinx Runtime Setup PASSED"
    else
        err_msg "Xilinx XRT runtime not installed - This is required if you are running on an F2 instance."
        return 1
    fi

    if ! get_install_cmd; then
        err_msg "Couldn't obtain Xilinx Runtime install command"
        return 1
    fi
}