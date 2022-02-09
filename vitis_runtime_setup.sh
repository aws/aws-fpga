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
current_dir=$(pwd)

source $script_dir/shared/bin/set_common_functions.sh
source $script_dir/shared/bin/set_common_env_vars.sh
source $VITIS_DIR/Runtime/xrt_common_functions.sh

# Source sdk_setup.sh
info_msg "Sourcing sdk_setup.sh"
if ! source $AWS_FPGA_REPO_DIR/sdk_setup.sh; then
    return 1
fi

if [ -z "$SDK_DIR" ]; then
    err_msg "SDK_DIR environment variable is not set.  Please use 'source sdk_setup.sh' from the aws-fpga directory."
    return 1
fi

debug=0
override=0
function usage {
    echo -e "USAGE: source [\$AWS_FPGA_REPO_DIR/]$script_name [-d|-debug] [-h|-help] [-o|-override]"
}

function help {
    info_msg "$script_name"
    info_msg " "
    info_msg "Checks & Sets up the runtime environment for AWS FPGA Vitis Application usage."
    info_msg " "
    info_msg "vitis_runtime_check.sh script will:"
    info_msg "  (1) install FPGA Management Tools,"
    info_msg "  (2) check if Xilinx Runtime (XRT) is installed"
    info_msg "  (3) check if correct version of Xilinx Runtime (XRT) is installed,"
    info_msg "  (4) check if the required XOCL driver is running "
    info_msg "  (5) source runtime setup script "
    echo " "
    usage
}

function check_xdma_driver {

    if lsmod | grep -q 'xdma' ; then
        err_msg "Found XDMA Driver running. Please remove xdma driver using below command"
        err_msg " rmmod xdma"
        return 1
    fi
}

function check_xocl_driver {
    if lsmod | grep -q 'xocl' ; then
        info_msg "Found 'xocl Driver is installed and running. ' "
    else
        err_msg "XOCL Driver not installed. Please install xocl driver using below instructions"
        err_msg "If using Vitis, please source $AWS_FPGA_REPO_DIR/vitis_setup.sh "
        return 1
    fi
}

function check_kernel_ver {

      ins_ker_ver=$(uname -r)
      info_msg "Installed kernel version : $ins_ker_ver"
      if grep -Fxq "$ins_ker_ver" $AWS_FPGA_REPO_DIR/Vitis/kernel_version.txt
       then
        info_msg "kernel version $ins_ker_ver has been validated for this devkit."
      else
          warn_msg "$ins_ker_ver does not match one of recommended kernel versions"
          cat $AWS_FPGA_REPO_DIR/Vitis/kernel_version.txt
          warn_msg "Xilinx Runtime not validated against your installed kernel version."
       fi
}

# Process command line args
args=( "$@" )
for (( i = 0; i < ${#args[@]}; i++ )); do
    arg=${args[$i]}
    case $arg in
        -d|-debug)
            debug=1
        ;;
        -h|-help)
            help
            return 0
        ;;
        -o|-override)
            override=1
        ;;
        *)
            err_msg "Invalid option: $arg\n"
            usage
            return 1
    esac
done


if ! exists vivado; then
   if [[ -z "${VIVADO_TOOL_VERSION}" ]]; then
      err_msg " VIVADO_TOOL_VERSION ENV variable is not set."
      err_msg " ENV Variable VIVADO_TOOL_VERSION needs to be set for runtime usage. "
      err_msg " If AFI was generated using V2019.2 tools use the command : export VIVADO_TOOL_VERSION=2019.2 "
      err_msg " Please set VIVADO_TOOL_VERSION to the correct value and re-run script."
      return 1
   else
      info_msg " VIVADO tools not found. Reading VIVADO_TOOL_VERSION ENV variable to determine runtime version... "
      VIVADO_TOOL_VERSION="${VIVADO_TOOL_VERSION}"
      export VIVADO_TOOL_VERSION=${VIVADO_TOOL_VERSION:0:6}
   fi
else
    info_msg "You are using instance with installed vivado tools. determining VIVADO version for runtime setup..."
    VIVADO_TOOL_VERSION=`vivado -version | grep Vivado | head -1 | sed 's:Vivado *::' | sed 's: .*$::' | sed 's:v::'`
    export VIVADO_TOOL_VERSION=${VIVADO_TOOL_VERSION:0:6}
fi
info_msg "VIVADO_TOOL_VERSION is $VIVADO_TOOL_VERSION"


check_kernel_ver
check_xdma_driver

if [[ "$VIVADO_TOOL_VERSION" =~ .*2019\.2.*  || "$VIVADO_TOOL_VERSION" =~ .*2020\.* || "$VIVADO_TOOL_VERSION" =~ .*2021\.*  ]]; then
    info_msg "Xilinx Vivado version is $VIVADO_TOOL_VERSION"

    if [ $override == 1 ]; then
      info_msg "XRT check override selected."
      source /opt/xilinx/xrt/setup.sh
      return 0
    fi

    if [ -f "/opt/xilinx/xrt/include/version.h" ]; then
       info_msg "XRT installed. proceeding to check version compatibility"
       xrt_build_ver=$VIVADO_TOOL_VERSION
       xrt_build_ver+=:
       xrt_build_ver+=$(grep  'xrt_build_version_hash\[\]' /opt/xilinx/xrt/include/version.h | sed 's/";//' | sed 's/^.*"//')
       info_msg "Installed XRT version : $xrt_build_ver"
       if grep -Fxq "$xrt_build_ver" $AWS_FPGA_REPO_DIR/Vitis/vitis_xrt_version.txt
       then
          info_msg "XRT version $xrt_build_ver is supported."
          info_msg " Now checking XOCL driver..."
          check_xocl_driver
          if [ -f "/opt/xilinx/xrt/setup.sh" ]; then
             source /opt/xilinx/xrt/setup.sh
          else
             err_msg " Cannot find /opt/xilinx/xrt/setup.sh"
             err_msg " Please check XRT is installed correctly"
             err_msg " Please Refer to $AWS_FPGA_REPO/Vitis/doc/XRT_installation_instructions.md for XRT installation instructions"
             return 1
          fi
          info_msg " XRT Runtime setup Done"
       else
          err_msg "$xrt_build_ver does not match recommended versions"
          cat $AWS_FPGA_REPO_DIR/Vitis/vitis_xrt_version.txt
          err_msg "Please Refer $AWS_FPGA_REPO/Vitis/doc/XRT_installation_instructions.md for XRT installation instructions"
          return 1
       fi
    else
       err_msg "XRT not installed. Please install XRT"
       err_msg "Please Refer $AWS_FPGA_REPO/Vitis/doc/XRT_installation_instructions.md for XRT installation instructions"
       return 1
    fi
else
   err_msg "Xilinx Vivado version is $VIVADO_TOOL_VERSION , only 2019.2, 2020.1, 2020.2, 2021.1 or 2021.2 are supported for Vitis "
   return 1
fi

setup_runtime

info_msg "Starting MPD"
systemctl is-active --quiet mpd || sudo systemctl start mpd

info_msg "Vitis runtime check PASSED"
