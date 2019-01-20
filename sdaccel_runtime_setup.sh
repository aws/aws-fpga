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
    info_msg "Checks & Sets up the runtime environment for AWS FPGA SDAccel Application usage."
    info_msg " "
    info_msg "sdaccel_runtime_check.sh script will:"
    info_msg "  (1) install FPGA Management Tools,"
    info_msg "  (2) check if Xilinx Runtime (XRT) is installed"
    info_msg "  (3) check if correct version of Xilinx Runtime (XRT) is installed,"
    info_msg "  (4) check if the required XOCL driver is running "
    info_msg "  (5) source runtime setup script "
    echo " "
    usage
}

function xrt_install_instructions_2018_2 {
    err_msg "AWS recommended XRT version release: https://github.com/Xilinx/XRT/releases/tag/2018.2_XDF.RC4"
    err_msg "refer to following link for instructions to install XRT"
    err_msg "https://www.xilinx.com/html_docs/xilinx2018_2_xdf/sdaccel_doc/ejy1538090924727.html"
    err_msg "use following command to download and install latest validated XRT rpms for centos distributions"
    err_msg "curl -s https://s3.amazonaws.com/aws-fpga-developer-ami/1.5.0/Patches/xrt_201802.2.1.0_7.5.1804-xrt.rpm -o xrt_201802.2.1.0_7.5.1804-xrt.rpm"
    err_msg "curl -s https://s3.amazonaws.com/aws-fpga-developer-ami/1.5.0/Patches/xrt_201802.2.1.0_7.5.1804-aws.rpm -o xrt_201802.2.1.0_7.5.1804-aws.rpm"
    err_msg "sudo yum reinstall -y xrt_*-xrt.rpm"
    err_msg "sudo yum reinstall -y xrt_*-aws.rpm"
}

function check_xdma_driver {
       
    if lsmod | grep -q 'xdma' ; then
        err_msg "Found XDMA Driver running. Please remove xdma driver using below command"
        err_msg " rmmod xdma"
        return 1
    fi
}

function check_edma_driver {
       
    if lsmod | grep -q 'edma' ; then
        err_msg "Found EDMA Driver running. Please remove edma driver using below command"
        err_msg " rmmod edma"
        return 1
    fi
}

function check_xocl_driver {
    if lsmod | grep -q 'xocl' ; then
        info_msg "Found 'xocl Driver is installed and running. ' "
    else
        err_msg " XOCL Driver not installed. Please install xocl driver using below instructions"
        err_msg " If using 2017.4 Vivado toolset please source $AWS_FPGA_REPO_DIR/sdaccel_setup.sh "
        err_msg " if using 2018.2 Vivado toolset please reinstall rpm using instructions below "
        xrt_install_instructions_2018_2
        return 1
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


if ! is_vivado_available; then
   if [[ -z "${VIVADO_TOOL_VERSION}" ]]; then
      err_msg " You are not using FPGA Developer AMI and VIVADO_TOOL_VERSION ENV variable is Empty. "
      err_msg " ENV Variable VIVADO_TOOL_VERSION is required to be set for runtime "
      err_msg " If AFI was generated using V2018.2 tools use the command : export VIVADO_TOOL_VERSION=2018.2 "
      err_msg " If AFI was generated using V2017.4 tools use the command : export VIVADO_TOOL_VERSION=2017.4 "
      err_msg " If you are using the FPGA Developer AMI then please request support on AWS FPGA Developers Forum."
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



check_xdma_driver
check_edma_driver

if [[ "$VIVADO_TOOL_VERSION" =~ .*2018\.2.* ]]; then
    info_msg "Xilinx Vivado version is 2018.2"
    
    if override; then
      info_msg "XRT check overide selected."
      source /opt/xilinx/xrt/setup.sh
      return 0
    fi

    if [ -f "/opt/xilinx/xrt/include/version.h" ]; then
       info_msg "XRT installed. proceeding to check version compatibility"
       xrt_build_ver=$(grep  'xrt_build_version_hash\[\]' /opt/xilinx/xrt/include/version.h | sed 's/";//' | sed 's/^.*"//')
       info_msg "Installed XRT version : $xrt_build_ver"
       if grep -Fxq "$xrt_build_ver" $AWS_FPGA_REPO_DIR/SDAccel/sdaccel_xrt_version.txt
       then
          info_msg "XRT version $xrt_build_ver is supported."
          info_msg " Now checking XOCL driver..."
          check_xocl_driver
          if [ -f "/opt/xilinx/xrt/setup.sh" ]; then 
             source /opt/xilinx/xrt/setup.sh
          else
             err_msg " Cannot find /opt/xilinx/xrt/setup.sh "
             err_msg " Please check XRT is installed correctly "  
             return 1
          fi
          info_msg " XRT Runtime setup Done "
       else
          err_msg "$xrt_build_ver does not match recommended version"
          cat $AWS_FPGA_REPO_DIR/SDAccel/sdaccel_xrt_version.txt
          xrt_install_instructions_2018_2
          return 1
       fi
    else
       err_msg "XRT not installed. Please install XRT"
       xrt_install_instructions_2018_2
       return 1
    fi
else
   info_msg "Xilinx Vivado version is $VIVADO_TOOL_VERSION "
   #info_msg " checking for file: /opt/Xilinx/SDx/${VIVADO_TOOL_VERSION}.rte.dyn/setup.sh"
   info_msg " Now checking XOCL driver..."
   check_xocl_driver
   if [ -f "/opt/Xilinx/SDx/${VIVADO_TOOL_VERSION}.rte.dyn/setup.sh" ]; then
      info_msg " Sourcing /opt/Xilinx/SDx/${VIVADO_TOOL_VERSION}.rte.dyn/setup.sh"
      source /opt/Xilinx/SDx/${VIVADO_TOOL_VERSION}.rte.dyn/setup.sh
      info_msg "$VIVADO_TOOL_VERSION Runtime setup Done"
   else
      err_msg " /opt/Xilinx/SDx/${VIVADO_TOOL_VERSION}.rte.dyn/setup.sh  Not found. "
      err_msg "$VIVADO_TOOL_VERSION runtime environment not installed. Please source $AWS_FPGA_REPO_DIR/sdaccel_setup.sh"
      return 1
   fi
fi

info_msg "SDAccel runtime check PASSED"
