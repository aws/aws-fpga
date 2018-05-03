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

function usage {
    echo -e "USAGE: source [\$AWS_FPGA_REPO_DIR/]$script_name [-d|-debug] [-h|-help]"
}

function help {
    info_msg "$script_name"
    info_msg " "
    info_msg "Sets up the environment for AWS FPGA SDAccel tools."
    info_msg " "
    info_msg "sdaccel_setup.sh script will:"
    info_msg "  (1) install FPGA Management Tools,"
    info_msg "  (2) check if Xilinx tools are available,"
    info_msg "  (3) check if required packages are installed,"
    info_msg "  (4) Download lastest AWS Platform,"
    info_msg "  (5) Install Runtime drivers "
    echo " "
    usage
}

function check_set_xilinx_sdx {
    if [[ ":$XILINX_SDX" == ':' ]]; then
        debug_msg "XILINX_SDX is not set"
        which sdx
        RET=$?
        if [ $RET != 0 ]; then
            debug_msg "sdx not found in path."
            err_msg "XILINX_SDX variable not set and sdx not in the path"
            err_msg "Please set XILINX_SDX variable to point to your location of your Xilinx installation or add location of sdx exectuable to your PATH variable"
            return $RET
        else
            export XILINX_SDX=`which sdx | sed 's:/bin/sdx::'`
            info_msg "Setting XILINX_SDX to $XILINX_SDX"
        fi
    else
        info_msg "XILINX_SDX is already set to $XILINX_SDX"
    fi
    # get sdaccel release version, i.e. "2017.1"
    RELEASE_VER=$(basename $XILINX_SDX)
    RELEASE_VER=${RELEASE_VER:0:6}
    export RELEASE_VER=$RELEASE_VER
    echo "RELEASE_VER equals $RELEASE_VER"
}

function check_install_packages {
#TODO: Check required packages are installed or install them
#TODO: Check version of gcc is above 4.8.5 (4.6.3 does not work)
  for pkg in `cat $SDACCEL_DIR/packages.txt`; do
    if yum list installed "$pkg" >/dev/null 2>&1; then
      true
    else
      warn_msg " $pkg not installed - please run: sudo yum install $pkg "
    fi
  done
}

function check_internet {
    curl --silent --head -m 30 http://www.amazon.com
    RET=$?
    if [ $RET != 0 ]; then
        err_msg "curl cannot connect to the internet using please check your internet connection or proxy settings"
        err_msg "To check your connection run:   curl --silent --head -m 30 http://www.amazon.com "
        return $RET
    else
        info_msg "Internet Access OK"
    fi
}

function check_icd {
    info_msg "Checking ICD is installed"
    if grep -q 'libxilinxopencl.so' /etc/OpenCL/vendors/xilinx.icd; then
        info_msg "Found 'libxilinxopencl.so"
    else
        info_msg "/etc/OpenCL/vendors/xilinx.icd does not exist or does not contain lbixilinxopencl.so creating and adding libxilinxopencl.so to it"
        sudo sh -c "echo libxilinxopencl.so > /etc/OpenCL/vendors/xilinx.icd"
        RET=$?
    if [ $RET != 0 ]; then
        err_msg "/etc/OpenCL/vendors/xilinx.icd does not exist and cannot be created, sudo permissions needed to update it."
        err_msg "Run the following with sudo permissions: sudo sh -c \"echo libxilinxopencl.so > /etc/OpenCL/vendors/xilinx.icd\" "
        return $RET
    else
        echo "Done with ICD installation"
    fi
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
        *)
            err_msg "Invalid option: $arg\n"
            usage
            return 1
    esac
done

# Install patches as required.
setup_patches

# Check XILINX_SDX is set
if ! check_set_xilinx_sdx; then
    return 1
fi

# Update Xilinx SDAccel Examples from GitHub
info_msg "Using SDx $RELEASE_VER"
if [[ $RELEASE_VER =~ .*2017\.4.* ]]; then
    info_msg "Updating Xilinx SDAccel Examples 2017.4"
    git submodule update --init -- SDAccel/examples/xilinx_2017.4
    export VIVADO_TOOL_VER=2017.4
    if [ -e $SDACCEL_DIR/examples/xilinx ]; then
        if [ ! -L $SDACCEL_DIR/examples/xilinx ]; then
          err_msg "ERROR:  SDAccel/examples/xilinx is not a symbolic link.  Backup any data and remove SDAccel/examples/xilinx directory.  The setup needs to create a symbolic link from SDAccel/examples/xilinx to SDAccel/examples/xilinx_2017.4"
          return 1
        fi
    fi
    rm -I $SDACCEL_DIR/examples/xilinx
    ln -s $SDACCEL_DIR/examples/xilinx_2017.4 $SDACCEL_DIR/examples/xilinx
else
    info_msg "Updating Xilinx SDAccel Examples 2017.1"
    git submodule update --init -- SDAccel/examples/xilinx_2017.1
    export VIVADO_TOOL_VER=2017.1
    if [ -e $SDACCEL_DIR/examples/xilinx ]; then
        if [ ! -L $SDACCEL_DIR/examples/xilinx ]; then
          err_msg "ERROR:  SDAccel/examples/xilinx is not a symbolic link.  Backup any data and remove SDAccel/examples/xilinx directory.  The setup needs to create a symbolic link from SDAccel/examples/xilinx to SDAccel/examples/xilinx_2017.1"
          return 1
        fi
    fi
    rm -I $SDACCEL_DIR/examples/xilinx
    ln -s $SDACCEL_DIR/examples/xilinx_2017.1 $SDACCEL_DIR/examples/xilinx
fi

# settings64 removal - once we put this in the AMI, we will add a check
#export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$XILINX_SDX/lib/lnx64.o

if [[ $RELEASE_VER =~ .*2017\.1.* ]]; then
    export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$XILINX_SDX/lib/lnx64.o
else
    export LD_LIBRARY_PATH=`$XILINX_SDX/bin/ldlibpath.sh $XILINX_SDX/lib/lnx64.o`:$XILINX_SDX/runtime/lib/x86_64
fi

export LD_LIBRARY_PATH=$XILINX_SDX/lnx64/tools/opencv/:$LD_LIBRARY_PATH

# Check if internet connection is available
if ! check_internet; then
    return 1
fi

# Check ICD is installed
if ! check_icd; then
    return 1
fi

# Check correct packages are installed
if ! check_install_packages; then
    return 1
fi

function setup_dsa {

    if [ "$#" -ne 3 ]; then
        err_msg "Illegal number of parameters sent to the setup_dsa function!"
        return 1
    fi

    DSA=$1
    DSA_S3_BASE_DIR=$2
    PLATFORM_ENV_VAR_NAME=$3

    dsa_dir=$SDACCEL_DIR/aws_platform/$DSA/hw/
    sdk_dsa=$dsa_dir/$DSA.dsa
    sdk_dsa_s3_bucket=aws-fpga-hdk-resources
    s3_sdk_dsa=$sdk_dsa_s3_bucket/SDAccel/$DSA_S3_BASE_DIR/$DSA/$DSA.dsa

    # set a variable to point to the platform for build and emulation runs
    export "$PLATFORM_ENV_VAR_NAME"=$SDACCEL_DIR/aws_platform/$DSA/$DSA.xpfm

    # Download the sha256
    if [ ! -e $dsa_dir ]; then
        mkdir -p $dsa_dir || { err_msg "Failed to create $dsa_dir"; return 2; }
    fi

    # Use curl instead of AWS CLI so that credentials aren't required.
    curl -s https://s3.amazonaws.com/$s3_sdk_dsa.sha256 -o $sdk_dsa.sha256 || { err_msg "Failed to download DSA checkpoint version from $s3_sdk_dsa.sha256 -o $sdk_dsa.sha256"; return 2; }
    if grep -q '<?xml version' $sdk_dsa.sha256; then
        err_msg "Failed to download SDK DSA checkpoint version from $s3_sdk_dsa.sha256"
        cat sdk_dsa.sha256
        return 2
    fi
    exp_sha256=$(cat $sdk_dsa.sha256)
    debug_msg "  latest   version=$exp_sha256"
    # If DSA already downloaded check its sha256
    if [ -e $sdk_dsa ]; then
        act_sha256=$( sha256sum $sdk_dsa | awk '{ print $1 }' )
        debug_msg "  existing version=$act_sha256"
        if [[ $act_sha256 != $exp_sha256 ]]; then
            info_msg "SDK DSA checkpoint version is incorrect"
            info_msg "  Saving old checkpoint to $sdk_dsa.back"
            mv $sdk_dsa $sdk_dsa.back
        fi
    else
        info_msg "SDK DSA hasn't been downloaded yet."
    fi

    if [ ! -e $sdk_dsa ]; then
        info_msg "Downloading latest SDK DSA checkpoint from $s3_sdk_dsa"
        # Use curl instead of AWS CLI so that credentials aren't required.
        curl -s https://s3.amazonaws.com/$s3_sdk_dsa -o $sdk_dsa || { err_msg "SDK dsa checkpoint download failed"; return 2; }
    fi
    # Check sha256
    act_sha256=$( sha256sum $sdk_dsa | awk '{ print $1 }' )
    if [[ $act_sha256 != $exp_sha256 ]]; then
        err_msg "Incorrect SDK dsa checkpoint version:"
        err_msg "  expected version=$exp_sha256"
        err_msg "  actual   version=$act_sha256"
        err_msg "  There may be an issue with the uploaded checkpoint or the download failed."
        return 2
    fi
}

if [[ ${RELEASE_VER} =~ .*2017\.1.* ]]; then
    #-------------------4 DDR--------------------
    setup_dsa xilinx_aws-vu9p-f1_4ddr-xpr-2pr_4_0 dsa_v0911_shell_v071417d3 AWS_PLATFORM_4DDR
    info_msg "AWS Platform: 4DDR is up-to-date"
    #-------------------4 DDR--------------------

    #-------------------1 DDR--------------------
    setup_dsa xilinx_aws-vu9p-f1_1ddr-xpr-2pr_4_0 dsa_v11517_shell_v071417d3 AWS_PLATFORM_1DDR
    info_msg "AWS Platform: 1DDR is up-to-date"
    #-------------------1 DDR--------------------

    #-------------------4 DDR RTL Kernel Debug--------------------
    setup_dsa xilinx_aws-vu9p-f1_4ddr-xpr-2pr-debug_4_0 dsa_v11517_shell_v071417d3 AWS_PLATFORM_4DDR_DEBUG
    info_msg "AWS Platform: 4DDR RTL Kernel is up-to-date"
    #-------------------4 DDR RTL Kernel Debug--------------------
else
    #-------------------Dynamic 5.0 Platform----------------------
    setup_dsa xilinx_aws-vu9p-f1_dynamic_5_0 dsa_v041618_shell_v071417d3 AWS_PLATFORM_DYNAMIC_5_0
    info_msg "AWS Platform: Dynamic 5.0 Platform is up-to-date"
    #-------------------Dynamic 5.0 Platform----------------------
fi



# Start of runtime xdma driver install
cd $SDACCEL_DIR
info_msg "Building SDAccel runtime"
if ! make ec2=1 debug=1 RELEASE_VER=$RELEASE_VER; then
    err_msg "Build of SDAccel runtime FAILED"
    return 1
fi
info_msg "Installing SDAccel runtime"


if [[ ${RELEASE_VER} =~ .*2017\.1.* ]]; then
    
    export INSTALL_ROOT=/opt/Xilinx/SDx/${RELEASE_VER}.rte.1ddr
    if ! sudo make ec2=1 debug=1 INSTALL_ROOT=$INSTALL_ROOT SDK_DIR=$SDK_DIR XILINX_SDX=$XILINX_SDX SDACCEL_DIR=$SDACCEL_DIR RELEASE_VER=$RELEASE_VER DSA=xilinx_aws-vu9p-f1_1ddr-xpr-2pr_4_0 install ; then
        err_msg "Install of 1DDR SDAccel runtime FAILED"
        return 1
    fi

    export INSTALL_ROOT=/opt/Xilinx/SDx/${RELEASE_VER}.rte.4ddr
    if ! sudo make ec2=1 debug=1 INSTALL_ROOT=$INSTALL_ROOT SDK_DIR=$SDK_DIR XILINX_SDX=$XILINX_SDX SDACCEL_DIR=$SDACCEL_DIR RELEASE_VER=$RELEASE_VER DSA=xilinx_aws-vu9p-f1_4ddr-xpr-2pr_4_0 install ; then
        err_msg "Install of 4DDR SDAccel runtime FAILED"
        return 1
    fi

    export INSTALL_ROOT=/opt/Xilinx/SDx/${RELEASE_VER}.rte.4ddr_debug
    if ! sudo make ec2=1 debug=1 INSTALL_ROOT=$INSTALL_ROOT SDK_DIR=$SDK_DIR XILINX_SDX=$XILINX_SDX SDACCEL_DIR=$SDACCEL_DIR RELEASE_VER=$RELEASE_VER DSA=xilinx_aws-vu9p-f1_4ddr-xpr-2pr-debug_4_0 install ; then
        err_msg "Install of 4DDR DEBUG SDAccel runtime FAILED"
        return 1
    fi
    
    export AWS_PLATFORM=$AWS_PLATFORM_4DDR
    info_msg "The default AWS Platform has been set to: \"AWS_PLATFORM=\$AWS_PLATFORM_4DDR\" "
    info_msg "To change the platform for 1DDR:  \"export AWS_PLATFORM=\$AWS_PLATFORM_1DDR\" "
    info_msg "To change the platform for 4DDR Debug:  \"export AWS_PLATFORM=\$AWS_PLATFORM_4DDR_DEBUG\" "
else
    export INSTALL_ROOT=/opt/Xilinx/SDx/${RELEASE_VER}.rte.dyn
    if ! sudo make ec2=1 debug=1 INSTALL_ROOT=$INSTALL_ROOT SDK_DIR=$SDK_DIR XILINX_SDX=$XILINX_SDX SDACCEL_DIR=$SDACCEL_DIR RELEASE_VER=$RELEASE_VER DSA=xilinx_aws-vu9p-f1_dynamic_5_0 install ; then
        err_msg "Install of SDAccel runtime FAILED"
        return 1
    fi
    
    export AWS_PLATFORM=$AWS_PLATFORM_DYNAMIC_5_0
fi
info_msg "SDAccel runtime installed"

cd $current_dir

info_msg "SDAccel Setup PASSED"
