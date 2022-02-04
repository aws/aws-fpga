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

function usage {
    echo -e "USAGE: source [\$AWS_FPGA_REPO_DIR/]$script_name [-d|-debug] [-h|-help]"
}

function help {
    info_msg "$script_name"
    info_msg " "
    info_msg "Sets up the environment for AWS FPGA Vitis tools."
    info_msg " "
    info_msg "vitis_setup.sh script will:"
    info_msg "  (1) install FPGA Management Tools,"
    info_msg "  (2) check if Xilinx tools are available,"
    info_msg "  (3) check if required packages are installed,"
    info_msg "  (4) Download lastest AWS Platform,"
    info_msg "  (5) Install Runtime drivers "
    echo " "
    usage
}

function check_set_xilinx_vitis {
    if [[ ":$XILINX_VITIS" == ':' ]]; then
        debug_msg "XILINX_VITIS is not set"
        which vitis
        RET=$?
        if [ $RET != 0 ]; then
            debug_msg "vitis not found in path."
            err_msg "XILINX_VITIS variable not set and vitis not in the path"
            err_msg "Please set XILINX_VITIS variable to point to your location of your Xilinx installation or add location of vitis exectuable to your PATH variable"
            return $RET
        else
            export XILINX_VITIS=`which vitis | sed 's:/bin/vitis::'`
            info_msg "Setting XILINX_VITIS to $XILINX_VITIS"
        fi
    else
        info_msg "XILINX_VITIS is already set to $XILINX_VITIS"
    fi
    # get Vitis release version, i.e. "2019.2"
    RELEASE_VER=$(basename $XILINX_VITIS)
    RELEASE_VER=${RELEASE_VER:0:6}
    export RELEASE_VER=$RELEASE_VER
    echo "RELEASE_VER equals $RELEASE_VER"
}

function check_install_packages_centos {
#TODO: Check required packages are installed or install them
#TODO: Check version of gcc is above 4.8.5 (4.6.3 does not work)
  for pkg in `cat $VITIS_DIR/packages.txt`; do
    if yum list installed "$pkg" >/dev/null 2>&1; then
      true
    else
      warn_msg " $pkg not installed - please run: sudo yum install $pkg "
    fi
  done
}

function check_install_packages_ubuntu {
  for pkg in `cat $VITIS_DIR/packages.txt`; do
    if apt -qq list "$pkg" >/dev/null 2>&1; then
      true
    else
      warn_msg " $pkg not installed - please run: sudo apt-get install $pkg "
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

# Check XILINX_VITIS is set
if ! check_set_xilinx_vitis; then
    return 1
fi

info_msg " XILINX_VITIS is set to $XILINX_VITIS"
# Install patches as required.
info_msg "Setting up Vitis patches if required."
setup_patches


# Update Xilinx Vitis Examples from GitHub
info_msg "Using Vitis $RELEASE_VER"
if [[ $RELEASE_VER =~ .*2019\.2.*  ||  $RELEASE_VER =~ .*2020\.* ||  $RELEASE_VER =~ .*2021\.* ]]; then
    info_msg "Updating Xilinx Vitis Examples $RELEASE_VER"
    git submodule update --init -- Vitis/examples/xilinx_$RELEASE_VER
    export VIVADO_TOOL_VER=$RELEASE_VER
    if [ -e $VITIS_DIR/examples/xilinx ]; then
        if [ ! -L $VITIS_DIR/examples/xilinx ]; then
          err_msg "ERROR:  Vitis/examples/xilinx is not a symbolic link.  Backup any data and remove Vitis/examples/xilinx directory.  The setup needs to create a symbolic link from Vitis/examples/xilinx to Vitis/examples/xilinx_$RELEASE_VER"
          return 1
        fi
    fi
    ln -sf $VITIS_DIR/examples/xilinx_$RELEASE_VER $VITIS_DIR/examples/xilinx
else
   echo " $RELEASE_VER is not supported (2019.2, 2020.1, 2020.2, 2021.1 or 2021.2 are supported).\n"
   return 2
fi

# Check if internet connection is available
if ! check_internet; then
    return 1
fi

# Check ICD is installed
if ! check_icd; then
    return 1
fi

# Check correct packages are installed

if [[ $(lsb_release -si) == "Centos" ]]; then
    if ! check_install_packages_centos; then
        return 1
    fi
elif [[ $(lsb_release -si) == "Ubuntu" ]]; then
    if ! check_install_packages_ubuntu; then
        return 1
    fi
#elif [[ $(lsb_release -si) == "Ubuntu" ]]; then
#    if ! check_install_packages_ubuntu; then
#        return 1
#    fi
fi

function setup_xsa {

    if [ "$#" -ne 3 ]; then
        err_msg "Illegal number of parameters sent to the setup_xsa function!"
        return 1
    fi

    XSA=$1
    XSA_S3_BASE_DIR=$2
    PLATFORM_ENV_VAR_NAME=$3

    xsa_dir=$VITIS_DIR/aws_platform/$XSA/hw/
    vitis_xsa=$xsa_dir/$XSA.xsa
    vitis_xsa_s3_bucket=aws-fpga-hdk-resources
    s3_vitis_xsa=$vitis_xsa_s3_bucket/Vitis/$XSA_S3_BASE_DIR/$XSA/$XSA.xsa

    # set a variable to point to the platform for build and emulation runs
    export "$PLATFORM_ENV_VAR_NAME"=$VITIS_DIR/aws_platform/$XSA/$XSA.xpfm

    # Download the sha256
    if [ ! -e $xsa_dir ]; then
        mkdir -p $xsa_dir || { err_msg "Failed to create $xsa_dir"; return 2; }
    fi

    # Use curl instead of AWS CLI so that credentials aren't required.
    curl -s https://s3.amazonaws.com/$s3_vitis_xsa.sha256 -o $vitis_xsa.sha256 || { err_msg "Failed to download XSA version from $s3_vitis_xsa.sha256 -o $vitis_xsa.sha256"; return 2; }
    if grep -q '<?xml version' $vitis_xsa.sha256; then
        err_msg "Failed to download VITIS XSA version from $s3_vitis_xsa.sha256"
        cat vitis_xsa.sha256
        return 2
    fi
    exp_sha256=$(cat $vitis_xsa.sha256)
    debug_msg "  latest   version=$exp_sha256"
    # If XSA already downloaded check its sha256
    if [ -e $vitis_xsa ]; then
        act_sha256=$( sha256sum $vitis_xsa | awk '{ print $1 }' )
        debug_msg "  existing version=$act_sha256"
        if [[ $act_sha256 != $exp_sha256 ]]; then
            info_msg "VITIS XSA version is incorrect"
            info_msg "  Saving old XSA to $vitis_xsa.back"
            mv $vitis_xsa $vitis_xsa.back
        fi
    else
        info_msg "VITIS XSA hasn't been downloaded yet."
    fi

    if [ ! -e $vitis_xsa ]; then
        info_msg "Downloading latest VITIS XSA from $s3_vitis_xsa"
        # Use curl instead of AWS CLI so that credentials aren't required.
        curl -s https://s3.amazonaws.com/$s3_vitis_xsa -o $vitis_xsa || { err_msg "VITIS XSA download failed"; return 2; }
    fi
    # Check sha256
    act_sha256=$( sha256sum $vitis_xsa | awk '{ print $1 }' )
    if [[ $act_sha256 != $exp_sha256 ]]; then
        err_msg "Incorrect VITIS XSA version:"
        err_msg "  expected version=$exp_sha256"
        err_msg "  actual   version=$act_sha256"
        err_msg "  There may be an issue with the uploaded XSA or the download failed."
        return 2
    fi
}

    #-------------------201920_3 Vitis Platform----------------------
    setup_xsa xilinx_aws-vu9p-f1_shell-v04261818_201920_3 xsa_v121319_shell_v04261818 AWS_PLATFORM_201920_3
    info_msg "AWS Platform: 201920_3 Vitis Platform is up-to-date"
    #-------------------201920_3 Vitis Platform----------------------


# Setup XRT as we need it for building
setup_runtime

export AWS_PLATFORM=$AWS_PLATFORM_201920_3
info_msg "The default AWS Platform has been set to: \"AWS_PLATFORM=\$AWS_PLATFORM_201920_3\" "

info_msg "Vitis Setup PASSED"

info_msg "To run a runtime example, start the MPD service by calling: \`systemctl is-active --quiet mpd || sudo systemctl start mpd\`"
