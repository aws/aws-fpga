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

XILINX_VITIS_XRT_DIR="/opt/xilinx/xrt"

dev_xsa_loc="/opt/XSA"
export PLATFORM_REPO_PATHS=/opt/XSA/xilinx_aws-vu47p-f2_202410_1

if ! source $XILINX_VITIS/settings64.sh; then
    err_msg "Setup of Xilinx 64-bit settings FAILED"
    return 1
fi
if ! source $script_dir/shared/bin/set_common_functions.sh; then
    err_msg "Setup of common functions FAILED"
    return 1
fi
if ! source $script_dir/shared/bin/set_common_env_vars.sh; then # Sets VITIS_DIR for the line below
    err_msg "Setup of common environment variables FAILED"
    return 1
fi
if ! source $VITIS_DIR/runtime/xrt_common_functions.sh; then
    err_msg "XRT Common Functions initialization FAILED"
    return 1
fi

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
            export XILINX_VITIS=$(which vitis | sed 's:/bin/vitis::')
            info_msg "Setting XILINX_VITIS to $XILINX_VITIS"
        fi
    else
        info_msg "XILINX_VITIS is already set to $XILINX_VITIS"
    fi
    # get Vitis release version, i.e. "2019.2"
    RELEASE_VER=$(basename $XILINX_VITIS)
    RELEASE_VER=${RELEASE_VER:0:6}
    export RELEASE_VER=$RELEASE_VER
    export VIVADO_TOOL_VER=$RELEASE_VER
    echo "RELEASE_VER equals $RELEASE_VER"
}

function check_install_packages_ubuntu {
    for pkg in $(cat $VITIS_DIR/packages.txt); do
        if apt -qq list "$pkg" >/dev/null 2>&1; then
            true
        else
            warn_msg " $pkg not installed - please run: sudo apt-get install $pkg "
        fi
    done
}

function check_internet {
    wget http://www.amazon.com --spider --timeout=30 --quiet
    RET=$?
    if [[ $RET != 0 && $RET != 8 ]]; then
        err_msg "wget cannot connect to the internet using please check your internet connection or proxy settings"
        err_msg "To check your connection run:   wget http://www.amazon.com --spider --timeout=30 --quiet"
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
args=("$@")
for ((i = 0; i < ${#args[@]}; i++)); do
    arg=${args[$i]}
    case $arg in
    -d | -debug)
        debug=1
        ;;
    -h | -help)
        help
        return 0
        ;;
    *)
        err_msg "Invalid option: $arg\n"
        usage
        return 1
        ;;
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
if [[ $RELEASE_VER =~ .*2024\.* ]]; then

    export VIVADO_TOOL_VER=$RELEASE_VER
    vitis_exs_repo_name=Vitis_Accel_Examples
    vitis_exs_repo_url=https://github.com/Xilinx/Vitis_Accel_Examples.git
    if [[ ! -d $VITIS_DIR/examples/$vitis_exs_repo_name ]]; then
        mkdir -p $VITIS_DIR/examples/
        cd $VITIS_DIR/examples/
        git clone $vitis_exs_repo_url
        git submodule init
        git submodule update
        cd $vitis_exs_repo_name
        git checkout $RELEASE_VER
        cd ..
    fi

    if [[ -d $VITIS_DIR/examples/vitis_examples ]]; then
        if [[ ! -L $VITIS_DIR/examples/vitis_examples ]]; then
            err_msg "vitis/examples/vitis_examples is not a symbolic link.  Backup any data and remove Vitis/examples/vitis_examples directory.  The setup needs to create a symbolic link from Vitis/examples/vitis_examples to Vitis/examples/vitis_examples_$RELEASE_VER"
            return 1
        else
            info_msg "vitis/examples/vitis_examples symbolic link correctly set up!"
        fi
    else
        ln -sf $VITIS_DIR/examples/$vitis_exs_repo_name $VITIS_DIR/examples/vitis_examples
    fi

else
    echo " $RELEASE_VER is not supported. Only 2024.1 is supported.\n"
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

if [[ $(lsb_release -si) == "Ubuntu" ]]; then
    if [[ ! check_install_packages_ubuntu ]]; then
        return 1
    fi
else
    echo "Only Ubuntu 20.04 is currently supported for F2 EC2 instances."
fi

function sha256_check {
    sha_file=$1
    xsa_file=$2
    s3_sha=$(awk '{print $1}' $sha_file)
    local_sha=$(sha256sum "$2" | awk '{print $1}')

    if [[ "$s3_sha" != "$local_sha" ]]; then
        err_msg "SHA256 mismatch for $2"
        info_msg "Moving existing $2 to $2.back"
        mv $2 $2.back
        return 1
    fi

    return 0
}

function setup_xsa {

    info_msg "Installing supporting libraries"
    export DEBIAN_FRONTEND=noninteractive
    sudo DEBIAN_FRONTEND=noninteractive $XILINX_VITIS/scripts/installLibs.sh >>/dev/null
    rm installLibs.sh_*

    if [ "$#" -ne 3 ]; then
        err_msg "Illegal number of parameters sent to the setup_xsa function!"
        return 1
    fi

    XSA=$1
    XSA_S3_BASE_DIR=$2
    PLATFORM_ENV_VAR_NAME=$3

    export SHELL_EMU_VERSION=$XSA

    xsa_dir=$VITIS_DIR/aws_platform/$XSA
    vitis_xsa=$xsa_dir/$XSA.xsa

    vitis_xsa_s3_url=https://aws-fpga-hdk-resources.s3.amazonaws.com/Vitis/$XSA_S3_BASE_DIR/$XSA

    vitis_xpfm=$XSA.xpfm
    vitis_xpfm_dir=/opt/Xilinx/Vitis/${RELEASE_VER}/platforms
    s3_vitis_xpfm=$vitis_xsa_s3_url/$XSA.xpfm

    vitis_hw_dir=$vitis_xpfm_dir/hw
    vitis_hw_emu_dir=$vitis_xpfm_dir/hw_emu
    vitis_sw_dir=$vitis_xpfm_dir/sw

    s3_vitis_hw_xsa=$vitis_xsa_s3_url/hw.xsa
    s3_vitis_hw_emu_xsa=$vitis_xsa_s3_url/hw_emu.xsa
    s3_vitis_sw_spfm=$vitis_xsa_s3_url/sw.spfm

    # set a variable to point to the platform for build and emulation runs
    export "$PLATFORM_ENV_VAR_NAME"=$VITIS_DIR/aws_platform/$XSA/$XSA.xpfm

    cd $AWS_FPGA_REPO_DIR

    if [ ! -e $vitis_hw_dir ]; then
        sudo mkdir -p $vitis_hw_dir
    fi

    if [ ! -e $vitis_hw_emu_dir ]; then
        sudo mkdir -p $vitis_hw_emu_dir
    fi

    if [ ! -e $vitis_sw_dir ]; then
        sudo mkdir -p $vitis_sw_dir
    fi

    if [ ! -d $xsa_dir ]; then
        mkdir -p $xsa_dir
    fi

    if [ ! -e $xsa_dir/$vitis_xpfm ]; then
        if ! wget $s3_vitis_xpfm -O $xsa_dir/$vitis_xpfm -q; then
            err_msg "Download of $s3_vitis_xpfm failed!"
            return 2
        fi
        sudo mv $xsa_dir/$vitis_xpfm $vitis_xpfm_dir
    else
        info_msg "Vitis XSA platform file already downloaded!"
    fi

    # Grab all XSAs
    for missing_xsa in "hw.xsa" "hw_emu.xsa" "sw.spfm"; do
        if [ ! -e $xsa_dir/$missing_xsa ]; then
            if ! wget $vitis_xsa_s3_url/$missing_xsa -O $xsa_dir/$missing_xsa -q; then
                err_msg "Download of Vitis XSA file $missing_xsa failed!"
                return 1
            fi
            # Gets the stem of the XSA file
            destination_dir=$(echo "${missing_xsa%.*}")
            sudo cp $xsa_dir/$missing_xsa $vitis_xpfm_dir/$destination_dir
        fi
    done

    # Grab all XSA SHA256 checksums
    for missing_sha in "hw.xsa.sha256" "hw_emu.xsa.sha256" "sw.spfm.sha256"; do
        if [ ! -e $xsa_dir/$missing_sha ]; then
            if ! wget $vitis_xsa_s3_url/$missing_sha -O $xsa_dir/$missing_sha -q; then
                err_msg "Download of Vitis XSA SHA256 file $missing_sha failed!"
                return 1
            fi
        fi
    done

    # Check those sums
    sha_mismatches=0
    for xsa_file in "hw.xsa" "hw_emu.xsa" "sw.spfm"; do
        if ! sha256_check $xsa_dir/$xsa_file.sha256 $xsa_dir/$xsa_file; then
            sha_mismatches=1
        fi
    done

    if [ $sha_mismatches -ne 0 ]; then
        return 1
    fi

}

function xrt_install_check {
    
    xrt_path=/opt/xilinx/xrt
    if [[ -n $(lsmod | grep "xocl") ]]; then
        info_msg "###############################################################################"
        info_msg "#                              XRT install detected!                          #"
        info_msg "# If XRT was installed using the devkit, run 'source /opt/xilinx/xrt/setup.sh #"
        info_msg "#        Otherwise, please source your XRT setup script, 'setup.sh'           #"
        info_msg "#                     To reinstall, run 'install_xrt -f'!                     #"
        info_msg "###############################################################################"
        return 2
    fi
    info_msg "###########################################################################"
    info_msg "#                       No XRT install detected!                          #"
    info_msg "#     To install the XRT for Vitis runtime support, run 'install_xrt'     #"
    info_msg "###########################################################################"
    return 0
}

function install_xrt {
    xrt_path=/opt/xilinx/xrt
    xrt_dpkg_install_path=$xrt_path/XRT/build/Release

    xrt_repo_name=XRT
    xrt_repo_url=https://github.com/Xilinx/XRT.git
    xrt_branch=2024.1
    xrt_2024_1_working_commit_hash=ea9e7d2d88719e08575dca15d2ca2c1ce624e800
    xrt_deps_script_path=src/runtime_src/tools/scripts/xrtdeps.sh
    xrt_build_script_run="build/build.sh -noert"
    xrt_build_release_dir="build/Release"
    xrt_setup_script_path=$xrt_path/setup.sh

    if [[ -z $AWS_FPGA_REPO_DIR ]]; then
        err_msg "\$AWS_FPGA_REPO_DIR not defined when trying to install XRT!"
        cd $AWS_FPGA_REPO_DIR && return 1
    fi

    xrt_install_check
    if [[ $? -eq 0 || $1 == "-f" || $1 == "--force" ]]; then
        if [[ -n $(echo $PATH | grep "cmake-3.3.2") ]]; then
            export PATH="/usr/bin:$PATH"
        fi

        cd $HOME
        if [[ ! -d $xrt_repo_name ]]; then
            info_msg "Cloning XRT repo into home directory: $HOME"
            info_msg "This directory may be moved to any destination, once the XRT install is complete!"
            if ! git clone $xrt_repo_url --recurse-submodules; then
                err_msg "Couldn't clone XRT repository!"
                cd $AWS_FPGA_REPO_DIR && return 1
            fi
        else
            info_msg "XRT repo found in $HOME"
        fi

        cd $xrt_repo_name
        if ! git fetch; then
            err_msg "Couldn't fetch updated references for XRT repo!"
            cd $AWS_FPGA_REPO_DIR && return 1
        fi

        if ! git checkout $xrt_branch; then
            err_msg "Couldn't checkout branch: $xrt_branch!"
            cd $AWS_FPGA_REPO_DIR && return 1
        fi

        if ! git checkout $xrt_2024_1_working_commit_hash; then
            err_msg "Couldn't checkout compatible commit: $xrt_2024_1_working_commit_hash!"
            cd $AWS_FPGA_REPO_DIR && return 1
        fi

        if ! sudo ./$xrt_deps_script_path; then
            err_msg "Couldn't install XRT dependencies!"
            cd $AWS_FPGA_REPO_DIR && return 1
        fi

        if ! ./$xrt_build_script_run; then
            err_msg "Couldn't build XRT dpkgs!"
            cd $AWS_FPGA_REPO_DIR && return 1
        fi

        cd $xrt_build_release_dir

        # Base XRT install first
        for file in $(ls *amd64-xrt.deb); do
            sudo dpkg -i $file
        done

        # AWS extension install
        for file in $(ls *amd64-aws.deb); do
            sudo dpkg -i $file
        done

        if ! source $xrt_setup_script_path; then
            err_msg "Couldn't setup XRT after install!"
            cd $AWS_FPGA_REPO_DIR && return 1
        fi

        info_msg "XRT installation complete!"
        cd $AWS_FPGA_REPO_DIR
        return 0
    fi
    info_msg "XRT already installed!"
    info_msg "Nothing to do!"
    return 0
}

function hw_file_check {
    required_files=("Makefile" "README.rst" "description.json" "details.rst" "makefile_us_alveo.mk" "qor.json" "utils.mk" "xrt.ini")
    missing_a_file=0
    for file in ${required_files[@]}; do
        if [[ ! -e $file ]]; then
            err_msg "!!! Required file: $file not found in current example directory !!!"
            missing_a_file=1
        fi
    done
    if [[ missing_a_file -eq 1 ]]; then
        return 1
    fi
    info_msg "All required simulation files are present!"
}

#-------------------2024.1 Vitis Platform----------------------
xsa_name=xilinx_aws-vu47p-f2_202410_1
shell_name=xsa_f2_2024_1
aws_platform_name=AWS_PLATFORM_202410_0
if ! setup_xsa $xsa_name $shell_name $aws_platform_name; then
    err_msg "!!! Vitis Setup FAILED !!!"
    return 2
fi
#-------------------2024.1 Vitis Platform----------------------

platform_file_name="$xsa_name.xpfm"
if [[ ! -e vitis/aws_platform/$xsa_name/$platform_file_name ]]; then
    info_msg "Locating AWS platform file"
    if [[ ! -e /opt/Xilinx/Vitis/${RELEASE_VER}/platforms/$platform_file_name ]]; then
        err_msg "Couldn't locate AWS platform file!"
        return 1
    fi
    if ! sudo cp /opt/Xilinx/Vitis/${RELEASE_VER}/platforms/$platform_file_name vitis/aws_platform/$xsa_name; then
        err_msg "Couldn't copy platform file to AWS platform directory!"
        return 1
    fi
fi

xrt_install_check
if [[ $? -eq 1 ]]; then
    err_msg "!!! Vitis Setup FAILED !!!"
    return $?
fi

info_msg "Vitis Setup PASSED"

export AWS_PLATFORM=$AWS_PLATFORM_202410_0
info_msg "The default AWS Platform has been set to: \"AWS_PLATFORM=\$AWS_PLATFORM_202410_0\" "

echo ""
info_msg "#-------------------------------------------------------------------------------#"
info_msg "How to run hardware emulation or synthesis on an example"
info_msg "cd vitis/examples/vitis_examples/hello_world"
info_msg "hw_file_check"
info_msg "#----------------------------- Emulation ---------------------------------------#"
info_msg "make build TARGET=hw_emu PLATFORM=\$SHELL_EMU_VERSION"
info_msg "#-------------------------------------------------------------------------------#"
