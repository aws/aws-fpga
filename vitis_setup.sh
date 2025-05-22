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
distro=$(sed -n 's/^NAME="\([^"]*\)"/\1/p' /etc/os-release)


function vitis_usage {
    echo -e "USAGE: source [\$AWS_FPGA_REPO_DIR]/$script_name [-h|-help]"
    return 0
}


function vitis_help {
    info_msg "$script_name"
    info_msg " "
    info_msg "Sets up the environment for AWS FPGA Vitis tools."
    info_msg " "
    info_msg "vitis_setup.sh script will:"
    info_msg "  (1) install FPGA Management Tools,"
    info_msg "  (2) check if Xilinx tools are available,"
    info_msg "  (3) check if required packages are installed,"
    info_msg "  (4) Download lastest AWS platform,"
    info_msg "  (5) Prepare environment to install runtime drivers "
    echo " "
    vitis_usage
    return 0
}


function check_xilinx_vitis {
    if [[ -z $XILINX_VITIS ]]; then
        err_msg "XILINX_VITIS not set!"
        info_msg "Please submit a question on RePost under the FPGA Development tag: "
        info_msg "    https://repost.aws/questions?view=all\&sort=recent\&tagIds=TAc7ofO5tbQRO57aX1lBYbjA"
        return 1
    fi
    RELEASE_VER=$(basename $XILINX_VITIS)
    RELEASE_VER=${RELEASE_VER:0:6}
    export RELEASE_VER="${RELEASE_VER}"
    export VIVADO_TOOL_VER=$(echo "${RELEASE_VER}" | tr -d '[:space:]')
    info_msg "RELEASE_VER = ${RELEASE_VER}"
    return 0
}


declare -A valid_tool_versions
valid_tool_versions["2024.1"]="true"
valid_tool_versions["2024.2"]="true"

declare -A valid_os
valid_os["Ubuntu"]="true"
valid_os["AlmaLinux"]="true"

function check_os_and_tool_ver {
    if [[ "${valid_tool_versions[${VIVADO_TOOL_VER}]}" != "true" ]]; then
        err_msg "Unsupported Vivado tool version detected: ${VIVADO_TOOL_VER}!!!"
        info_msg "Supported versions are: 2024.1 and 2024.2"
        return 1
    fi

    echo "Distro: ${distro}"
    if [[ "${valid_os[${distro}]}" != "true" ]]; then
        err_msg "Unsupported OS detected!!!"
        info_msg "Supported OS are: Ubuntu 24.04, Ubuntu 20.04, and AlmaLinux 9.4"
        return 1
    fi
    return 0
}


function check_internet {
    info_msg "Checking instance internet connection"
    if ! curl -I -s --max-time 5 https://www.google.com 2>/dev/null; then
        err_msg "No internet access detected!"
        return 1
    fi
    info_msg "Active internet connection detected!"
    return 0
}


function check_icd {
    icd_path=/etc/OpenCL/vendors/xilinx.icd
    icd_so_entry=libxilinxopencl.so

    info_msg "Checking for ICD installation"
    if [[ $(cat $icd_path) == *"${icd_so_entry}"* ]]; then
        info_msg "Found ${icd_so_entry}"
    else
        motd_contents=$(cat /etc/motd)
        if [[ "${motd_contents}" == *"aws-fpga"* ]]; then
            err_msg "No entry for ${icd_so_entry} found in ${icd_path} on Developer AMI!"
            info_msg "Please submit a question on RePost under the FPGA Development tag: "
            info_msg "    https://repost.aws/questions?view=all\&sort=recent\&tagIds=TAc7ofO5tbQRO57aX1lBYbjA"
            return 1
        else
            info_msg "Detected use of non FPGA Developer AMI!"
            info_msg "Make sure that your OpenCL ICD installation is valid for ${icd_so_entry}!"
        fi
    fi
    return 0
}


function set_up_vitis_examples {

    vitis_exs_repo_name="Vitis_Accel_Examples"
    vitis_exs_repo_url="https://github.com/Xilinx/Vitis_Accel_Examples.git"
    if [[ ! -d "$VITIS_DIR/examples/$vitis_exs_repo_name" ]]; then
        mkdir -p $VITIS_DIR/examples/
        cd $VITIS_DIR/examples/

        if ! git clone "${vitis_exs_repo_url}" --recurse-submodules; then
            err_msg "Couldn't clone in ${vitis_exs_repo_name} repo!"
            return 1
        fi

        cd $vitis_exs_repo_name
        if ! git checkout "${VIVADO_TOOL_VER}"; then
            err_msg "Couldn't check out ${VIVADO_TOOL_VER} branch of ${vitis_exs_repo_name}"
            return 1
        fi
        cd ..
    fi

    if [[ -d "${VITIS_DIR}/examples/vitis_examples" && ! -L "${VITIS_DIR}/examples/vitis_examples" ]]; then
        err_msg "Directory ${VITIS_DIR}/examples/vitis_examples already exists!"
        info_msg "Please remove this directory, then run again!"
        return 1
    fi

    if [[ ! -L "${VITIS_DIR}/examples/vitis_examples" ]]; then
        if ! ln -sf "${VITIS_DIR}/examples/${vitis_exs_repo_name}" "${VITIS_DIR}/examples/vitis_examples"; then
            err_msg "Could not set up symbolic link to Vitis_Accel_Examples repo!"
            return 1
        fi
    else
        info_msg "vitis/examples/vitis_examples symbolic link correctly set up!"
    fi
    return 0
}


function sha256_check {
    sha_file=$1
    xsa_file=$2
    s3_sha=$(awk '{print $1}' $sha_file)
    local_sha=$(sha256sum "$2" | awk '{print $1}')

    if [[ "${s3_sha}" != "${local_sha}" ]]; then
        err_msg "SHA256 mismatch for $2"
        info_msg "Moving existing $2 to $2.back"
        sudo mv $2 $2.back
        return 1
    fi

    return 0
}


function get_sha_file {
    missing_sha="${missing_xsa}.sha256"
    if [ ! -e "${vitis_xpfm_dir}/${missing_sha}" ]; then
        if ! sudo wget "${vitis_xsa_s3_url}/${missing_sha}" -O "${vitis_xpfm_dir}/${missing_sha}" -q; then
            err_msg "Download of Vitis XSA SHA256 file ${missing_sha} failed!"
            return 1
        fi
    fi

    sha_path=""
    if [[ "${missing_xsa}" != "${vitis_xpfm}" ]]; then
        sha_path="${vitis_xpfm_dir}/${missing_xsa%.*}/${missing_xsa}"
    else
        sha_path="${vitis_xpfm_dir}/${missing_xsa}"
    fi
    if ! sha256_check "${vitis_xpfm_dir}/${missing_xsa}.sha256" "${sha_path}"; then
        sha_mismatches=1
    fi
    return 0
}


function get_xsa_file {
    if [ ! -e "${vitis_xpfm_dir}/${missing_xsa}" ]; then
        if ! sudo wget "${vitis_xsa_s3_url}/${missing_xsa}" -O "${vitis_xpfm_dir}/${missing_xsa}" -q; then
            err_msg "Download of Vitis XSA file ${missing_xsa} failed!"
            return 1
        fi
        if [[ "${missing_xsa}" != "${vitis_xpfm}" ]]; then
            # Gets the stem of the XSA file
            destination_dir=$(echo "${missing_xsa%.*}")
            sudo mv "${vitis_xpfm_dir}/${missing_xsa}" "${vitis_xpfm_dir}/${destination_dir}"
        fi
    else
        info_msg "Vitis XSA file $missing_xsa already downloaded!"
    fi
    return 0
}


function create_xsa_dirs {
    vitis_xpfm_dir=/opt/Xilinx/Vitis/${VIVADO_TOOL_VER}/platforms
    vitis_hw_dir=$vitis_xpfm_dir/hw
    vitis_hw_emu_dir=$vitis_xpfm_dir/hw_emu
    vitis_sw_dir=$vitis_xpfm_dir/sw

    xsa_dirs=(
        "${vitis_hw_dir}"
        "${vitis_hw_emu_dir}"
        "${vitis_sw_dir}"
    )

    for dir in "${xsa_dirs[@]}"; do
        if [ ! -d $dir ]; then
            if ! sudo mkdir -p $dir; then
                err_msg "Couldn't create directory $dir!"
                return 1
            fi
        fi
    done
    return 0
}


declare -A xsa_dir_map
xsa_dir_map["2024.1"]="2024_1_2"
xsa_dir_map["2024.2"]="2024_2"

declare -A xsa_map
xsa_map["2024.1"]="202410_1_2"
xsa_map["2024.2"]="202420_1"


function setup_xsa {

    info_msg "Installing supporting libraries"
    export DEBIAN_FRONTEND=noninteractive
    sudo DEBIAN_FRONTEND=noninteractive $XILINX_VITIS/scripts/installLibs.sh >>/dev/null
    rm installLibs.sh_*

    # Get XSA for right tool version
    xsa_for_tool_ver="${xsa_map[${VIVADO_TOOL_VER}]}"
    XSA="xilinx_aws-vu47p-f2_${xsa_for_tool_ver}"
    export SHELL_EMU_VERSION="${XSA}"

    XSA_S3_BASE_DIR="xsa_f2_${xsa_dir_map[${VIVADO_TOOL_VER}]}"

    if ! create_xsa_dirs; then
        return 1
    fi

    # set a variable to point to the platform for build and emulation runs
    vitis_xpfm="${XSA}.xpfm"
    PLATFORM_ENV_VAR_NAME="AWS_PLATFORM_${xsa_for_tool_ver}"
    export "${PLATFORM_ENV_VAR_NAME}"="${vitis_xpfm_dir}/${vitis_xpfm}"
    export PLATFORM_REPO_PATHS="${XILINX_VITIS}/platforms/${vitis_xpfm}"

    # Grab all XSAs, check their SHAs, and move to necessary Vitis dir
    xsas=(
        "hw.xsa"
        "hw_emu.xsa"
        "sw.spfm"
        "${vitis_xpfm}"
    )
    sha_mismatches=0
    vitis_xsa_s3_url="https://aws-fpga-hdk-resources.s3.amazonaws.com/Vitis/${XSA_S3_BASE_DIR}/${XSA}"
    for missing_xsa in "${xsas[@]}"; do
        if ! get_xsa_file; then
            return 1
        fi

        if ! get_sha_file; then
            return 1
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
        info_msg "#                Attempting to source XRT setup script, 'setup.sh'            #"
        info_msg "###############################################################################"
        source $xrt_path/setup.sh
    else
        info_msg "###########################################################################"
        info_msg "#                       No XRT install detected!                          #"
        info_msg "#     To install the XRT for Vitis runtime support, run 'install_xrt'     #"
        info_msg "###########################################################################"
    fi
    return 0
}


declare -A xrt_install_map
xrt_install_map["Ubuntu_pkg_ext"]="deb"
xrt_install_map["Ubuntu_install_cmd"]="sudo dpkg -i"
xrt_install_map["Ubuntu_xrt_pkg_prefix"]="amd64-xrt"
xrt_install_map["Ubuntu_aws_pkg_prefix"]="amd64-aws"

xrt_install_map["AlmaLinux_pkg_ext"]="rpm"
xrt_install_map["AlmaLinux_install_cmd"]="sudo dnf install -y"
xrt_install_map["AlmaLinux_xrt_pkg_prefix"]="x86_64-xrt"
xrt_install_map["AlmaLinux_aws_pkg_prefix"]="x86_64-aws"


function build_and_install_xrt {
    if ! sudo -E ./$xrt_deps_script_path; then
        err_msg "Couldn't install XRT dependencies!"
        cd $AWS_FPGA_REPO_DIR && return 1
    fi

    if ! ./$xrt_build_script_run; then
        err_msg "Couldn't build XRT dpkgs!"
        cd $AWS_FPGA_REPO_DIR && return 1
    fi

    cd $xrt_build_release_dir

    install_pkg_ext="${xrt_install_map[${distro}_pkg_ext]}"
    xrt_pkg_prefix="${xrt_install_map[${distro}_xrt_pkg_prefix]}"
    aws_pkg_prefix="${xrt_install_map[${distro}_aws_pkg_prefix]}"
    install_cmd="${xrt_install_map[${distro}_install_cmd]}"

    # Base XRT install first
    for file in $(ls *${xrt_pkg_prefix}.${install_pkg_ext}); do
        info_msg "Installing $file"
        $install_cmd $file
    done

    # AWS extension install
    for file in $(ls *${aws_pkg_prefix}.${install_pkg_ext}); do
        info_msg "Installing $file"
        $install_cmd $file
    done

    if ! source $xrt_setup_script_path; then
        err_msg "Couldn't setup XRT after install!"
        cd $AWS_FPGA_REPO_DIR && return 1
    fi

    info_msg "XRT installation complete!"
    cd $AWS_FPGA_REPO_DIR
    return 0
}


function set_up_xrt_repo {
    if [[ -n "$(echo $PATH | grep "cmake-3.3.2")" ]]; then
        export PATH="/usr/bin:$PATH"
    fi
    cd $HOME
    if [[ ! -d $xrt_repo_name ]]; then
        info_msg "Cloning XRT repo into home directory: ${HOME}"
        info_msg "This directory may be moved to any destination, once the XRT install is complete!"
        if ! git clone $xrt_repo_url --recurse-submodules; then
            err_msg "Couldn't clone XRT repository!"
            cd $AWS_FPGA_REPO_DIR && return 1
        fi
    else
        info_msg "XRT repo found in ${HOME}"
    fi

    cd $xrt_repo_name
    if ! git fetch; then
        err_msg "Couldn't fetch updated references for XRT repo!"
        cd $AWS_FPGA_REPO_DIR && return 1
    fi

    if ! git checkout $xrt_branch; then
        err_msg "Couldn't checkout branch: ${xrt_branch}!"
        cd $AWS_FPGA_REPO_DIR && return 1
    fi

    if ! git checkout $xrt_working_commit_hash; then
        err_msg "Couldn't checkout compatible commit: ${xrt_working_commit_hash}!"
        cd $AWS_FPGA_REPO_DIR && return 1
    fi
    return 0
}


declare -A commit_hash_map
commit_hash_map["2024.1"]="7c27d759993a184bb7782fa9af0b3b7a92de5d32"
commit_hash_map["2024.2"]="a3f9984cdcf687d1cd960b3b6270a097516de3b5"


function set_up_xrt_vars {
    if [[ -z "${AWS_FPGA_REPO_DIR}" ]]; then
        err_msg "\$AWS_FPGA_REPO_DIR not defined when trying to install XRT!"
        cd $HOME && return 1
    fi

    xrt_path="/opt/xilinx/xrt"
    xrt_dpkg_install_path="${xrt_path}/XRT/build/Release"

    xrt_repo_name="XRT"
    xrt_repo_url="https://github.com/Xilinx/XRT.git"
    xrt_deps_script_path="src/runtime_src/tools/scripts/xrtdeps.sh"
    xrt_build_script_run="build/build.sh -noert"
    xrt_build_release_dir="build/Release"
    xrt_setup_script_path="${xrt_path}/setup.sh"
    xrt_branch="${VIVADO_TOOL_VER}"
    xrt_working_commit_hash="${commit_hash_map[${VIVADO_TOOL_VER}]}"

    return 0
}


function install_xrt {

    if ! set_up_xrt_vars; then
        return 1
    fi

    if [[ -n $(lsmod | grep "xdma") ]]; then
        info_msg "###############################################################################"
        info_msg "#                      XDMA driver install detected!                          #"
        info_msg "#             XDMA driver install prevents XRT functionality!                 #"
        info_msg "#              Uninstall XDMA driver and re-run 'install_xrt'                 #"
        info_msg "###############################################################################"
        cd $AWS_FPGA_REPO_DIR && return 1
    fi

    if [[ -z $(lsmod | grep "xocl") ]]; then
        if ! set_up_xrt_repo; then
            return 1
        fi

        if ! build_and_install_xrt; then
            return 1
        fi
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


function pre_flight_checks {

    # Process command line args
    args=("$@")
    for ((i = 0; i < ${#args[@]}; i++)); do
        arg=${args[$i]}
        case $arg in
        -h | -help)
            vitis_help
            return 0
            ;;
        *)
            err_msg "Invalid option: $arg\n"
            usage
            return 1
            ;;
        esac
    done

    export NEEDRESTART_MODE=a
    export DEBIAN_FRONTEND="noninteractive"

    if ! source $script_dir/shared/bin/set_common_functions.sh; then
        err_msg "Setup of common functions FAILED"
        return 1
    fi

    if ! source $script_dir/shared/bin/set_common_env_vars.sh; then # Sets VITIS_DIR for the line below
        err_msg "Setup of common environment variables FAILED"
        return 1
    fi

    if ! check_xilinx_vitis; then
        return 1
    fi

    if ! check_os_and_tool_ver; then
        return 1
    fi

    if ! check_internet; then
        return 1
    fi

    if ! check_icd; then
        return 1
    fi

    if ! source $XILINX_VITIS/settings64.sh; then
        err_msg "Setup of Xilinx 64-bit settings FAILED"
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

    return 0
}


function main {

    if ! pre_flight_checks; then
        return 1
    fi

    if ! set_up_vitis_examples; then
        return 1
    fi

    #------------------- Vitis Platform ----------------------
    if ! setup_xsa; then
        err_msg "!!! Vitis Setup FAILED !!!"
        cd $AWS_FPGA_REPO_DIR
        return 1
    fi
    #------------------- Vitis Platform ----------------------

    xrt_install_check
    cd $AWS_FPGA_REPO_DIR

    export AWS_PLATFORM="AWS_PLATFORM_${xsa_for_tool_ver}"
    info_msg "The default AWS Platform has been set to: \"AWS_PLATFORM=${AWS_PLATFORM}\" "

    echo ""
    info_msg "#-------------------------------------------------------------------------------#"
    info_msg "How to run Hardware Emulation on an example"
    info_msg "cd vitis/examples/vitis_examples/hello_world"
    info_msg "hw_file_check"
    info_msg "#----------------------------- Emulation: Build --------------------------------#"
    info_msg "make build TARGET=hw_emu PLATFORM=\$SHELL_EMU_VERSION"
    info_msg "#--------------------------- Emulation: Simulation -----------------------------#"
    info_msg "make run TARGET=hw_emu PLATFORM=\$SHELL_EMU_VERSION"
    info_msg "#-------------------------------------------------------------------------------#"

    info_msg "Vitis Setup PASSED"
}

main
