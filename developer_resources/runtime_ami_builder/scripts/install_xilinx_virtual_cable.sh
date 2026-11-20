#!/bin/bash

# Amazon FPGA Runtime AMI Builder
#
# Copyright 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

xvc_install_help() {
cat << 'EOF'
SYNOPSIS
    install_xilinx_virtual_cable.sh [-v VERSION | -p VIVADO_DIR] [-h]

DESCRIPTION
    Installs the Xilinx Virtual Cable driver from a Vivado or Vivado Lab Edition install.
    Requires root/sudo privileges for installation.

    The Vivado install is chosen in this order:
      1. -p VIVADO_DIR
      2. -v VERSION, using the Vivado Lab Edition install set up by the Runtime AMI Builder
      3. $XILINX_VIVADO, which is set when Vivado's environment is set up, as on the FPGA Developer AMI
    If none of these are given, the script stops without installing anything.

OPTIONS
    -v VERSION
        Version of the Vivado Lab Edition install to use
        Supported version(s):
          - 2025.1
          - 2025.2

    -p VIVADO_DIR
        Path to a Vivado or Vivado Lab Edition install
        Example:
          - /opt/Xilinx/2025.2/Vivado

EXAMPLES
    Install from the FPGA Developer AMI's Vivado:
        $ ./install_xilinx_virtual_cable.sh
    Install from Vivado Lab Edition 2025.1 installed by the Runtime AMI Builder:
        $ ./install_xilinx_virtual_cable.sh -v 2025.1
    Install from a specific Vivado install:
        $ ./install_xilinx_virtual_cable.sh -p /opt/Xilinx/Vivado/2024.2
EOF
    exit 1

}

# The script changes directory below, so remember where it was run from to resolve a relative -p path
invocation_dir="${PWD}"

# Resolve the repo from this script's location so it works from any directory, whether run or sourced.
# set_common_env_vars.sh also looks up the repo from the current directory, so run it from the repo root.
repo_root=$(cd "$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")/../../.." && pwd)
cd "${repo_root}"
. "${repo_root}/shared/bin/set_common_functions.sh"
. "${repo_root}/shared/bin/set_common_env_vars.sh"

vivado_lab_edition_version=""
vivado_version_loc=""
while getopts ":hv:p:" opt; do
  case $opt in
    h) xvc_install_help;;
    v) vivado_lab_edition_version="$OPTARG";;
    p) vivado_version_loc=$(cd "${invocation_dir}" && readlink -m -- "$OPTARG");;
    :) err_msg "Option -$OPTARG requires a value!" >&2; xvc_install_help;;
    \?) err_msg "Invalid option -$OPTARG" >&2; xvc_install_help;;
  esac
done


cd $HOME

if [[ -n "${vivado_version_loc}" && -n "${vivado_lab_edition_version}" ]]; then
    err_msg "Use either -p or -v, not both!"
    exit 1
fi

if [[ -z "${vivado_version_loc}" && -z "${vivado_lab_edition_version}" && -n "${XILINX_VIVADO:-}" ]]; then
    info_msg "Using the Vivado install from XILINX_VIVADO: ${XILINX_VIVADO}"
    vivado_version_loc="${XILINX_VIVADO}"
fi

if [[ -z "${vivado_version_loc}" && -z "${vivado_lab_edition_version}" ]]; then
    err_msg "No Vivado install given! Pass -p VIVADO_DIR or -v VERSION, or set up Vivado's environment so XILINX_VIVADO is set."
    err_msg "Run with -h for help."
    exit 1
fi

if [[ -z "${vivado_version_loc}" ]]; then
    vivado_install_path=$(sed -n 's/^Destination=//p' "${AWS_FPGA_REPO_DIR}/developer_resources/runtime_ami_builder/install_config.txt")
    if ! check_for_empty_var "vivado_install_path" \
                             "$vivado_install_path" \
                             "Invalid Vivado Lab Edition install path: ${vivado_install_path}!"; then
        exit 1
    fi
    vivado_version_loc="${vivado_install_path}/${vivado_lab_edition_version}/Vivado_Lab"
    if [[ ! -d "${vivado_version_loc}" ]]; then
        err_msg "No Vivado Lab Edition v${vivado_lab_edition_version} installation detected at ${vivado_version_loc}!"
        err_msg "Pass a Vivado install with -p, or set up Vivado's environment so XILINX_VIVADO is set."
        exit 1
    fi
fi

driver_zip_file="xvc_pcie.zip"
driver_zip_file_loc="${vivado_version_loc}/data/xicom/drivers/pcie/${driver_zip_file}"
driver_executable="xvc_pcie"
driver_executable_loc="${vivado_version_loc}/bin/${driver_executable}"

if [[ ! -f "${driver_zip_file_loc}" ]]; then
    err_msg "No XVC driver found at ${driver_zip_file_loc}! Is ${vivado_version_loc} a Vivado install?"
    exit 1
fi

info_msg "Driver zip file: ${driver_zip_file}"
info_msg "Driver zip file location: ${driver_zip_file_loc}"
info_msg "Driver executable: ${driver_executable}"
info_msg "Driver executable location: ${driver_executable_loc}"

if ! unzip -o -q "${driver_zip_file_loc}"; then
    err_msg "Couldn't unzip driver archive!"
    err_msg "Exiting!"
    exit 1
fi

cd driver_v0.4

# Sed wizardry that replaces the default PCIE_VENDOR_ID, PCIE_DEVICE_ID,
# bar_index, and bar_offset with the ones we show here:
# https://awsdocs-fpga-f2.readthedocs-hosted.com/latest/hdk/docs/Virtual-JTAG-XVC.html#install-xvc-driver-on-f2-instances
sed -i 's/\r$//' xvc_pcie_user_config.h # First, remove any existing Windows line endings
sed -i '
    s/#define PCIE_VENDOR_ID.*/#define PCIE_VENDOR_ID  0x1D0F/
    s/#define PCIE_DEVICE_ID.*/#define PCIE_DEVICE_ID  0x9248/
    /^[[:space:]]*\.bar_index[[:space:]]*=/s/= 0x[0-9A-Fa-f]*,/= 0x2,/
    /^[[:space:]]*\.bar_offset[[:space:]]*=/s/= 0x[0-9A-Fa-f]*,/= 0x0000,/
' xvc_pcie_user_config.h

install_cmd=$(get_install_command)
packages="gcc make"
if is_ubuntu; then
    sed -i '/class_create/ s/class_create(THIS_MODULE,/class_create(/' xvc_pcie_driver_base.c
    packages="${packages} linux-headers-$(uname -r) build-essential"
else
    # Only kernel-devel is needed to build the module. Installing kernel-headers would change the
    # AMI's version of it: dnf upgrades it if it's already installed.
    packages="${packages} kernel-devel-$(uname -r)"
fi
${install_cmd} ${packages}

if ! sudo make install; then
    err_msg "Couldn't build and install the XVC PCIe driver!"
    err_msg "Exiting!"
    exit 1
fi

info_msg "Built and installed XVC PCIe driver!"

if ! sudo depmod -a; then
    err_msg "Couldn't update the kernel modules!"
    err_msg "Exiting!"
    exit 1
fi

info_msg "Updated the kernel modules!"

if ! sudo modprobe xilinx_xvc_pci_driver; then
    err_msg "Couldn't load the XVC PCIe driver!"
    err_msg "Exiting!"
    exit 1
fi

info_msg "Initialized the XVC PCIe driver!"

if [[ -z $(lsmod | grep xilinx_xvc_pci_driver) ]]; then
    err_msg "Couldn't load the xvc driver!"
    err_msg "Exiting!"
    exit 1
fi

info_msg "XVC PCIe driver loaded and active!"

# Check the driver on every FPGA by running xvc_pcie, which performs a loopback test on start-up, for each
# driver character file. xvc_pcie keeps serving until it's stopped, and stopping the sudo/loader wrapper
# leaves the real binary running, so stop it by name after each check.
# XVC_DEVICE_DIR is only for tests.
xvc_device_dir="${XVC_DEVICE_DIR:-/dev/xil_xvc}"
xvc_devices=("${xvc_device_dir}"/cfg_ioc*)
if [[ ! -e "${xvc_devices[0]}" ]]; then
    # The driver only creates a character file per FPGA it finds, so there are none on instances without FPGAs,
    # such as the Runtime AMI Builder's build instance
    info_msg "No XVC driver character files in ${xvc_device_dir}, so there are no FPGAs to run the loopback test on."
    info_msg "This is expected on instances without FPGAs, such as the Runtime AMI Builder's build instance."
elif pgrep -x "${driver_executable}" > /dev/null; then
    # Stopping it after the test would end a running debug session, and its port would make the test fail
    info_msg "${driver_executable} is already running, so skipping the XVC loopback test to avoid interrupting it."
    info_msg "To run the test, stop ${driver_executable} and run this script again."
else
    set +e
    failed_devices=()
    for xvc_device in "${xvc_devices[@]}"; do
        xvc_port=$((10200 + ${xvc_device##*cfg_ioc}))
        sudo timeout 10 stdbuf -o0 -e0 "${driver_executable_loc}" -d "${xvc_device}" -s "TCP::${xvc_port}" &> output.txt
        sudo pkill -x "${driver_executable}"
        cat output.txt
        if ! grep -q "Loopback test successful" output.txt; then
            failed_devices+=("${xvc_device}")
        fi
    done
    rm -f output.txt
    set -e

    if [[ ${#failed_devices[@]} -ne 0 ]]; then
        err_msg "XVC loopback test failed for: ${failed_devices[*]}"
        err_msg "Exiting!"
        exit 1
    fi

    info_msg "XVC loopback test passed on ${#xvc_devices[@]} FPGA(s)!"
fi

info_msg "XVC PCIe driver installation complete!"

exit 0
