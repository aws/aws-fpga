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

set -ex

xdma_install_help() {
cat << 'EOF'
SYNOPSIS
    install_xdma_driver.sh -d DEVICE_ID [-h]

DESCRIPTION
    Installs the Xilinx DMA (XDMA) driver.
    Requires root/sudo privileges for installation.

OPTIONS

    -h HELP
        Prints this help prompt and quits.

    -d CL DEVICE NUMBER
        The device number set cl_id_defines.vh.
        Example:
          - 0xBEEF

EXAMPLES
    Install XDMA driver:
        $ ./install_xdma_driver.sh -h
        $ ./install_xdma_driver.sh -d 0xBEEF
EOF
    exit 0

}

# Resolve the repo from this script's location so it works from any directory, whether run or sourced.
# set_common_env_vars.sh also looks up the repo from the current directory, so run it from the repo root.
repo_root=$(cd "$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")/../../.." && pwd)
cd "${repo_root}"
. "${repo_root}/shared/bin/set_common_functions.sh"
. "${repo_root}/shared/bin/set_common_env_vars.sh"

xdma_driver_repo="https://github.com/Xilinx/dma_ip_drivers.git"
# Upstream commit known to build and to pass the PCI ID table check below. Tried once, only if master doesn't work.
# XDMA_DRIVER_FALLBACK_COMMIT is only for tests, and an empty value turns the fallback off.
xdma_driver_fallback_commit="${XDMA_DRIVER_FALLBACK_COMMIT-a918c5196a09f95756af244a607d543d9dce5bfb}"

while getopts ":hd:" opt; do
  case $opt in
    h) xdma_install_help;;
    d) customer_device_id="$OPTARG";;
    :) err_msg "Option -$OPTARG requires a value!"; exit 1;;
    \?) echo "Invalid option -$OPTARG" >&2; exit 1;;
  esac
done

# The ID is pasted into the driver's C source, so it must be a hex literal
if [[ ! "${customer_device_id:-}" =~ ^0x[0-9A-Fa-f]{4}$ ]]; then
    err_msg "A 4-digit hex device ID such as 0xf001 is required! Pass it with -d. Run with -h for help."
    exit 1
fi

info_msg "Checking for XOCL driver install before proceeding with XDMA driver install!"

if [[ -n $(lsmod | grep xocl) ]]; then
    err_msg "XDMA driver and XOCL driver cannot be installed on the same system!"
    exit 1
fi

info_msg "No XOCL driver install detected. Proceeding with XDMA driver build!"

kernel_version=$(uname -r)
# XDMA_KERNEL_BUILD_DIR is only for tests
kernel_build_dir="${XDMA_KERNEL_BUILD_DIR:-/lib/modules/${kernel_version}/build}"
info_msg "Checking for system header files needed to build XDMA kernel driver"

if [[ ! -d "${kernel_build_dir}" ]]; then
    info_msg "System headers build directory not found. Installing system headers..."

    if is_ubuntu; then
        info_msg "Detected Ubuntu"
        packages="linux-headers-${kernel_version}"
        install_cmd="sudo apt-get update && sudo apt-get install -y ${packages}"
    elif is_rocky_linux; then
        info_msg "Detected Rocky Linux"
        # Only kernel-devel is needed to build the module. Installing kernel-headers would change the
        # AMI's version of it.
        packages="kernel-devel-${kernel_version}"
        install_cmd="sudo yum install -y ${packages}"
    else
        err_msg "Unsupported distribution! This script supports Ubuntu and Rocky Linux only."
        exit 1
    fi

    if ! eval ${install_cmd}; then
        err_msg "Failed to install kernel headers: ${packages}"
        err_msg "Please manually install: ${packages}"
        exit 1
    fi

    if [[ ! -d "${kernel_build_dir}" ]]; then
        err_msg "Kernel build directory still not found after package installation!"
        err_msg "Expected directory: ${kernel_build_dir}"
        exit 1
    fi

    info_msg "Kernel build environment installed successfully!"
else
    info_msg "Kernel build environment already present at ${kernel_build_dir}"
fi

# A real install builds in a fresh directory that this script owns and removes, so it never resets or deletes a
# clone the user keeps in ${HOME}/dma_ip_drivers. -d 0x0000 only prepares the source for the user to finish
# building later, so that source stays in ${HOME}/dma_ip_drivers.
if [[ "${customer_device_id}" == *"0x0000"* ]]; then
    xdma_source_parent="${HOME}"
elif ! xdma_source_parent=$(mktemp -d "${TMPDIR:-/tmp}/xdma_driver_build.XXXXXX"); then
    err_msg "Couldn't create a directory to build the XDMA driver in!"
    exit 1
fi
cd "${xdma_source_parent}"

if [[ -d dma_ip_drivers ]]; then
    # Left by an earlier -d 0x0000 run, or a manual build. It is reset to the upstream source below.
    info_msg "Reusing the existing XDMA driver source at ${HOME}/dma_ip_drivers"
    if [[ ! -d dma_ip_drivers/.git ]]; then
        err_msg "${HOME}/dma_ip_drivers exists but isn't a git repo! Remove it and try again."
        exit 1
    fi
elif ! git clone "${xdma_driver_repo}"; then
    err_msg "Couldn't download the XDMA driver git repo!"
    exit 1
fi

# Gets one upstream ref, adds the device ID, and for a real install builds and installs the driver. Returns non-zero,
# after saying why, if that ref can't be used. Called from an if, so every failure has to be checked explicitly.
function try_xdma_driver_ref {
    local ref="${1}"
    info_msg "Using ${ref} of the XDMA driver source"
    cd "${xdma_source_parent}" || return 1

    # Earlier `sudo make` runs leave root-owned build output, which git can't clean up as this user
    sudo chown -R "$(id -u):$(id -g)" dma_ip_drivers || return 1
    if ! git -C dma_ip_drivers fetch --quiet "${xdma_driver_repo}" "${ref}"; then
        err_msg "Couldn't fetch ${ref} of the XDMA driver git repo!"
        return 1
    fi
    # Discards edits and build output from earlier runs and attempts, such as a previously added device ID
    git -C dma_ip_drivers reset --quiet --hard FETCH_HEAD || return 1
    git -C dma_ip_drivers clean --quiet -fdx || return 1

    cd dma_ip_drivers/XDMA/linux-kernel/xdma/ || return 1

    # Update the device ID the driver will bind to, next to the existing AWS entries
    if ! grep -q '/\* aws \*/' xdma_mod.c; then
        err_msg "Couldn't find the AWS device ID entries in xdma_mod.c!"
        return 1
    fi
    # Match only real table entries, not the 0x1042 one compiled out behind INTERNAL_TESTING
    if grep -qi "PCI_DEVICE(0x1d0f, ${customer_device_id}), }," xdma_mod.c; then
        info_msg "Device ID ${customer_device_id} is already in the driver's device table"
    else
        sed -i "/\/\* aws \*\//a\	{ PCI_DEVICE(0x1d0f, ${customer_device_id}), }," xdma_mod.c || return 1
    fi

    # xdma_mod.c comes from upstream, so confirm the ID ended up inside the pci_ids[] table rather than
    # wherever the /* aws */ comment might move to
    if ! awk -v entry="pci_device(0x1d0f, ${customer_device_id,,}), }," '
            /pci_ids\[\] = \{/ { in_table = 1 }
            in_table && index(tolower($0), entry) { found = 1 }
            in_table && /\{0,\}/ { exit }
            END { exit !found }' xdma_mod.c; then
        err_msg "Couldn't add ${customer_device_id} to the driver's PCI ID table! The upstream xdma_mod.c layout may have changed."
        return 1
    fi

    if [[ "${customer_device_id}" != *"0x0000"* ]] && ! sudo make install; then
        err_msg "Couldn't build and install the XDMA driver!"
        return 1
    fi
    return 0
}

xdma_driver_refs=(master)
if [[ -n "${xdma_driver_fallback_commit}" ]]; then
    xdma_driver_refs+=("${xdma_driver_fallback_commit}")
fi

xdma_driver_ready=0
for xdma_driver_ref in "${xdma_driver_refs[@]}"; do
    if try_xdma_driver_ref "${xdma_driver_ref}"; then
        xdma_driver_ready=1
        break
    fi
    if [[ "${xdma_driver_ref}" == "master" && -n "${xdma_driver_fallback_commit}" ]]; then
        warn_msg "The XDMA driver at master didn't work. Trying the last known good commit ${xdma_driver_fallback_commit}"
    fi
done

if [[ ${xdma_driver_ready} -ne 1 ]]; then
    err_msg "Couldn't prepare the XDMA driver from ${xdma_driver_refs[*]}!"
    # Only the last attempt's files are left, and a real install keeps them for diagnosis
    if [[ "${customer_device_id}" != *"0x0000"* ]]; then
        err_msg "The files from the last attempt are in ${xdma_source_parent}"
    fi
    exit 1
fi

if [[ "${customer_device_id}" != *"0x0000"* ]]; then
    info_msg "Built and installed the XDMA driver successfully!"

    # modprobe does nothing while an older xdma is loaded, so unload it to pick up the new device ID
    if lsmod | awk '$1 == "xdma" { found = 1 } END { exit !found }' && ! sudo modprobe -r xdma; then
        err_msg "Couldn't unload the running XDMA driver! Stop anything using /dev/xdma* and re-run."
        exit 1
    fi

    if ! sudo modprobe xdma; then
        err_msg "Couldn't start the XDMA driver!"
        exit 1
    fi

    # make install puts the module here, so this is the one that was just built
    xdma_ko="/lib/modules/${kernel_version}/xdma/xdma.ko"
    if [[ "$(modinfo -n xdma)" != "${xdma_ko}" ]] || ! lsmod | awk '$1 == "xdma" { found = 1 } END { exit !found }'; then
        err_msg "The XDMA driver at ${xdma_ko} isn't the one loaded!"
        exit 1
    fi

    info_msg "XDMA driver activated!"
else
    info_msg "XDMA driver source prepared at: ${HOME}/dma_ip_drivers/XDMA/linux-kernel/xdma/"
    info_msg "Manual installation steps required:"
    info_msg "  1. Edit xdma_mod.c and change the device ID entry:"
    info_msg "     From: { PCI_DEVICE(0x1d0f, 0x0000), },"
    info_msg "     To:   { PCI_DEVICE(0x1d0f, 0xDEVICE_ID), },"
    info_msg "  2. Run: sudo make clean"
    info_msg "  3. Run: sudo make install"
    info_msg "  4. Run: sudo modprobe xdma"
    exit 0
fi

if [[ "${customer_device_id}" != *"0x0000"* ]]; then
    cd "${HOME}"
    sudo rm -rf "${xdma_source_parent}"
fi

set +ex
