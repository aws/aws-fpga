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

vle_install_help() {
cat << 'EOF'
SYNOPSIS
    install_vivado_lab_edition.sh -v VERSION [-h]

DESCRIPTION
    Installs the specified version of Xilinx Vivado Lab Edition.
    Requires root/sudo privileges for installation.

OPTIONS
    -v VERSION
        Version of Vivado Lab Edition to install (optional)
        Supported version(s):
          - 2025.1
          - 2025.2
        Default value:
            2025.2

EXAMPLES
    Install Vivado Lab Edition 2025.2:
        $ ./install_vivado_lab_edition.sh (defaults to version 2025.2)
        $ ./install_vivado_lab_edition.sh -v 2025.1
EOF
    exit 1
}

. $(git rev-parse --show-toplevel)/shared/bin/set_common_functions.sh
. $(git rev-parse --show-toplevel)/shared/bin/set_common_env_vars.sh
export RAB_DIR="${AWS_FPGA_REPO_DIR}/developer_resources/runtime_ami_builder"

vivado_lab_tool_version="2025.2"
while getopts ":hv:" opt; do
  case $opt in
    h) vle_install_help;;
    v) vivado_lab_tool_version="$OPTARG";;
    :) err_msg "Option -$OPTARG requires a value!" >&2; vle_install_help;;
    \?) err_msg "Invalid option -$OPTARG" >&2; vle_install_help;;
  esac
done

vivado_lab_installer_tarball="Vivado_Lab_Lin_${vivado_lab_tool_version}.tar"
install_path=$(sed -n 's/^Destination=//p' "${RAB_DIR}/install_config.txt")
if ! check_for_empty_var "install_path" \
                         "$install_path" \
                         "Invalid Vivado Lab Edition install path: ${install_path}!"; then
    exit 1
fi

info_msg "Tool Version: ${vivado_lab_tool_version}"
info_msg "Install Location: ${install_path}"
info_msg "Installer Tarball: ${vivado_lab_installer_tarball}"
materials_loc="https://aws-fpga-hdk-resources.s3.amazonaws.com/vivado_lab_installers"

info_msg "Creating install location dir!"
sudo mkdir -p "${install_path}"

lsblk
df -h

info_msg "Fetching Vivado Lab Edition v${vivado_lab_tool_version}!"
if ! wget "${materials_loc}/${vivado_lab_installer_tarball}" -O "/dev/shm/${vivado_lab_installer_tarball}" -q; then
    err_msg "Couldn't download the installer tarball!"
    err_msg "Exiting!"
    exit 1
fi

cd /dev/shm/
set +o pipefail
tarball_dir=$(tar -tf "${vivado_lab_installer_tarball}" | head -1)
tar -tvf "${vivado_lab_installer_tarball}" | awk '{total += $3} END {print total}'
set -o pipefail
if ! tar -xf "${vivado_lab_installer_tarball}"; then
    err_msg "Couldn't untar the Vivado Lab Edition installer archive!"
    exit 1
fi

info_msg "Extracted tarball dir is ${tarball_dir}"
rm "${vivado_lab_installer_tarball}"

cd "${tarball_dir}"
ls -l

echo ""
df -h "${install_path}"
echo ""

install_cfg_path="${RAB_DIR}/install_config.txt"
if ! sudo ./xsetup --batch Install --config $install_cfg_path --agree XilinxEULA,3rdPartyEULA; then
    err_msg "Vivado Lab Edition v${vivado_lab_tool_version} failed to install!"
    err_msg "Exiting!"
    exit 1
fi

# Make vivado_lab callable from anywhere and available at session start
vivado_lab_exec_loc=$(find $install_path -wholename "*/bin/vivado_lab")
vivado_lab_bin_dir=$(dirname "$vivado_lab_exec_loc")
sudo tee /etc/profile.d/vivado.sh << EOF
export PATH="${vivado_lab_bin_dir}:\$PATH"
EOF

sudo chmod +x /etc/profile.d/vivado.sh
cat /etc/profile.d/vivado.sh
. /etc/profile.d/vivado.sh

if [[ -z $(vivado_lab -version) ]]; then
    err_msg "Couldn't check Vivado Lab Edition version after installing!"
    exit 1
fi

rm -rf "${tarball_dir}"
info_msg "Vivado Lab Edition v${vivado_lab_tool_version} install complete!"

exit 0
