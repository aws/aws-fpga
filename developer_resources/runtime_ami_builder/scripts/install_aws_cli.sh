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

aws_cli_install_help() {
cat << 'EOF'
SYNOPSIS
    install_aws_cli.sh [-h]

DESCRIPTION
    Downloads and installs the latest version of the AWS CLI v2.
    Requires root/sudo privileges for installation.
EOF
    exit 1
}

while getopts ":h" opt; do
  case $opt in
    h) aws_cli_install_help;;
    \?) echo "ERROR: Invalid option -$OPTARG" >&2 && exit 1;;
  esac
done

curr_dir=$(pwd)
install_command=""
os_info=$(cat /etc/os-release)
if [[ "${os_info}" == *"Ubuntu"* ]]; then
    install_command="sudo apt install -y"
elif [[ "${os_info}" == *"Rocky Linux"* ]]; then
    install_command="sudo dnf install -y"
else
    echo "ERROR: Package manager detection failed!" >&2
    exit 1
fi

cd /dev/shm
curl "https://awscli.amazonaws.com/awscli-exe-linux-x86_64.zip" -o "awscliv2.zip"
$install_command zip
unzip -q awscliv2.zip
sudo ./aws/install
rm awscliv2.zip
rm -rf aws
cd $curr_dir

echo "AWS CLI installed successfully!"
