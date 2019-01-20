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

s3_ami_bucket=aws-fpga-developer-ami
s3_ami_version=1.5.0
xrt_rpm_name=xrt_201802.2.1.0_7.5.1804-xrt.rpm
aws_xrt_rpm_name=xrt_201802.2.1.0_7.5.1804-aws.rpm

xrt_rpm_path=$s3_ami_bucket/$s3_ami_version/Patches/$xrt_rpm_name
aws_xrt_rpm_path=$s3_ami_bucket/$s3_ami_version/Patches/$aws_xrt_rpm_name

VIVADO_TOOL_VERSION=`vivado -version | grep Vivado | head -1 | sed 's:Vivado *::' | sed 's: .*$::' | sed 's:v::'`
export VIVADO_TOOL_VERSION=${VIVADO_TOOL_VERSION:0:6}
echo "VIVADO_TOOL_VERSION is $VIVADO_TOOL_VERSION"


if [[ "$VIVADO_TOOL_VERSION" =~ .*2018\.2.* ]]; then
    echo "Xilinx Vivado version is 2018.2"

    if [ -f "/opt/xilinx/xrt/include/version.h" ]; then
       echo "XRT installed. proceeding to check version compatibility"
       xrt_build_ver=$(grep  'xrt_build_version_hash\[\]' /opt/xilinx/xrt/include/version.h | sed 's/";//' | sed 's/^.*"//')
       echo "Installed XRT version hash : $xrt_build_ver"
       if grep -Fxq "$xrt_build_ver" $AWS_FPGA_REPO_DIR/SDAccel/sdaccel_xrt_version.txt
       then
          echo "XRT version $xrt_build_ver is up-to-date."
       else
          echo "$xrt_build_ver is stale. upgrading XRT to"
          cat $AWS_FPGA_REPO_DIR/SDAccel/sdaccel_xrt_version.txt
          curl -s https://s3.amazonaws.com/$xrt_rpm_path  -o $xrt_rpm_name || { echo " Error: Failed to download xrt rpm from  $xrt_rpm_path"; return 2; }
          curl -s https://s3.amazonaws.com/$aws_xrt_rpm_path -o $aws_xrt_rpm_name || { echo " Error: Failed to download aws xrt rpm from  $aws_xrt_rpm_path"; return 2; }
          sudo yum reinstall -y $xrt_rpm_name
          echo " XRT patch rpm installed successfully"
          sudo yum install -y $aws_xrt_rpm_name
          echo " XRT patch aws rpm installed successfully"
       fi
    else
       echo "XRT not installed. Please install XRT"
       curl -s https://s3.amazonaws.com/$xrt_rpm_path  -o $xrt_rpm_name || { echo " Error: Failed to download xrt rpm from  $xrt_rpm_path"; return 2; }
       curl -s https://s3.amazonaws.com/$aws_xrt_rpm_path -o $aws_xrt_rpm_name || { echo " Error: Failed to download aws xrt rpm from  $aws_xrt_rpm_path"; return 2; }
       sudo yum reinstall -y $xrt_rpm_name
       echo " XRT patch rpm installed successfully"
       sudo yum install -y $aws_xrt_rpm_name
       echo " XRT patch aws rpm installed successfully"
    fi
 else
   echo "Xilinx Vivado version is $VIVADO_TOOL_VERSION "
fi   
