#!/bin/bash

#
# Copyright 2015-2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License"). You may
# not use this file except in compliance with the License. A copy of the
# License is located at
#
#     http://aws.amazon.com/apache2.0/
#
# or in the "license" file accompanying this file. This file is distributed
# on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
# express or implied. See the License for the specific language governing
# permissions and limitations under the License.
#


if [ -z "$SDK_DIR" ]; then
	echo "Error: SDK_DIR environment variable is not set.  Please 'source sdk_setup.sh' from the aws-fpga directory first."
	exit 1
fi

if [ $EUID != 0 ]; then
	echo ""
	echo "Root privileges are required to install. You may be asked for your password..."
	sudo -E "$0" "$@"
	exit $?
else
	echo "Executing as root..."
	echo ""
fi

BASE_PATH=/usr/local

# check to see if the /usr/local/bin is on the sudo PATH (is secure_path enabled?)
echo $PATH | grep "$BASE_PATH"
ret=$?
if [ $ret -ne "0" ]; then
	BASE_PATH=/usr
fi

SDK_MGMT_DIR=$SDK_DIR/userspace
AFI_MGMT_TOOLS_SRC_DIR=$SDK_MGMT_DIR/fpga_mgmt_tools/src
AFI_MGMT_TOOLS_DST_DIR=$BASE_PATH/bin
AFI_MGMT_TOOLS_LIB_DIR=$SDK_MGMT_DIR/lib/so

# in order to accommodate different distributions, check several options for the user-libraries directory
if [ -d "/usr/local/lib64" ]; then
	AFI_MGMT_LIBS_DST_DIR=/usr/local/lib64
elif [ -d "/usr/local/lib" ]; then
	AFI_MGMT_LIBS_DST_DIR=/usr/local/lib
elif [ -d "/usr/lib64" ]; then
	AFI_MGMT_LIBS_DST_DIR=/usr/lib64
elif [ -d "/usr/lib" ]; then
	AFI_MGMT_LIBS_DST_DIR=/usr/lib
else
	echo "Error: No directory for installing libraries."
	exit 1
fi

if [ ! -d "$AFI_MGMT_TOOLS_DST_DIR" ]; then
	mkdir -p $AFI_MGMT_TOOLS_DST_DIR
fi

# /usr/bin requires sudo permissions 
echo "AWS FPGA: Copying Amazon FPGA Image (AFI) Management Tools to $AFI_MGMT_TOOLS_DST_DIR"
cp -f $AFI_MGMT_TOOLS_SRC_DIR/fpga-* $AFI_MGMT_TOOLS_DST_DIR
cp -f $AFI_MGMT_TOOLS_LIB_DIR/libfpga_mgmt.so.1.0.0 $AFI_MGMT_LIBS_DST_DIR
ln -sf libfpga_mgmt.so.1 $AFI_MGMT_LIBS_DST_DIR/libfpga_mgmt.so

echo "AWS FPGA: Installing shared library to $AFI_MGMT_LIBS_DST_DIR"
ld_conf_change="0"
while true; do
	# update the dynamic linker cache
	ldconfig

	# confirm that the linker cache stored the library we want
	ldconfig -p | grep "libfpga_mgmt\.so\.1"
	ret=$?
	if [ $ret -ne "0" ]; then
		if [ "$ld_conf_change" -eq "1" ]; then
			echo "Error: Unable to automatically install the fpga_mgmt library."
			exit 1
		fi
		ld_conf_change="1"
		echo "$AFI_MGMT_LIBS_DST_DIR" > /etc/ld.so.conf.d/fpga_mgmt-x86_64.conf
	else
		break
	fi
done

echo "AWS FPGA: Done with Amazon FPGA Image (AFI) Management Tools install."
