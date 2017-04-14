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

# Build script for the Amazon FPGA Image Management Tools and libraries.

TOP=`pwd` 

LOGLEVEL=$1
if [ -z "$LOGLEVEL" ]; then
	CONFIG_LOGLEVEL=0
else
	CONFIG_LOGLEVEL=$LOGLEVEL
fi

#
# gcc optimizations
#OPT="-O3 -fno-strict-aliasing"

#
# The max number of FPGA BARs that may be attached,
# e.g. (FPGA_SLOT_MAX * FPGA_PF_MAX * FPGA_BAR_PER_PF_MAX) is the upper bound.
#
FPGA_PCI_BARS_DFLT=64
FPGA_PCI_BARS_MAX=$2
if [ -z "$FPGA_PCI_BARS_MAX" ]; then
	FPGA_PCI_BARS_MAX=$FPGA_PCI_BARS_DFLT
else
	FPGA_PCI_BARS_MAX=$FPGA_PCI_BARS_MAX
fi

function build_exec {
	cd $TOP/$BUILD_DIR 
	echo "Entering $TOP/$BUILD_DIR"
	RET=$?
	if [ $RET -ne 0 ]; then
		echo "could not cd to $TOP/$BUILD_DIR"
		exit 1
	fi
	make clean
	RET=$?
	if [ $RET -ne 0 ]; then
		echo "make clean failed"
		exit 1
	fi
	make OPT="$OPT -DCONFIG_LOGLEVEL="$CONFIG_LOGLEVEL" -DFPGA_PCI_BARS_MAX="$FPGA_PCI_BARS_MAX""
	RET=$?
	if [ $RET -ne 0 ]; then
		echo "make failed"
		exit 1
	fi
	cd $TOP
}


BUILD_DIR="utils"
build_exec

BUILD_DIR="fpga_libs/fpga_pci"
build_exec

BUILD_DIR="fpga_libs/fpga_mgmt"
build_exec

BUILD_DIR="fpga_mgmt_tools/src"
build_exec
