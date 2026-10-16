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

# Clean script for the Amazon FPGA Image Management Tools and associated libraries.

set -euo pipefail

TOP=$(pwd)

function build_exec {
	if ! cd "$TOP/$BUILD_DIR"; then
		echo "could not cd to $TOP/$BUILD_DIR"
		exit 1
	fi
	echo "Entering $TOP/$BUILD_DIR"

	if ! make clean; then
		echo "make clean failed"
		exit 1
	fi

	cd "$TOP"
}


BUILD_DIR="utils"
build_exec

BUILD_DIR="fpga_libs/fpga_pci"
build_exec

BUILD_DIR="fpga_libs/fpga_dma"
build_exec

BUILD_DIR="fpga_libs/fpga_clkgen"
build_exec

BUILD_DIR="fpga_mgmt_tools/src"
build_exec

BUILD_DIR="fpga_mgmt_examples/src"
build_exec

# fpga_mgmt last: its clean removes the shared-library symlinks from lib/so.
BUILD_DIR="fpga_libs/fpga_mgmt"
build_exec

# The library output directory is created by the per-directory builds; remove it
# once everything else has been cleaned.
rm -rf "$TOP/lib"
