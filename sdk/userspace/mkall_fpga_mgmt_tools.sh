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
#
# Usage: ./mkall_fpga_mgmt_tools.sh [loglevel] [max_bars]
#
# Environment:
#   SDK_BUILD_INCREMENTAL=1  skip the `make clean` before each build
#   SDK_BUILD_JOBS=<n>       pass -j<n> to make
#   OPT=<flags>              override the optimization level

set -euo pipefail

TOP=$(pwd)

source "${AWS_FPGA_REPO_DIR:-$TOP/../..}/shared/bin/set_common_functions.sh"

LOGLEVEL=${1:-}
if [ -z "$LOGLEVEL" ]; then
	CONFIG_LOGLEVEL=0
else
	CONFIG_LOGLEVEL=$LOGLEVEL
fi

# Preprocessor defines stay separate from OPT so callers can select an
# optimization level without dropping required SDK definitions.
EXTRA_CPPFLAGS=""

if allow_non_root ; then
	EXTRA_CPPFLAGS="$EXTRA_CPPFLAGS -DFPGA_ALLOW_NON_ROOT=1"
fi

#
# gcc optimizations. Overridable from the environment.
#
OPT=${OPT:-}

#
# The max number of FPGA BARs that may be attached,
# e.g. (FPGA_SLOT_MAX * FPGA_PF_MAX * FPGA_BAR_PER_PF_MAX) is the upper bound.
#
FPGA_PCI_BARS_DFLT=64
FPGA_PCI_BARS_MAX=${2:-}
if [ -z "$FPGA_PCI_BARS_MAX" ]; then
	FPGA_PCI_BARS_MAX=$FPGA_PCI_BARS_DFLT
fi

# get the HDK/SDK version number
source "$TOP/../../release_version.txt"

EXTRA_CPPFLAGS="$EXTRA_CPPFLAGS -DFPGA_PCI_BARS_MAX=$FPGA_PCI_BARS_MAX"
EXTRA_CPPFLAGS="$EXTRA_CPPFLAGS -DCLI_VERSION=\\\"$RELEASE_VERSION\\\""

MAKE_ARGS=()
if [ -n "${SDK_BUILD_JOBS:-}" ]; then
	MAKE_ARGS+=("-j${SDK_BUILD_JOBS}")
fi

function build_exec {
	if ! cd "$TOP/$BUILD_DIR"; then
		echo "could not cd to $TOP/$BUILD_DIR"
		exit 1
	fi
	echo "Entering $TOP/$BUILD_DIR"

	if [ -z "${SDK_BUILD_INCREMENTAL:-}" ]; then
		if ! make clean; then
			echo "make clean failed"
			exit 1
		fi
	fi

	if ! make "${MAKE_ARGS[@]}" OPT="$OPT" CONFIG_LOGLEVEL="$CONFIG_LOGLEVEL" EXTRA_CPPFLAGS="$EXTRA_CPPFLAGS"; then
		echo "make failed"
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

BUILD_DIR="fpga_libs/fpga_mgmt"
build_exec

BUILD_DIR="fpga_mgmt_tools/src"
build_exec

BUILD_DIR="fpga_mgmt_examples/src"
build_exec
