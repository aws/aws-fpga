#!/bin/bash

# Build script for the Amazon FPGA Image Management Tools and associated HAL/utils. 

TOP=`pwd` 

LOGLEVEL=$1
if [ -z "$LOGLEVEL" ]; then
	CONFIG_LOGLEVEL=3
else
	CONFIG_LOGLEVEL=$LOGLEVEL
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
	cd $TOP
}


BUILD_DIR="utils/libs/lcd"
build_exec

BUILD_DIR="hal/src/api/mbox/hw"
build_exec

BUILD_DIR="hal/src/api/reg"
build_exec

BUILD_DIR="hal/src/platform/hw"
build_exec

BUILD_DIR="fpga_image_tools/src"
build_exec
