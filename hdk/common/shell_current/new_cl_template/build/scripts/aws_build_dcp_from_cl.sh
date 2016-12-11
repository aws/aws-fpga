#!/bin/bash

echo "AWS FPGA: Starting the design checkpoint build process"
echo "AWS FPGA: Checking for proper environment variables and build directories"

if ! [ $HDK_SHELL_DIR ]
then
	echo "ERROR: HDK_SHELL_DIR environment variable is not set, try running hdk_setup.sh script from the root directory of AWS FPGA repository"
	exit 1
fi

if ! [ -x $HDK_SHELL_DIR/build/prepare_build_environment.sh ]
then
	echo "prepare_build_env.sh script is not eXecutable, trying to apply chmod +x"
	chmod +x $HDK_SHELL_DIR/build/prepare_build_environment.sh
	if ! [ -x $HDK_SHELL_DIR/build/prepare_build_environment.sh ]
	then
		echo "ERROR: Failed to change prepare_build_environment.sh to eXecutable, aborting!"
		exit 1
	fi
fi

$HDK_SHELL_DIR/build/prepare_build_environment.sh

if ! [[ $? -eq 0 ]]
then
	echo "ERROR: Missing environment variable or unable to create the needed build directories, aborting!"
	exit 1
fi

echo "AWS FPGA: Finishing checking environment varilables and build directories, starting Vivado"

nohup vivado -mode batch -nojournal -source create_dcp_from_cl.tcl &

echo "AWS FPGA: Build through Vivado is running as background process, this may take few hours"
echo "AWS FPGA: You can set up an email notification upon Vivado run finish by following the instructions in TBD"


