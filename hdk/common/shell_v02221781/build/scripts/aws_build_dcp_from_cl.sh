#!/bin/bash

## Amazon FGPA Hardware Development Kit
## 
## Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
## 
## Licensed under the Amazon Software License (the "License"). You may not use
## this file except in compliance with the License. A copy of the License is
## located at
## 
##    http://aws.amazon.com/asl/
## 
## or in the "license" file accompanying this file. This file is distributed on
## an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
## implied. See the License for the specific language governing permissions and
## limitations under the License.

# Usage help
function usage
{
    echo "usage: aws_build_dcp_from_cl.sh [ [-script <vivado_script>] | [-strategy BASIC | DEFAULT | EXPLORE | TIMING | CONGESTION] [-foreground] | [-h] | [-H] | [-help] |  ]"
    echo " "
    echo "By default the build is run in the background using nohup so that the"
    echo "process will not be terminated if the terminal window is closed."
    echo "The window can be closed if it is running on your computer and the"
    echo "network connection is lost. All build output will be redirected to a"
    echo "log file called *.nohup.out."
    echo " "
    echo "The -foreground option runs the build in the foreground. All output will"
    echo "go to the terminal and the build may be terminated if the terminal"
    echo "is closed. This option is useful if you want to wait for the build"
    echo "to complete. This option is safe if the terminal is running on the"
    echo "AWS instance, for example on a GUI desktop on the instance."
}

# Default arguments for script and strategy
strategy=DEFAULT
vivado_script="create_dcp_from_cl.tcl"
foreground=0

# Parse command-line arguments
while [ "$1" != "" ]; do
    case $1 in
        -script )               shift
                                vivado_script=$1
                                ;;
        -strategy )             shift
                                strategy=$1
                                ;;
        -foreground )           foreground=1
                                ;;
        -h | -H | -help )       usage
                                exit
                                ;;
        * )                     usage
                                exit 1
    esac
    shift
done

# Check that script exists
if ! [ -f "$vivado_script" ]; then
  echo "ERROR: $vivado_script doesn't exist." 
  exit 1
fi

# Check that strategy is valid
shopt -s extglob
if [[ $strategy != @(BASIC|DEFAULT|EXPLORE|TIMING|CONGESTION) ]]; then
  echo "ERROR: $strategy isn't a valid strategy. Valid strategies are BASIC, DEFAULT, EXPLORE, TIMING and CONGESTION." 
  exit 1
fi

echo "AWS FPGA: Starting the design checkpoint build process"
echo "AWS FPGA: Checking for proper environment variables and build directories"

if ! [ $HDK_SHELL_DIR ]
then
	echo "ERROR: HDK_SHELL_DIR environment variable is not set, try running hdk_setup.sh script from the root directory of AWS FPGA repository."
	exit 1
fi

if ! [ $HDK_DIR ]
then
	echo "ERROR: HDK_DIR environment variable is not set, try running hdk_setup.sh script from the root directory of AWS FPGA repository."
	exit 1
fi

if ! [ -x $HDK_SHELL_DIR/build/scripts/prepare_build_environment.sh ]
then
	echo "prepare_build_env.sh script is not eXecutable, trying to apply chmod +x"
	chmod +x $HDK_SHELL_DIR/build/scripts/prepare_build_environment.sh
	if ! [ -x $HDK_SHELL_DIR/build/scripts/prepare_build_environment.sh ]
	then
		echo "ERROR: Failed to change prepare_build_environment.sh to eXecutable, aborting!"
		exit 1
	fi
fi

$HDK_SHELL_DIR/build/scripts/prepare_build_environment.sh

if ! [[ $? -eq 0 ]]
then
	echo "ERROR: Missing environment variable or unable to create the needed build directories, aborting!"
	exit 1
fi

# Use timestamp for logs and output files
timestamp=$(date +"%y_%m_%d-%H%M%S")
logname=$timestamp.vivado.log

echo "AWS FPGA: Environment variables and directories are present. Checking for Vivado installation."

# Before going too far make sure Vivado is available
vivado -version >/dev/null 2>&1 || { echo >&2 "ERROR - Please install/enable Vivado." ; return 1; }

# Get the HDK Version
hdk_version=$(grep 'HDK_VERSION' $HDK_DIR/hdk_version.txt | sed 's/=/ /g' | awk '{print $2}')

# Get the Shell Version
shell_version=$(grep 'SHELL_VERSION' $HDK_SHELL_DIR/shell_version.txt | sed 's/=/ /g' | awk '{print $2}')

# Run vivado
cmd="vivado -mode batch -nojournal -log $logname -source $vivado_script -tclargs $timestamp $strategy $hdk_version $shell_version"
if [[ "$foreground" == "0" ]]; then
  nohup $cmd > $timestamp.nohup.out 2>&1 &
  
  echo "AWS FPGA: Build through Vivado is running as background process, this may take few hours."
  echo "AWS FPGA: Output is being redirected to $timestamp.nohup.out"
  echo "AWS FPGA: You can set up an email notification upon Vivado run finish by following the instructions in TBD"
else
  echo "AWS FPGA: Build through Vivado is running in the foreground, this may take a few hours."
  echo "AWS FPGA: The build may be terminated if the network connection to this terminal window is lost."
  $cmd
fi
