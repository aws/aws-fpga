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
    echo "usage: aws_build_dcp_from_cl.sh [ [-script <vivado_script>] | [-strategy BASIC | DEFAULT | EXPLORE | TIMING | CONGESTION] [-clock_recipe_a A0 | A1 | A2] [-clock_recipe_b B0 | B1] [-clock_recipe_c C0 | C1] [-run_aws_emulation] [-foreground] | [-h] | [-H] | [-help] |  ]"
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
clock_recipe_a=A0
clock_recipe_b=B0
clock_recipe_c=C0
vivado_script="create_dcp_from_cl.tcl"
foreground=0
run_aws_emulation=0

# Parse command-line arguments
while [ "$1" != "" ]; do
    case $1 in
        -script )               shift
                                vivado_script=$1
                                ;;
        -strategy )             shift
                                strategy=$1
                                ;;
        -clock_recipe_a )       shift
                                clock_recipe_a=$1
                                ;;
        -clock_recipe_b )       shift
                                clock_recipe_b=$1
                                ;;
        -clock_recipe_c )       shift
                                clock_recipe_c=$1
                                ;;
        -run_aws_emulation )    run_aws_emulation=1
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

# Check that clock_recipe_a is valid
shopt -s extglob
if [[ $clock_recipe_a != @(A0|A1|A2) ]]; then
  echo "ERROR: $clock_recipe_a isn't a valid Clock Group A recipe. Valid Clock Group A recipes are A0, A1, and A2." 
  exit 1
fi

# Check that clock_recipe_b is valid
shopt -s extglob
if [[ $clock_recipe_b != @(B0|B1) ]]; then
  echo "ERROR: $clock_recipe_b isn't a valid Clock Group B recipe. Valid Clock Group B recipes are B0 and B1." 
  exit 1
fi

# Check that clock_recipe_c is valid
shopt -s extglob
if [[ $clock_recipe_c != @(C0|C1) ]]; then
  echo "ERROR: $clock_recipe_c isn't a valid Clock Group C recipe. Valid Clock Group C recipes are C0 and C1." 
  exit 1
fi

echo "AWS FPGA: Starting the design checkpoint build process"
echo "AWS FPGA: Checking for proper environment variables and build directories"

if ! [ $HDK_SHELL_DIR ]
then
	echo "ERROR: HDK_SHELL_DIR environment variable is not set, try running hdk_setup.sh script from the root directory of AWS FPGA repository."
	exit 1
fi

if ! [ $CL_DIR ]
then
	echo "ERROR: CL_DIR environment variable is not set. Set CL_DIR to a valid directory."
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

# Get the PCIe Device & Vendor ID from ID0
id0_version=$(grep 'CL_SH_ID0' $CL_DIR/design/cl_id_defines.vh | grep 'define' | sed 's/_//g' | awk -F "h" '{print $2}')
device_id="0x${id0_version:0:4}";
vendor_id="0x${id0_version:4:4}";

# Get the PCIe Subsystem & Subsystem Vendor ID from ID1
id1_version=$(grep 'CL_SH_ID1' $CL_DIR/design/cl_id_defines.vh | grep 'define' | sed 's/_//g' | awk -F "h" '{print $2}')
subsystem_id="0x${id1_version:0:4}";
subsystem_vendor_id="0x${id1_version:4:4}";

# Run vivado
#cmd="vivado -mode batch -nojournal -log $logname -source $vivado_script -tclargs $timestamp $strategy $hdk_version $shell_version $device_id $vendor_id $subsystem_id $subsystem_vendor_id $clock_recipe_a $clock_recipe_b $clock_recipe_c $run_aws_emulation"
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
