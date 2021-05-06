#!/bin/bash

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

# Usage help
function usage
{
    echo "usage: aws_build_dcp_from_cl.sh [ [-script <vivado_script>] | [-strategy BASIC | DEFAULT | EXPLORE | TIMING | CONGESTION] [-clock_recipe_a A0 | A1 | A2] [-clock_recipe_b B0 | B1 | B2 | B3 | B4 | B5] [-clock_recipe_c C0 | C1 | C2 | C3] [-uram_option 2 | 3 | 4] [-vdefine macro1,macro2,macro3,.....,macrox] -foreground] [-notify] | [-h] | [-H] | [-help] ]"
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
notify=0
ignore_memory_requirement=0
expected_memory_usage=30000000
uram_option=2
vdefine=""

function info_msg {
  echo -e "INFO: $1"
}

function debug_msg {
  if [[ $debug == 0 ]]; then
    return
  fi
  echo -e "DEBUG: $1"
}

function warn_msg {
  echo -e "WARNING: $1"
}

function err_msg {
  echo -e >&2 "ERROR: $1"
}

function get_instance_memory {
  local mem=$(awk -F"[: ]+" '/MemTotal/ {print $2;exit}' /proc/meminfo)
  echo "$mem"
}

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
        -uram_option )          shift
                                uram_option=$1
                                ;;
        -vdefine )              shift
                                vdefine=$1
                                ;;
        -foreground )           foreground=1
                                ;;
        -notify )               notify=1
                                ;;
        -ignore_memory_requirement) ignore_memory_requirement=1
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
  err_msg "$vivado_script doesn't exist."
  exit 1
fi

# Check that strategy is valid
shopt -s extglob
if [[ $strategy != @(BASIC|DEFAULT|EXPLORE|TIMING|CONGESTION) ]]; then
  err_msg "$strategy isn't a valid strategy. Valid strategies are BASIC, DEFAULT, EXPLORE, TIMING and CONGESTION."
  exit 1
fi

# Check that clock_recipe_a is valid
shopt -s extglob
if [[ $clock_recipe_a != @(A0|A1|A2) ]]; then
  err_msg "$clock_recipe_a isn't a valid Clock Group A recipe. Valid Clock Group A recipes are A0, A1, and A2."
  exit 1
fi

# Check that clock_recipe_b is valid
shopt -s extglob
if [[ $clock_recipe_b != @(B0|B1|B2|B3|B4|B5) ]]; then
  err_msg "$clock_recipe_b isn't a valid Clock Group B recipe. Valid Clock Group B recipes are B0, B1, B2, B3, B4, and B5."
  exit 1
fi

# Check that clock_recipe_c is valid
shopt -s extglob
if [[ $clock_recipe_c != @(C0|C1|C2|C3) ]]; then
  err_msg "$clock_recipe_c isn't a valid Clock Group C recipe. Valid Clock Group C recipes are C0, C1, C2, and C3."
  exit 1
fi

# Check that uram_option is valid
shopt -s extglob
if [[ $uram_option != @(2|3|4) ]]; then
  err_msg "$uram_option isn't a valid URAM option. Valid URAM options are 2 (50%), 3 (75%), and 4 (100%)."
  exit 1
fi
# process vdefines
info_msg "VDEFINE is : $vdefine"
shopt -s extglob
IFS=',' read -r -a vdefine_array <<< "$vdefine"

opt_vdefine=""

for index in "${!vdefine_array[@]}"
do 
 echo "$index ${vdefine_array[index]}"
 opt_vdefine+=" -verilog_define "
 opt_vdefine+=${vdefine_array[index]}
done
echo "$opt_vdefine"
if [ $expected_memory_usage -gt `get_instance_memory` ]; then

    output_message="YOUR INSTANCE has less memory than is necessary for certain builds. This means that your builds will take longer than expected. \nTo change to an instance type with more memory, please check our instance resize guide: http://docs.aws.amazon.com/AWSEC2/latest/UserGuide/ec2-instance-resize.html"

  if [[ $ignore_memory_requirement == 0 ]]; then
      err_msg "$output_message"
      err_msg "To ignore this memory requirement, run this script again with -ignore_memory_requirement as an argument."
      exit 1
  else
      warn_msg "$output_message"
  fi
fi

info_msg "Starting the design checkpoint build process"
info_msg "Checking for proper environment variables and build directories"

if ! [ $HDK_SHELL_DIR ]
then
	err_msg "HDK_SHELL_DIR environment variable is not set, try running hdk_setup.sh script from the root directory of AWS FPGA repository."
	exit 1
fi

if ! [ $CL_DIR ]
then
	err_msg "CL_DIR environment variable is not set. Set CL_DIR to a valid directory."
	exit 1
fi

if ! [ $HDK_DIR ]
then
	err_msg "HDK_DIR environment variable is not set, try running hdk_setup.sh script from the root directory of AWS FPGA repository."
	exit 1
fi

if ! [ -x $HDK_SHELL_DIR/build/scripts/prepare_build_environment.sh ]
then
	info_msg "prepare_build_env.sh script is not eXecutable, trying to apply chmod +x"
	chmod +x $HDK_SHELL_DIR/build/scripts/prepare_build_environment.sh
	if ! [ -x $HDK_SHELL_DIR/build/scripts/prepare_build_environment.sh ]
	then
		err_msg "Failed to change prepare_build_environment.sh to eXecutable, aborting!"
		exit 1
	fi
fi

$HDK_SHELL_DIR/build/scripts/prepare_build_environment.sh

if ! [[ $? -eq 0 ]]
then
	err_msg "Missing environment variable or unable to create the needed build directories, aborting!"
	exit 1
fi

# Use timestamp for logs and output files
timestamp=$(date +"%y_%m_%d-%H%M%S") 
logname=$timestamp.vivado.log
ln -s -f $logname last_log

info_msg "Environment variables and directories are present. Checking for Vivado installation."

# Before going too far make sure Vivado is available
vivado -version >/dev/null 2>&1 || { err_msg "Please install/enable Vivado." ; return 1; }

# Get the HDK Version
hdk_version=$(grep 'HDK_VERSION' $HDK_DIR/hdk_version.txt | sed 's/=/ /g' | awk '{print $2}')

# Get the Shell Version
shell_version=$(grep 'SHELL_VERSION' $HDK_SHELL_DIR/shell_version.txt | sed 's/=/ /g' | awk '{print $2}')

# Get the PCIe Device & Vendor ID from ID0
id0_version=$(grep -v '^\//' $CL_DIR/design/cl_id_defines.vh | grep 'CL_SH_ID0' | grep 'define' | sed 's/_//g' | awk -F "h" '{print $2}')
device_id="0x${id0_version:0:4}";
vendor_id="0x${id0_version:4:4}";

# Get the PCIe Subsystem & Subsystem Vendor ID from ID1
id1_version=$(grep -v '^\//' $CL_DIR/design/cl_id_defines.vh | grep 'CL_SH_ID1' | grep 'define' | sed 's/_//g' | awk -F "h" '{print $2}')
subsystem_id="0x${id1_version:0:4}";
subsystem_vendor_id="0x${id1_version:4:4}";

# Run vivado
cmd="vivado -mode batch -nojournal -log $logname -source $vivado_script -tclargs $timestamp $strategy $hdk_version $shell_version $device_id $vendor_id $subsystem_id $subsystem_vendor_id $clock_recipe_a $clock_recipe_b $clock_recipe_c $uram_option $notify $opt_vdefine"
if [[ "$foreground" == "0" ]]; then
  nohup $cmd > $timestamp.nohup.out 2>&1 &
  
  info_msg "Build through Vivado is running as background process, this may take few hours."
  info_msg "Output is being redirected to $timestamp.nohup.out"
  info_msg "If you have set your EMAIL environment variable and -notify is specified, you will receive a notification when complete."
  info_msg "  (See \$HDK_DIR/cl/examples/README.md for details)"
else
  info_msg "Build through Vivado is running in the foreground, this may take a few hours."
  info_msg "The build may be terminated if the network connection to this terminal window is lost."
  $cmd
fi
