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
    echo "usage: aws_build_dcp_from_cl.sh [ [-script <vivado_script>] [-gui] [-foreground] [-notify] [-ignore_memory_requirement] | [-h] | [-H] | [-help] ]"
    echo " "
    echo "By default the build is run in the background using nohup so that the"
    echo "process will not be terminated if the terminal window is closed."
    echo "The window can be closed if it is running on your computer and the"
    echo "network connection is lost. All build output will be redirected to a"
    echo "log file called *.nohup.out."
    echo " "
    echo "The -foreground option runs the build in the foreground."
    echo "This will open Vivado GUI, create a Block Design Hello World Example"
    echo "and run Synthesis and Implementation."
    echo "The terminal and the build may be terminated if the terminal"
    echo "is closed. This option is useful if you want to access the GUI."
    echo ""
    echo "The tar file used to generate the AFI image will be located in:"
    echo "$CL_DIR/build/scripts/example_projects/<name_of_example_design>.runs/faas_1/build/checkpoints/to_aws"
}

vivado_script="create_dcp_from_cl.tcl"
gui=0
foreground=0
notify=0
ignore_memory_requirement=0
expected_memory_usage=30000000

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
        -gui )                  gui=1
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

# Run vivado
if [[ $gui == 0 ]]
then
  cmd="vivado -mode batch -nojournal -log $logname -source $vivado_script -tclargs $timestamp $notify $gui"
else
  foreground=1
  cmd="vivado -nojournal -log $logname -source $vivado_script -tclargs $timestamp $notify $gui"
fi

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
