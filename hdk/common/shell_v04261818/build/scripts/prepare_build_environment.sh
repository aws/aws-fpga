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

if ! [[ $CL_DIR ]]
then
	err_msg "Environment variable CL_DIR is not defined"
	exit 1
fi

if ! [[ $HDK_SHELL_DIR ]]
then
	err_msg "Environment variable HDK_SHELL_DIR is not defined"
	exit 1
fi

if ! [ -d $CL_DIR/build/constraints ]
then
	err_msg "Constraints directory is not found in $CL_DIR/build/ directory"
	exit 1
fi

if ! [ -d $CL_DIR/build/reports ]
then
	info_msg "Creating the reports directory"
	mkdir $CL_DIR/build/reports
	if ! [ -d $CL_DIR/build/reports ]
	then	
		err_msg "Failed to create reports directory, please check directory permissions"
		exit 1	
	fi
fi


if ! [ -d $CL_DIR/build/checkpoints ] 
then
        info_msg "Creating the checkpoints directory"
        mkdir $CL_DIR/build/checkpoints
        if ! [ -d $CL_DIR/build/checkpoints ]
        then
                err_msg "Failed to create checkpoints directory, please check directory permissions"
                exit 1
        fi
fi


if ! [ -d $CL_DIR/build/checkpoints/to_aws ]
then
        info_msg "Creating the checkpoints/to_aws directory"
        mkdir $CL_DIR/build/checkpoints/to_aws
        if ! [ -d $CL_DIR/build/checkpoints/to_aws ]
        then
                err_msg "Failed to create directory, please check directory permissions"
                exit 1
        fi
fi


if ! [ -d $CL_DIR/build/src_post_encryption ]
then
        info_msg "Creating the src_port_encryption directory"
        mkdir $CL_DIR/build/src_post_encryption
        if ! [ -d $CL_DIR/build/src_post_encryption ]
        then
                err_msg "Failed to create directory, please check directory permissions"
                exit 1
        fi
fi
