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

if ! [[ $CL_DIR ]]
then
	echo "ERROR: Environment variable CL_DIR is not defined"
	exit 1
fi

if ! [[ $HDK_SHELL_DIR ]]
then
	echo "ERROR: Environment variable HDK_SHELL_DIR is not defined"
	exit 1
fi

if ! [ -d $CL_DIR/build/constraints ]
then
	echo "ERROR: Constraints directory is not found in $CL_DIR/build/ directory"
	exit 1
fi

if ! [ -d $CL_DIR/build/reports ]
then
	echo "Creating the reports directory"
	mkdir $CL_DIR/build/reports
	if ! [ -d $CL_DIR/build/reports ]
	then	
		echo "ERROR: Failed to create reports directory, please check directory permissions"
		exit 1	
	fi
fi


if ! [ -d $CL_DIR/build/checkpoints ] 
then
        echo "Creating the checkpointss directory"
        mkdir $CL_DIR/build/checkpoints
        if ! [ -d $CL_DIR/build/checkpoints ]
        then
                echo "ERROR: Failed to create checkpoints directory, please check directory permissions"
                exit 1
        fi
fi


if ! [ -d $CL_DIR/build/checkpoints/to_aws ]
then
        echo "Creating the checkpoints /to_aws directory"
        mkdir $CL_DIR/build/checkpoints/to_aws
        if ! [ -d $CL_DIR/build/checkpoints/to_aws ]
        then
                echo "ERROR: Failed to create directory, please check directory permissions"
                exit 1
        fi
fi


if ! [ -d $CL_DIR/build/src_post_encryption ]
then
        echo "Creating the src_port_encryption directory"
        mkdir $CL_DIR/build/src_post_encryption
        if ! [ -d $CL_DIR/build/src_post_encryption ]
        then
                echo "ERROR: Failed to create directory, please check directory permissions"
                exit 1
        fi
fi
