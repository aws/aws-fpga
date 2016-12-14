#!/bin/bash

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
        echo "Creating the checkpoints\/to_aws directory"
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
