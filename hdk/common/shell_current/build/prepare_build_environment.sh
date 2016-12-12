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

if ! [ -d ../constraints ]
then
	echo "ERROR: Constrains directory is not found in .. directory"
	exit 1
fi

if ! [ -d ../reports ]
then
	echo "Creating the reports directory"
	mkdir ../reports
	if ! [ -d ../reports ]
	then	
		echo "ERROR: Failed to create reports directory, please check directory permissions"
		exit 1	
	fi
fi


if ! [ -d ../checkpoints ] 
then
        echo "Creating the checkpointss directory"
        mkdir ../checkpoints
        if ! [ -d ../checkpoints ]
        then
                echo "ERROR: Failed to create checkpoints directory, please check directory permissions"
                exit 1
        fi
fi


if ! [ -d ../checkpoints/to_aws ]
then
        echo "Creating the checkpoints\/to_aws directory"
        mkdir ../checkpoints/to_aws
        if ! [ -d ../checkpoints/to_aws ]
        then
                echo "ERROR: Failed to create directory, please check directory permissions"
                exit 1
        fi
fi


if ! [ -d ../src_post_encryption ]
then
        echo "Creating the src_port_encryption directory"
        mkdir ../src_post_encryption
        if ! [ -d ../src_post_encryption ]
        then
                echo "ERROR: Failed to create directory, please check directory permissions"
                exit 1
        fi
fi
