#!/usr/bin/env bash

# Process command line args
while [[ $# -gt 1 ]]
do
key="$1"

case $key in
    -t|--test)
    test="$2"
    shift # past argument
    ;;
    *)
    echo -e >&2 "ERROR: Invalid option: $1\n"
    exit 1
    ;;
esac
shift # past argument or value
done

if [ "$test" = "" ]; then
    echo -e >&2 "ERROR: Invalid test: $test\n"
    exit 1
fi

source $WORKSPACE/hdk_setup.sh;

export CL_DIR=$HDK_DIR/cl/examples/$test

if [ ! -d $CL_DIR ]; then
    echo -e >&2 'ERROR: The test passed in does not exist!'
    exit 1
fi


cd $HDK_DIR/cl/examples/$test/build/scripts
./aws_build_dcp_from_cl.sh -foreground
