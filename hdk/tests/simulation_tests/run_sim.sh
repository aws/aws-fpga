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

if [ ":$test" = ":" ]; then
    echo -e >&2 "ERROR: Invalid test: $test\n"
    exit 1
fi

if [ ! -d $WORKSPACE/hdk/cl/examples/$test/verif/scripts ]; then
    echo -e >&2 'ERROR: The test passed in does not exist!'
    exit 1
fi

source $WORKSPACE/hdk_setup.sh;

# Example test = cl_hello_world
# makefile makes test_hello_world, so removing cl_ from the string
test_name=${test:3}

# Run the test
cd $WORKSPACE/hdk/cl/examples/$test/verif/scripts;
make TEST=test_$test_name;
