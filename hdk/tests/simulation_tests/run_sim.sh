#!/usr/bin/env bash

# Exit on any error
set -e

# Process command line args
while [[ $# -gt 1 ]]
do
key="$1"

case $key in
    --test-name)
        test_name="$2"
        shift
        shift
        ;;
    --test-dir)
        test_dir="$2"
        shift
        shift
        ;;
    --test-type)
        test_type="$2"
        shift
        shift
        ;;
    *)
        echo -e >&2 "ERROR: Invalid option: $1\n"
        exit 1
        ;;
esac
done

pushd $WORKSPACE

source $WORKSPACE/hdk_setup.sh;

popd

# Run the test
pushd $test_dir

case "$test_type" in
    sv)
        make TEST="$test_name"
        ;;
    vhdl)
        make TEST="$test_name"
        ;;
    c)
        make C_TEST="$test_name"
        ;;
    *)
        echo -e >&2 "ERROR: Invalid option: $1\n"
        exit 1
        ;;
esac

# Exit out of the test dir
popd
