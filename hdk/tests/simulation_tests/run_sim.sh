#!/usr/bin/env bash

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
