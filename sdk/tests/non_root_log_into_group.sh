#!/usr/bin/bash

# Amazon FPGA Hardware Development Kit
#
# Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

set -e
SLOT=$1
fpga-describe-local-image -S $SLOT
echo "$WORKSPACE/hdk/cl/examples/cl_hello_world/software/runtime/test_hello_world --slot $SLOT" > /tmp/run_non_root_cmd_as_new_group
newgrp fpgauser << ES
chmod 755 /tmp/run_non_root_cmd_as_new_group
/tmp/run_non_root_cmd_as_new_group
ES

