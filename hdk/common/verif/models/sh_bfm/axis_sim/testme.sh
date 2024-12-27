#!/bin/bash

# =============================================================================
# Amazon FPGA Hardware Development Kit
#
# Copyright 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
# =============================================================================


./runme.sh\
   +AXIS_CHECK_DRIVE_AND_MONITOR +AXIS_RAND_READY\
   +GEN_STIM +AXIS_DUMP_PACKET +AXIS_DUMP_PACKET_WITH_IDLE\
   +ntb_random_seed=9 +PACKETS=100 +MAX_LEN=1516

cp -rf master.out master.in

./runme.sh\
   +AXIS_CHECK_DRIVE_AND_MONITOR +AXIS_RAND_READY

./clean.sh
