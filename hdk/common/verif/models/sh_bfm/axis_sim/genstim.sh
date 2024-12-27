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


./runme.sh +GEN_STIM +AXIS_DUMP_PACKET +AXIS_DUMP_PACKET_WITH_IDLE +ntb_random_seed=9 +PACKETS=50 +MIN_LEN=20 +MAX_LEN=1516
cp -rf master.out $CL_DIR/verif/scripts/stimulus/mac0_tx.in

./runme.sh +GEN_STIM +AXIS_DUMP_PACKET +AXIS_DUMP_PACKET_WITH_IDLE +ntb_random_seed=1 +PACKETS=50 +MIN_LEN=20 +MAX_LEN=1516
cp -rf master.out $CL_DIR/verif/scripts/stimulus/mac1_tx.in

./runme.sh +GEN_STIM +AXIS_DUMP_PACKET +AXIS_DUMP_PACKET_WITH_IDLE +ntb_random_seed=5 +PACKETS=100 +MIN_LEN=20 +MAX_LEN=1516
cp -rf master.out $CL_DIR/verif/scripts/stimulus/h2c.in

./clean.sh
