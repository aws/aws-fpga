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


vcs -R -sverilog +vcs+lic+wait\
   -timescale=1ns/1ns\
   -debug_access+all\
   +incdir+$HDK_COMMON_DIR/verif/packages\
   $HDK_COMMON_DIR/verif/packages/anp_base_pkg.sv\
   ../axis_bfm_pkg.sv\
   ../axis_bfm.sv\
   test.sv\
   +ANP_DEBUG\
   +ANP_MSG_SHOW_FILE_INFO\
   +AXIS_DUMP_MONITORED_PACKET\
   -l sim.log\
   $*
