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


# MIG I/O training for sh_ddr (Refer to Xilinx UG912 for more details)


###############################################################################
# Place the MIG IP in a 3-CR hidden region for QoR
###############################################################################
set DDR_CELL [get_cells WRAPPER/CL/SH_DDR/genblk1.IS_DDR_PRESENT.DDR4_0]
if {$DDR_CELL != ""} {
    set_property MIG_FLOORPLAN_MODE FULL [get_cells WRAPPER/CL/SH_DDR/genblk1.IS_DDR_PRESENT.DDR4_0]
} else {
    print "Skipped ddr_io_train.tcl. No DDR Core in the design"
}
