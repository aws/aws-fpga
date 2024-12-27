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


# This is a workaround for Vivado 2022.1 placement hang issue
set DDR_CELL [get_cells WRAPPER/CL/SH_DDR/genblk1.IS_DDR_PRESENT.DDR4_0]
if {$DDR_CELL != ""} {
    current_instance WRAPPER/CL/SH_DDR/genblk1.IS_DDR_PRESENT.DDR4_0
    set_property SRL_TO_REG 1 [get_cells -hierarchical "*dly*" -filter {PRIMITIVE_SUBGROUP == SRL} ]
    current_instance
} else {
    puts "__INFO__: Skipped placement_fix_v22_1.tcl since DDR core is not found in the design."
}
