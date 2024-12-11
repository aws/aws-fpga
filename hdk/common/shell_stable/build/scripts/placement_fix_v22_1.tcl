# =============================================================================
# Copyright 2021 Amazon.com, Inc. or its affiliates.
# All Rights Reserved Worldwide.
# Amazon Confidential information
# Restricted NDA Material
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
