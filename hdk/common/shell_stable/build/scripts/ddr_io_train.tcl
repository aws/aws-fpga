# =============================================================================
# Copyright 2021 Amazon.com, Inc. or its affiliates.
# All Rights Reserved Worldwide.
# Amazon Confidential information
# Restricted NDA Material
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
