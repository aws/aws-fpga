# =============================================================================
# Copyright 2024 Amazon.com, Inc. or its affiliates.
# All Rights Reserved Worldwide.
# =============================================================================

###############################################################################
# Need this as a workaround for MMCM cascading when using AWS_CLK_GEN IP
###############################################################################
set_property CLOCK_DEDICATED_ROUTE ANY_CMT_COLUMN [get_nets WRAPPER/IO_SHIM/MMCM_CLK_HBM_REF/inst/clk_out1]
