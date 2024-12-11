# =============================================================================
# Copyright 2021 Amazon.com, Inc. or its affiliates.
# All Rights Reserved Worldwide.
# Amazon Confidential information
# Restricted NDA Material
# =============================================================================

###############################################################################
# Need this as a workaround for MMCM cascading when using AWS_CLK_GEN IP
###############################################################################
set_property CLOCK_DEDICATED_ROUTE ANY_CMT_COLUMN [get_nets WRAPPER/IO_SHIM/MMCM_CLK_HBM_REF/inst/clk_out1]
