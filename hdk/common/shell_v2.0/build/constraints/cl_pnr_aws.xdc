#######################################################################
# Copyright 2016 Amazon.com, Inc. or its affiliates.
# All Rights Reserved Worldwide.
# Amazon Confidential information
# Restricted NDA Material
#######################################################################

#######################################################################
# Clocks - These are Top level Constraints (Will generate warnings at CL synthesis)
#######################################################################
set_clock_groups -asynchronous -group [get_clocks clk_core] -group [get_clocks mmcm_clkout0*]

set_clock_groups -asynchronous -group [get_clocks -of_objects [get_nets SH/clk_main*]] -group [get_clocks mmcm_clkout0*]
set_clock_groups -asynchronous -group [get_clocks -of_objects [get_nets SH/clk_extra*]] -group [get_clocks mmcm_clkout0*] 
