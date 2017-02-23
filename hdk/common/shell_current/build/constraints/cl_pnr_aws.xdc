#######################################################################
# Copyright 2016 Amazon.com, Inc. or its affiliates.
# All Rights Reserved Worldwide.
# Amazon Confidential information
# Restricted NDA Material
#######################################################################

#######################################################################
# Clocks - These are Top level Constraints (Will generate warnings at CL synthesis)
#######################################################################
create_clock -period 3.334 -name CLK_300M_DIMM0_DP [get_ports CLK_300M_DIMM0_DP]
create_clock -period 3.334 -name CLK_300M_DIMM1_DP [get_ports CLK_300M_DIMM1_DP]
create_clock -period 3.334 -name CLK_300M_DIMM2_DP [get_ports CLK_300M_DIMM2_DP]
create_clock -period 3.334 -name CLK_300M_DIMM3_DP [get_ports CLK_300M_DIMM3_DP]

set_clock_groups -asynchronous -group [get_clocks clk_core] -group [get_clocks CLK_300M_DIMM0_DP]
set_clock_groups -asynchronous -group [get_clocks clk_core] -group [get_clocks CLK_300M_DIMM1_DP]
set_clock_groups -asynchronous -group [get_clocks clk_core] -group [get_clocks CLK_300M_DIMM2_DP]
set_clock_groups -asynchronous -group [get_clocks clk_core] -group [get_clocks CLK_300M_DIMM3_DP]

set_clock_groups -asynchronous -group [get_clocks clk_core] -group [get_clocks mmcm_clkout0*]

