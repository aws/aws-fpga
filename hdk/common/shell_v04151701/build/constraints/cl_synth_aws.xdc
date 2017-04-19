#######################################################################
# Copyright 2016 Amazon.com, Inc. or its affiliates.
# All Rights Reserved Worldwide.
# Amazon Confidential information
# Restricted NDA Material
#######################################################################

#create_clock -period 3.334 -name CLK_300M_DIMM0_DP [get_ports CLK_300M_DIMM0_DP]
#create_clock -period 3.334 -name CLK_300M_DIMM1_DP [get_ports CLK_300M_DIMM1_DP]
#create_clock -period 3.334 -name CLK_300M_DIMM3_DP [get_ports CLK_300M_DIMM3_DP]

#set_false_path -from [get_clocks cl_clk0] -to [get_clocks CLK_300M_DIMM0_DP]
#set_false_path -from [get_clocks cl_clk0] -to [get_clocks CLK_300M_DIMM1_DP]
#set_false_path -from [get_clocks cl_clk0] -to [get_clocks CLK_300M_DIMM3_DP]
#set_false_path -from [get_clocks CLK_300M_DIMM0_DP] -to [get_clocks cl_clk0]
#set_false_path -from [get_clocks CLK_300M_DIMM1_DP] -to [get_clocks cl_clk0]
#set_false_path -from [get_clocks CLK_300M_DIMM3_DP] -to [get_clocks cl_clk0]

#set_clock_groups -asynchronous -group [get_clocks cl_clk0] -group [get_clocks mmcm_clkout0*]

#set_clock_groups -asynchronous -group [get_clocks cl_clk0] -group [get_clocks CLK_300M_DIMM0_DP]
#set_clock_groups -asynchronous -group [get_clocks cl_clk0] -group [get_clocks CLK_300M_DIMM1_DP]
#set_clock_groups -asynchronous -group [get_clocks cl_clk0] -group [get_clocks CLK_300M_DIMM3_DP]

set_max_delay -datapath_only \
              -from [get_clocks -of_objects [get_pins SH_DDR/ddr_cores.DDR4_0/inst/u_ddr4_infrastructure/gen_mmcme4.u_mmcme_adv_inst/CLKOUT0]] \
              -to [get_clocks -of [get_ports clk_main_a0]] \
              [get_property PERIOD [get_clocks -of_objects [get_pins SH_DDR/ddr_cores.DDR4_0/inst/u_ddr4_infrastructure/gen_mmcme4.u_mmcme_adv_inst/CLKOUT0]]]
set_max_delay -datapath_only \
              -from [get_clocks -of_objects [get_pins SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_infrastructure/gen_mmcme4.u_mmcme_adv_inst/CLKOUT0]]    \
              -to [get_clocks -of [get_ports clk_main_a0]] \
              [get_property PERIOD [get_clocks -of_objects [get_pins SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_infrastructure/gen_mmcme4.u_mmcme_adv_inst/CLKOUT0]]]
set_max_delay -datapath_only \
              -from [get_clocks -of_objects [get_pins SH_DDR/ddr_cores.DDR4_2/inst/u_ddr4_infrastructure/gen_mmcme4.u_mmcme_adv_inst/CLKOUT0]]    \
              -to [get_clocks -of [get_ports clk_main_a0]] \
              [get_property PERIOD [get_clocks -of_objects [get_pins SH_DDR/ddr_cores.DDR4_2/inst/u_ddr4_infrastructure/gen_mmcme4.u_mmcme_adv_inst/CLKOUT0]]]
set_max_delay -datapath_only \
              -from [get_clocks -of [get_ports clk_main_a0]] \
              -to [get_clocks -of_objects [get_pins SH_DDR/ddr_cores.DDR4_*/inst/u_ddr4_infrastructure/gen_mmcme4.u_mmcme_adv_inst/CLKOUT0]] \
              [get_property PERIOD [get_clocks -of_objects [get_ports clk_main_a0]]]

