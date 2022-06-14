# This contains the CL specific constraints for Top level PNR

# Constrain the generated clocks in CL
create_generated_clock -name clk_div2 -source [get_pins WRAPPER_INST/CL/uram_ctrl_i/clk_div2_reg/C] -divide_by 2 [get_pins WRAPPER_INST/CL/uram_ctrl_i/clk_div2_reg/Q]
create_generated_clock -name clk_div4 -source [get_pins WRAPPER_INST/CL/uram_ctrl_i/clk_div4_reg/C] -divide_by 4 [get_pins WRAPPER_INST/CL/uram_ctrl_i/clk_div4_reg/Q]
create_generated_clock -name clk_div8 -source [get_pins WRAPPER_INST/CL/uram_ctrl_i/clk_div8_reg/C] -divide_by 8 [get_pins WRAPPER_INST/CL/uram_ctrl_i/clk_div8_reg/Q]

# False paths between main clock and tck
set_clock_groups -name TIG_SRAI_1 -asynchronous -group [get_clocks -of_objects [get_pins static_sh/SH_DEBUG_BRIDGE/inst/bsip/inst/USE_SOFTBSCAN.U_TAP_TCKBUFG/O]] -group [get_clocks -of_objects [get_pins WRAPPER_INST/SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst/CLKOUT0]]
set_clock_groups -name TIG_SRAI_2 -asynchronous -group [get_clocks -of_objects [get_pins static_sh/SH_DEBUG_BRIDGE/inst/bsip/inst/USE_SOFTBSCAN.U_TAP_TCKBUFG/O]] -group [get_clocks drck]
set_clock_groups -name TIG_SRAI_3 -asynchronous -group [get_clocks -of_objects [get_pins static_sh/SH_DEBUG_BRIDGE/inst/bsip/inst/USE_SOFTBSCAN.U_TAP_TCKBUFG/O]] -group [get_clocks -of_objects [get_pins static_sh/pcie_inst/inst/gt_top_i/diablo_gt.diablo_gt_phy_wrapper/phy_clk_i/bufg_gt_userclk/O]]
