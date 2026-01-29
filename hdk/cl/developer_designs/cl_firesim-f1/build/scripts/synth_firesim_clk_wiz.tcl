read_ip [list $CL_DIR/ip/clk_wiz_0_firesim/clk_wiz_0_firesim.xci]
upgrade_ip [get_ips clk_wiz_0_firesim]
set_property CONFIG.CLKOUT1_REQUESTED_OUT_FREQ $desired_host_frequency [get_ips clk_wiz_0_firesim]
# # Generates half the output files
generate_target {all} [get_ips clk_wiz_0_firesim]
# # Generates some missing stub files for sim and the dcp
synth_ip [get_ips clk_wiz_0_firesim]
