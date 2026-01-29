read_ip [list $CL_DIR/ip/clk_wiz_0_firesim/clk_wiz_0_firesim.xci]
upgrade_ip [get_ips clk_wiz_0_firesim]

# F2 shell provides clk_main_a0 at 250 MHz (vs 125 MHz on F1)
# Note: XCI should already have correct value, but override for safety
set_property CONFIG.PRIM_IN_FREQ 250.000 [get_ips clk_wiz_0_firesim]
set_property CONFIG.CLKIN1_JITTER_PS 40.0 [get_ips clk_wiz_0_firesim]

# Set the target output frequency from config_build_recipes.yaml
set_property CONFIG.CLKOUT1_REQUESTED_OUT_FREQ $desired_host_frequency [get_ips clk_wiz_0_firesim]

# Generates half the output files
generate_target {all} [get_ips clk_wiz_0_firesim]
# Generates some missing stub files for sim and the dcp
synth_ip [get_ips clk_wiz_0_firesim]
