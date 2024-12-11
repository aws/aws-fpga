# aclk {FREQ_HZ 250000000 CLK_DOMAIN cl_axi_sc_1x1_aclk_250 PHASE 0.0} aclk1 {FREQ_HZ 450000000 CLK_DOMAIN cl_axi_sc_1x1_aclk_450 PHASE 0.0}
# Clock Domain: cl_axi_sc_1x1_aclk_250
create_clock -name aclk -period 4.000 [get_ports aclk]
# Clock Domain: cl_axi_sc_1x1_aclk_450
create_clock -name aclk1 -period 2.222 [get_ports aclk1]
# Generated clocks
