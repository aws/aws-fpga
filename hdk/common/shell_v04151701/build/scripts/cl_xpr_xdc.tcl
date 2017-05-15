if {[llength [get_nets -quiet CL/SH_DDR/ddr_cores.DDR4_0/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/div_clk]]} {
   set_property HIGH_PRIORITY true [get_nets CL/SH_DDR/ddr_cores.DDR4_0/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/div_clk]
}
if {[llength [get_nets -quiet CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/div_clk]]} {
   set_property HIGH_PRIORITY true [get_nets CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/div_clk]
}
if {[llength [get_nets -quiet CL/SH_DDR/ddr_cores.DDR4_2/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/div_clk]]} {
   set_property HIGH_PRIORITY true [get_nets CL/SH_DDR/ddr_cores.DDR4_2/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/div_clk]
}
if {[llength [get_nets -quiet SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/clk_out1]]} {
   set_property HIGH_PRIORITY true [get_nets SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/clk_out1]
}


if {[llength [get_pins -quiet {CL/SH_DDR/ddr*/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/inst/u_ddr4_phy_pll/plle_loop[*].gen_plle4.PLLE4_BASE_INST_OTHER/CLKOUTPHY}]]} {
   set __high_pri_clk [get_clocks -of [get_pins {CL/SH_DDR/ddr*/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/inst/u_ddr4_phy_pll/plle_loop[*].gen_plle4.PLLE4_BASE_INST_OTHER/CLKOUTPHY}]]
   foreach __pll_clk $__high_pri_clk {
      group_path -name $__pll_clk -weight 2
   }
}

if {[llength [get_pins -quiet {CL/SH_DDR/ddr*/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/inst/generate_block1.u_ddr_xiphy/byte_num[1].xiphy_byte_wrapper.u_xiphy_byte_wrapper/I_CONTROL[1].GEN_I_CONTROL.u_xiphy_control/xiphy_control/TX_BIT_CTRL_OUT0[26]}]]} {
   # pll_clk[0]_DIV pll_clk[0]_1_DIV pll_clk[0]_2_DIV pll_clk[0]_3_DIV clocks
   set __high_pri_clk [get_clocks -of [get_pins {CL/SH_DDR/ddr*/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/inst/generate_block1.u_ddr_xiphy/byte_num[1].xiphy_byte_wrapper.u_xiphy_byte_wrapper/I_CONTROL[1].GEN_I_CONTROL.u_xiphy_control/xiphy_control/TX_BIT_CTRL_OUT0[26]}]]
   foreach __pll_clk $__high_pri_clk {
      group_path -name $__pll_clk -weight 2
   }
}

if {[llength [get_pins -quiet {CL/SH_DDR/ddr*/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/inst/generate_block1.u_ddr_xiphy/byte_num[5].xiphy_byte_wrapper.u_xiphy_byte_wrapper/I_CONTROL[1].GEN_I_CONTROL.u_xiphy_control/xiphy_control/TX_BIT_CTRL_OUT0[26]}]]} {
   # pll_clk[1]_DIV pll_clk[1]_1_DIV pll_clk[1]_2_DIV pll_clk[1]_3_DIV clocks
   set __high_pri_clk [get_clocks -of [get_pins {CL/SH_DDR/ddr*/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/inst/generate_block1.u_ddr_xiphy/byte_num[5].xiphy_byte_wrapper.u_xiphy_byte_wrapper/I_CONTROL[1].GEN_I_CONTROL.u_xiphy_control/xiphy_control/TX_BIT_CTRL_OUT0[26]}]]
   foreach __pll_clk $__high_pri_clk {
      group_path -name $__pll_clk -weight 2
   }
}

if {[llength [get_pins -quiet {CL/SH_DDR/ddr*/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/inst/generate_block1.u_ddr_xiphy/byte_num[9].xiphy_byte_wrapper.u_xiphy_byte_wrapper/I_CONTROL[1].GEN_I_CONTROL.u_xiphy_control/xiphy_control/TX_BIT_CTRL_OUT0[26]}]]} {
   # pll_clk[2]_DIV pll_clk[2]_1_DIV pll_clk[2]_2_DIV pll_clk[2]_3_DIV clocks
   set __high_pri_clk [get_clocks -of [get_pins {CL/SH_DDR/ddr*/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/inst/generate_block1.u_ddr_xiphy/byte_num[9].xiphy_byte_wrapper.u_xiphy_byte_wrapper/I_CONTROL[1].GEN_I_CONTROL.u_xiphy_control/xiphy_control/TX_BIT_CTRL_OUT0[26]}]]
   foreach __pll_clk $__high_pri_clk {
      group_path -name $__pll_clk -weight 2
   }
}
