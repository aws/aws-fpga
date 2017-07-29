# Amazon FPGA Hardware Development Kit
#
# Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Amazon Software License (the "License"). You may not use
# this file except in compliance with the License. A copy of the License is
# located at
#
#    http://aws.amazon.com/asl/
#
# or in the "license" file accompanying this file. This file is distributed on
# an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
# implied. See the License for the specific language governing permissions and
# limitations under the License.

# Set Clock Group properties based on specified recipe
# Clock Group A
set_property CLKFBOUT_MULT_F   6 [get_cells SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
set_property DIVCLK_DIVIDE     1 [get_cells SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
if {[string compare $clock_recipe_a "A1"] == 0} {
   set_property CLKOUT0_DIVIDE_F   6 [get_cells SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property CLKOUT1_DIVIDE    12 [get_cells SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property CLKOUT2_DIVIDE     4 [get_cells SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property CLKOUT3_DIVIDE     3 [get_cells SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
} elseif {[string compare $clock_recipe_a "A2"] == 0} {
   set_property CLKOUT0_DIVIDE_F  96 [get_cells SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property CLKOUT1_DIVIDE    96 [get_cells SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property CLKOUT2_DIVIDE    12 [get_cells SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property CLKOUT3_DIVIDE    24 [get_cells SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
} else { #A0
   set_property CLKOUT0_DIVIDE_F  12 [get_cells SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property CLKOUT1_DIVIDE    24 [get_cells SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property CLKOUT2_DIVIDE     8 [get_cells SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property CLKOUT3_DIVIDE     6 [get_cells SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
}                              

# Clock Group B
if {[string compare $clock_recipe_b "B1"] == 0} {
   set_property CLKFBOUT_MULT_F   5 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property DIVCLK_DIVIDE     1 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property CLKOUT0_DIVIDE_F 10 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property CLKOUT1_DIVIDE   20 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
} elseif {[string compare $clock_recipe_b "B2"] == 0} {
   set_property CLKFBOUT_MULT_F  18 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property DIVCLK_DIVIDE     5 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property CLKOUT0_DIVIDE_F  2 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property CLKOUT1_DIVIDE    4 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
} elseif {[string compare $clock_recipe_b "B3"] == 0} {
   set_property CLKFBOUT_MULT_F   5 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property DIVCLK_DIVIDE     1 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property CLKOUT0_DIVIDE_F  5 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property CLKOUT1_DIVIDE   20 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
} elseif {[string compare $clock_recipe_b "B4"] == 0} {
   set_property CLKFBOUT_MULT_F  24 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property DIVCLK_DIVIDE     5 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property CLKOUT0_DIVIDE_F  4 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property CLKOUT1_DIVIDE   16 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
} elseif {[string compare $clock_recipe_b "B5"] == 0} {
   set_property CLKFBOUT_MULT_F  24 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property DIVCLK_DIVIDE     5 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property CLKOUT0_DIVIDE_F  3 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property CLKOUT1_DIVIDE   12 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
} else { #B0
   set_property CLKFBOUT_MULT_F   5 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property DIVCLK_DIVIDE     1 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property CLKOUT0_DIVIDE_F  5 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property CLKOUT1_DIVIDE   10 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
}

# Clock Group C
if {[string compare $clock_recipe_c "C1"] == 0} {
   set_property CLKFBOUT_MULT_F  24 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property DIVCLK_DIVIDE     5 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property CLKOUT0_DIVIDE_F  8 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property CLKOUT1_DIVIDE    6 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
} elseif {[string compare $clock_recipe_c "C2"] == 0} {
   set_property CLKFBOUT_MULT_F  24 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property DIVCLK_DIVIDE     5 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property CLKOUT0_DIVIDE_F 16 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property CLKOUT1_DIVIDE   12 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
} elseif {[string compare $clock_recipe_c "C3"] == 0} {
   set_property CLKFBOUT_MULT_F  16 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property DIVCLK_DIVIDE     5 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property CLKOUT0_DIVIDE_F  4 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property CLKOUT1_DIVIDE    3 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
} else { #C0
   set_property CLKFBOUT_MULT_F  24 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property DIVCLK_DIVIDE     5 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property CLKOUT0_DIVIDE_F  4 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
   set_property CLKOUT1_DIVIDE    3 [get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst]
}

