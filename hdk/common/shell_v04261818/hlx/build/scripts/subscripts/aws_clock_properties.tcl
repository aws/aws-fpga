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

#Temp for testing should be in main script
open_bd_design [get_files -quiet cl.bd]

if {[info exist FAAS_CL_DIR] eq 0} {
	if {[info exist ::env(FAAS_CL_DIR)]} {
		set FAAS_CL_DIR $::env(FAAS_CL_DIR)
	} else {
		::tclapp::xilinx::faasutils::make_faas -force -bypass_drcs -partial
	}
}


set const_dir $FAAS_CL_DIR

#set clock_recipe_a "A0"
#set clock_recipe_b "B0"
#set clock_recipe_c "C0"

set clock_recipe_a [get_property CONFIG.CLOCK_A_RECIPE [get_bd_cells aws_0]]
set clock_recipe_b [get_property CONFIG.CLOCK_B_RECIPE [get_bd_cells aws_0]]
set clock_recipe_c [get_property CONFIG.CLOCK_C_RECIPE [get_bd_cells aws_0]]


# Write out CL clocks constraints

if { [file exists ${const_dir}/aws_gen_clk_constraints.xdc] } {
        puts "Deleting old CL clocks constraints file since it will be replaced.";
        file delete -force ${const_dir}/aws_gen_clk_constraints.xdc
}
set clocks_file [open "${const_dir}/aws_gen_clk_constraints.xdc" w]
# Set Clock Group properties based on specified recipe
# Clock Group A
puts $clocks_file "set_property CLKFBOUT_MULT_F   6 \[get_cells SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property DIVCLK_DIVIDE     1 \[get_cells SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]\n"
if {[string compare $clock_recipe_a "1"] == 0} {
puts $clocks_file "set_property CLKOUT0_DIVIDE_F   6 \[get_cells SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property CLKOUT1_DIVIDE    12 \[get_cells SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property CLKOUT2_DIVIDE     4 \[get_cells SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property CLKOUT3_DIVIDE     3 \[get_cells SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]\n"
} elseif {[string compare $clock_recipe_a "2"] == 0} {
puts $clocks_file "set_property CLKOUT0_DIVIDE_F  96 \[get_cells SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property CLKOUT1_DIVIDE    96 \[get_cells SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property CLKOUT2_DIVIDE    12 \[get_cells SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property CLKOUT3_DIVIDE    24 \[get_cells SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]\n"
} else { #A0
puts $clocks_file "set_property CLKOUT0_DIVIDE_F  12 \[get_cells SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property CLKOUT1_DIVIDE    24 \[get_cells SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property CLKOUT2_DIVIDE     8 \[get_cells SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property CLKOUT3_DIVIDE     6 \[get_cells SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]\n"
}                              

# Clock Group B
if {[string compare $clock_recipe_b "1"] == 0} {
puts $clocks_file "set_property CLKFBOUT_MULT_F   5 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property DIVCLK_DIVIDE     1 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property CLKOUT0_DIVIDE_F 10 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property CLKOUT1_DIVIDE   20 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]\n"
} elseif {[string compare $clock_recipe_b "2"] == 0} {
puts $clocks_file "set_property CLKFBOUT_MULT_F  18 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property DIVCLK_DIVIDE     5 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property CLKOUT0_DIVIDE_F  2 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property CLKOUT1_DIVIDE    4 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]\n"
} elseif {[string compare $clock_recipe_b "3"] == 0} {
puts $clocks_file "set_property CLKFBOUT_MULT_F   5 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property DIVCLK_DIVIDE     1 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property CLKOUT0_DIVIDE_F  5 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property CLKOUT1_DIVIDE   20 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]\n"
} elseif {[string compare $clock_recipe_b "4"] == 0} {
puts $clocks_file "set_property CLKFBOUT_MULT_F  24 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property DIVCLK_DIVIDE     5 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property CLKOUT0_DIVIDE_F  4 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property CLKOUT1_DIVIDE   16 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]\n"
} elseif {[string compare $clock_recipe_b "5"] == 0} {
puts $clocks_file "set_property CLKFBOUT_MULT_F  24 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property DIVCLK_DIVIDE     5 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property CLKOUT0_DIVIDE_F  3 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property CLKOUT1_DIVIDE   12 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]\n"
} else { #B0
puts $clocks_file "set_property CLKFBOUT_MULT_F   5 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property DIVCLK_DIVIDE     1 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property CLKOUT0_DIVIDE_F  5 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property CLKOUT1_DIVIDE   10 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk0/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]\n"
}

# Clock Group C
if {[string compare $clock_recipe_c "1"] == 0} {
puts $clocks_file "set_property CLKFBOUT_MULT_F  24 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property DIVCLK_DIVIDE     5 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property CLKOUT0_DIVIDE_F  8 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property CLKOUT1_DIVIDE    6 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]\n"
} elseif {[string compare $clock_recipe_c "2"] == 0} {
puts $clocks_file "set_property CLKFBOUT_MULT_F  24 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property DIVCLK_DIVIDE     5 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property CLKOUT0_DIVIDE_F 16 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property CLKOUT1_DIVIDE   12 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]\n"
} elseif {[string compare $clock_recipe_c "3"] == 0} {
puts $clocks_file "set_property CLKFBOUT_MULT_F  16 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property DIVCLK_DIVIDE     5 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property CLKOUT0_DIVIDE_F  4 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property CLKOUT1_DIVIDE    3 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]\n"
} else { #C0
puts $clocks_file "set_property CLKFBOUT_MULT_F  24 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property DIVCLK_DIVIDE     5 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property CLKOUT0_DIVIDE_F  4 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]"
puts $clocks_file "set_property CLKOUT1_DIVIDE    3 \[get_cells SH/kernel_clks_i/clkwiz_kernel_clk1/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst\]\n"
}

close $clocks_file
