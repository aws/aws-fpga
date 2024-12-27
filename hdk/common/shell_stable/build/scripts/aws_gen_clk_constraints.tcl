# =============================================================================
# Amazon FPGA Hardware Development Kit
#
# Copyright 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
# =============================================================================


# Clock Group A
switch $clock_recipe_a {
    "A0" {
        #NOT SUPPORTED# set clk_main_a0_period        8
        #NOT SUPPORTED# set clk_main_a0_half_period   4
        set clk_main_a0_period        4
        set clk_main_a0_half_period   2
        set clk_extra_a1_period      16
        set clk_extra_a1_half_period  8
        set clk_extra_a2_period       5.333
        set clk_extra_a2_half_period  2.667
        set clk_extra_a3_period       4
        set clk_extra_a3_half_period  2
    }
    "A1" {
        set clk_main_a0_period        4
        set clk_main_a0_half_period   2
        set clk_extra_a1_period       8
        set clk_extra_a1_half_period  4
        set clk_extra_a2_period       2.667
        set clk_extra_a2_half_period  1.333
        set clk_extra_a3_period       2
        set clk_extra_a3_half_period  1
    }
    "A2" {
        #NOT SUPPORTED# set clk_main_a0_period        64
        #NOT SUPPORTED# set clk_main_a0_half_period   32
        set clk_main_a0_period         4
        set clk_main_a0_half_period    2
        set clk_extra_a1_period      128
        set clk_extra_a1_half_period  64
        set clk_extra_a2_period        8
        set clk_extra_a2_half_period   4
        set clk_extra_a3_period       16
        set clk_extra_a3_half_period   8
    }
    default {
        puts "$clock_recipe_a is NOT a valid clock_recipe_a."
    }
}

# Clock Group B
switch $clock_recipe_b {
    "B0" {
        set clk_extra_b0_period       4
        set clk_extra_b0_half_period  2
        set clk_extra_b1_period       8
        set clk_extra_b1_half_period  4
    }
    "B1" {
        set clk_extra_b0_period       8
        set clk_extra_b0_half_period  4
        set clk_extra_b1_period      16
        set clk_extra_b1_half_period  8
    }
    "B2" {
        set clk_extra_b0_period       2.222
        set clk_extra_b0_half_period  1.111
        set clk_extra_b1_period       4.444
        set clk_extra_b1_half_period  2.222
    }
    "B3" {
        set clk_extra_b0_period       4
        set clk_extra_b0_half_period  2
        set clk_extra_b1_period      16
        set clk_extra_b1_half_period  8
    }
    "B4" {
        set clk_extra_b0_period       3.333
        set clk_extra_b0_half_period  1.667
        set clk_extra_b1_period      13.333
        set clk_extra_b1_half_period  6.667
    }
    "B5" {
        set clk_extra_b0_period       2.5
        set clk_extra_b0_half_period  1.25
        set clk_extra_b1_period      10
        set clk_extra_b1_half_period  5
    }
    default {
        puts "$clock_recipe_b is NOT a valid clock_recipe_b."
    }
}

# Clock Group C
switch $clock_recipe_c {
    "C0" {
        set clk_extra_c0_period       3.333
        set clk_extra_c0_half_period  1.667
        set clk_extra_c1_period       2.5
        set clk_extra_c1_half_period  1.25
    }
    "C1" {
        set clk_extra_c0_period       6.667
        set clk_extra_c0_half_period  3.333
        set clk_extra_c1_period       5
        set clk_extra_c1_half_period  2.5
    }
    "C2" {
        set clk_extra_c0_period      13.333
        set clk_extra_c0_half_period  6.667
        set clk_extra_c1_period      10
        set clk_extra_c1_half_period  5
    }
    "C3" {
        set clk_extra_c0_period       5
        set clk_extra_c0_half_period  2.5
        set clk_extra_c1_period       3.75
        set clk_extra_c1_half_period  1.875
    }
    default {
        puts "$clock_recipe_c is NOT a valid clock_recipe_c."
    }
}

# Clock Group HBM
switch $clock_recipe_hbm {
    "H0" {
        set clk_hbm_axi_period       4
        set clk_hbm_axi_half_period  2
    }
    "H1" {
        set clk_hbm_axi_period       8
        set clk_hbm_axi_half_period  4
    }
    "H2" {
        set clk_hbm_axi_period       2.222
        set clk_hbm_axi_half_period  1.111
    }
    "H3" {
        set clk_hbm_axi_period       3.333
        set clk_hbm_axi_half_period  1.667
    }
    "H4" {
        set clk_hbm_axi_period       2.5
        set clk_hbm_axi_half_period  1.25
    }
    default {
        puts "$clock_recipe_hbm is NOT a valid clock_recipe_hbm."
    }
}

#
# Get Clock Ports from AWS_CLK_GEN module
#
set pin_clk_extra_a1 "\[get_pins -of_objects \[get_cells -hierarchical -regexp .*AWS_CLK_GEN/CLK_GRP_A_EN_I.CLK_MMCM_A_I/inst/CLK_CORE_DRP_I/clk_inst/mmcme4_adv_inst\] -filter {NAME=~*CLKOUT0}\]"
set pin_clk_extra_a2 "\[get_pins -of_objects \[get_cells -hierarchical -regexp .*AWS_CLK_GEN/CLK_GRP_A_EN_I.CLK_MMCM_A_I/inst/CLK_CORE_DRP_I/clk_inst/mmcme4_adv_inst\] -filter {NAME=~*CLKOUT1}\]"
set pin_clk_extra_a3 "\[get_pins -of_objects \[get_cells -hierarchical -regexp .*AWS_CLK_GEN/CLK_GRP_A_EN_I.CLK_MMCM_A_I/inst/CLK_CORE_DRP_I/clk_inst/mmcme4_adv_inst\] -filter {NAME=~*CLKOUT2}\]"
set pin_clk_extra_b0 "\[get_pins -of_objects \[get_cells -hierarchical -regexp .*AWS_CLK_GEN/CLK_GRP_B_EN_I.CLK_MMCM_B_I/inst/CLK_CORE_DRP_I/clk_inst/mmcme4_adv_inst\] -filter {NAME=~*CLKOUT0}\]"
set pin_clk_extra_b1 "\[get_pins -of_objects \[get_cells -hierarchical -regexp .*AWS_CLK_GEN/CLK_GRP_B_EN_I.CLK_MMCM_B_I/inst/CLK_CORE_DRP_I/clk_inst/mmcme4_adv_inst\] -filter {NAME=~*CLKOUT1}\]"
set pin_clk_extra_c0 "\[get_pins -of_objects \[get_cells -hierarchical -regexp .*AWS_CLK_GEN/CLK_GRP_C_EN_I.CLK_MMCM_C_I/inst/CLK_CORE_DRP_I/clk_inst/mmcme4_adv_inst\] -filter {NAME=~*CLKOUT0}\]"
set pin_clk_extra_c1 "\[get_pins -of_objects \[get_cells -hierarchical -regexp .*AWS_CLK_GEN/CLK_GRP_C_EN_I.CLK_MMCM_C_I/inst/CLK_CORE_DRP_I/clk_inst/mmcme4_adv_inst\] -filter {NAME=~*CLKOUT1}\]"
set pin_clk_hbm_axi  "\[get_pins -of_objects \[get_cells -hierarchical -regexp .*AWS_CLK_GEN/CLK_HBM_EN_I.CLK_MMCM_HBM_I/inst/CLK_CORE_DRP_I/clk_inst/mmcme4_adv_inst\] -filter {NAME=~*CLKOUT0}\]"


#
# Write out CL clocks constraints
#
if { [file exists $CL_DIR/build/constraints/generated_cl_clocks_aws.xdc] } {
    puts "Deleting old CL clocks constraints file since it will be replaced.";
    file delete -force $CL_DIR/build/constraints/generated_cl_clocks_aws.xdc
}
set clocks_file [open "$CL_DIR/build/constraints/generated_cl_clocks_aws.xdc" w]

puts $clocks_file "#-------------------------------------------------------------------------"
puts $clocks_file "# Do not edit this file! It is auto-generated from $argv0."
puts $clocks_file "#-------------------------------------------------------------------------"

puts $clocks_file "###############################################################################                          "
puts $clocks_file "# OOC Source Clocks                                                                                      "
puts $clocks_file "###############################################################################                          "
puts $clocks_file "#CL HBM reference clock @100MHz                                                                          "
puts $clocks_file "create_clock -period 10.000 -name clk_hbm_ref  -waveform {0.000 5.000} \[get_ports clk_hbm_ref\]       \n"

puts $clocks_file "# Group A Clocks"
puts $clocks_file "create_clock -period $clk_main_a0_period  -name clk_main_a0 -waveform {0.000 $clk_main_a0_half_period}  \[get_ports clk_main_a0\]"

close $clocks_file
