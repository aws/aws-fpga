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

#####################################################################
#
# Procedure to configure MMCM Cell
#
#####################################################################
proc proc_set_mmcm {mmcm_cell clkfbout_mult_f divclk_divide clkout0_divide_f {clkout1_divide 1} {clkout2_divide 1}} {
    set cell_name [get_cells -quiet $mmcm_cell]
    if {$cell_name != ""} {
        set_property CLKFBOUT_MULT_F  $clkfbout_mult_f  $cell_name
        set_property DIVCLK_DIVIDE    $divclk_divide    $cell_name
        set_property CLKOUT0_DIVIDE_F $clkout0_divide_f $cell_name
        set_property CLKOUT1_DIVIDE   $clkout1_divide   $cell_name
        set_property CLKOUT2_DIVIDE   $clkout2_divide   $cell_name
    } else {
        puts "\nCRITICAL WARNING: $mmcm_cell cell not found. Clock recipe for this MMCM not applied.\n"
    }
}

#
# Set MMCM cell names
#
set RL_A0_MMCM "WRAPPER/IO_SHIM/RL_CLKS/MMCM_CLK_MAIN_A/inst/CLK_CORE_DRP_I/clk_inst/mmcme4_adv_inst"
set GRP_A_MMCM "WRAPPER/CL/AWS_CLK_GEN/CLK_GRP_A_EN_I.CLK_MMCM_A_I/inst/CLK_CORE_DRP_I/clk_inst/mmcme4_adv_inst"
set GRP_B_MMCM "WRAPPER/CL/AWS_CLK_GEN/CLK_GRP_B_EN_I.CLK_MMCM_B_I/inst/CLK_CORE_DRP_I/clk_inst/mmcme4_adv_inst"
set GRP_C_MMCM "WRAPPER/CL/AWS_CLK_GEN/CLK_GRP_C_EN_I.CLK_MMCM_C_I/inst/CLK_CORE_DRP_I/clk_inst/mmcme4_adv_inst"
set GRP_H_MMCM "WRAPPER/CL/AWS_CLK_GEN/CLK_HBM_EN_I.CLK_MMCM_HBM_I/inst/CLK_CORE_DRP_I/clk_inst/mmcme4_adv_inst"

############################
# Clock Group A
############################
if {[string compare $clock_recipe_a "A1"] == 0} {
    #
    # clk_main_a0
    #
    set CLKFBOUT_MULT_F  9.5
    set DIVCLK_DIVIDE    1
    set CLKOUT0_DIVIDE_F 4.750
    proc_set_mmcm $RL_A0_MMCM $CLKFBOUT_MULT_F $DIVCLK_DIVIDE $CLKOUT0_DIVIDE_F

    #
    # clk_extra_a1, clk_extra_a2, clk_extra_a3
    #
    set CLKFBOUT_MULT_F  15
    set DIVCLK_DIVIDE    1
    set CLKOUT0_DIVIDE_F 12
    set CLKOUT1_DIVIDE   4
    set CLKOUT2_DIVIDE   3
    proc_set_mmcm $GRP_A_MMCM $CLKFBOUT_MULT_F $DIVCLK_DIVIDE $CLKOUT0_DIVIDE_F $CLKOUT1_DIVIDE $CLKOUT2_DIVIDE

} elseif {[string compare $clock_recipe_a "A2"] == 0} {
    #
    # clk_main_a0
    #
    #NOT SUPPORTED# set CLKFBOUT_MULT_F  63.625
    #NOT SUPPORTED# set DIVCLK_DIVIDE    8
    #NOT SUPPORTED# set CLKOUT0_DIVIDE_F 63.625
    set CLKFBOUT_MULT_F  9.5
    set DIVCLK_DIVIDE    1
    set CLKOUT0_DIVIDE_F 4.750
    proc_set_mmcm $RL_A0_MMCM $CLKFBOUT_MULT_F $DIVCLK_DIVIDE $CLKOUT0_DIVIDE_F

    #
    # clk_extra_a1, clk_extra_a2, clk_extra_a3
    #
    set CLKFBOUT_MULT_F  12.500
    set DIVCLK_DIVIDE    1
    set CLKOUT0_DIVIDE_F 80
    set CLKOUT1_DIVIDE   10
    set CLKOUT2_DIVIDE   20
    proc_set_mmcm $GRP_A_MMCM $CLKFBOUT_MULT_F $DIVCLK_DIVIDE $CLKOUT0_DIVIDE_F $CLKOUT1_DIVIDE $CLKOUT2_DIVIDE

} else { #A0
    #
    # clk_main_a0
    #
    #NOT SUPPORTED# set CLKFBOUT_MULT_F  9.625
    #NOT SUPPORTED# set DIVCLK_DIVIDE    1
    #NOT SUPPORTED# set CLKOUT0_DIVIDE_F 9.625
    set CLKFBOUT_MULT_F  9.5
    set DIVCLK_DIVIDE    1
    set CLKOUT0_DIVIDE_F 4.750
    proc_set_mmcm $RL_A0_MMCM $CLKFBOUT_MULT_F $DIVCLK_DIVIDE $CLKOUT0_DIVIDE_F

    #
    # clk_extra_a1, clk_extra_a2, clk_extra_a3
    #
    set CLKFBOUT_MULT_F  15
    set DIVCLK_DIVIDE    1
    set CLKOUT0_DIVIDE_F 24
    set CLKOUT1_DIVIDE   8
    set CLKOUT2_DIVIDE   6
    proc_set_mmcm $GRP_A_MMCM $CLKFBOUT_MULT_F $DIVCLK_DIVIDE $CLKOUT0_DIVIDE_F $CLKOUT1_DIVIDE $CLKOUT2_DIVIDE
}


#############################################
# Clock Group B (clk_extra_b0, clk_extra_b1)
#############################################
if {[string compare $clock_recipe_b "B1"] == 0} {
    set CLKFBOUT_MULT_F  11.875
    set DIVCLK_DIVIDE    1
    set CLKOUT0_DIVIDE_F 9.5
    set CLKOUT1_DIVIDE   19
} elseif {[string compare $clock_recipe_b "B2"] == 0} {
    set CLKFBOUT_MULT_F  11.250
    set DIVCLK_DIVIDE    1
    set CLKOUT0_DIVIDE_F 2.5
    set CLKOUT1_DIVIDE   5
} elseif {[string compare $clock_recipe_b "B3"] == 0} {
    set CLKFBOUT_MULT_F  11.875
    set DIVCLK_DIVIDE    1
    set CLKOUT0_DIVIDE_F 4.750
    set CLKOUT1_DIVIDE   19
} elseif {[string compare $clock_recipe_b "B4"] == 0} {
    set CLKFBOUT_MULT_F  12
    set DIVCLK_DIVIDE    1
    set CLKOUT0_DIVIDE_F 4
    set CLKOUT1_DIVIDE   16
} elseif {[string compare $clock_recipe_b "B5"] == 0} {
    set CLKFBOUT_MULT_F  12
    set DIVCLK_DIVIDE    1
    set CLKOUT0_DIVIDE_F 3
    set CLKOUT1_DIVIDE   12
} else { #B0
    set CLKFBOUT_MULT_F  12.5
    set DIVCLK_DIVIDE    1
    set CLKOUT0_DIVIDE_F 5
    set CLKOUT1_DIVIDE   10
}
proc_set_mmcm $GRP_B_MMCM $CLKFBOUT_MULT_F $DIVCLK_DIVIDE $CLKOUT0_DIVIDE_F $CLKOUT1_DIVIDE


################################################
# Clock Group C ( clk_extra_c0, clk_extra_c1)
################################################
if {[string compare $clock_recipe_c "C1"] == 0} {
    set CLKFBOUT_MULT_F  12
    set DIVCLK_DIVIDE    1
    set CLKOUT0_DIVIDE_F 8
    set CLKOUT1_DIVIDE   6
} elseif {[string compare $clock_recipe_c "C2"] == 0} {
    set CLKFBOUT_MULT_F  12
    set DIVCLK_DIVIDE    1
    set CLKOUT0_DIVIDE_F 16
    set CLKOUT1_DIVIDE   12
} elseif {[string compare $clock_recipe_c "C3"] == 0} {
    set CLKFBOUT_MULT_F  8
    set DIVCLK_DIVIDE    1
    set CLKOUT0_DIVIDE_F 4
    set CLKOUT1_DIVIDE   3
} else { #C0
    set CLKFBOUT_MULT_F  12
    set DIVCLK_DIVIDE    1
    set CLKOUT0_DIVIDE_F 4
    set CLKOUT1_DIVIDE   3
}
proc_set_mmcm $GRP_C_MMCM $CLKFBOUT_MULT_F $DIVCLK_DIVIDE $CLKOUT0_DIVIDE_F $CLKOUT1_DIVIDE


####################################################
# Clock Group HBM (clk_hbm_axi)
####################################################
if {[string compare $clock_recipe_hbm "H1"] == 0} {
    set CLKFBOUT_MULT_F  11.875
    set DIVCLK_DIVIDE    1
    set CLKOUT0_DIVIDE_F 9.5
} elseif {[string compare $clock_recipe_hbm "H2"] == 0} {
    set CLKFBOUT_MULT_F  11.250
    set DIVCLK_DIVIDE    1
    set CLKOUT0_DIVIDE_F 2.5
} elseif {[string compare $clock_recipe_hbm "H3"] == 0} {
    set CLKFBOUT_MULT_F  12
    set DIVCLK_DIVIDE    1
    set CLKOUT0_DIVIDE_F 4
} elseif {[string compare $clock_recipe_hbm "H4"] == 0} {
    set CLKFBOUT_MULT_F  12
    set DIVCLK_DIVIDE    1
    set CLKOUT0_DIVIDE_F 3
} else { #H0
    set CLKFBOUT_MULT_F  12.5
    set DIVCLK_DIVIDE    1
    set CLKOUT0_DIVIDE_F 5
}
proc_set_mmcm $GRP_H_MMCM $CLKFBOUT_MULT_F $DIVCLK_DIVIDE $CLKOUT0_DIVIDE_F $CLKOUT1_DIVIDE

#
# DONE
#
puts "INFO: aws_clock_properties.tcl successfully applied clock recipes to MMCMs"
