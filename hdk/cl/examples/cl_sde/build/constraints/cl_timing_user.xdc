###############################################################################
# This contains the CL specific timing constraints for CL
###############################################################################

#################################################################################
### Generated Clocks
#################################################################################
# HBM AXI clock
create_generated_clock -name          clk_hbm_axi \
                       -master_clock  [get_clocks -of_objects [get_pins -hierarchical -regexp {.*CL/clk_hbm_ref}]] \
                       [get_pins -hierarchical -regexp {.*/HBM_MMCM_I/.*/mmcme4_adv_inst/CLKOUT0}]

#################################################################################
### Timing Exceptions
#################################################################################
# Clock enable exception
set_false_path -from [get_pins -hierarchical -regexp {.*/HBM_PRESENT_EQ_1.HBM_WRAPPER_I/HBM_MMCM_I/inst/seq_reg1_reg.*/C}] \
               -to   [get_pins -hierarchical -regexp {.*/HBM_PRESENT_EQ_1.HBM_WRAPPER_I/HBM_MMCM_I/inst/clkout1_buf/CE}]


#################################################################################
### Clock Groups
#################################################################################
# false path inside sh_ddr
set_false_path -from [get_pins -of_objects \
                          [get_cells -hierarchical -filter { NAME =~ *ram_reg*}] -filter {REF_PIN_NAME == CLK}] \
               -to   [get_cells -hierarchical -filter { NAME =~ *rd_do_reg[*]}]

# clk_main_a0 and clk_hbm_ref are asynchronous
set_clock_groups -asynchronous -group [get_clocks clk_main_a0] \
    -group [get_clocks clk_hbm_ref] \
    -group [get_clocks clk_hbm_axi]

set_clock_groups -asynchronous -group [get_clocks clk_main_a0] \
    -group [get_clocks -of_objects [get_pins -hierarchical -regexp {.*CL/clk_hbm_ref}]]
