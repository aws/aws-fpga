###############################################################################
# This contains the specific constraints required by AWS
###############################################################################

#################################################################################
# false path inside sh_ddr.sv
#################################################################################
set_false_path -from [get_pins -of_objects \
                          [get_cells -hierarchical -filter { NAME =~ *ram_reg*}] -filter {REF_PIN_NAME == CLK}] \
               -to   [get_cells -hierarchical -filter { NAME =~ *rd_do_reg[*]}]

set_clock_groups -asynchronous \
    -group [get_clocks clk_main_a0] \
    -group [get_clocks -of_objects [get_pins -hierarchical -filter {NAME=~*SH_DDR/genblk1.IS_DDR_PRESENT.DDR4_0/inst/u_ddr4_infrastructure/gen_mmcme4.u_mmcme_adv_inst/CLKOUT0}]]
