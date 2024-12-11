###############################################################################
# This contains the CL specific timing constraints for CL
###############################################################################

#################################################################################
### Timing Exceptions
#################################################################################
set_multicycle_path -from [get_pins -regexp -filter {NAME =~ ".*\/C"} -of_objects [get_cells -hierarchical -regexp -filter { NAME =~  ".*PIPE_AXLEN_HBM.*pipe_reg\[3\].*" }]] -setup 2
set_multicycle_path -from [get_pins -regexp -filter {NAME =~ ".*\/C"} -of_objects [get_cells -hierarchical -regexp -filter { NAME =~  ".*PIPE_AXLEN_HBM.*pipe_reg\[3\].*" }]] -hold 1
set_multicycle_path -from [get_pins -regexp -filter {NAME =~ ".*\/C"} -of_objects [get_cells -hierarchical -regexp -filter { NAME =~  ".*PIPE_WDATA_PAT_HBM.*pipe_reg\[3\].*" }]] -setup 2
set_multicycle_path -from [get_pins -regexp -filter {NAME =~ ".*\/C"} -of_objects [get_cells -hierarchical -regexp -filter { NAME =~  ".*PIPE_WDATA_PAT_HBM.*pipe_reg\[3\].*" }]] -hold 1
set_multicycle_path -from [get_pins -regexp -filter {NAME =~ ".*\/C"} -of_objects [get_cells -hierarchical -regexp -filter { NAME =~  ".*PIPE_KERN_EN_HBM.*pipe_reg\[3\].*" }]] -setup 2
set_multicycle_path -from [get_pins -regexp -filter {NAME =~ ".*\/C"} -of_objects [get_cells -hierarchical -regexp -filter { NAME =~  ".*PIPE_KERN_EN_HBM.*pipe_reg\[3\].*" }]] -hold 1

#################################################################################
### Clock Groups
#################################################################################
# false path inside sh_ddr
set_false_path -from [get_pins -of_objects \
                          [get_cells -hierarchical -filter { NAME =~ *ram_reg*}] -filter {REF_PIN_NAME == CLK}] \
               -to   [get_cells -hierarchical -filter { NAME =~ *rd_do_reg[*]}]

# XPM CDC:
set_false_path -from \
    [get_pins -of_objects \
         [get_cells -hierarchical -filter {PRIMITIVE_SUBGROUP==LUTRAM && NAME=~ *gnuram_async_fifo.xpm_fifo_base_inst*}]\
         -filter {REF_PIN_NAME == CLK}] \
    -to \
    [get_cells -hierarchical -filter {NAME =~ *doutb*reg* && PRIMITIVE_TYPE =~ REGISTER* && RTL_RAM_TYPE == "" }]
