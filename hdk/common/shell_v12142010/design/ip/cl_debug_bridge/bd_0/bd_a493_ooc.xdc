################################################################################

# This XDC is used only for OOC mode of synthesis, implementation
# This constraints file contains default clock frequencies to be used during
# out-of-context flows such as OOC Synthesis and Hierarchical Designs.
# This constraints file is not used in normal top-down synthesis (default flow
# of Vivado)
################################################################################
create_clock -name clk -period 10 [get_ports clk]
create_clock -name S_BSCAN_drck -period 10 [get_ports S_BSCAN_drck]
create_clock -name S_BSCAN_tck -period 10 [get_ports S_BSCAN_tck]
create_clock -name S_BSCAN_update -period 10 [get_ports S_BSCAN_update]

################################################################################