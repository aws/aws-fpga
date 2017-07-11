# This contains the CL specific constraints for synthesis at the CL level
set_property MAX_FANOUT 50 [get_nets -of_objects [get_pins CL/SH_DDR/ddr_cores.DDR4_0/inst/div_clk_rst_r1_reg/Q]]
set_property MAX_FANOUT 50 [get_nets -of_objects [get_pins CL/CL_PCIM_MSTR/CL_TST_PCI/sync_rst_n_reg/Q]]


