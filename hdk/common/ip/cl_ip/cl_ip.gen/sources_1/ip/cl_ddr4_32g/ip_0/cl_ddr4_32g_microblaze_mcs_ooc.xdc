# file: cl_ddr4_32g_microblaze_mcs_ooc.xdc

# This constraints file contains default clock frequencies to be used during 
# out-of-context flows such as OOC Synthesis and Hierarchical Designs.
# This constraints file is not used in normal top-down synthesis (the default
# flow of Vivado).

create_clock -name Clk -period 10.000 [get_ports Clk]
# set_property HD.CLK_SRC BUFGCTRL_X0Y0 [get_ports Clk]
