# This contains the CL specific constraints for Top level PNR
#This should be in the pnr user constraints
set_false_path -from [get_pins {CL/cl_inst/axi_gpio_1/U0/gpio_core_1/Not_Dual.gpio_Data_Out_reg[*]/C}] -to [get_pins {SH/SH/MGT_TOP/int_rql_rdata_reg_reg[*]/D}]
set_false_path -from [get_pins {CL/cl_inst/axi_gpio_1/U0/gpio_core_1/Not_Dual.gpio_Data_Out_reg[*]/C}] -to [get_pins {SH/SH/MGT_TOP/SH_ILA_0/inst/PROBE_PIPE.shift_probes_reg[*][*]/D}]
      





