# This contains the CL specific constraints for Top level PNR

# False path between vled on CL clock and Shell asynchronous clock
set_false_path -from [get_cells CL/cl_vhdl_wrapper/*/vled_reg[*]]

