# This contains the CL specific constraints for Top level PNR

# False path between vled on CL clock and Shell asynchronous clock

set_false_path -from [get_cells WRAPPER_INST/CL/vled_q_reg*]

# Constrain the generated clocks in CL
create_generated_clock -name clk_div2 -source [get_pins WRAPPER_INST/CL/uram_ctrl_i/clk_div2_reg/C] -divide_by 2 [get_pins WRAPPER_INST/CL/uram_ctrl_i/clk_div2_reg/Q]
create_generated_clock -name clk_div4 -source [get_pins WRAPPER_INST/CL/uram_ctrl_i/clk_div4_reg/C] -divide_by 4 [get_pins WRAPPER_INST/CL/uram_ctrl_i/clk_div4_reg/Q]
create_generated_clock -name clk_div8 -source [get_pins WRAPPER_INST/CL/uram_ctrl_i/clk_div8_reg/C] -divide_by 8 [get_pins WRAPPER_INST/CL/uram_ctrl_i/clk_div8_reg/Q]
