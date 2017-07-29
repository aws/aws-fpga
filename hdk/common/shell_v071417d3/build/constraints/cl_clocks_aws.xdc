#---------------------------------------
# Create Clock Constraints - CL 
#---------------------------------------
create_clock -period 4.000 -name cl_clk0 -waveform {0.000 2.000} [get_ports clk_main_a0]
set_false_path -from [get_ports rst_main_n]
