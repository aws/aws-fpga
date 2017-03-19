#---------------------------------------
# Create Clock Constraints - CL 
#---------------------------------------
create_clock -period 8.000 -name cl_clk0 -waveform {0.000 4.000} [get_ports clk_main_a0]

