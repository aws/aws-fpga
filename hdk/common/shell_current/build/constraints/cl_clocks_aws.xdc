#---------------------------------------
# Create Clock Constraints - CL 
#---------------------------------------
create_clock -period 4.000 -name cl_clk -waveform {0.000 2.000} [get_ports clk]
create_clock -period 8.000 -name cl_clk_xtra -waveform {0.000 4.000} [get_ports clk_xtra]
