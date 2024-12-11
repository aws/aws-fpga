
#create_clock -period 10.0 [get_ports APB_0_PCLK]
#create_clock -period 10.0 [get_ports APB_1_PCLK]



#set_false_path -from [get_clocks */APB_0_PCLK] -to [get_clocks */APB_1_PCLK]
#set_false_path -from [get_clocks */APB_1_PCLK] -to [get_clocks */APB_0_PCLK] 

 
 
 
 
 
 
 
 
 
 
