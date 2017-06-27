###############################################################################################################
# Core-Level Timing Constraints for axi_clock_converter Component "axi_clock_converter_0"
###############################################################################################################
#
# This component is configured to perform asynchronous clock-domain-crossing.
# In order for these core-level constraints to work properly, 
# the following rules apply to your system-level timing constraints:
#   1. Each of the nets connected to the s_axi_aclk and m_axi_aclk ports of this component
#      must have exactly one clock defined on it, using either
#      a) a create_clock command on a top-level clock pin specified in your system XDC file, or
#      b) a create_generated_clock command, typically generated automatically by a core 
#          producing a derived clock signal.
#   2. The s_axi_aclk and m_axi_aclk ports of this component should not be connected to the
#      same clock source.
#
set s_clk [get_clocks -of_objects [get_ports -scoped_to_current_instance s_axi_aclk]]
set m_clk [get_clocks -of_objects [get_ports -scoped_to_current_instance m_axi_aclk]]
set_false_path -through [get_ports -filter {NAME =~ *_axi_aresetn}] -to [get_pins -hierarchical -filter {NAME =~ */inst_fifo_gen/*rstblk*/*PRE}]
set_false_path -from [get_cells  -hierarchical -filter {NAME =~ */inst_fifo_gen/*rstblk*/*rst_reg_reg[*]}]
set_max_delay -from [filter [all_fanout -from [get_ports -scoped_to_current_instance s_axi_aclk] -flat -endpoints_only] {IS_LEAF}] -to [filter [all_fanout -from [get_ports -scoped_to_current_instance m_axi_aclk] -flat -only_cells] {IS_SEQUENTIAL && (NAME !~ *dout_i_reg[*])}] -datapath_only [get_property -min PERIOD $s_clk]
set_max_delay -from [filter [all_fanout -from [get_ports -scoped_to_current_instance m_axi_aclk] -flat -endpoints_only] {IS_LEAF}] -to [filter [all_fanout -from [get_ports -scoped_to_current_instance s_axi_aclk] -flat -only_cells] {IS_SEQUENTIAL && (NAME !~ *dout_i_reg[*])}] -datapath_only [get_property -min PERIOD $m_clk]
set s_ram_cells [filter [all_fanout -from [get_ports -scoped_to_current_instance s_axi_aclk] -flat -endpoints_only -only_cells] {PRIMITIVE_SUBGROUP==dram || PRIMITIVE_SUBGROUP==LUTRAM}]
set m_ram_cells [filter [all_fanout -from [get_ports -scoped_to_current_instance m_axi_aclk] -flat -endpoints_only -only_cells] {PRIMITIVE_SUBGROUP==dram || PRIMITIVE_SUBGROUP==LUTRAM}]
set_false_path -from [get_pins -of $s_ram_cells -filter {REF_PIN_NAME == CLK}] -through [get_pins -of $s_ram_cells -filter {REF_PIN_NAME == O}] 
set_false_path -from [get_pins -of $m_ram_cells -filter {REF_PIN_NAME == CLK}] -through [get_pins -of $m_ram_cells -filter {REF_PIN_NAME == O}] 
