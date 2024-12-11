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
set s_ram_cells [filter [all_fanout -from [get_ports -scoped_to_current_instance s_axi_aclk] -flat -endpoints_only -only_cells] {PRIMITIVE_SUBGROUP==dram || PRIMITIVE_SUBGROUP==LUTRAM}]
set m_ram_cells [filter [all_fanout -from [get_ports -scoped_to_current_instance m_axi_aclk] -flat -endpoints_only -only_cells] {PRIMITIVE_SUBGROUP==dram || PRIMITIVE_SUBGROUP==LUTRAM}]
set_false_path -from [get_pins -of $s_ram_cells -filter {REF_PIN_NAME == CLK}] -through [get_pins -of $s_ram_cells -filter {REF_PIN_NAME == O}] 
set_false_path -from [get_pins -of $m_ram_cells -filter {REF_PIN_NAME == CLK}] -through [get_pins -of $m_ram_cells -filter {REF_PIN_NAME == O}] 
create_waiver -internal -scope -type CDC -id CDC-10 -user axi_clock_converter -tags "1024161" -to [get_pins -quiet *gen_clock_conv.gen_async_conv.asyncfifo_axi/inst_fifo_gen/gaxi_full_lite.g*_ch.g*ch2.axi_*/grf.rf/rstblk/ngwrdrst.grst.g7serrst.gnsckt_*_reg2_inst/arststages_ff_reg[0]/PRE]\
-description {Waiving CDC-10 Although there is combo logic going into FIFO Gen reset, the expectation/rule is that the reset signal will be held for 1 clk cycles on the slowest clock.  Hence there should not be any issues cause by this logic}

create_waiver -internal -scope -type CDC -id CDC-11 -user axi_clock_converter -tags "1024161" -to [get_pins -quiet *gen_clock_conv.gen_async_conv.asyncfifo_axi/inst_fifo_gen/gaxi_full_lite.g*_ch.g*ch2.axi_*/grf.rf/rstblk/ngwrdrst.grst.g7serrst.gnsckt_*_reg2_inst/arststages_ff_reg[0]/PRE]\
-description {Waiving CDC-11 Although there is combo logic going into FIFO Gen reset, the expectation/rule is that the reset signal will be held for 1 clk cycles on the slowest clock.  Hence there should not be any issues cause by this logic}

create_waiver -internal -scope -type CDC -id CDC-15 -user axi_clock_converter -tags "1024442" -from [get_pins -quiet *gen_clock_conv.gen_async_conv.asyncfifo_axi/inst_fifo_gen/gaxi_full_lite.g*_ch.g*ch2.axi_*/grf.rf/gntv_or_sync_fifo.mem/gdm.dm_gen.dm/RAM_reg_0_15_*/RAM*/CLK]\ 
-to [get_pins -quiet *gen_clock_conv.gen_async_conv.asyncfifo_axi/inst_fifo_gen/gaxi_full_lite.g*_ch.g*ch2.axi_*/grf.rf/gntv_or_sync_fifo.mem/gdm.dm_gen.dm/gpr1.dout_i_reg*/D]\
-description {Waiving CDC-15 Timing constraints are processed during implementation, not synthesis. The xdc is marked only to be used during implementation, as advised by the XDC folks at the time.}

create_waiver -internal -scope -type METHODOLOGY -id {LUTAR-1} -user "axi_clock_converter" -desc {the pathway is completely within fifo-gen, and that path is present dual-clock usage}\
-tags "1024444"\
 -objects [get_cells -hierarchical "*gen_clock_conv.gen_async_conv.asyncfifo_axi*"] \
 -objects [get_pins -hierarchical * -filter "(NAME=~*gen_clock_conv.gen_async_conv.asyncfifo_axi/inst_fifo_gen/gaxi_full_lite.g*_ch.g*ch2.axi_*/grf.rf/rstblk/ngwrdrst.grst.g7serrst.gnsckt_wrst.gic_rst.rst_rd_reg2_inst/arststages_ff_reg*/PRE) || (NAME=~*gen_clock_conv.gen_async_conv.asyncfifo_axi/inst_fifo_gen/gaxi_full_lite.g*_ch.g*ch2.axi_*/grf.rf/rstblk/ngwrdrst.grst.g7serrst.gnsckt_wrst.rst_wr_reg2_inst/arststages_ff_reg*/PRE)"]

create_waiver -type CDC -id {CDC-1} -user "axi_clock_converter" -desc "Timing uncritical paths" -tags "1165269" -scope -internal \
    -from [get_pins -quiet -filter REF_PIN_NAME=~*C -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_clock_conv.gen_sync_conv.axic_sample_cycle_inst/gen_sample_cycle.slow_aclk_div2_reg}]] \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_clock_conv.gen_sync_conv.axic_sample_cycle_inst/gen_sample_cycle.posedge_finder_*_reg}]]

create_waiver -type CDC -id {CDC-1} -user "axi_clock_converter" -desc "Timing uncritical paths" -tags "1165269" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_clock_conv.gen_sync_conv.gen_conv_*_ch.*_sync_clock_converter/gen_sync_clock_converter.*_*_*_reg}]]

create_waiver -type CDC -id {CDC-1} -user "axi_clock_converter" -desc "Timing uncritical paths" -tags "1165269" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~* -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_clock_conv.gen_sync_conv.gen_conv_*_ch.*_sync_clock_converter/*[*]}]]

create_waiver -type CDC -id {CDC-1} -user "axi_clock_converter" -desc "Timing uncritical paths" -tags "1165269" -scope -internal \
    -from [get_pins -quiet -filter REF_PIN_NAME=~*C -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_clock_conv.gen_sync_conv.gen_conv_*_ch.*_sync_clock_converter/FSM_sequential_gen_sync_clock_converter.state_reg[*]}]] \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_clock_conv.gen_sync_conv.gen_conv_*_ch.*_sync_clock_converter/gen_sync_clock_converter.*_t*_r_reg}]]

create_waiver -type CDC -id {CDC-10} -user "axi_clock_converter" -desc "Timing uncritical paths" -tags "1165269" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_clock_conv.gen_sync_conv.axic_sample_cycle_inst/gen_sample_cycle.gen_delay[*].sample_cycle_*_reg[*]}]]

create_waiver -type CDC -id {CDC-1} -user "axi_clock_converter" -desc "Timing uncritical paths" -tags "1165269" -scope -internal \
    -from [get_pins -quiet -filter REF_PIN_NAME=~*C -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_clock_conv.gen_sync_conv.axic_sample_cycle_inst/gen_sample_cycle.slow_aclk_div2_reg}]] \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_clock_conv.gen_sync_conv.axic_sample_cycle_inst/gen_sample_cycle.*.sample_cycle_*_reg[*]}]]

create_waiver -type CDC -id {CDC-1} -user "axi_clock_converter" -desc "Timing uncritical paths" -tags "1165269" -scope -internal \
    -from [get_pins -quiet -filter REF_PIN_NAME=~*C -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_clock_conv.gen_sync_conv.axic_sample_cycle_inst/gen_sample_cycle.slow_aclk_div2_reg}]] \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_clock_conv.gen_sync_conv.axic_sample_cycle_inst/gen_sample_cycle.sample_cycle_*_reg}]]

create_waiver -type CDC -id {CDC-1} -user "axi_clock_converter" -desc "Timing uncritical paths" -tags "1165269" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_clock_conv.gen_sync_conv.gen_conv_*_ch.*_sync_clock_converter/FSM_sequential_gen_sync_clock_converter.state_reg[*]_rep}]]

create_waiver -type CDC -id {CDC-1} -user "axi_clock_converter" -desc "Timing uncritical paths" -tags "1165269" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_clock_conv.gen_sync_conv.gen_conv_*_ch.*_sync_clock_converter/FSM_sequential_gen_sync_clock_converter.state_reg[*]_rep__*}]]
 
create_waiver -type CDC -id {CDC-1} -user "axi_clock_converter" -desc "Timing uncritical paths" -tags "1165269" -scope -internal \
    -from [get_pins -quiet -filter REF_PIN_NAME=~*C -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_clock_conv.gen_sync_conv.gen_conv_*_ch.*_sync_clock_converter/gen_sync_clock_converter.m_tready_hold_reg_rep__*}]] \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*CE -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_clock_conv.gen_sync_conv.gen_conv_*_ch.*_sync_clock_converter/FSM_sequential_gen_sync_clock_converter.m_tpayload_r_reg[*]}]]

create_waiver -type CDC -id {CDC-2} -user "axi_clock_converter" -desc "Timing uncritical paths" -tags "1165269" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_clock_conv.gen_sync_conv.axic_sample_cycle_inst/gen_sample_cycle.gen_delay[*].sample_cycle_d_reg[*]}]]

