set bridge [get_debug_cores -filter {NAME=~CL/dbg_hub_1}]
current_instance $bridge/inst/BSCANID.u_xsdbm_id/CORE_XSDB.UUT_MASTER/U_ICON_INTERFACE/U_CMD6_RD/U_RD_FIFO/SUBCORE_FIFO.xsdbm_v3_0_0_rdfifo_inst

set wr_clock          [get_clocks -of_objects [get_ports -scoped_to_current_instance clk]]
set rd_clock          [get_clocks -of_objects [get_ports -scoped_to_current_instance tck]]
set wr_clk_period     [get_property PERIOD $wr_clock]
set rd_clk_period     [get_property PERIOD $rd_clock]
set skew_value [expr {(($wr_clk_period < $rd_clk_period) ? $wr_clk_period : $rd_clk_period)} ]

# Ignore paths from the write clock to the read data registers for Asynchronous Distributed RAM based FIFO
set_false_path -from [filter [all_fanout -from [get_ports -scoped_to_current_instance clk] -flat -endpoints_only] {IS_LEAF}] -to [get_cells -hierarchical -filter {NAME =~ *gdm.dm_gen.dm*/gpr1.dout_i_reg*}]

# Set max delay on cross clock domain path for Block/Distributed RAM based FIFO

set_max_delay -from [get_cells inst_fifo_gen/gconvfifo.rf/grf.rf/gntv_or_sync_fifo.gcx.clkx/*rd_pntr_gc_reg[*]] -to [get_cells inst_fifo_gen/gconvfifo.rf/grf.rf/gntv_or_sync_fifo.gcx.clkx/*gsync_stage[1].wr_stg_inst/Q_reg_reg[*]] -datapath_only [get_property -min PERIOD $rd_clock]
set_bus_skew -from [get_cells inst_fifo_gen/gconvfifo.rf/grf.rf/gntv_or_sync_fifo.gcx.clkx/*rd_pntr_gc_reg[*]] -to [get_cells inst_fifo_gen/gconvfifo.rf/grf.rf/gntv_or_sync_fifo.gcx.clkx/*gsync_stage[1].wr_stg_inst/Q_reg_reg[*]] $skew_value

set_max_delay -from [get_cells inst_fifo_gen/gconvfifo.rf/grf.rf/gntv_or_sync_fifo.gcx.clkx/*wr_pntr_gc_reg[*]] -to [get_cells inst_fifo_gen/gconvfifo.rf/grf.rf/gntv_or_sync_fifo.gcx.clkx/*gsync_stage[1].rd_stg_inst/Q_reg_reg[*]] -datapath_only [get_property -min PERIOD $wr_clock]
set_bus_skew -from [get_cells inst_fifo_gen/gconvfifo.rf/grf.rf/gntv_or_sync_fifo.gcx.clkx/*wr_pntr_gc_reg[*]] -to [get_cells inst_fifo_gen/gconvfifo.rf/grf.rf/gntv_or_sync_fifo.gcx.clkx/*gsync_stage[1].rd_stg_inst/Q_reg_reg[*]] $skew_value

current_instance

current_instance $bridge/inst/BSCANID.u_xsdbm_id/CORE_XSDB.UUT_MASTER/U_ICON_INTERFACE/U_CMD6_WR/U_WR_FIFO/SUBCORE_FIFO.xsdbm_v3_0_0_wrfifo_inst

set wr_clock          [get_clocks -of_objects [get_ports -scoped_to_current_instance tck]]
set rd_clock          [get_clocks -of_objects [get_ports -scoped_to_current_instance clk]]
set wr_clk_period     [get_property PERIOD $wr_clock]
set rd_clk_period     [get_property PERIOD $rd_clock]
set skew_value [expr {(($wr_clk_period < $rd_clk_period) ? $wr_clk_period : $rd_clk_period)} ]

# Ignore paths from the write clock to the read data registers for Asynchronous Distributed RAM based FIFO
set_false_path -from [filter [all_fanout -from [get_ports -scoped_to_current_instance tck] -flat -endpoints_only] {IS_LEAF}] -to [get_cells -hierarchical -filter {NAME =~ *gdm.dm_gen.dm*/gpr1.dout_i_reg*}]

# Set max delay on cross clock domain path for Block/Distributed RAM based FIFO

set_max_delay -from [get_cells inst_fifo_gen/gconvfifo.rf/grf.rf/gntv_or_sync_fifo.gcx.clkx/*rd_pntr_gc_reg[*]] -to [get_cells inst_fifo_gen/gconvfifo.rf/grf.rf/gntv_or_sync_fifo.gcx.clkx/*gsync_stage[1].wr_stg_inst/Q_reg_reg[*]] -datapath_only [get_property -min PERIOD $rd_clock]
set_bus_skew -from [get_cells inst_fifo_gen/gconvfifo.rf/grf.rf/gntv_or_sync_fifo.gcx.clkx/*rd_pntr_gc_reg[*]] -to [get_cells inst_fifo_gen/gconvfifo.rf/grf.rf/gntv_or_sync_fifo.gcx.clkx/*gsync_stage[1].wr_stg_inst/Q_reg_reg[*]] $skew_value

set_max_delay -from [get_cells inst_fifo_gen/gconvfifo.rf/grf.rf/gntv_or_sync_fifo.gcx.clkx/*wr_pntr_gc_reg[*]] -to [get_cells inst_fifo_gen/gconvfifo.rf/grf.rf/gntv_or_sync_fifo.gcx.clkx/*gsync_stage[1].rd_stg_inst/Q_reg_reg[*]] -datapath_only [get_property -min PERIOD $wr_clock]
set_bus_skew -from [get_cells inst_fifo_gen/gconvfifo.rf/grf.rf/gntv_or_sync_fifo.gcx.clkx/*wr_pntr_gc_reg[*]] -to [get_cells inst_fifo_gen/gconvfifo.rf/grf.rf/gntv_or_sync_fifo.gcx.clkx/*gsync_stage[1].rd_stg_inst/Q_reg_reg[*]] $skew_value

current_instance
