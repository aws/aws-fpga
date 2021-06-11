#######################################################################
# Copyright 2016 Amazon.com, Inc. or its affiliates.
# All Rights Reserved Worldwide.
# Amazon Confidential information
# Restricted NDA Material
#######################################################################

#create_clock -period 3.334 -name CLK_300M_DIMM0_DP [get_ports CLK_300M_DIMM0_DP]
#create_clock -period 3.334 -name CLK_300M_DIMM1_DP [get_ports CLK_300M_DIMM1_DP]
#create_clock -period 3.334 -name CLK_300M_DIMM3_DP [get_ports CLK_300M_DIMM3_DP]

#set_false_path -from [get_clocks cl_clk0] -to [get_clocks CLK_300M_DIMM0_DP]
#set_false_path -from [get_clocks cl_clk0] -to [get_clocks CLK_300M_DIMM1_DP]
#set_false_path -from [get_clocks cl_clk0] -to [get_clocks CLK_300M_DIMM3_DP]
#set_false_path -from [get_clocks CLK_300M_DIMM0_DP] -to [get_clocks cl_clk0]
#set_false_path -from [get_clocks CLK_300M_DIMM1_DP] -to [get_clocks cl_clk0]
#set_false_path -from [get_clocks CLK_300M_DIMM3_DP] -to [get_clocks cl_clk0]

#set_clock_groups -asynchronous -group [get_clocks cl_clk0] -group [get_clocks mmcm_clkout0*]

#set_clock_groups -asynchronous -group [get_clocks cl_clk0] -group [get_clocks CLK_300M_DIMM0_DP]
#set_clock_groups -asynchronous -group [get_clocks cl_clk0] -group [get_clocks CLK_300M_DIMM1_DP]
#set_clock_groups -asynchronous -group [get_clocks cl_clk0] -group [get_clocks CLK_300M_DIMM3_DP]

set_max_delay -datapath_only \
              -from [get_clocks -of_objects [get_pins SH_DDR/ddr_cores.DDR4_0/inst/u_ddr4_infrastructure/gen_mmcme4.u_mmcme_adv_inst/CLKOUT0]] \
              -to [get_clocks -of [get_ports clk_main_a0]] \
              [get_property PERIOD [get_clocks -of_objects [get_pins SH_DDR/ddr_cores.DDR4_0/inst/u_ddr4_infrastructure/gen_mmcme4.u_mmcme_adv_inst/CLKOUT0]]]
set_max_delay -datapath_only \
              -from [get_clocks -of_objects [get_pins SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_infrastructure/gen_mmcme4.u_mmcme_adv_inst/CLKOUT0]]    \
              -to [get_clocks -of [get_ports clk_main_a0]] \
              [get_property PERIOD [get_clocks -of_objects [get_pins SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_infrastructure/gen_mmcme4.u_mmcme_adv_inst/CLKOUT0]]]
set_max_delay -datapath_only \
              -from [get_clocks -of_objects [get_pins SH_DDR/ddr_cores.DDR4_2/inst/u_ddr4_infrastructure/gen_mmcme4.u_mmcme_adv_inst/CLKOUT0]]    \
              -to [get_clocks -of [get_ports clk_main_a0]] \
              [get_property PERIOD [get_clocks -of_objects [get_pins SH_DDR/ddr_cores.DDR4_2/inst/u_ddr4_infrastructure/gen_mmcme4.u_mmcme_adv_inst/CLKOUT0]]]
set_max_delay -datapath_only \
              -from [get_clocks -of [get_ports clk_main_a0]] \
              -to [get_clocks -of_objects [get_pins SH_DDR/ddr_cores.DDR4_*/inst/u_ddr4_infrastructure/gen_mmcme4.u_mmcme_adv_inst/CLKOUT0]] \
              [get_property PERIOD [get_clocks -of_objects [get_ports clk_main_a0]]]

set asyncFFs [get_cells -quiet -hier -filter {\
                                                  NAME =~ *SH_DDR/*sync_wr_rst/in_q_reg[0] || \
                                                  NAME =~ *SH_DDR/*sync_wr_rst/sync_out_reg[0] ||\
                                                  NAME =~ *SH_DDR/*sync_rd_rst/in_q_reg[0] || \
                                                  NAME =~ *SH_DDR/*sync_rd_rst/sync_out_reg[0] \
                                              }]
set asyncFFPins [get_pins -quiet -filter REF_PIN_NAME==CLR -of $asyncFFs]
set_false_path -quiet -to $asyncFFPins
set_property -quiet ASYNC_REG true $asyncFFs

#
# False Paths for Synchronizers inside sh_ddr.sv
#
set syncCells [get_cells -quiet -hierarchical -filter {\
                                                           NAME =~ *SH_DDR/*DDR_STAT_INC_SYNC0/in_q_reg*     || \
                                                           NAME =~ *SH_DDR/*DDR_STAT_INC_SYNC1/in_q_reg*     || \
                                                           NAME =~ *SH_DDR/*DDR_STAT_INC_SYNC2/in_q_reg*     || \
                                                           NAME =~ *SH_DDR/*SAVE_RST_TO_DDR_SYNC/in_q_reg*   || \
                                                           NAME =~ *SH_DDR/*SAVE_RST_FROM_DDR_SYNC/in_q_reg* || \
                                                           NAME =~ *SH_DDR/*CCF_XSDB_*/CCF_CTL/sync_write_ptr_rd/in_q_reg* || \
                                                           NAME =~ *SH_DDR/*CCF_XSDB_*/CCF_CTL/sync_read_ptr_wr/in_q_reg*  || \
                                                           NAME =~ *SH_DDR/*CCF_DDR_STAT_*/CCF_CTL/sync_write_ptr_rd/in_q_reg* || \
                                                           NAME =~ *SH_DDR/*CCF_DDR_STAT_*/CCF_CTL/sync_read_ptr_wr/in_q_reg*  \
                                                       }]
set syncPins [get_pins -quiet -filter {REF_PIN_NAME==D} -of_objects $syncCells]
set_false_path -quiet -to $syncPins

# Set ASYNC_REG property on syncrhonizer flops.
set syncOutCells [get_cells -quiet -hierarchical -filter {\
                                                           NAME =~ *SH_DDR/*DDR_STAT_INC_SYNC0/sync_out_reg*     || \
                                                           NAME =~ *SH_DDR/*DDR_STAT_INC_SYNC1/sync_out_reg*     || \
                                                           NAME =~ *SH_DDR/*DDR_STAT_INC_SYNC2/sync_out_reg*     || \
                                                           NAME =~ *SH_DDR/*SAVE_RST_TO_DDR_SYNC/sync_out_reg*   || \
                                                           NAME =~ *SH_DDR/*SAVE_RST_FROM_DDR_SYNC/sync_out_reg* || \
                                                           NAME =~ *SH_DDR/*CCF_XSDB_*/CCF_CTL/sync_write_ptr_rd/sync_out_reg* || \
                                                           NAME =~ *SH_DDR/*CCF_XSDB_*/CCF_CTL/sync_read_ptr_wr/sync_out_reg*  || \
                                                           NAME =~ *SH_DDR/*CCF_DDR_STAT_*/CCF_CTL/sync_write_ptr_rd/sync_out_reg* || \
                                                           NAME =~ *SH_DDR/*CCF_DDR_STAT_*/CCF_CTL/sync_read_ptr_wr/sync_out_reg*  \
                                                          }]
set_property -quiet ASYNC_REG true $syncCells $syncOutCells

#
# CDC False Paths in sh_ddr.sv
#
set fromPins [get_pins -quiet -filter {REF_PIN_NAME==CLK} -of_objects [get_cells -quiet -hierarchical -filter {\
                                                                                                                   NAME =~ *SH_DDR/*CCF_XSDB_*/ram_reg* || \
                                                                                                                   NAME =~ *SH_DDR/*CCF_DDR_STAT_*/ram_reg* \
                                                                                                               }]]
set toPins [get_pins -quiet -filter {REF_PIN_NAME==D} -of_objects [get_cells -hierarchical -quiet -filter {\
                                                                                                               NAME =~ *SH_DDR/*CCF_XSDB_*/rd_do_reg* || \
                                                                                                               NAME =~ *SH_DDR/*CCF_DDR_STAT_*/rd_do_reg* \
                                                                                                           }]]
set_false_path -quiet -from $fromPins -to $toPins
