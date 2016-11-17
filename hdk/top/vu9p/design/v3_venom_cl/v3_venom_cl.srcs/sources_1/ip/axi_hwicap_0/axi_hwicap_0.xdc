# file: axi_hwicap_0.xdc
# (c) Copyright 2009 - 2011 Xilinx, Inc. All rights reserved.
# 
# This file contains confidential and proprietary information
# of Xilinx, Inc. and is protected under U.S. and
# international copyright and other intellectual property
# laws.
# 
# DISCLAIMER
# This disclaimer is not a license and does not grant any
# rights to the materials distributed herewith. Except as
# otherwise provided in a valid license issued to you by
# Xilinx, and to the maximum extent permitted by applicable
# law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
# WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
# AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
# BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
# INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
# (2) Xilinx shall not be liable (whether in contract or tort,
# including negligence, or under any other theory of
# liability) for any loss or damage of any kind or nature
# related to, arising under or in connection with these
# materials, including for any direct, or any indirect,
# special, incidental, or consequential loss or damage
# (including loss of data, profits, goodwill, or any type of
# loss or damage suffered as a result of any action brought
# by a third party) even if such damage or loss was
# reasonably foreseeable or Xilinx had been advised of the
# possibility of the same.
# 
# CRITICAL APPLICATIONS
# Xilinx products are not designed or intended to be fail-
# safe, or for use in any application requiring fail-safe
# performance, such as life-support or safety devices or
# systems, Class III medical devices, nuclear facilities,
# applications related to the deployment of airbags, or any
# other applications that could lead to death, personal
# injury, or severe property or environmental damage
# (individually and collectively, "Critical
# Applications"). Customer assumes the sole risk and
# liability of any use of Xilinx products in Critical
# Applications, subject only to applicable laws and
# regulations governing limitations on product liability.
# 
# THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
# PART OF THIS FILE AT ALL TIMES.

set_false_path -to [get_pins -hier *cdc_to*/D]



# Following are the constrains for FIFO Generator to eliminate setup/hold violation warnings in simulations
# This example is using the Set Max Delay constrains for the cross clock domain pointers

# For WR FIFO
set_false_path -from [get_cells -hierarchical -filter {NAME =~*HWICAP_CTRL_I/IPIC_IF_I/WRFIFO.WRDATA_FIFO_I/USE_2N_DEPTH.V6_S6_AND_LATER.I_ASYNC_FIFO_BRAM/*rstblk*/*rst_reg_reg[*]}]
set_false_path -to [get_pins -hierarchical -filter {NAME =~*HWICAP_CTRL_I/IPIC_IF_I/WRFIFO.WRDATA_FIFO_I/USE_2N_DEPTH.V6_S6_AND_LATER.I_ASYNC_FIFO_BRAM/*rstblk*/*PRE}]
set_false_path -from [get_cells -hierarchical -filter {NAME =~ *gsckt_wrst.gic_rst.sckt_wrst_i_reg}] -to [get_cells -hierarchical -filter {NAME =~ *gsckt_wrst.gic_rst.garst_sync_ic[1].rd_rst_inst/Q_reg_reg[0]}]
set_false_path -from [get_cells -hierarchical -filter {NAME =~ *gsckt_wrst.gic_rst.garst_sync_ic[3].rd_rst_inst/Q_reg_reg[0]}] -to [get_cells -hierarchical -filter {NAME =~ *gsckt_wrst.gic_rst.garst_sync_ic[1].rd_rst_wr_inst/Q_reg_reg[0]}]

##set_false_path -to [get_pins -hierarchical -filter {NAME =~*/*rstblk*/*CLR}]






#set_false_path -to [get_pins -hierarchical -filter {NAME =~*HWICAP_CTRL_I/IPIC_IF_I/*full_int_1*/*PRE}]
# For RD FIFO
set_false_path -from [get_cells -hierarchical -filter {NAME =~*HWICAP_CTRL_I/IPIC_IF_I/RD_FIFO.RDDATA_FIFO_I/USE_2N_DEPTH.V6_S6_AND_LATER.I_ASYNC_FIFO_BRAM/*rstblk*/*rst_reg_reg[*]}]
set_false_path -to [get_pins -hierarchical -filter {NAME =~*HWICAP_CTRL_I/IPIC_IF_I/RD_FIFO.RDDATA_FIFO_I/USE_2N_DEPTH.V6_S6_AND_LATER.I_ASYNC_FIFO_BRAM/*rstblk*/*PRE}]
##set_false_path -to [get_pins -hierarchical -filter {NAME =~*/*rstblk*/*CLR}]
set_false_path -from [get_cells -hierarchical -filter {NAME =~ *gsckt_wrst.gic_rst.sckt_wrst_i_reg}] -to [get_cells -hierarchical -filter {NAME =~ *gsckt_wrst.gic_rst.garst_sync_ic[1].rd_rst_inst/Q_reg_reg[0]}]
set_false_path -from [get_cells -hierarchical -filter {NAME =~ *gsckt_wrst.gic_rst.garst_sync_ic[3].rd_rst_inst/Q_reg_reg[0]}] -to [get_cells -hierarchical -filter {NAME =~ *gsckt_wrst.gic_rst.garst_sync_ic[1].rd_rst_wr_inst/Q_reg_reg[0]}]




