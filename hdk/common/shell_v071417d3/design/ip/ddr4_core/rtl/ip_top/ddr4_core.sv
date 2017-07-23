

/******************************************************************************
// (c) Copyright 2013 - 2014 Xilinx, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of Xilinx, Inc. and is protected under U.S. and
// international copyright and other intellectual property
// laws.
//
// DISCLAIMER
// This disclaimer is not a license and does not grant any
// rights to the materials distributed herewith. Except as
// otherwise provided in a valid license issued to you by
// Xilinx, and to the maximum extent permitted by applicable
// law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// (2) Xilinx shall not be liable (whether in contract or tort,
// including negligence, or under any other theory of
// liability) for any loss or damage of any kind or nature
// related to, arising under or in connection with these
// materials, including for any direct, or any indirect,
// special, incidental, or consequential loss or damage
// (including loss of data, profits, goodwill, or any type of
// loss or damage suffered as a result of any action brought
// by a third party) even if such damage or loss was
// reasonably foreseeable or Xilinx had been advised of the
// possibility of the same.
//
// CRITICAL APPLICATIONS
// Xilinx products are not designed or intended to be fail-
// safe, or for use in any application requiring fail-safe
// performance, such as life-support or safety devices or
// systems, Class III medical devices, nuclear facilities,
// applications related to the deployment of airbags, or any
// other applications that could lead to death, personal
// injury, or severe property or environmental damage
// (individually and collectively, "Critical
// Applications"). Customer assumes the sole risk and
// liability of any use of Xilinx products in Critical
// Applications, subject only to applicable laws and
// regulations governing limitations on product liability.
//
// THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// PART OF THIS FILE AT ALL TIMES.
******************************************************************************/
//   ____  ____
//  /   /\/   /
// /___/  \  /    Vendor             : Xilinx
// \   \   \/     Version            : 1.0
//  \   \         Application        : DDR4
//  /   /         Filename           : ddr4_core.v
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4_SDRAM
// Purpose          :
//   Wrapper module for the user design top level file. This module can be 
//   instantiated in the system and interconnect as shown in example design 
//   (example_top module).
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ns/1ps
(* CORE_GENERATION_INFO = "DDR4_SDRAM, DDR4_SDRAM,{x_ipProduct=Vivado 2017.1.0,x_ipVendor=xilinx.com,x_ipLibrary=ip,x_ipName=DDR4_SDRAM,x_ipVersion=2.2, Controller_Type = DDR4_SDRAM, Time_Period = 937, Input_Clock_Period = 3332, Memory_Type = RDIMMs, Memory_Part = MTA18ASF2G72PZ-2G3, Ecc = true, Cas_Latency = 17, Cas_Write_Latency = 12, DQ_Width = 72, Chip_Select = true, Data_Mask = NONE, MEM_ADDR_ORDER = ROW_COLUMN_BANK_INTLV,  Is_AXI_Enabled = true , Slot_cofiguration =  Single , Clamshell_cofiguration =  false ,IS_FASTER_SPEED_RAM = No, Is_custom_part = false, Memory_Voltage = 1.2V, Phy_Only = Complete_Memory_Controller, Debug_Port = Disable, Burst_Length = 8, System_Clock = Differential, AXI_Selection = true, AXI_Data_Width = 512,  AXI_ArbitrationScheme = RD_PRI_REG, AXI_Narrow_Burst = true, Simulation_Mode = BFM, Debug_Mode = Disable, Example_TG = SIMPLE_TG, Self_Refresh = true, Save_Restore = true, MicroBlaze_ECC = false,  Specify_MandD = false, CLKBOUT_MULT = 8, DIVCLK_DIVIDE = 3, CLKOUT0_DIVIDE = 3}" *) 
(* X_CORE_INFO = "ddr4_v2_2_0,Vivado 2017.1_sdxop" *)
module ddr4_core
   (
   input  sys_rst,

   input                 c0_sys_clk_p,
   input                 c0_sys_clk_n,

   
   // Self-Refresh
    input         c0_ddr4_app_sref_req,        // application interface self-refresh request (to memory controller)
    output        c0_ddr4_app_sref_ack,        // application interface self-refresh acknowledgement (from memory controller)
    input         c0_ddr4_app_mem_init_skip,  
    // Save-Restore
    input         c0_ddr4_app_restore_en,  
    input         c0_ddr4_app_restore_complete,
    input         c0_ddr4_app_xsdb_select,
    input         c0_ddr4_app_xsdb_rd_en,
    input         c0_ddr4_app_xsdb_wr_en,
    input  [15:0] c0_ddr4_app_xsdb_addr,
    input  [8:0]  c0_ddr4_app_xsdb_wr_data,
    output [8:0]  c0_ddr4_app_xsdb_rd_data,
    output        c0_ddr4_app_xsdb_rdy,
    output [31:0] c0_ddr4_app_dbg_out,

   output                c0_ddr4_act_n,
   output [16:0]          c0_ddr4_adr,
   output [1:0]          c0_ddr4_ba,
   output [1:0]          c0_ddr4_bg,
   output [0:0]          c0_ddr4_cke,
   output [0:0]          c0_ddr4_odt,
   output [0:0]          c0_ddr4_cs_n,
   output [0:0]               c0_ddr4_ck_t,
   output [0:0]               c0_ddr4_ck_c,
   output                c0_ddr4_reset_n,
    output                c0_ddr4_parity,
   inout  [71:0]          c0_ddr4_dq,
   inout  [17:0]         c0_ddr4_dqs_c,
   inout  [17:0]         c0_ddr4_dqs_t,

   output                c0_init_calib_complete,
   output                c0_ddr4_ui_clk,
   output                c0_ddr4_ui_clk_sync_rst,
   output               dbg_clk,

    // AXI CTRL port
    input                              c0_ddr4_s_axi_ctrl_awvalid,
    output                             c0_ddr4_s_axi_ctrl_awready,
    input  [31:0]                      c0_ddr4_s_axi_ctrl_awaddr,
    // Slave Interface Write Data Ports
    input                              c0_ddr4_s_axi_ctrl_wvalid,
    output                             c0_ddr4_s_axi_ctrl_wready,
    input  [31:0]                      c0_ddr4_s_axi_ctrl_wdata,
    // Slave Interface Write Response Ports
    output                             c0_ddr4_s_axi_ctrl_bvalid,
    input                              c0_ddr4_s_axi_ctrl_bready,
    output [1:0]                       c0_ddr4_s_axi_ctrl_bresp,
    // Slave Interface Read Address Ports
    input                              c0_ddr4_s_axi_ctrl_arvalid,
    output                             c0_ddr4_s_axi_ctrl_arready,
    input  [31:0]                      c0_ddr4_s_axi_ctrl_araddr,
    // Slave Interface Read Data Ports
    output                             c0_ddr4_s_axi_ctrl_rvalid,
    input                              c0_ddr4_s_axi_ctrl_rready,
    output [31:0]                      c0_ddr4_s_axi_ctrl_rdata,
    output [1:0]                       c0_ddr4_s_axi_ctrl_rresp,

    // Interrupt output
    output                             c0_ddr4_interrupt,
   // Slave Interface Write Address Ports
   input                 c0_ddr4_aresetn,
   input  [15:0]      c0_ddr4_s_axi_awid,
   input  [33:0]    c0_ddr4_s_axi_awaddr,
   input  [7:0]                       c0_ddr4_s_axi_awlen,
   input  [2:0]                       c0_ddr4_s_axi_awsize,
   input  [1:0]                       c0_ddr4_s_axi_awburst,
   input  [0:0]                       c0_ddr4_s_axi_awlock,
   input  [3:0]                       c0_ddr4_s_axi_awcache,
   input  [2:0]                       c0_ddr4_s_axi_awprot,
   input  [3:0]                       c0_ddr4_s_axi_awqos,
   input                              c0_ddr4_s_axi_awvalid,
   output                             c0_ddr4_s_axi_awready,
   // Slave Interface Write Data Ports
   input  [511:0]    c0_ddr4_s_axi_wdata,
   input  [63:0]  c0_ddr4_s_axi_wstrb,
   input                              c0_ddr4_s_axi_wlast,
   input                              c0_ddr4_s_axi_wvalid,
   output                             c0_ddr4_s_axi_wready,
   // Slave Interface Write Response Ports
   input                              c0_ddr4_s_axi_bready,
   output [15:0]      c0_ddr4_s_axi_bid,
   output [1:0]                       c0_ddr4_s_axi_bresp,
   output                             c0_ddr4_s_axi_bvalid,
   // Slave Interface Read Address Ports
   input  [15:0]      c0_ddr4_s_axi_arid,
   input  [33:0]    c0_ddr4_s_axi_araddr,
   input  [7:0]                       c0_ddr4_s_axi_arlen,
   input  [2:0]                       c0_ddr4_s_axi_arsize,
   input  [1:0]                       c0_ddr4_s_axi_arburst,
   input  [0:0]                       c0_ddr4_s_axi_arlock,
   input  [3:0]                       c0_ddr4_s_axi_arcache,
   input  [2:0]                       c0_ddr4_s_axi_arprot,
   input  [3:0]                       c0_ddr4_s_axi_arqos,
   input                              c0_ddr4_s_axi_arvalid,
   output                             c0_ddr4_s_axi_arready,
   // Slave Interface Read Data Ports
   input                              c0_ddr4_s_axi_rready,
   output [15:0]      c0_ddr4_s_axi_rid,
   output [511:0]    c0_ddr4_s_axi_rdata,
   output [1:0]                       c0_ddr4_s_axi_rresp,
   output                             c0_ddr4_s_axi_rlast,
   output                             c0_ddr4_s_axi_rvalid,

   // Debug Port
   output wire [511:0]             dbg_bus
   );


ddr4_core_ddr4
   inst (
   .sys_rst           (sys_rst),

   .c0_sys_clk_p                   (c0_sys_clk_p),
   .c0_sys_clk_n                   (c0_sys_clk_n),

   .c0_ddr4_app_sref_req         (c0_ddr4_app_sref_req),
   .c0_ddr4_app_sref_ack         (c0_ddr4_app_sref_ack), 
   .c0_ddr4_app_mem_init_skip    (c0_ddr4_app_mem_init_skip),
  .c0_ddr4_app_restore_en         (c0_ddr4_app_restore_en),
  .c0_ddr4_app_restore_complete   (c0_ddr4_app_restore_complete),
  .c0_ddr4_app_xsdb_select        (c0_ddr4_app_xsdb_select),
  .c0_ddr4_app_xsdb_rd_en         (c0_ddr4_app_xsdb_rd_en),
  .c0_ddr4_app_xsdb_wr_en         (c0_ddr4_app_xsdb_wr_en ),
  .c0_ddr4_app_xsdb_addr          (c0_ddr4_app_xsdb_addr),
  .c0_ddr4_app_xsdb_wr_data       (c0_ddr4_app_xsdb_wr_data),
  .c0_ddr4_app_xsdb_rd_data       (c0_ddr4_app_xsdb_rd_data),
  .c0_ddr4_app_xsdb_rdy           (c0_ddr4_app_xsdb_rdy ),
  .c0_ddr4_app_dbg_out            (c0_ddr4_app_dbg_out ),
   .c0_init_calib_complete (c0_init_calib_complete),
   .c0_ddr4_act_n          (c0_ddr4_act_n),
   .c0_ddr4_adr            (c0_ddr4_adr),
   .c0_ddr4_ba             (c0_ddr4_ba),
   .c0_ddr4_bg             (c0_ddr4_bg),
   .c0_ddr4_cke            (c0_ddr4_cke),
   .c0_ddr4_odt            (c0_ddr4_odt),
   .c0_ddr4_cs_n           (c0_ddr4_cs_n),
   .c0_ddr4_ck_t           (c0_ddr4_ck_t),
   .c0_ddr4_ck_c           (c0_ddr4_ck_c),
   .c0_ddr4_reset_n        (c0_ddr4_reset_n),
   .c0_ddr4_parity         (c0_ddr4_parity),
   .c0_ddr4_dq             (c0_ddr4_dq),
   .c0_ddr4_dqs_c          (c0_ddr4_dqs_c),
   .c0_ddr4_dqs_t          (c0_ddr4_dqs_t),
   .c0_ddr4_ui_clk                (c0_ddr4_ui_clk),
   .c0_ddr4_ui_clk_sync_rst       (c0_ddr4_ui_clk_sync_rst),
   .addn_ui_clkout1                            (),
   .addn_ui_clkout2                            (),
   .addn_ui_clkout3                            (),
   .addn_ui_clkout4                            (),
   .dbg_clk                                    (dbg_clk),
   .sl_iport0                                  (37'b0),
   .sl_oport0                                  (),

   // AXI CTRL port
   .c0_ddr4_s_axi_ctrl_awvalid                     (c0_ddr4_s_axi_ctrl_awvalid),
   .c0_ddr4_s_axi_ctrl_awready                     (c0_ddr4_s_axi_ctrl_awready),
   .c0_ddr4_s_axi_ctrl_awaddr                      (c0_ddr4_s_axi_ctrl_awaddr),
   // Slave Interface Write Data Ports
   .c0_ddr4_s_axi_ctrl_wvalid                      (c0_ddr4_s_axi_ctrl_wvalid),
   .c0_ddr4_s_axi_ctrl_wready                      (c0_ddr4_s_axi_ctrl_wready),
   .c0_ddr4_s_axi_ctrl_wdata                       (c0_ddr4_s_axi_ctrl_wdata),
   // Slave Interface Write Response Ports
   .c0_ddr4_s_axi_ctrl_bvalid                      (c0_ddr4_s_axi_ctrl_bvalid),
   .c0_ddr4_s_axi_ctrl_bready                      (c0_ddr4_s_axi_ctrl_bready),
   .c0_ddr4_s_axi_ctrl_bresp                       (c0_ddr4_s_axi_ctrl_bresp),
   // Slave Interface Read Address Ports
   .c0_ddr4_s_axi_ctrl_arvalid                     (c0_ddr4_s_axi_ctrl_arvalid),
   .c0_ddr4_s_axi_ctrl_arready                     (c0_ddr4_s_axi_ctrl_arready),
   .c0_ddr4_s_axi_ctrl_araddr                      (c0_ddr4_s_axi_ctrl_araddr),
   // Slave Interface Read Data Ports
   .c0_ddr4_s_axi_ctrl_rvalid                      (c0_ddr4_s_axi_ctrl_rvalid),
   .c0_ddr4_s_axi_ctrl_rready                      (c0_ddr4_s_axi_ctrl_rready),
   .c0_ddr4_s_axi_ctrl_rdata                       (c0_ddr4_s_axi_ctrl_rdata),
   .c0_ddr4_s_axi_ctrl_rresp                       (c0_ddr4_s_axi_ctrl_rresp),
   // Interrupt output
   .c0_ddr4_interrupt                              (c0_ddr4_interrupt),
   .c0_ddr4_aresetn                                (c0_ddr4_aresetn),
   // Slave Interface Write Address Ports
   .c0_ddr4_s_axi_awid                             (c0_ddr4_s_axi_awid),
   .c0_ddr4_s_axi_awaddr                           (c0_ddr4_s_axi_awaddr),
   .c0_ddr4_s_axi_awlen                            (c0_ddr4_s_axi_awlen),
   .c0_ddr4_s_axi_awsize                           (c0_ddr4_s_axi_awsize),
   .c0_ddr4_s_axi_awburst                          (c0_ddr4_s_axi_awburst),
   .c0_ddr4_s_axi_awlock                           (c0_ddr4_s_axi_awlock),
   .c0_ddr4_s_axi_awcache                          (c0_ddr4_s_axi_awcache),
   .c0_ddr4_s_axi_awprot                           (c0_ddr4_s_axi_awprot),
   .c0_ddr4_s_axi_awqos                            (c0_ddr4_s_axi_awqos),
   .c0_ddr4_s_axi_awvalid                          (c0_ddr4_s_axi_awvalid),
   .c0_ddr4_s_axi_awready                          (c0_ddr4_s_axi_awready),
   // Slave Interface Write Data Ports
   .c0_ddr4_s_axi_wdata                            (c0_ddr4_s_axi_wdata),
   .c0_ddr4_s_axi_wstrb                            (c0_ddr4_s_axi_wstrb),
   .c0_ddr4_s_axi_wlast                            (c0_ddr4_s_axi_wlast),
   .c0_ddr4_s_axi_wvalid                           (c0_ddr4_s_axi_wvalid),
   .c0_ddr4_s_axi_wready                           (c0_ddr4_s_axi_wready),
   // Slave Interface Write Response Ports
   .c0_ddr4_s_axi_bid                              (c0_ddr4_s_axi_bid),
   .c0_ddr4_s_axi_bresp                            (c0_ddr4_s_axi_bresp),
   .c0_ddr4_s_axi_bvalid                           (c0_ddr4_s_axi_bvalid),
   .c0_ddr4_s_axi_bready                           (c0_ddr4_s_axi_bready),
   // Slave Interface Read Address Ports
   .c0_ddr4_s_axi_arid                             (c0_ddr4_s_axi_arid),
   .c0_ddr4_s_axi_araddr                           (c0_ddr4_s_axi_araddr),
   .c0_ddr4_s_axi_arlen                            (c0_ddr4_s_axi_arlen),
   .c0_ddr4_s_axi_arsize                           (c0_ddr4_s_axi_arsize),
   .c0_ddr4_s_axi_arburst                          (c0_ddr4_s_axi_arburst),
   .c0_ddr4_s_axi_arlock                           (c0_ddr4_s_axi_arlock),
   .c0_ddr4_s_axi_arcache                          (c0_ddr4_s_axi_arcache),
   .c0_ddr4_s_axi_arprot                           (c0_ddr4_s_axi_arprot),
   .c0_ddr4_s_axi_arqos                            (c0_ddr4_s_axi_arqos),
   .c0_ddr4_s_axi_arvalid                          (c0_ddr4_s_axi_arvalid),
   .c0_ddr4_s_axi_arready                          (c0_ddr4_s_axi_arready),
   // Slave Interface Read Data Ports
   .c0_ddr4_s_axi_rid                              (c0_ddr4_s_axi_rid),
   .c0_ddr4_s_axi_rdata                            (c0_ddr4_s_axi_rdata),
   .c0_ddr4_s_axi_rresp                            (c0_ddr4_s_axi_rresp),
   .c0_ddr4_s_axi_rlast                            (c0_ddr4_s_axi_rlast),
   .c0_ddr4_s_axi_rvalid                           (c0_ddr4_s_axi_rvalid),
   .c0_ddr4_s_axi_rready                           (c0_ddr4_s_axi_rready),
   // Debug Port
   .dbg_bus               (dbg_bus) 
   );

 endmodule
