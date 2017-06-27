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
// \   \   \/     Version            : 1.1
//  \   \         Application        : MIG
//  /   /         Filename           : ddr4_v2_2_0_axi_register_slice.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Apr 17 2014
//  \___\/\___\
//
//Device: UltraScale
//Design Name: AXI Upsizer
//Purpose:
// AXI Register Slice
//   Register selected channels on the forward and/or reverse signal paths.
//   5-channel memory-mapped AXI4 interfaces.
//
//--------------------------------------------------------------------------
//
// Structure:
//   ddr_axi_register_slice
//      ddr_axic_register_slice
//
//--------------------------------------------------------------------------
//Reference:
//Revision History:
//*****************************************************************************

`timescale 1ps/1ps

module ddr4_v2_2_0_axi_register_slice #
  (
   parameter C_FAMILY                            = "virtex6",
   parameter integer C_AXI_ID_WIDTH              = 4,
   parameter integer C_AXI_ADDR_WIDTH            = 32,
   parameter integer C_AXI_DATA_WIDTH            = 32,
   parameter integer C_AXI_SUPPORTS_USER_SIGNALS = 0,
   parameter integer C_AXI_AWUSER_WIDTH          = 1,
   parameter integer C_AXI_ARUSER_WIDTH          = 1,
   parameter integer C_AXI_WUSER_WIDTH           = 1,
   parameter integer C_AXI_RUSER_WIDTH           = 1,
   parameter integer C_AXI_BUSER_WIDTH           = 1,
   // C_REG_CONFIG_*:
   //   0 => BYPASS    = The channel is just wired through the module.
   //   1 => FWD_REV   = Both FWD and REV (fully-registered)
   //   2 => FWD       = The master VALID and payload signals are registrated. 
   //   3 => REV       = The slave ready signal is registrated
   //   4 => SLAVE_FWD = All slave side signals and master VALID and payload are registrated.
   //   5 => SLAVE_RDY = All slave side signals and master READY are registrated.
   //   6 => INPUTS    = Slave and Master side inputs are registrated.
   //   7 => LIGHT_WT  = 1-stage pipeline register with bubble cycle, both FWD and REV pipelining
   parameter         C_REG_CONFIG_AW = 32'h00000000,
   parameter         C_REG_CONFIG_W  = 32'h00000000,
   parameter         C_REG_CONFIG_B  = 32'h00000000,
   parameter         C_REG_CONFIG_AR = 32'h00000000,
   parameter         C_REG_CONFIG_R  = 32'h00000000
   )
  (
   // System Signals
   input wire ACLK,
   input wire ARESETN,

   // Slave Interface Write Address Ports
   input  wire [C_AXI_ID_WIDTH-1:0]     S_AXI_AWID,
   input  wire [C_AXI_ADDR_WIDTH-1:0]   S_AXI_AWADDR,
   input  wire [8-1:0]                  S_AXI_AWLEN,
   input  wire [3-1:0]                  S_AXI_AWSIZE,
   input  wire [2-1:0]                  S_AXI_AWBURST,
   input  wire [2-1:0]                  S_AXI_AWLOCK,
   input  wire [4-1:0]                  S_AXI_AWCACHE,
   input  wire [3-1:0]                  S_AXI_AWPROT,
   input  wire [4-1:0]                  S_AXI_AWREGION,
   input  wire [4-1:0]                  S_AXI_AWQOS,
   input  wire [C_AXI_AWUSER_WIDTH-1:0] S_AXI_AWUSER,
   input  wire                          S_AXI_AWVALID,
   output wire                          S_AXI_AWREADY,

   // Slave Interface Write Data Ports
   input wire [C_AXI_ID_WIDTH-1:0]      S_AXI_WID,
   input  wire [C_AXI_DATA_WIDTH-1:0]   S_AXI_WDATA,
   input  wire [C_AXI_DATA_WIDTH/8-1:0] S_AXI_WSTRB,
   input  wire                          S_AXI_WLAST,
   input  wire [C_AXI_WUSER_WIDTH-1:0]  S_AXI_WUSER,
   input  wire                          S_AXI_WVALID,
   output wire                          S_AXI_WREADY,

   // Slave Interface Write Response Ports
   output wire [C_AXI_ID_WIDTH-1:0]    S_AXI_BID,
   output wire [2-1:0]                 S_AXI_BRESP,
   output wire [C_AXI_BUSER_WIDTH-1:0] S_AXI_BUSER,
   output wire                         S_AXI_BVALID,
   input  wire                         S_AXI_BREADY,

   // Slave Interface Read Address Ports
   input  wire [C_AXI_ID_WIDTH-1:0]     S_AXI_ARID,
   input  wire [C_AXI_ADDR_WIDTH-1:0]   S_AXI_ARADDR,
   input  wire [8-1:0]                  S_AXI_ARLEN,
   input  wire [3-1:0]                  S_AXI_ARSIZE,
   input  wire [2-1:0]                  S_AXI_ARBURST,
   input  wire [2-1:0]                  S_AXI_ARLOCK,
   input  wire [4-1:0]                  S_AXI_ARCACHE,
   input  wire [3-1:0]                  S_AXI_ARPROT,
   input  wire [4-1:0]                  S_AXI_ARREGION,
   input  wire [4-1:0]                  S_AXI_ARQOS,
   input  wire [C_AXI_ARUSER_WIDTH-1:0] S_AXI_ARUSER,
   input  wire                          S_AXI_ARVALID,
   output wire                          S_AXI_ARREADY,

   // Slave Interface Read Data Ports
   output wire [C_AXI_ID_WIDTH-1:0]    S_AXI_RID,
   output wire [C_AXI_DATA_WIDTH-1:0]  S_AXI_RDATA,
   output wire [2-1:0]                 S_AXI_RRESP,
   output wire                         S_AXI_RLAST,
   output wire [C_AXI_RUSER_WIDTH-1:0] S_AXI_RUSER,
   output wire                         S_AXI_RVALID,
   input  wire                         S_AXI_RREADY,
   
   // Master Interface Write Address Port
   output wire [C_AXI_ID_WIDTH-1:0]     M_AXI_AWID,
   output wire [C_AXI_ADDR_WIDTH-1:0]   M_AXI_AWADDR,
   output wire [8-1:0]                  M_AXI_AWLEN,
   output wire [3-1:0]                  M_AXI_AWSIZE,
   output wire [2-1:0]                  M_AXI_AWBURST,
   output wire [2-1:0]                  M_AXI_AWLOCK,
   output wire [4-1:0]                  M_AXI_AWCACHE,
   output wire [3-1:0]                  M_AXI_AWPROT,
   output wire [4-1:0]                  M_AXI_AWREGION,
   output wire [4-1:0]                  M_AXI_AWQOS,
   output wire [C_AXI_AWUSER_WIDTH-1:0] M_AXI_AWUSER,
   output wire                          M_AXI_AWVALID,
   input  wire                          M_AXI_AWREADY,
   
   // Master Interface Write Data Ports
   output wire [C_AXI_ID_WIDTH-1:0]     M_AXI_WID,
   output wire [C_AXI_DATA_WIDTH-1:0]   M_AXI_WDATA,
   output wire [C_AXI_DATA_WIDTH/8-1:0] M_AXI_WSTRB,
   output wire                          M_AXI_WLAST,
   output wire [C_AXI_WUSER_WIDTH-1:0]  M_AXI_WUSER,
   output wire                          M_AXI_WVALID,
   input  wire                          M_AXI_WREADY,
   
   // Master Interface Write Response Ports
   input  wire [C_AXI_ID_WIDTH-1:0]    M_AXI_BID,
   input  wire [2-1:0]                 M_AXI_BRESP,
   input  wire [C_AXI_BUSER_WIDTH-1:0] M_AXI_BUSER,
   input  wire                         M_AXI_BVALID,
   output wire                         M_AXI_BREADY,
   
   // Master Interface Read Address Port
   output wire [C_AXI_ID_WIDTH-1:0]     M_AXI_ARID,
   output wire [C_AXI_ADDR_WIDTH-1:0]   M_AXI_ARADDR,
   output wire [8-1:0]                  M_AXI_ARLEN,
   output wire [3-1:0]                  M_AXI_ARSIZE,
   output wire [2-1:0]                  M_AXI_ARBURST,
   output wire [2-1:0]                  M_AXI_ARLOCK,
   output wire [4-1:0]                  M_AXI_ARCACHE,
   output wire [3-1:0]                  M_AXI_ARPROT,
   output wire [4-1:0]                  M_AXI_ARREGION,
   output wire [4-1:0]                  M_AXI_ARQOS,
   output wire [C_AXI_ARUSER_WIDTH-1:0] M_AXI_ARUSER,
   output wire                          M_AXI_ARVALID,
   input  wire                          M_AXI_ARREADY,
   
   // Master Interface Read Data Ports
   input  wire [C_AXI_ID_WIDTH-1:0]    M_AXI_RID,
   input  wire [C_AXI_DATA_WIDTH-1:0]  M_AXI_RDATA,
   input  wire [2-1:0]                 M_AXI_RRESP,
   input  wire                         M_AXI_RLAST,
   input  wire [C_AXI_RUSER_WIDTH-1:0] M_AXI_RUSER,
   input  wire                         M_AXI_RVALID,
   output wire                         M_AXI_RREADY
  );

  (* shift_extract="no", iob="false", equivalent_register_removal = "no" *) reg reset;
  always @(posedge ACLK) begin
    reset <= ~ARESETN;
  end

  // Write Address Port bit positions
  localparam C_AWUSER_RIGHT   = 0;
  localparam C_AWUSER_LEN     = C_AXI_SUPPORTS_USER_SIGNALS*C_AXI_AWUSER_WIDTH;
  localparam C_AWQOS_RIGHT    = C_AWUSER_RIGHT + C_AWUSER_LEN;
  localparam C_AWQOS_LEN      = 4;
  localparam C_AWREGION_RIGHT = C_AWQOS_RIGHT + C_AWQOS_LEN;
  localparam C_AWREGION_LEN   = 4;
  localparam C_AWPROT_RIGHT   = C_AWREGION_RIGHT + C_AWREGION_LEN;
  localparam C_AWPROT_LEN     = 3;
  localparam C_AWCACHE_RIGHT  = C_AWPROT_RIGHT + C_AWPROT_LEN;
  localparam C_AWCACHE_LEN    = 4;
  localparam C_AWLOCK_RIGHT   = C_AWCACHE_RIGHT + C_AWCACHE_LEN;
  localparam C_AWLOCK_LEN     = 2;
  localparam C_AWBURST_RIGHT  = C_AWLOCK_RIGHT + C_AWLOCK_LEN;
  localparam C_AWBURST_LEN    = 2;
  localparam C_AWSIZE_RIGHT   = C_AWBURST_RIGHT + C_AWBURST_LEN;
  localparam C_AWSIZE_LEN     = 3;
  localparam C_AWLEN_RIGHT    = C_AWSIZE_RIGHT + C_AWSIZE_LEN;
  localparam C_AWLEN_LEN      = 8;
  localparam C_AWADDR_RIGHT   = C_AWLEN_RIGHT + C_AWLEN_LEN;
  localparam C_AWADDR_LEN     = C_AXI_ADDR_WIDTH;
  localparam C_AWID_RIGHT     = C_AWADDR_RIGHT + C_AWADDR_LEN;
  localparam C_AWID_LEN       = C_AXI_ID_WIDTH;
  localparam C_AW_SIZE        = C_AWID_RIGHT+C_AWID_LEN;

  // Write Address Port FIFO data read and write
  wire [C_AW_SIZE-1:0] s_aw_data ;
  wire [C_AW_SIZE-1:0] m_aw_data ;
  
  // Write Data Port bit positions
  localparam C_WUSER_RIGHT   = 0;
  localparam C_WUSER_LEN     = C_AXI_SUPPORTS_USER_SIGNALS*C_AXI_WUSER_WIDTH;
  localparam C_WLAST_RIGHT   = C_WUSER_RIGHT + C_WUSER_LEN;
  localparam C_WLAST_LEN     = 1;
  localparam C_WSTRB_RIGHT   = C_WLAST_RIGHT + C_WLAST_LEN;
  localparam C_WSTRB_LEN     = C_AXI_DATA_WIDTH/8;
  localparam C_WDATA_RIGHT   = C_WSTRB_RIGHT + C_WSTRB_LEN;
  localparam C_WDATA_LEN     = C_AXI_DATA_WIDTH;
  localparam C_WID_RIGHT     = C_WDATA_RIGHT + C_WDATA_LEN;
  localparam C_WID_LEN       = C_AXI_ID_WIDTH;
  localparam C_W_SIZE        = C_WID_RIGHT+C_WID_LEN;

  // Write Data Port FIFO data read and write
  wire [C_W_SIZE-1:0] s_w_data;
  wire [C_W_SIZE-1:0] m_w_data;

  // Write Response Port bit positions
  localparam C_BUSER_RIGHT   = 0;
  localparam C_BUSER_LEN     = C_AXI_SUPPORTS_USER_SIGNALS*C_AXI_BUSER_WIDTH;
  localparam C_BRESP_RIGHT   = C_BUSER_RIGHT + C_BUSER_LEN;
  localparam C_BRESP_LEN     = 2;
  localparam C_BID_RIGHT     = C_BRESP_RIGHT + C_BRESP_LEN;
  localparam C_BID_LEN       = C_AXI_ID_WIDTH;
  localparam C_B_SIZE        = C_BID_RIGHT+C_BID_LEN;

  // Write Response Port FIFO data read and write
  wire [C_B_SIZE-1:0] s_b_data;
  wire [C_B_SIZE-1:0] m_b_data;

  // Read Address Port bit positions
  localparam C_ARUSER_RIGHT   = 0;
  localparam C_ARUSER_LEN     = C_AXI_SUPPORTS_USER_SIGNALS*C_AXI_ARUSER_WIDTH;
  localparam C_ARQOS_RIGHT    = C_ARUSER_RIGHT + C_ARUSER_LEN;
  localparam C_ARQOS_LEN      = 4;
  localparam C_ARREGION_RIGHT = C_ARQOS_RIGHT + C_ARQOS_LEN;
  localparam C_ARREGION_LEN   = 4;
  localparam C_ARPROT_RIGHT   = C_ARREGION_RIGHT + C_ARREGION_LEN;
  localparam C_ARPROT_LEN     = 3;
  localparam C_ARCACHE_RIGHT  = C_ARPROT_RIGHT + C_ARPROT_LEN;
  localparam C_ARCACHE_LEN    = 4;
  localparam C_ARLOCK_RIGHT   = C_ARCACHE_RIGHT + C_ARCACHE_LEN;
  localparam C_ARLOCK_LEN     = 2;
  localparam C_ARBURST_RIGHT  = C_ARLOCK_RIGHT + C_ARLOCK_LEN;
  localparam C_ARBURST_LEN    = 2;
  localparam C_ARSIZE_RIGHT   = C_ARBURST_RIGHT + C_ARBURST_LEN;
  localparam C_ARSIZE_LEN     = 3;
  localparam C_ARLEN_RIGHT    = C_ARSIZE_RIGHT + C_ARSIZE_LEN;
  localparam C_ARLEN_LEN      = 8;
  localparam C_ARADDR_RIGHT   = C_ARLEN_RIGHT + C_ARLEN_LEN;
  localparam C_ARADDR_LEN     = C_AXI_ADDR_WIDTH;
  localparam C_ARID_RIGHT     = C_ARADDR_RIGHT + C_ARADDR_LEN;
  localparam C_ARID_LEN       = C_AXI_ID_WIDTH;
  localparam C_AR_SIZE        = C_ARID_RIGHT+C_ARID_LEN;

  // Read Address Port FIFO data read and write
  wire [C_AR_SIZE-1:0] s_ar_data;
  wire [C_AR_SIZE-1:0] m_ar_data;

  // Read Data Ports bit positions
  localparam C_RUSER_RIGHT   = 0;
  localparam C_RUSER_LEN     = C_AXI_SUPPORTS_USER_SIGNALS*C_AXI_RUSER_WIDTH;
  localparam C_RLAST_RIGHT   = C_RUSER_RIGHT + C_RUSER_LEN;
  localparam C_RLAST_LEN     = 1;
  localparam C_RRESP_RIGHT   = C_RLAST_RIGHT + C_RLAST_LEN;
  localparam C_RRESP_LEN     = 2;
  localparam C_RDATA_RIGHT   = C_RRESP_RIGHT + C_RRESP_LEN;
  localparam C_RDATA_LEN     = C_AXI_DATA_WIDTH;
  localparam C_RID_RIGHT     = C_RDATA_RIGHT + C_RDATA_LEN;
  localparam C_RID_LEN       = C_AXI_ID_WIDTH;
  localparam C_R_SIZE        = C_RID_RIGHT+C_RID_LEN;

  // Read Data Ports FIFO data read and write
  wire [C_R_SIZE-1:0] s_r_data;
  wire [C_R_SIZE-1:0] m_r_data;

  generate
    
    ///////////////////////////////////////////////////////
    //
    // AW PIPE
    //
    ///////////////////////////////////////////////////////
    
    if (C_AXI_SUPPORTS_USER_SIGNALS == 1) begin : gen_async_aw_user
      assign s_aw_data    = {S_AXI_AWID, S_AXI_AWADDR, S_AXI_AWLEN, S_AXI_AWSIZE, 
                             S_AXI_AWBURST, S_AXI_AWLOCK, S_AXI_AWCACHE, S_AXI_AWPROT, 
                             S_AXI_AWREGION, S_AXI_AWQOS, S_AXI_AWUSER};
      assign M_AXI_AWUSER = m_aw_data[C_AWUSER_RIGHT+:C_AWUSER_LEN];
    end
    else begin : gen_asynch_aw_no_user
      assign s_aw_data    = {S_AXI_AWID, S_AXI_AWADDR, S_AXI_AWLEN, S_AXI_AWSIZE, 
                             S_AXI_AWBURST, S_AXI_AWLOCK, S_AXI_AWCACHE, S_AXI_AWPROT, 
                             S_AXI_AWREGION, S_AXI_AWQOS};
      assign M_AXI_AWUSER = {C_AXI_AWUSER_WIDTH{1'b0}};
    end

    assign M_AXI_AWID     = m_aw_data[C_AWID_RIGHT+:C_AWID_LEN];
    assign M_AXI_AWADDR   = m_aw_data[C_AWADDR_RIGHT+:C_AWADDR_LEN];
    assign M_AXI_AWLEN    = m_aw_data[C_AWLEN_RIGHT+:C_AWLEN_LEN];
    assign M_AXI_AWSIZE   = m_aw_data[C_AWSIZE_RIGHT+:C_AWSIZE_LEN];
    assign M_AXI_AWBURST  = m_aw_data[C_AWBURST_RIGHT+:C_AWBURST_LEN];
    assign M_AXI_AWLOCK   = m_aw_data[C_AWLOCK_RIGHT+:C_AWLOCK_LEN];
    assign M_AXI_AWCACHE  = m_aw_data[C_AWCACHE_RIGHT+:C_AWCACHE_LEN];
    assign M_AXI_AWPROT   = m_aw_data[C_AWPROT_RIGHT+:C_AWPROT_LEN];
    assign M_AXI_AWREGION = m_aw_data[C_AWREGION_RIGHT+:C_AWREGION_LEN];
    assign M_AXI_AWQOS    = m_aw_data[C_AWQOS_RIGHT+:C_AWQOS_LEN];
    
    ddr4_v2_2_0_axic_register_slice #
      (
       .C_FAMILY(C_FAMILY),
       .C_DATA_WIDTH(C_AW_SIZE),
       .C_REG_CONFIG(C_REG_CONFIG_AW)
       )
    aw_pipe
      (
       // System Signals
       .ACLK(ACLK),
       .ARESET(reset),

       // Slave side
       .S_PAYLOAD_DATA(s_aw_data),
       .S_VALID(S_AXI_AWVALID),
       .S_READY(S_AXI_AWREADY),

       // Master side
       .M_PAYLOAD_DATA(m_aw_data),
       .M_VALID(M_AXI_AWVALID),
       .M_READY(M_AXI_AWREADY)
       );
    

    ///////////////////////////////////////////////////////
    //
    //  Data Write PIPE
    //
    ///////////////////////////////////////////////////////  
    if (C_AXI_SUPPORTS_USER_SIGNALS == 1) begin : gen_async_w_user
      assign s_w_data     = {S_AXI_WID, S_AXI_WDATA, S_AXI_WSTRB, S_AXI_WLAST, S_AXI_WUSER};
      assign M_AXI_WUSER = m_w_data[C_WUSER_RIGHT+:C_WUSER_LEN];
    end
    else begin : gen_asynch_w_no_user
      assign s_w_data     = {S_AXI_WID, S_AXI_WDATA, S_AXI_WSTRB, S_AXI_WLAST};
      assign M_AXI_WUSER  = {C_AXI_WUSER_WIDTH{1'b0}};
    end

    assign M_AXI_WID      = m_w_data[C_WID_RIGHT+:C_WID_LEN];
    assign M_AXI_WDATA    = m_w_data[C_WDATA_RIGHT+:C_WDATA_LEN];
    assign M_AXI_WSTRB    = m_w_data[C_WSTRB_RIGHT+:C_WSTRB_LEN];
    assign M_AXI_WLAST    = m_w_data[C_WLAST_RIGHT+:C_WLAST_LEN];

    ddr4_v2_2_0_axic_register_slice #
      (
       .C_FAMILY(C_FAMILY),
       .C_DATA_WIDTH(C_W_SIZE),
       .C_REG_CONFIG(C_REG_CONFIG_W)
       )
      w_pipe
      (
       // System Signals
       .ACLK(ACLK),
       .ARESET(reset),

       // Slave side
       .S_PAYLOAD_DATA(s_w_data),
       .S_VALID(S_AXI_WVALID),
       .S_READY(S_AXI_WREADY),

       // Master side
       .M_PAYLOAD_DATA(m_w_data),
       .M_VALID(M_AXI_WVALID),
       .M_READY(M_AXI_WREADY)
       );

    
    ///////////////////////////////////////////////////////
    //
    // Write Response PIPE
    //
    ///////////////////////////////////////////////////////  
    if (C_AXI_SUPPORTS_USER_SIGNALS == 1) begin : gen_async_b_user
      assign m_b_data     = {M_AXI_BID, M_AXI_BRESP, M_AXI_BUSER};
      assign S_AXI_BUSER  = s_b_data[C_BUSER_RIGHT+:C_BUSER_LEN];
    end
    else begin : gen_asynch_b_no_user
      assign m_b_data     = {M_AXI_BID, M_AXI_BRESP};
      assign S_AXI_BUSER  = {C_AXI_BUSER_WIDTH{1'b0}};
    end

    assign S_AXI_BID      = s_b_data[C_BID_RIGHT+:C_BID_LEN];
    assign S_AXI_BRESP    = s_b_data[C_BRESP_RIGHT+:C_BRESP_LEN];

    ddr4_v2_2_0_axic_register_slice #
      (
       .C_FAMILY(C_FAMILY),
       .C_DATA_WIDTH(C_B_SIZE),
       .C_REG_CONFIG(C_REG_CONFIG_B)
       )
      b_pipe
      (
       // System Signals
       .ACLK(ACLK),
       .ARESET(reset),

       // Slave side
       .S_PAYLOAD_DATA(m_b_data),
       .S_VALID(M_AXI_BVALID),
       .S_READY(M_AXI_BREADY),

       // Master side
       .M_PAYLOAD_DATA(s_b_data),
       .M_VALID(S_AXI_BVALID),
       .M_READY(S_AXI_BREADY)
       );
 
    ///////////////////////////////////////////////////////
    //
    // Address Read PIPE
    //
    ///////////////////////////////////////////////////////  

    if (C_AXI_SUPPORTS_USER_SIGNALS == 1) begin : gen_async_ar_user
      assign s_ar_data    = {S_AXI_ARID, S_AXI_ARADDR, S_AXI_ARLEN, S_AXI_ARSIZE, 
                             S_AXI_ARBURST, S_AXI_ARLOCK, S_AXI_ARCACHE, S_AXI_ARPROT, 
                             S_AXI_ARREGION, S_AXI_ARQOS, S_AXI_ARUSER};
      assign M_AXI_ARUSER = m_ar_data[C_ARUSER_RIGHT+:C_ARUSER_LEN];
    end
    else begin : gen_asynch_ar_no_user
      assign s_ar_data    = {S_AXI_ARID, S_AXI_ARADDR, S_AXI_ARLEN, S_AXI_ARSIZE, 
                             S_AXI_ARBURST, S_AXI_ARLOCK, S_AXI_ARCACHE, S_AXI_ARPROT, 
                             S_AXI_ARREGION, S_AXI_ARQOS};
      
      assign M_AXI_ARUSER = {C_AXI_ARUSER_WIDTH{1'b0}};
    end

    assign M_AXI_ARID     = m_ar_data[C_ARID_RIGHT+:C_ARID_LEN];
    assign M_AXI_ARADDR   = m_ar_data[C_ARADDR_RIGHT+:C_ARADDR_LEN];
    assign M_AXI_ARLEN    = m_ar_data[C_ARLEN_RIGHT+:C_ARLEN_LEN];
    assign M_AXI_ARSIZE   = m_ar_data[C_ARSIZE_RIGHT+:C_ARSIZE_LEN];
    assign M_AXI_ARBURST  = m_ar_data[C_ARBURST_RIGHT+:C_ARBURST_LEN];
    assign M_AXI_ARLOCK   = m_ar_data[C_ARLOCK_RIGHT+:C_ARLOCK_LEN];
    assign M_AXI_ARCACHE  = m_ar_data[C_ARCACHE_RIGHT+:C_ARCACHE_LEN];
    assign M_AXI_ARPROT   = m_ar_data[C_ARPROT_RIGHT+:C_ARPROT_LEN];
    assign M_AXI_ARREGION = m_ar_data[C_ARREGION_RIGHT+:C_ARREGION_LEN];
    assign M_AXI_ARQOS    = m_ar_data[C_ARQOS_RIGHT+:C_ARQOS_LEN];

    ddr4_v2_2_0_axic_register_slice #
      (
       .C_FAMILY(C_FAMILY),
       .C_DATA_WIDTH(C_AR_SIZE),
       .C_REG_CONFIG(C_REG_CONFIG_AR)
       )
      ar_pipe
      (
       // System Signals
       .ACLK(ACLK),
       .ARESET(reset),

       // Slave side
       .S_PAYLOAD_DATA(s_ar_data),
       .S_VALID(S_AXI_ARVALID),
       .S_READY(S_AXI_ARREADY),

       // Master side
       .M_PAYLOAD_DATA(m_ar_data),
       .M_VALID(M_AXI_ARVALID),
       .M_READY(M_AXI_ARREADY)
       );
        
    ///////////////////////////////////////////////////////
    //
    //  Data Read PIPE
    //
    ///////////////////////////////////////////////////////
    
    if (C_AXI_SUPPORTS_USER_SIGNALS == 1) begin : gen_async_r_user
      assign m_r_data     = {M_AXI_RID, M_AXI_RDATA, M_AXI_RRESP, M_AXI_RLAST, M_AXI_RUSER};
      assign S_AXI_RUSER  = s_r_data[C_RUSER_RIGHT+:C_RUSER_LEN];
    end
    else begin : gen_asynch_r_no_user
      assign m_r_data     = {M_AXI_RID, M_AXI_RDATA, M_AXI_RRESP, M_AXI_RLAST};
      assign S_AXI_RUSER  = {C_AXI_RUSER_WIDTH{1'b0}};
    end
    
    assign S_AXI_RID      = s_r_data[C_RID_RIGHT+:C_RID_LEN];
    assign S_AXI_RDATA    = s_r_data[C_RDATA_RIGHT+:C_RDATA_LEN];
    assign S_AXI_RRESP    = s_r_data[C_RRESP_RIGHT+:C_RRESP_LEN];
    assign S_AXI_RLAST    = s_r_data[C_RLAST_RIGHT+:C_RLAST_LEN];

    ddr4_v2_2_0_axic_register_slice #
      (
       .C_FAMILY(C_FAMILY),
       .C_DATA_WIDTH(C_R_SIZE),
       .C_REG_CONFIG(C_REG_CONFIG_R)
       )
      r_pipe
      (
       // System Signals
       .ACLK(ACLK),
       .ARESET(reset),

       // Slave side
       .S_PAYLOAD_DATA(m_r_data),
       .S_VALID(M_AXI_RVALID),
       .S_READY(M_AXI_RREADY),

       // Master side
       .M_PAYLOAD_DATA(s_r_data),
       .M_VALID(S_AXI_RVALID),
       .M_READY(S_AXI_RREADY)
       );

  endgenerate

endmodule // ddr_axi_register_slice

