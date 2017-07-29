
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
//  /   /         Filename           : ddr4_v2_2_0_axi_upsizer.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Apr 17 2014
//  \___\/\___\
//
//Device: UltraScale
//Design Name: AXI Upsizer
//Description: Up-Sizer
//Up-Sizer for generic SI- and MI-side data widths. This module instantiates
//Address, Write Data and Read Data Up-Sizer modules, each one taking care
//of the channel specific tasks.
//The Address Up-Sizer can handle both AR and AW channels.
//
//Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   ddr_axi_upsizer
//     ddr_a_upsizer
//       fifo
//         fifo_gen
//           fifo_coregen
//     ddr_w_upsizer
//     ddr_r_upsizer
//
//Reference:
//Revision History:
//*****************************************************************************
`timescale 1ps/1ps
`default_nettype none

module ddr4_v2_2_0_axi_upsizer #
  (
   parameter         C_FAMILY                         = "rtl", 
                       // FPGA Family. Current version: virtex6 or spartan6.
   parameter integer C_AXI_ID_WIDTH                 = 4, 
                       // Width of all ID signals on SI and MI side of converter.
                       // Range: >= 1.
   parameter integer C_AXI_ADDR_WIDTH                 = 32, 
                       // Width of all ADDR signals on SI and MI side of converter.
                       // Range: 32.
   parameter         C_S_AXI_DATA_WIDTH               = 32'h00000020, 
                       // Width of S_AXI_WDATA and S_AXI_RDATA.
                       // Format: Bit32; 
                       // Range: 'h00000020, 'h00000040, 'h00000080, 'h00000100.
   parameter         C_M_AXI_DATA_WIDTH               = 32'h00000040, 
                       // Width of M_AXI_WDATA and M_AXI_RDATA.
                       // Assume greater than or equal to C_S_AXI_DATA_WIDTH.
                       // Format: Bit32;
                       // Range: 'h00000020, 'h00000040, 'h00000080, 'h00000100.
   parameter integer C_M_AXI_AW_REGISTER              = 0,
                       // Simple register AW output.
                       // Range: 0, 1
   parameter integer C_M_AXI_W_REGISTER               = 1,  // Parameter not used; W reg always implemented.
   parameter integer C_M_AXI_AR_REGISTER              = 0,
                       // Simple register AR output.
                       // Range: 0, 1
   parameter integer C_S_AXI_R_REGISTER               = 0,
                       // Simple register R output (SI).
                       // Range: 0, 1
   parameter integer C_M_AXI_R_REGISTER               = 1,
                       // Register slice on R input (MI) side.
                       // 0 = Bypass (not recommended due to combinatorial M_RVALID -> M_RREADY path)
                       // 1 = Fully-registered (needed only when upsizer propagates bursts at 1:1 width ratio)
                       // 7 = Light-weight (safe when upsizer always packs at 1:n width ratio, as in interconnect)
   parameter integer C_AXI_SUPPORTS_USER_SIGNALS      = 0,
                       // 1 = Propagate all USER signals, 0 = Dont propagate.
   parameter integer C_AXI_AWUSER_WIDTH               = 1,
                       // Width of AWUSER signals. 
                       // Range: >= 1.
   parameter integer C_AXI_ARUSER_WIDTH               = 1,
                       // Width of ARUSER signals. 
                       // Range: >= 1.
   parameter integer C_AXI_WUSER_WIDTH                = 1,
                       // Width of WUSER signals. 
                       // Range: >= 1.
   parameter integer C_AXI_RUSER_WIDTH                = 1,
                       // Width of RUSER signals. 
                       // Range: >= 1.
   parameter integer C_AXI_BUSER_WIDTH                = 1,
                       // Width of BUSER signals. 
                       // Range: >= 1.
   parameter integer C_AXI_SUPPORTS_WRITE             = 1,
   parameter integer C_AXI_SUPPORTS_READ              = 1,
   parameter integer C_PACKING_LEVEL                    = 1,
                       // 0 = Never pack (expander only); packing logic is omitted.
                       // 1 = Pack only when CACHE[1] (Modifiable) is high.
                       // 2 = Always pack, regardless of sub-size transaction or Modifiable bit.
                       //     (Required when used as helper-core by mem-con. Same size AXI interfaces
                       //      should only be used when always packing)
   parameter integer C_SUPPORT_BURSTS                 = 1,
                       // Disabled when all connected masters and slaves are AxiLite,
                       //   allowing logic to be simplified.
   parameter integer C_SINGLE_THREAD                  = 1
                       // 0 = Ignore ID when propagating transactions (assume all responses are in order).
                       // 1 = Allow multiple outstanding transactions only if the IDs are the same
                       //   to prevent response reordering.
                       //   (If ID mismatches, stall until outstanding transaction counter = 0.)
   )
  (
   // Global Signals
   input  wire                                                    ARESETN,
   input  wire                                                    ACLK,

   // Slave Interface Write Address Ports
   input  wire [C_AXI_ID_WIDTH-1:0]             S_AXI_AWID,
   input  wire [C_AXI_ADDR_WIDTH-1:0]           S_AXI_AWADDR,
   input  wire [8-1:0]                          S_AXI_AWLEN,
   input  wire [3-1:0]                          S_AXI_AWSIZE,
   input  wire [2-1:0]                          S_AXI_AWBURST,
   input  wire [2-1:0]                          S_AXI_AWLOCK,
   input  wire [4-1:0]                          S_AXI_AWCACHE,
   input  wire [3-1:0]                          S_AXI_AWPROT,
   input  wire [4-1:0]                          S_AXI_AWREGION,
   input  wire [4-1:0]                          S_AXI_AWQOS,
   input  wire [C_AXI_AWUSER_WIDTH-1:0]         S_AXI_AWUSER,
   input  wire                                  S_AXI_AWVALID,
   output wire                                  S_AXI_AWREADY,
   // Slave Interface Write Data Ports
   input  wire [C_S_AXI_DATA_WIDTH-1:0]         S_AXI_WDATA,
   input  wire [C_S_AXI_DATA_WIDTH/8-1:0]       S_AXI_WSTRB,
   input  wire                                  S_AXI_WLAST,
   input  wire [C_AXI_WUSER_WIDTH-1:0]          S_AXI_WUSER,
   input  wire                                  S_AXI_WVALID,
   output wire                                  S_AXI_WREADY,
   // Slave Interface Write Response Ports
   output wire [C_AXI_ID_WIDTH-1:0]             S_AXI_BID,
   output wire [2-1:0]                          S_AXI_BRESP,
   output wire [C_AXI_BUSER_WIDTH-1:0]          S_AXI_BUSER,
   output wire                                  S_AXI_BVALID,
   input  wire                                  S_AXI_BREADY,
   // Slave Interface Read Address Ports
   input  wire [C_AXI_ID_WIDTH-1:0]             S_AXI_ARID,
   input  wire [C_AXI_ADDR_WIDTH-1:0]           S_AXI_ARADDR,
   input  wire [8-1:0]                          S_AXI_ARLEN,
   input  wire [3-1:0]                          S_AXI_ARSIZE,
   input  wire [2-1:0]                          S_AXI_ARBURST,
   input  wire [2-1:0]                          S_AXI_ARLOCK,
   input  wire [4-1:0]                          S_AXI_ARCACHE,
   input  wire [3-1:0]                          S_AXI_ARPROT,
   input  wire [4-1:0]                          S_AXI_ARREGION,
   input  wire [4-1:0]                          S_AXI_ARQOS,
   input  wire [C_AXI_ARUSER_WIDTH-1:0]         S_AXI_ARUSER,
   input  wire                                  S_AXI_ARVALID,
   output wire                                  S_AXI_ARREADY,
   // Slave Interface Read Data Ports
   output wire [C_AXI_ID_WIDTH-1:0]             S_AXI_RID,
   output wire [C_S_AXI_DATA_WIDTH-1:0]         S_AXI_RDATA,
   output wire [2-1:0]                          S_AXI_RRESP,
   output wire                                  S_AXI_RLAST,
   output wire [C_AXI_RUSER_WIDTH-1:0]          S_AXI_RUSER,
   output wire                                  S_AXI_RVALID,
   input  wire                                  S_AXI_RREADY,

   // Master Interface Write Address Port
   output wire [C_AXI_ID_WIDTH-1:0]          M_AXI_AWID,
   output wire [C_AXI_ADDR_WIDTH-1:0]          M_AXI_AWADDR,
   output wire [8-1:0]                         M_AXI_AWLEN,
   output wire [3-1:0]                         M_AXI_AWSIZE,
   output wire [2-1:0]                         M_AXI_AWBURST,
   output wire [2-1:0]                         M_AXI_AWLOCK,
   output wire [4-1:0]                         M_AXI_AWCACHE,
   output wire [3-1:0]                         M_AXI_AWPROT,
   output wire [4-1:0]                         M_AXI_AWREGION,
   output wire [4-1:0]                         M_AXI_AWQOS,
   output wire [C_AXI_AWUSER_WIDTH-1:0]        M_AXI_AWUSER,
   output wire                                                   M_AXI_AWVALID,
   input  wire                                                   M_AXI_AWREADY,
   // Master Interface Write Data Ports
   output wire [C_M_AXI_DATA_WIDTH-1:0]    M_AXI_WDATA,
   output wire [C_M_AXI_DATA_WIDTH/8-1:0]  M_AXI_WSTRB,
   output wire                                                   M_AXI_WLAST,
   output wire [C_AXI_WUSER_WIDTH-1:0]         M_AXI_WUSER,
   output wire                                                   M_AXI_WVALID,
   input  wire                                                   M_AXI_WREADY,
   // Master Interface Write Response Ports
   input  wire [C_AXI_ID_WIDTH-1:0]          M_AXI_BID,
   input  wire [2-1:0]                         M_AXI_BRESP,
   input  wire [C_AXI_BUSER_WIDTH-1:0]         M_AXI_BUSER,
   input  wire                                                   M_AXI_BVALID,
   output wire                                                   M_AXI_BREADY,
   // Master Interface Read Address Port
   output wire [C_AXI_ID_WIDTH-1:0]          M_AXI_ARID,
   output wire [C_AXI_ADDR_WIDTH-1:0]          M_AXI_ARADDR,
   output wire [8-1:0]                         M_AXI_ARLEN,
   output wire [3-1:0]                         M_AXI_ARSIZE,
   output wire [2-1:0]                         M_AXI_ARBURST,
   output wire [2-1:0]                         M_AXI_ARLOCK,
   output wire [4-1:0]                         M_AXI_ARCACHE,
   output wire [3-1:0]                         M_AXI_ARPROT,
   output wire [4-1:0]                         M_AXI_ARREGION,
   output wire [4-1:0]                         M_AXI_ARQOS,
   output wire [C_AXI_ARUSER_WIDTH-1:0]        M_AXI_ARUSER,
   output wire                                                   M_AXI_ARVALID,
   input  wire                                                   M_AXI_ARREADY,
   // Master Interface Read Data Ports
   input  wire [C_AXI_ID_WIDTH-1:0]          M_AXI_RID,
   input  wire [C_M_AXI_DATA_WIDTH-1:0]      M_AXI_RDATA,
   input  wire [2-1:0]                       M_AXI_RRESP,
   input  wire                               M_AXI_RLAST,
   input  wire [C_AXI_RUSER_WIDTH-1:0]       M_AXI_RUSER,
   input  wire                               M_AXI_RVALID,
   output wire                               M_AXI_RREADY
   );

   
  /////////////////////////////////////////////////////////////////////////////
  // Functions
  /////////////////////////////////////////////////////////////////////////////
  
  // Log2.
  function integer log2;
    input integer value;
  begin
    for (log2=0; value>1; log2=log2+1) begin
      value = value >> 1;
    end
  end
  endfunction
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Local params
  /////////////////////////////////////////////////////////////////////////////
  
  // Log2 of number of 32bit word on SI-side.
  localparam integer C_S_AXI_BYTES_LOG                = log2(C_S_AXI_DATA_WIDTH/8);
  
  // Log2 of number of 32bit word on MI-side.
  localparam integer C_M_AXI_BYTES_LOG                = log2(C_M_AXI_DATA_WIDTH/8);
  
  // Log2 of Up-Sizing ratio for data.
  localparam integer C_RATIO                          = C_M_AXI_DATA_WIDTH / C_S_AXI_DATA_WIDTH;
  localparam integer C_RATIO_LOG                      = log2(C_RATIO);
  localparam P_BYPASS = 32'h0;
  localparam P_LIGHTWT = 32'h7;
  localparam P_FWD_REV = 32'h1;
  
  /////////////////////////////////////////////////////////////////////////////
  // Internal signals
  /////////////////////////////////////////////////////////////////////////////
  
  wire [C_AXI_ID_WIDTH-1:0]          sr_AWID      ;   
  wire [C_AXI_ADDR_WIDTH-1:0]        sr_AWADDR    ;   
  wire [8-1:0]                       sr_AWLEN     ;   
  wire [3-1:0]                       sr_AWSIZE    ;   
  wire [2-1:0]                       sr_AWBURST   ;   
  wire [2-1:0]                       sr_AWLOCK    ;   
  wire [4-1:0]                       sr_AWCACHE   ;   
  wire [3-1:0]                       sr_AWPROT    ;   
  wire [4-1:0]                       sr_AWREGION  ;   
  wire [4-1:0]                       sr_AWQOS     ;   
  wire [C_AXI_AWUSER_WIDTH-1:0]      sr_AWUSER    ;   
  wire                               sr_AWVALID   ;   
  wire                               sr_AWREADY   ;   
  wire [C_AXI_ID_WIDTH-1:0]          sr_ARID      ;    
  wire [C_AXI_ADDR_WIDTH-1:0]        sr_ARADDR    ;    
  wire [8-1:0]                       sr_ARLEN     ;    
  wire [3-1:0]                       sr_ARSIZE    ;    
  wire [2-1:0]                       sr_ARBURST   ;    
  wire [2-1:0]                       sr_ARLOCK    ;    
  wire [4-1:0]                       sr_ARCACHE   ;    
  wire [3-1:0]                       sr_ARPROT    ;    
  wire [4-1:0]                       sr_ARREGION  ;    
  wire [4-1:0]                       sr_ARQOS     ;    
  wire [C_AXI_ARUSER_WIDTH-1:0]      sr_ARUSER    ;    
  wire                               sr_ARVALID   ;    
  wire                               sr_ARREADY   ;    
  
  wire [C_S_AXI_DATA_WIDTH-1:0]      sr_WDATA     ;
  wire [(C_S_AXI_DATA_WIDTH/8)-1:0]  sr_WSTRB     ;
  wire                               sr_WLAST     ;
  wire                               sr_WVALID    ;
  wire                               sr_WREADY    ;
  
  wire [C_AXI_ID_WIDTH-1:0]          mr_RID       ;  
  wire [C_M_AXI_DATA_WIDTH-1:0]      mr_RDATA     ;  
  wire [2-1:0]                       mr_RRESP     ;  
  wire                               mr_RLAST     ;  
  wire [C_AXI_RUSER_WIDTH-1:0]       mr_RUSER     ;  
  wire                               mr_RVALID    ;  
  wire                               mr_RREADY    ;   
  reg ARESET ;
  
  assign M_AXI_WUSER   = {C_AXI_WUSER_WIDTH{1'b0}};
  assign S_AXI_RUSER   = {C_AXI_RUSER_WIDTH{1'b0}};

    ddr4_v2_2_0_axi_register_slice #
      (
        .C_FAMILY                         (C_FAMILY),
        .C_AXI_ID_WIDTH                   (C_AXI_ID_WIDTH),
        .C_AXI_ADDR_WIDTH                 (C_AXI_ADDR_WIDTH),
        .C_AXI_DATA_WIDTH                 (C_S_AXI_DATA_WIDTH),
        .C_AXI_SUPPORTS_USER_SIGNALS      (C_AXI_SUPPORTS_USER_SIGNALS),
        .C_AXI_AWUSER_WIDTH               (C_AXI_AWUSER_WIDTH),
        .C_AXI_ARUSER_WIDTH               (C_AXI_ARUSER_WIDTH),
        .C_REG_CONFIG_AW                  (C_AXI_SUPPORTS_WRITE ? P_LIGHTWT : P_BYPASS),
        .C_REG_CONFIG_AR                  (C_AXI_SUPPORTS_READ ? P_LIGHTWT : P_BYPASS)
      )
      si_register_slice_inst 
      (
        .ARESETN                          (ARESETN),
        .ACLK                             (ACLK),
        .S_AXI_AWID                       (S_AXI_AWID     ),
        .S_AXI_AWADDR                     (S_AXI_AWADDR   ),
        .S_AXI_AWLEN                      (S_AXI_AWLEN    ),
        .S_AXI_AWSIZE                     (S_AXI_AWSIZE   ),
        .S_AXI_AWBURST                    (S_AXI_AWBURST  ),
        .S_AXI_AWLOCK                     (S_AXI_AWLOCK   ),
        .S_AXI_AWCACHE                    (S_AXI_AWCACHE  ),
        .S_AXI_AWPROT                     (S_AXI_AWPROT   ),
        .S_AXI_AWREGION                   (S_AXI_AWREGION ),
        .S_AXI_AWQOS                      (S_AXI_AWQOS    ),
        .S_AXI_AWUSER                     (S_AXI_AWUSER   ),
        .S_AXI_AWVALID                    (S_AXI_AWVALID  ),
        .S_AXI_AWREADY                    (S_AXI_AWREADY  ),
        .S_AXI_WID                        ( {C_AXI_ID_WIDTH{1'b0}}),
        .S_AXI_WDATA                      ( {C_S_AXI_DATA_WIDTH{1'b0}}    ),
        .S_AXI_WSTRB                      ( {C_S_AXI_DATA_WIDTH/8{1'b0}}  ),
        .S_AXI_WLAST                      ( 1'b0 ),
        .S_AXI_WUSER                      ( 1'b0  ),
        .S_AXI_WVALID                     ( 1'b0 ),
        .S_AXI_WREADY                     ( ),
        .S_AXI_BID                        ( ),
        .S_AXI_BRESP                      ( ),
        .S_AXI_BUSER                      ( ),
        .S_AXI_BVALID                     ( ),
        .S_AXI_BREADY                     ( 1'b0 ),
        .S_AXI_ARID                       (S_AXI_ARID     ),
        .S_AXI_ARADDR                     (S_AXI_ARADDR   ),
        .S_AXI_ARLEN                      (S_AXI_ARLEN    ),
        .S_AXI_ARSIZE                     (S_AXI_ARSIZE   ),
        .S_AXI_ARBURST                    (S_AXI_ARBURST  ),
        .S_AXI_ARLOCK                     (S_AXI_ARLOCK   ),
        .S_AXI_ARCACHE                    (S_AXI_ARCACHE  ),
        .S_AXI_ARPROT                     (S_AXI_ARPROT   ),
        .S_AXI_ARREGION                   (S_AXI_ARREGION ),
        .S_AXI_ARQOS                      (S_AXI_ARQOS    ),
        .S_AXI_ARUSER                     (S_AXI_ARUSER   ),
        .S_AXI_ARVALID                    (S_AXI_ARVALID  ),
        .S_AXI_ARREADY                    (S_AXI_ARREADY  ),
        .S_AXI_RID                        ( ) ,
        .S_AXI_RDATA                      ( ) ,
        .S_AXI_RRESP                      ( ) ,
        .S_AXI_RLAST                      ( ) ,
        .S_AXI_RUSER                      ( ) ,
        .S_AXI_RVALID                     ( ) ,
        .S_AXI_RREADY                     ( 1'b0 ) ,
        .M_AXI_AWID                       (sr_AWID     ),
        .M_AXI_AWADDR                     (sr_AWADDR   ),
        .M_AXI_AWLEN                      (sr_AWLEN    ),
        .M_AXI_AWSIZE                     (sr_AWSIZE   ),
        .M_AXI_AWBURST                    (sr_AWBURST  ),
        .M_AXI_AWLOCK                     (sr_AWLOCK   ),
        .M_AXI_AWCACHE                    (sr_AWCACHE  ),
        .M_AXI_AWPROT                     (sr_AWPROT   ),
        .M_AXI_AWREGION                   (sr_AWREGION ),
        .M_AXI_AWQOS                      (sr_AWQOS    ),
        .M_AXI_AWUSER                     (sr_AWUSER   ),
        .M_AXI_AWVALID                    (sr_AWVALID  ),
        .M_AXI_AWREADY                    (sr_AWREADY  ),
        .M_AXI_WID                        () ,
        .M_AXI_WDATA                      (),
        .M_AXI_WSTRB                      (),
        .M_AXI_WLAST                      (),
        .M_AXI_WUSER                      (),
        .M_AXI_WVALID                     (),
        .M_AXI_WREADY                     (1'b0),
        .M_AXI_BID                        ( {C_AXI_ID_WIDTH{1'b0}} ) ,
        .M_AXI_BRESP                      ( 2'b0 ) ,
        .M_AXI_BUSER                      ( 1'b0 ) ,
        .M_AXI_BVALID                     ( 1'b0 ) ,
        .M_AXI_BREADY                     ( ) ,
        .M_AXI_ARID                       (sr_ARID     ),
        .M_AXI_ARADDR                     (sr_ARADDR   ),
        .M_AXI_ARLEN                      (sr_ARLEN    ),
        .M_AXI_ARSIZE                     (sr_ARSIZE   ),
        .M_AXI_ARBURST                    (sr_ARBURST  ),
        .M_AXI_ARLOCK                     (sr_ARLOCK   ),
        .M_AXI_ARCACHE                    (sr_ARCACHE  ),
        .M_AXI_ARPROT                     (sr_ARPROT   ),
        .M_AXI_ARREGION                   (sr_ARREGION ),
        .M_AXI_ARQOS                      (sr_ARQOS    ),
        .M_AXI_ARUSER                     (sr_ARUSER   ),
        .M_AXI_ARVALID                    (sr_ARVALID  ),
        .M_AXI_ARREADY                    (sr_ARREADY  ),
        .M_AXI_RID                        ( {C_AXI_ID_WIDTH{1'b0}}),
        .M_AXI_RDATA                      ( {C_S_AXI_DATA_WIDTH{1'b0}}    ),
        .M_AXI_RRESP                      ( 2'b00 ),
        .M_AXI_RLAST                      ( 1'b0  ),
        .M_AXI_RUSER                      ( 1'b0  ),
        .M_AXI_RVALID                     ( 1'b0  ),
        .M_AXI_RREADY                     (  )
      );
  
    ddr4_v2_2_0_axi_register_slice #
      (
        .C_FAMILY                         (C_FAMILY),
        .C_AXI_ID_WIDTH                   (C_AXI_ID_WIDTH),
        .C_AXI_ADDR_WIDTH                 (C_AXI_ADDR_WIDTH),
        .C_AXI_DATA_WIDTH                 (C_M_AXI_DATA_WIDTH),
        .C_AXI_SUPPORTS_USER_SIGNALS      (C_AXI_SUPPORTS_USER_SIGNALS),
        .C_AXI_RUSER_WIDTH                (C_AXI_RUSER_WIDTH),
        .C_REG_CONFIG_R                   (C_AXI_SUPPORTS_READ ? C_M_AXI_R_REGISTER : P_BYPASS)
      )
      mi_register_slice_inst 
      (
        .ARESETN                          (ARESETN),
        .ACLK                             (ACLK),
        .S_AXI_AWID                       ({C_AXI_ID_WIDTH{1'b0}}     ),
        .S_AXI_AWADDR                     ( {C_AXI_ADDR_WIDTH{1'b0}} ),
        .S_AXI_AWLEN                      ( 8'b0 ),
        .S_AXI_AWSIZE                     ( 3'b0 ),
        .S_AXI_AWBURST                    ( 2'b0 ),
        .S_AXI_AWLOCK                     ( 2'b0 ),
        .S_AXI_AWCACHE                    ( 4'b0 ),
        .S_AXI_AWPROT                     ( 3'b0 ),
        .S_AXI_AWREGION                   ( 4'b0 ),
        .S_AXI_AWQOS                      ( 4'b0 ),
        .S_AXI_AWUSER                     ( 1'b0 ),
        .S_AXI_AWVALID                    ( 1'b0 ),
        .S_AXI_AWREADY                    (     ),
        .S_AXI_WID                        ( {C_AXI_ID_WIDTH{1'b0}}),
        .S_AXI_WDATA                      ( {C_M_AXI_DATA_WIDTH{1'b0}}  ),
        .S_AXI_WSTRB                      ( {C_M_AXI_DATA_WIDTH/8{1'b0}}  ),
        .S_AXI_WLAST                      ( 1'b0 ),
        .S_AXI_WUSER                      ( 1'b0  ),
        .S_AXI_WVALID                     ( 1'b0 ),
        .S_AXI_WREADY                     ( ),
        .S_AXI_BID                        ( ),
        .S_AXI_BRESP                      ( ),
        .S_AXI_BUSER                      ( ),
        .S_AXI_BVALID                     ( ),
        .S_AXI_BREADY                     ( 1'b0 ),
        .S_AXI_ARID                       ({C_AXI_ID_WIDTH{1'b0}}     ),
        .S_AXI_ARADDR                     ( {C_AXI_ADDR_WIDTH{1'b0}} ),
        .S_AXI_ARLEN                      ( 8'b0 ),
        .S_AXI_ARSIZE                     ( 3'b0 ),
        .S_AXI_ARBURST                    ( 2'b0 ),
        .S_AXI_ARLOCK                     ( 2'b0 ),
        .S_AXI_ARCACHE                    ( 4'b0 ),
        .S_AXI_ARPROT                     ( 3'b0 ),
        .S_AXI_ARREGION                   ( 4'b0 ),
        .S_AXI_ARQOS                      ( 4'b0 ),
        .S_AXI_ARUSER                     ( 1'b0 ),
        .S_AXI_ARVALID                    ( 1'b0 ),
        .S_AXI_ARREADY                    (     ),
        .S_AXI_RID                        (mr_RID       ),
        .S_AXI_RDATA                      (mr_RDATA     ),
        .S_AXI_RRESP                      (mr_RRESP     ),
        .S_AXI_RLAST                      (mr_RLAST     ),
        .S_AXI_RUSER                      (mr_RUSER     ),
        .S_AXI_RVALID                     (mr_RVALID    ),
        .S_AXI_RREADY                     (mr_RREADY    ),
        .M_AXI_AWID                       (),
        .M_AXI_AWADDR                     (),
        .M_AXI_AWLEN                      (),
        .M_AXI_AWSIZE                     (),
        .M_AXI_AWBURST                    (),
        .M_AXI_AWLOCK                     (),
        .M_AXI_AWCACHE                    (),
        .M_AXI_AWPROT                     (),
        .M_AXI_AWREGION                   (),
        .M_AXI_AWQOS                      (),
        .M_AXI_AWUSER                     (),
        .M_AXI_AWVALID                    (),
        .M_AXI_AWREADY                    (1'b0),
        .M_AXI_WID                        () ,
        .M_AXI_WDATA                      (),
        .M_AXI_WSTRB                      (),
        .M_AXI_WLAST                      (),
        .M_AXI_WUSER                      (),
        .M_AXI_WVALID                     (),
        .M_AXI_WREADY                     (1'b0),
        .M_AXI_BID                        ( {C_AXI_ID_WIDTH{1'b0}} ) ,
        .M_AXI_BRESP                      ( 2'b0 ) ,
        .M_AXI_BUSER                      ( 1'b0 ) ,
        .M_AXI_BVALID                     ( 1'b0 ) ,
        .M_AXI_BREADY                     ( ) ,
        .M_AXI_ARID                       (),
        .M_AXI_ARADDR                     (),
        .M_AXI_ARLEN                      (),
        .M_AXI_ARSIZE                     (),
        .M_AXI_ARBURST                    (),
        .M_AXI_ARLOCK                     (),
        .M_AXI_ARCACHE                    (),
        .M_AXI_ARPROT                     (),
        .M_AXI_ARREGION                   (),
        .M_AXI_ARQOS                      (),
        .M_AXI_ARUSER                     (),
        .M_AXI_ARVALID                    (),
        .M_AXI_ARREADY                    (1'b0),
        .M_AXI_RID                        (M_AXI_RID    ),
        .M_AXI_RDATA                      (M_AXI_RDATA  ),
        .M_AXI_RRESP                      (M_AXI_RRESP  ),
        .M_AXI_RLAST                      (M_AXI_RLAST  ),
        .M_AXI_RUSER                      (M_AXI_RUSER  ),
        .M_AXI_RVALID                     (M_AXI_RVALID ),
        .M_AXI_RREADY                     (M_AXI_RREADY )
      );
  
  /////////////////////////////////////////////////////////////////////////////
  // Handle Internal Reset
  /////////////////////////////////////////////////////////////////////////////
  always @ (posedge ACLK) begin
    ARESET <= !ARESETN;
  end
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Handle Write Channels (AW/W/B)
  /////////////////////////////////////////////////////////////////////////////
  generate
    if (C_AXI_SUPPORTS_WRITE == 1) begin : USE_WRITE
    
      // Write Channel Signals for Commands Queue Interface.
      wire                              wr_cmd_valid;
      wire                              wr_cmd_fix;
      wire                              wr_cmd_modified;
      wire                              wr_cmd_complete_wrap;
      wire                              wr_cmd_packed_wrap;
      wire [C_M_AXI_BYTES_LOG-1:0]      wr_cmd_first_word;
      wire [C_M_AXI_BYTES_LOG-1:0]      wr_cmd_next_word;
      wire [C_M_AXI_BYTES_LOG-1:0]      wr_cmd_last_word;
      wire [C_M_AXI_BYTES_LOG-1:0]      wr_cmd_offset;
      wire [C_M_AXI_BYTES_LOG-1:0]      wr_cmd_mask;
      wire [C_S_AXI_BYTES_LOG:0]        wr_cmd_step;
      wire [8-1:0]                      wr_cmd_length;
      wire                              wr_cmd_ready;
      
      // Write Address Channel.
      ddr4_v2_2_0_a_upsizer #
      (
       //.C_FAMILY                    (C_FAMILY),
       .C_AXI_ID_WIDTH              (C_AXI_ID_WIDTH),
       .C_AXI_ADDR_WIDTH            (C_AXI_ADDR_WIDTH),
       .C_S_AXI_DATA_WIDTH          (C_S_AXI_DATA_WIDTH),
       .C_M_AXI_DATA_WIDTH          (C_M_AXI_DATA_WIDTH),
       .C_M_AXI_REGISTER            (C_M_AXI_AW_REGISTER),
       .C_AXI_SUPPORTS_USER_SIGNALS (C_AXI_SUPPORTS_USER_SIGNALS),
       .C_AXI_AUSER_WIDTH           (C_AXI_AWUSER_WIDTH),
       .C_AXI_CHANNEL               (0),
       .C_PACKING_LEVEL             (C_PACKING_LEVEL),
       .C_SUPPORT_BURSTS            (C_SUPPORT_BURSTS),
       .C_SINGLE_THREAD             (C_SINGLE_THREAD),
       .C_S_AXI_BYTES_LOG           (C_S_AXI_BYTES_LOG),
       .C_M_AXI_BYTES_LOG           (C_M_AXI_BYTES_LOG)
        ) write_addr_inst
       (
        // Global Signals
        .ARESET                     (ARESET),
        .ACLK                       (ACLK),
    
        // Command Interface
        .cmd_valid                  (wr_cmd_valid),
        .cmd_fix                    (wr_cmd_fix),
        .cmd_modified               (wr_cmd_modified),
        .cmd_complete_wrap          (wr_cmd_complete_wrap),
        .cmd_packed_wrap            (wr_cmd_packed_wrap),
        .cmd_first_word             (wr_cmd_first_word),
        .cmd_next_word              (wr_cmd_next_word),
        .cmd_last_word              (wr_cmd_last_word),
        .cmd_offset                 (wr_cmd_offset),
        .cmd_mask                   (wr_cmd_mask),
        .cmd_step                   (wr_cmd_step),
        .cmd_length                 (wr_cmd_length),
        .cmd_ready                  (wr_cmd_ready),
       
        // Slave Interface Write Address Ports
        .S_AXI_AID                  (sr_AWID),
        .S_AXI_AADDR                (sr_AWADDR),
        .S_AXI_ALEN                 (sr_AWLEN),
        .S_AXI_ASIZE                (sr_AWSIZE),
        .S_AXI_ABURST               (sr_AWBURST),
        .S_AXI_ALOCK                (sr_AWLOCK),
        .S_AXI_ACACHE               (sr_AWCACHE),
        .S_AXI_APROT                (sr_AWPROT),
        .S_AXI_AREGION              (sr_AWREGION),
        .S_AXI_AQOS                 (sr_AWQOS),
        .S_AXI_AUSER                (sr_AWUSER),
        .S_AXI_AVALID               (sr_AWVALID),
        .S_AXI_AREADY               (sr_AWREADY),
        
        // Master Interface Write Address Port
        .M_AXI_AID                  (M_AXI_AWID),
        .M_AXI_AADDR                (M_AXI_AWADDR),
        .M_AXI_ALEN                 (M_AXI_AWLEN),
        .M_AXI_ASIZE                (M_AXI_AWSIZE),
        .M_AXI_ABURST               (M_AXI_AWBURST),
        .M_AXI_ALOCK                (M_AXI_AWLOCK),
        .M_AXI_ACACHE               (M_AXI_AWCACHE),
        .M_AXI_APROT                (M_AXI_AWPROT),
        .M_AXI_AREGION              (M_AXI_AWREGION),
        .M_AXI_AQOS                 (M_AXI_AWQOS),
        .M_AXI_AUSER                (M_AXI_AWUSER),
        .M_AXI_AVALID               (M_AXI_AWVALID),
        .M_AXI_AREADY               (M_AXI_AWREADY)
       );
       
      // Write Data channel.
      ddr4_v2_2_0_w_upsizer #
      (
       //.C_FAMILY                    (C_FAMILY),
       .C_S_AXI_DATA_WIDTH          (C_S_AXI_DATA_WIDTH),
       .C_M_AXI_DATA_WIDTH          (C_M_AXI_DATA_WIDTH),
       .C_M_AXI_REGISTER            (1),
       .C_AXI_SUPPORTS_USER_SIGNALS (C_AXI_SUPPORTS_USER_SIGNALS),
       .C_AXI_WUSER_WIDTH           (C_AXI_WUSER_WIDTH),
       .C_PACKING_LEVEL             (C_PACKING_LEVEL),
       .C_SUPPORT_BURSTS            (C_SUPPORT_BURSTS),
       .C_S_AXI_BYTES_LOG           (C_S_AXI_BYTES_LOG),
       .C_M_AXI_BYTES_LOG           (C_M_AXI_BYTES_LOG),
       .C_RATIO                     (C_RATIO),
       .C_RATIO_LOG                 (C_RATIO_LOG)
        ) write_data_inst
       (
        // Global Signals
        .ARESET                     (ARESET),
        .ACLK                       (ACLK),
    
        // Command Interface
        .cmd_valid                  (wr_cmd_valid),
        .cmd_fix                    (wr_cmd_fix),
        .cmd_modified               (wr_cmd_modified),
        .cmd_complete_wrap          (wr_cmd_complete_wrap),
        .cmd_packed_wrap            (wr_cmd_packed_wrap),
        .cmd_first_word             (wr_cmd_first_word),
        .cmd_next_word              (wr_cmd_next_word),
        .cmd_last_word              (wr_cmd_last_word),
        .cmd_offset                 (wr_cmd_offset),
        .cmd_mask                   (wr_cmd_mask),
        .cmd_step                   (wr_cmd_step),
        .cmd_length                 (wr_cmd_length),
        .cmd_ready                  (wr_cmd_ready),
       
        // Slave Interface Write Data Ports
        .S_AXI_WDATA                (S_AXI_WDATA),
        .S_AXI_WSTRB                (S_AXI_WSTRB),
        .S_AXI_WLAST                (S_AXI_WLAST),
        .S_AXI_WUSER                (S_AXI_WUSER),
        .S_AXI_WVALID               (S_AXI_WVALID),
        .S_AXI_WREADY               (S_AXI_WREADY),
        
        // Master Interface Write Data Ports
        .M_AXI_WDATA                (M_AXI_WDATA),
        .M_AXI_WSTRB                (M_AXI_WSTRB),
        .M_AXI_WLAST                (M_AXI_WLAST),
        .M_AXI_WUSER                (),
        .M_AXI_WVALID               (M_AXI_WVALID),
        .M_AXI_WREADY               (M_AXI_WREADY)
       );
      
      // Write Response channel.
      assign S_AXI_BID     = M_AXI_BID;
      assign S_AXI_BRESP   = M_AXI_BRESP;
      assign S_AXI_BUSER   = M_AXI_BUSER;
      assign S_AXI_BVALID  = M_AXI_BVALID;
      assign M_AXI_BREADY  = S_AXI_BREADY;
       
    end else begin : NO_WRITE
      assign sr_AWREADY = 1'b0;
      assign S_AXI_WREADY  = 1'b0;
      assign S_AXI_BID     = {C_AXI_ID_WIDTH{1'b0}};
      assign S_AXI_BRESP   = 2'b0;
      assign S_AXI_BUSER   = {C_AXI_BUSER_WIDTH{1'b0}};
      assign S_AXI_BVALID  = 1'b0;
      
      assign M_AXI_AWID    = {C_AXI_ID_WIDTH{1'b0}};
      assign M_AXI_AWADDR  = {C_AXI_ADDR_WIDTH{1'b0}};
      assign M_AXI_AWLEN   = 8'b0;
      assign M_AXI_AWSIZE  = 3'b0;
      assign M_AXI_AWBURST = 2'b0;
      assign M_AXI_AWLOCK  = 2'b0;
      assign M_AXI_AWCACHE = 4'b0;
      assign M_AXI_AWPROT  = 3'b0;
      assign M_AXI_AWQOS   = 4'b0;
      assign M_AXI_AWUSER  = {C_AXI_AWUSER_WIDTH{1'b0}};
      assign M_AXI_AWVALID = 1'b0;
      assign M_AXI_WDATA   = {C_M_AXI_DATA_WIDTH{1'b0}};
      assign M_AXI_WSTRB   = {C_M_AXI_DATA_WIDTH/8{1'b0}};
      assign M_AXI_WLAST   = 1'b0;
      assign M_AXI_WVALID  = 1'b0;
      assign M_AXI_BREADY  = 1'b0;
      
    end
  endgenerate
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Handle Read Channels (AR/R)
  /////////////////////////////////////////////////////////////////////////////
  generate
    if (C_AXI_SUPPORTS_READ == 1) begin : USE_READ
    
      // Read Channel Signals for Commands Queue Interface.
      wire                              rd_cmd_valid;
      wire                              rd_cmd_fix;
      wire                              rd_cmd_modified;
      wire                              rd_cmd_complete_wrap;
      wire                              rd_cmd_packed_wrap;
      wire [C_M_AXI_BYTES_LOG-1:0]      rd_cmd_first_word;
      wire [C_M_AXI_BYTES_LOG-1:0]      rd_cmd_next_word;
      wire [C_M_AXI_BYTES_LOG-1:0]      rd_cmd_last_word;
      wire [C_M_AXI_BYTES_LOG-1:0]      rd_cmd_offset;
      wire [C_M_AXI_BYTES_LOG-1:0]      rd_cmd_mask;
      wire [C_S_AXI_BYTES_LOG:0]        rd_cmd_step;
      wire [8-1:0]                      rd_cmd_length;
      wire                              rd_cmd_ready;
      
      // Write Address Channel.
      ddr4_v2_2_0_a_upsizer #
      (
       //.C_FAMILY                    (C_FAMILY),
       .C_AXI_ID_WIDTH              (C_AXI_ID_WIDTH),
       .C_AXI_ADDR_WIDTH            (C_AXI_ADDR_WIDTH),
       .C_S_AXI_DATA_WIDTH          (C_S_AXI_DATA_WIDTH),
       .C_M_AXI_DATA_WIDTH          (C_M_AXI_DATA_WIDTH),
       .C_M_AXI_REGISTER            (C_M_AXI_AR_REGISTER),
       .C_AXI_SUPPORTS_USER_SIGNALS (C_AXI_SUPPORTS_USER_SIGNALS),
       .C_AXI_AUSER_WIDTH           (C_AXI_ARUSER_WIDTH),
       .C_AXI_CHANNEL               (1),
       .C_PACKING_LEVEL             (C_PACKING_LEVEL),
       .C_SUPPORT_BURSTS            (C_SUPPORT_BURSTS),
       .C_SINGLE_THREAD             (C_SINGLE_THREAD),
       .C_S_AXI_BYTES_LOG           (C_S_AXI_BYTES_LOG),
       .C_M_AXI_BYTES_LOG           (C_M_AXI_BYTES_LOG)
        ) read_addr_inst
       (
        // Global Signals
        .ARESET                     (ARESET),
        .ACLK                       (ACLK),
    
        // Command Interface
        .cmd_valid                  (rd_cmd_valid),
        .cmd_fix                    (rd_cmd_fix),
        .cmd_modified               (rd_cmd_modified),
        .cmd_complete_wrap          (rd_cmd_complete_wrap),
        .cmd_packed_wrap            (rd_cmd_packed_wrap),
        .cmd_first_word             (rd_cmd_first_word),
        .cmd_next_word              (rd_cmd_next_word),
        .cmd_last_word              (rd_cmd_last_word),
        .cmd_offset                 (rd_cmd_offset),
        .cmd_mask                   (rd_cmd_mask),
        .cmd_step                   (rd_cmd_step),
        .cmd_length                 (rd_cmd_length),
        .cmd_ready                  (rd_cmd_ready),
       
        // Slave Interface Write Address Ports
        .S_AXI_AID                  (sr_ARID),
        .S_AXI_AADDR                (sr_ARADDR),
        .S_AXI_ALEN                 (sr_ARLEN),
        .S_AXI_ASIZE                (sr_ARSIZE),
        .S_AXI_ABURST               (sr_ARBURST),
        .S_AXI_ALOCK                (sr_ARLOCK),
        .S_AXI_ACACHE               (sr_ARCACHE),
        .S_AXI_APROT                (sr_ARPROT),
        .S_AXI_AREGION              (sr_ARREGION),
        .S_AXI_AQOS                 (sr_ARQOS),
        .S_AXI_AUSER                (sr_ARUSER),
        .S_AXI_AVALID               (sr_ARVALID),
        .S_AXI_AREADY               (sr_ARREADY),
        
        // Master Interface Write Address Port
        .M_AXI_AID                  (M_AXI_ARID),
        .M_AXI_AADDR                (M_AXI_ARADDR),
        .M_AXI_ALEN                 (M_AXI_ARLEN),
        .M_AXI_ASIZE                (M_AXI_ARSIZE),
        .M_AXI_ABURST               (M_AXI_ARBURST),
        .M_AXI_ALOCK                (M_AXI_ARLOCK),
        .M_AXI_ACACHE               (M_AXI_ARCACHE),
        .M_AXI_APROT                (M_AXI_ARPROT),
        .M_AXI_AREGION              (M_AXI_ARREGION),
        .M_AXI_AQOS                 (M_AXI_ARQOS),
        .M_AXI_AUSER                (M_AXI_ARUSER),
        .M_AXI_AVALID               (M_AXI_ARVALID),
        .M_AXI_AREADY               (M_AXI_ARREADY)
       );
       
      // Read Data channel.
      ddr4_v2_2_0_r_upsizer #
      (
       //.C_FAMILY                    (C_FAMILY),
       .C_AXI_ID_WIDTH              (C_AXI_ID_WIDTH),
       .C_S_AXI_DATA_WIDTH          (C_S_AXI_DATA_WIDTH),
       .C_M_AXI_DATA_WIDTH          (C_M_AXI_DATA_WIDTH),
       .C_S_AXI_REGISTER            (C_S_AXI_R_REGISTER),
       .C_AXI_SUPPORTS_USER_SIGNALS (C_AXI_SUPPORTS_USER_SIGNALS),
       .C_AXI_RUSER_WIDTH           (C_AXI_RUSER_WIDTH),
       .C_PACKING_LEVEL             (C_PACKING_LEVEL),
       .C_SUPPORT_BURSTS            (C_SUPPORT_BURSTS),
       .C_S_AXI_BYTES_LOG           (C_S_AXI_BYTES_LOG),
       .C_M_AXI_BYTES_LOG           (C_M_AXI_BYTES_LOG),
       .C_RATIO                     (C_RATIO),
       .C_RATIO_LOG                 (C_RATIO_LOG)
        ) read_data_inst
       (
        // Global Signals
        .ARESET                     (ARESET),
        .ACLK                       (ACLK),
    
        // Command Interface
        .cmd_valid                  (rd_cmd_valid),
        .cmd_fix                    (rd_cmd_fix),
        .cmd_modified               (rd_cmd_modified),
        .cmd_complete_wrap          (rd_cmd_complete_wrap),
        .cmd_packed_wrap            (rd_cmd_packed_wrap),
        .cmd_first_word             (rd_cmd_first_word),
        .cmd_next_word              (rd_cmd_next_word),
        .cmd_last_word              (rd_cmd_last_word),
        .cmd_offset                 (rd_cmd_offset),
        .cmd_mask                   (rd_cmd_mask),
        .cmd_step                   (rd_cmd_step),
        .cmd_length                 (rd_cmd_length),
        .cmd_ready                  (rd_cmd_ready),
       
        // Slave Interface Read Data Ports
        .S_AXI_RID                  (S_AXI_RID),
        .S_AXI_RDATA                (S_AXI_RDATA),
        .S_AXI_RRESP                (S_AXI_RRESP),
        .S_AXI_RLAST                (S_AXI_RLAST),
        .S_AXI_RUSER                (),
        .S_AXI_RVALID               (S_AXI_RVALID),
        .S_AXI_RREADY               (S_AXI_RREADY),
        
        // Master Interface Read Data Ports
        .M_AXI_RID                  (mr_RID),
        .M_AXI_RDATA                (mr_RDATA),
        .M_AXI_RRESP                (mr_RRESP),
        .M_AXI_RLAST                (mr_RLAST),
        .M_AXI_RUSER                (mr_RUSER),
        .M_AXI_RVALID               (mr_RVALID),
        .M_AXI_RREADY               (mr_RREADY)
       );
       
    end else begin : NO_READ
      assign sr_ARREADY = 1'b0;
      assign S_AXI_RID     = {C_AXI_ID_WIDTH{1'b0}};
      assign S_AXI_RDATA   = {C_S_AXI_DATA_WIDTH{1'b0}};
      assign S_AXI_RRESP   = 2'b0;
      assign S_AXI_RLAST   = 1'b0;
      assign S_AXI_RVALID  = 1'b0;
      
      assign M_AXI_ARID    = {C_AXI_ID_WIDTH{1'b0}};
      assign M_AXI_ARADDR  = {C_AXI_ADDR_WIDTH{1'b0}};
      assign M_AXI_ARLEN   = 8'b0;
      assign M_AXI_ARSIZE  = 3'b0;
      assign M_AXI_ARBURST = 2'b0;
      assign M_AXI_ARLOCK  = 2'b0;
      assign M_AXI_ARCACHE = 4'b0;
      assign M_AXI_ARPROT  = 3'b0;
      assign M_AXI_ARQOS   = 4'b0;
      assign M_AXI_ARUSER  = {C_AXI_ARUSER_WIDTH{1'b0}};
      assign M_AXI_ARVALID = 1'b0;
      assign mr_RREADY  = 1'b0;
      
    end
  endgenerate
  
  
endmodule
`default_nettype wire

