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
//  /   /         Filename           : ddr4_v2_2_0_axi_aw_channel.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Apr 17 2014
//  \___\/\___\
//
//Device: UltraScale
//Design Name: AXI Slave
//Purpose:
//Reference:
//Revision History:
//*****************************************************************************

`timescale 1ps/1ps
`default_nettype none

module ddr4_v2_2_0_axi_aw_channel #
(
///////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
///////////////////////////////////////////////////////////////////////////////
                    // Width of ID signals.
                    // Range: >= 1.
  parameter integer C_ID_WIDTH          = 4, 
                    // Width of AxADDR
                    // Range: 32.
  parameter integer C_AXI_ADDR_WIDTH    = 32, 
                    // Width of cmd_byte_addr
                    // Range: 30
  parameter integer C_MC_ADDR_WIDTH    = 30,
                    // Width of AXI xDATA and MC xx_data
                    // Range: 32, 64, 128.
  parameter integer C_DATA_WIDTH        = 32,
                    // MC burst length. = 1 for BL4 or BC4, = 2 for BL8
  parameter integer C_MC_BURST_LEN              = 1,
                    // DRAM clock to AXI clock ratio
                    // supported values 2, 4
  parameter integer C_MC_nCK_PER_CLK             = 2, 
                    // Static value of axsize
                    // Range: 2-4
  parameter integer C_AXSIZE            = 2,
  parameter         C_ECC               = "OFF"
)
(
///////////////////////////////////////////////////////////////////////////////
// Port Declarations     
///////////////////////////////////////////////////////////////////////////////
  // AXI Slave Interface
  // Slave Interface System Signals           
  input  wire                                 clk             , 
  input  wire                                 reset           , 

  // Slave Interface Write Address Ports
  input  wire [C_ID_WIDTH-1:0]                awid            , 
  input  wire [C_AXI_ADDR_WIDTH-1:0]          awaddr          , 
  input  wire [7:0]                           awlen           , 
  input  wire [2:0]                           awsize          , 
  input  wire [1:0]                           awburst         , 
  input  wire [1:0]                           awlock          , 
  input  wire [3:0]                           awcache         , 
  input  wire [2:0]                           awprot          , 
  input  wire [3:0]                           awqos           , 
  input  wire                                 awvalid         , 
  output wire                                 awready         , 

  // MC Master Interface
  //CMD PORT
  output wire                                 cmd_en           , 
  output wire                                 cmd_en_last      ,
  output wire [2:0]                           cmd_instr        , 
  output wire [C_MC_ADDR_WIDTH-1:0]           cmd_byte_addr    , 
  input  wire                                 cmd_full         ,

  // Connections to/from axi_mc_w_channel module
  input  wire                                 w_data_rdy       ,
  input  wire                                 cmd_wr_bytes     ,
  output wire                                 w_cmd_rdy        ,
  output wire                                 w_ignore_begin   ,
  output wire                                 w_ignore_end     ,
  output wire                                 awvalid_int      ,
  output wire [3:0]                           awqos_int        ,
     

  // Connections to/from axi_mc_b_channel module
  output wire                                 b_push           , 
  output wire [C_ID_WIDTH-1:0]                b_awid           ,
  input  wire                                 b_full       

);

////////////////////////////////////////////////////////////////////////////////
// Local parameters
////////////////////////////////////////////////////////////////////////////////
localparam                          P_CMD_WRITE                = 3'b000;
localparam                          P_CMD_READ                 = 3'b001;
localparam                          P_CMD_WRITE_BYTES          = 3'b011;

////////////////////////////////////////////////////////////////////////////////
// Wires/Reg declarations
////////////////////////////////////////////////////////////////////////////////
wire                        next         ;
wire                        next_pending ;

reg  [C_ID_WIDTH-1:0]       axid         ;
reg  [C_AXI_ADDR_WIDTH-1:0] axaddr       ;
reg  [7:0]                  axlen        ;
reg  [3:0]                  axqos        ;
reg  [1:0]                  axburst      ;
reg                         axvalid      ;

wire [C_ID_WIDTH-1:0]       axid_int     ;
wire [C_AXI_ADDR_WIDTH-1:0] axaddr_int   ;
wire [7:0]                  axlen_int    ;
wire [3:0]                  axqos_int    ;
wire [1:0]                  axburst_int  ;
wire                        axvalid_int  ;

////////////////////////////////////////////////////////////////////////////////
// BEGIN RTL
////////////////////////////////////////////////////////////////////////////////
assign awvalid_int = axvalid_int;
assign awqos_int = axqos_int;

assign axid_int    = awready ? awid : axid;
assign axlen_int   = awready ? awlen : axlen;
assign axqos_int   = awready ? awqos : axqos;
assign axaddr_int  = awready ? awaddr : axaddr;
assign axburst_int = awready ? awburst : axburst;
assign axvalid_int = awready ? awvalid : axvalid;

always @(posedge clk) begin
  if(reset)
    axvalid <= 1'b0;
  else
    axvalid <= axvalid_int;
end

always @(posedge clk) begin
  axid <= axid_int;
  axlen <= axlen_int;
  axqos <= axqos_int;
  axaddr <= axaddr_int;
  axburst <= axburst_int;
end

// Translate the AXI transaction to the MC transaction(s)
ddr4_v2_2_0_axi_cmd_translator #
(
  .C_AXI_ADDR_WIDTH ( C_AXI_ADDR_WIDTH ) ,
  .C_MC_ADDR_WIDTH  ( C_MC_ADDR_WIDTH  ) ,
  .C_DATA_WIDTH     ( C_DATA_WIDTH     ) ,
  .C_MC_BURST_LEN   ( C_MC_BURST_LEN   ) ,
  .C_MC_nCK_PER_CLK ( C_MC_nCK_PER_CLK ) ,
  .C_AXSIZE         ( C_AXSIZE         ) ,
  .C_MC_RD_INST     ( 0                )
)
axi_mc_cmd_translator_0
(
  .clk           ( clk                   ) ,
  .reset         ( reset                 ) ,
  .axaddr        ( axaddr_int            ) ,
  .axlen         ( axlen_int             ) ,
  .axsize        ( awsize                ) , // This is a constant, need not be sampled. Fed the direct input to aviod timing violations.
  .axburst       ( axburst_int           ) ,
  .axvalid       ( axvalid_int           ) ,
  .axready       ( awready               ) ,
  .cmd_byte_addr ( cmd_byte_addr         ) ,
  .ignore_begin  ( w_ignore_begin        ) ,
  .ignore_end    ( w_ignore_end          ) ,
  .next          ( next                  ) ,
  .next_pending  ( next_pending          ) 
);

ddr4_v2_2_0_axi_wr_cmd_fsm #
(
 .C_MC_BURST_LEN   (C_MC_BURST_LEN   ),
 .C_MC_RD_INST     (0                )
)
aw_cmd_fsm_0
(
  .clk          ( clk            ) ,
  .reset        ( reset          ) ,
  .axready      ( awready        ) ,
  .axvalid      ( axvalid_int    ) ,
  .cmd_en       ( cmd_en         ) ,
  .cmd_full     ( cmd_full       ) ,
  .next         ( next           ) ,
  .next_pending ( next_pending   ) ,
  .data_rdy     ( w_data_rdy     ) ,
  .b_push       ( b_push         ) ,
  .b_full       ( b_full         ) ,
  .cmd_en_last  ( cmd_en_last    )
);

// assign cmd_instr = (C_ECC == "ON") ? P_CMD_WRITE_BYTES : P_CMD_WRITE;
assign cmd_instr = ((C_ECC == "ON") & cmd_wr_bytes) ? P_CMD_WRITE_BYTES : P_CMD_WRITE;

assign b_awid = axid_int;

assign w_cmd_rdy = next;

endmodule

`default_nettype wire

