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
//  /   /         Filename           : ddr4_v2_2_0_axi_cmd_translator.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Apr 17 2014
//  \___\/\___\
//
//Device: UltraScale
//Design Name: AXI Slave
//Purpose:
// INCR and WRAP burst modes are decoded in parallel and then the output is
// chosen based on the AxBURST value.  FIXED burst mode is not supported and
// is mapped to the INCR command instead.  
//Reference:
//Revision History:
//*****************************************************************************
`timescale 1ps/1ps
`default_nettype none

module ddr4_v2_2_0_axi_cmd_translator #
(
///////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
///////////////////////////////////////////////////////////////////////////////
                    // Width of AxADDR
                    // Range: 32.
  parameter integer C_AXI_ADDR_WIDTH            = 32, 
                    // Width of cmd_byte_addr
                    // Range: 30
  parameter integer C_MC_ADDR_WIDTH             = 30,
                    // Width of AXI xDATA and MC xx_data
                    // Range: 32, 64, 128.
  parameter integer C_DATA_WIDTH                = 32,
                     // MC burst length. = 1 for BL4 or BC4, = 2 for BL8
  parameter integer C_MC_BURST_LEN              = 1,
                      // DRAM clock to AXI clock ratio
                    // supported values 2, 4
  parameter integer C_MC_nCK_PER_CLK             = 2, 
                    // Static value of axsize
                    // Range: 2-5
  parameter integer C_AXSIZE                    = 2,
                    // Instance for Read channel or write channel
  parameter integer C_MC_RD_INST                = 0
)
(
///////////////////////////////////////////////////////////////////////////////
// Port Declarations     
///////////////////////////////////////////////////////////////////////////////
  input  wire                                 clk           , 
  input  wire                                 reset         , 
  input  wire [C_AXI_ADDR_WIDTH-1:0]          axaddr        , 
  input  wire [7:0]                           axlen         , 
  input  wire [2:0]                           axsize        , 
  input  wire [1:0]                           axburst       , 
  input  wire                                 axvalid       , 
  input  wire                                 axready       , 
  output wire [C_MC_ADDR_WIDTH-1:0]           cmd_byte_addr , 
  output wire                                 ignore_begin  ,
  output wire                                 ignore_end    ,

  // Connections to/from fsm module
  // signal to increment to the next mc transaction 
  input  wire                                 next          , 
  // signal to the fsm there is another transaction required
  output wire                                 next_pending


);

////////////////////////////////////////////////////////////////////////////////
// Local parameters
////////////////////////////////////////////////////////////////////////////////
localparam P_MC_BURST_MASK = {C_MC_ADDR_WIDTH{1'b1}} ^ 
                             {C_MC_BURST_LEN+(C_MC_nCK_PER_CLK/2){1'b1}};
////////////////////////////////////////////////////////////////////////////////
// Wires/Reg declarations
////////////////////////////////////////////////////////////////////////////////
wire [C_AXI_ADDR_WIDTH-1:0]     cmd_byte_addr_i;

wire [C_AXI_ADDR_WIDTH-1:0]     axi_mc_incr_cmd_byte_addr;
wire                            incr_next_pending;
wire [C_AXI_ADDR_WIDTH-1:0]     axi_mc_wrap_cmd_byte_addr;
wire                            wrap_next_pending;
wire                            incr_ignore_begin;
wire                            incr_ignore_end;
wire                            wrap_ignore_begin;
wire                            wrap_ignore_end;  
wire                            axhandshake;
wire                            incr_axhandshake;
wire                            wrap_axhandshake;
wire                            incr_next;
wire                            wrap_next;
wire 	[C_AXI_ADDR_WIDTH-1:0]  cmd_byte_addr_4to1;
wire 	[C_AXI_ADDR_WIDTH-1:0]  cmd_byte_addr_2to1;

////////////////////////////////////////////////////////////////////////////////
// BEGIN RTL
////////////////////////////////////////////////////////////////////////////////

assign axhandshake = axvalid & axready;

// INCR and WRAP translations are calcuated in independently, select the one
// for our transactions
// right shift by the UI width to the DRAM width ratio 
 
assign cmd_byte_addr    = (C_MC_nCK_PER_CLK == 4) ?
                          cmd_byte_addr_4to1[C_MC_ADDR_WIDTH -1:0] : 
                          cmd_byte_addr_2to1[C_MC_ADDR_WIDTH -1:0] ;

assign cmd_byte_addr_4to1 = (cmd_byte_addr_i >> C_AXSIZE-3) & P_MC_BURST_MASK ; // spyglass disable W164a
assign cmd_byte_addr_2to1 = (cmd_byte_addr_i >> C_AXSIZE-2) & P_MC_BURST_MASK ;


assign cmd_byte_addr_i  = (axburst[1]) ? axi_mc_wrap_cmd_byte_addr : axi_mc_incr_cmd_byte_addr;

assign ignore_begin     = (axburst[1]) ? wrap_ignore_begin : incr_ignore_begin;

assign ignore_end       = (axburst[1]) ? wrap_ignore_end : incr_ignore_end;

assign next_pending     = (axburst[1]) ? wrap_next_pending : incr_next_pending;

assign incr_axhandshake = (axburst[1]) ? 1'b0 : axhandshake;

assign wrap_axhandshake = (axburst[1]) ? axhandshake : 1'b0;

assign incr_next        = (axburst[1]) ? 1'b0 : next;

assign wrap_next        = (axburst[1]) ? next : 1'b0;

ddr4_v2_2_0_axi_incr_cmd #
(
  .C_AXI_ADDR_WIDTH  (C_AXI_ADDR_WIDTH),
  .C_MC_ADDR_WIDTH  (C_MC_ADDR_WIDTH),
  .C_DATA_WIDTH     (C_DATA_WIDTH),
  .C_MC_BURST_LEN   (C_MC_BURST_LEN),
  .C_AXSIZE         (C_AXSIZE),
  .C_MC_RD_INST     (C_MC_RD_INST)
)
axi_mc_incr_cmd_0
(
  .clk           ( clk                ) ,
  .reset         ( reset              ) ,
  .axaddr        ( axaddr             ) ,
  .axlen         ( axlen              ) ,
  .axsize        ( axsize             ) ,
  .axhandshake   ( incr_axhandshake   ) ,
  .cmd_byte_addr ( axi_mc_incr_cmd_byte_addr ) ,
  .ignore_begin  ( incr_ignore_begin  ) ,
  .ignore_end    ( incr_ignore_end    ) ,
  .next          ( incr_next          ) ,
  .next_pending  ( incr_next_pending  ) 
);

ddr4_v2_2_0_axi_wrap_cmd #
(
  .C_AXI_ADDR_WIDTH (C_AXI_ADDR_WIDTH),
  .C_MC_ADDR_WIDTH  (C_MC_ADDR_WIDTH),
  .C_MC_BURST_LEN   (C_MC_BURST_LEN),
  .C_DATA_WIDTH     (C_DATA_WIDTH),
  .C_AXSIZE         (C_AXSIZE),
  .C_MC_RD_INST     (C_MC_RD_INST)
)
axi_mc_wrap_cmd_0
(
  .clk           ( clk                ) ,
  .reset         ( reset              ) ,
  .axaddr        ( axaddr             ) ,
  .axlen         ( axlen              ) ,
  .axsize        ( axsize             ) ,
  .axhandshake   ( wrap_axhandshake   ) ,
  .ignore_begin  ( wrap_ignore_begin  ) ,
  .ignore_end    ( wrap_ignore_end    ) ,
  .cmd_byte_addr ( axi_mc_wrap_cmd_byte_addr ) ,
  .next          ( wrap_next          ) ,
  .next_pending  ( wrap_next_pending  ) 
);

endmodule
`default_nettype wire

