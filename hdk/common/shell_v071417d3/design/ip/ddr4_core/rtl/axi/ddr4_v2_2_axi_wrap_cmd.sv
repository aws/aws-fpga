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
//  /   /         Filename           : ddr4_v2_2_0_axi_wrap_cmd.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Apr 17 2014
//  \___\/\___\
//
//Device: UltraScale
//Design Name: AXI Slave
//Purpose:
//
// Description: 
// MC does not support an AXI WRAP command directly.  
// To complete an AXI WRAP transaction we will issue one transaction if the
// address is wrap boundary aligned, otherwise two transactions are issued.
// The first transaction is from the starting offset to the wrap address upper
// boundary.  The second transaction is from the wrap boundary lowest address
// to the address offset. WRAP burst types will never exceed 16 beats.
//
// Calculates the number of MC beats for each axi transaction for WRAP
// burst type ( for all axsize values = C_DATA_WIDTH ):
// AR_SIZE   | AR_LEN     | OFFSET | NUM_BEATS 1 | NUM_BEATS 2
// b010(  4) | b0001(  2) |  b0000 |   2         |   0 
// b010(  4) | b0001(  2) |  b0001 |   1         |   1 
// b010(  4) | b0011(  4) |  b0000 |   4         |   0 
// b010(  4) | b0011(  4) |  b0001 |   3         |   1 
// b010(  4) | b0011(  4) |  b0010 |   2         |   2 
// b010(  4) | b0011(  4) |  b0011 |   1         |   3 
// b010(  4) | b0111(  8) |  b0000 |   8         |   0 
// b010(  4) | b0111(  8) |  b0001 |   7         |   1 
// b010(  4) | b0111(  8) |  b0010 |   6         |   2 
// b010(  4) | b0111(  8) |  b0011 |   5         |   3 
// b010(  4) | b0111(  8) |  b0100 |   4         |   4 
// b010(  4) | b0111(  8) |  b0101 |   3         |   5 
// b010(  4) | b0111(  8) |  b0110 |   2         |   6 
// b010(  4) | b0111(  8) |  b0111 |   1         |   7 
// b010(  4) | b1111( 16) |  b0000 |  16         |   0 
// b010(  4) | b1111( 16) |  b0001 |  15         |   1 
// b010(  4) | b1111( 16) |  b0010 |  14         |   2 
// b010(  4) | b1111( 16) |  b0011 |  13         |   3 
// b010(  4) | b1111( 16) |  b0100 |  12         |   4 
// b010(  4) | b1111( 16) |  b0101 |  11         |   5 
// b010(  4) | b1111( 16) |  b0110 |  10         |   6 
// b010(  4) | b1111( 16) |  b0111 |   9         |   7 
// b010(  4) | b1111( 16) |  b1000 |   8         |   8 
// b010(  4) | b1111( 16) |  b1001 |   7         |   9 
// b010(  4) | b1111( 16) |  b1010 |   6         |  10 
// b010(  4) | b1111( 16) |  b1011 |   5         |  11 
// b010(  4) | b1111( 16) |  b1100 |   4         |  12 
// b010(  4) | b1111( 16) |  b1101 |   3         |  13 
// b010(  4) | b1111( 16) |  b1110 |   2         |  14 
// b010(  4) | b1111( 16) |  b1111 |   1         |  15 
//
//Reference:
//Revision History:
//*****************************************************************************

`timescale 1ps/1ps
`default_nettype none

module ddr4_v2_2_0_axi_wrap_cmd #
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
                    // MC burst length. = 1 for BL4 or BC4, = 2 for BL8
  parameter integer C_MC_BURST_LEN              = 1,
                    // Width of AXI xDATA and MC xx_data
                    // Range: 32, 64, 128.
  parameter integer C_DATA_WIDTH                = 32,
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
  input  wire [2:0]                           axsize        , // C_AXSIZE parameter is used instead
  // axhandshake = axvalid & axready
  input  wire                                 axhandshake   , 
  output wire [C_AXI_ADDR_WIDTH-1:0]          cmd_byte_addr ,
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
localparam P_AXLEN_WIDTH = 4;
////////////////////////////////////////////////////////////////////////////////
// Wire and register declarations
////////////////////////////////////////////////////////////////////////////////
reg                         sel_first_r;
reg  [3:0]                  axlen_cnt;
reg  [3:0]                  int_addr;
reg                         int_next_pending_r;

wire                        sel_first;
wire [3:0]                  axlen_i;
wire [3:0]                  axlen_cnt_i;
wire [3:0]                  axlen_cnt_t;
wire [3:0]                  axlen_cnt_p;

wire                        addr_offset;
wire  [C_AXI_ADDR_WIDTH-1:0] axaddr_wrap;
wire [3:0]                  int_addr_t;
wire [3:0]                  int_addr_p;
wire [3:0]                  int_addr_t_inc;
wire                        int_next_pending;
wire                        extra_cmd;

////////////////////////////////////////////////////////////////////////////////
// BEGIN RTL
////////////////////////////////////////////////////////////////////////////////
assign cmd_byte_addr = axaddr_wrap;
assign axlen_i = axlen[3:0];

assign axaddr_wrap = {axaddr[C_AXI_ADDR_WIDTH-1:C_AXSIZE+4], int_addr_t[3:0], axaddr[C_AXSIZE-1:0]};

generate
  if(C_MC_BURST_LEN == 1) begin
    assign addr_offset = 1'b0;
    assign int_addr_t = axhandshake ? (axaddr[C_AXSIZE+: 4]) : int_addr;

  end else begin
    // Figuring out if the address have an offset for padding data in BL8 case
    assign addr_offset = axaddr[C_AXSIZE];

    if(C_MC_RD_INST == 0) // axhandshake & next won't occur in same cycle in Write channel 2:1 mode
      assign int_addr_t = int_addr;
    else
      assign int_addr_t = axhandshake ? (axaddr[C_AXSIZE+: 4]) : int_addr;
  end
endgenerate

assign int_addr_t_inc = int_addr_t + C_MC_BURST_LEN; // spyglass disable W164a

assign int_addr_p = ((int_addr_t & ~axlen_i) | (int_addr_t_inc & axlen_i));

always @(posedge clk) begin
  if(reset)
    int_addr <= 4'h0;
  else if (axhandshake & ~next)
    int_addr <= (axaddr[C_AXSIZE+: 4]);
  else if(next)
    int_addr <= int_addr_p;
end

// assign axlen_cnt_i = (C_MC_BURST_LEN == 1) ? axlen_i : (extra_cmd ? ((axlen_i >> 1) + 1'b1) : (axlen_i >> 1));
assign axlen_cnt_i = (C_MC_BURST_LEN == 1) ? axlen_i : (axlen_i >> 1);

assign axlen_cnt_t = axhandshake ? axlen_cnt_i : axlen_cnt;

assign axlen_cnt_p = (axlen_cnt_t - 1'b1);

always @(posedge clk) begin
  if(reset)
    axlen_cnt <= 4'hf;
  else if (axhandshake & ~next)
    axlen_cnt <= axlen_cnt_i;
  else if(next)
    axlen_cnt <= axlen_cnt_p;
end  

assign extra_cmd = addr_offset;

assign next_pending = extra_cmd ? int_next_pending_r : int_next_pending;

assign int_next_pending = |axlen_cnt_t;

always @(posedge clk) begin
  if(reset)
    int_next_pending_r <= 1'b1;
  else if(extra_cmd & next)
    int_next_pending_r <= int_next_pending;
end

// Ignore logic for first transaction        
assign ignore_begin = sel_first ? addr_offset : 1'b0;

// Ignore logic for second transaction.    
assign ignore_end = next_pending ? 1'b0 : addr_offset;

// Indicates if we are on the first transaction of a mc translation with more than 1 transaction.
assign sel_first = (axhandshake | sel_first_r);

always @(posedge clk) begin
  if (reset)
    sel_first_r <= 1'b0;
  else if(axhandshake & ~next)
    sel_first_r <= 1'b1;
  else if(next)
    sel_first_r <= 1'b0;
end

endmodule
`default_nettype wire

