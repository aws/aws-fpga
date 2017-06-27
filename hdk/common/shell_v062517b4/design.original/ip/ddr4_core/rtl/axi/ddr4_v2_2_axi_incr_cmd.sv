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
//  /   /         Filename           : ddr4_v2_2_0_axi_incr_cmd.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Apr 17 2014
//  \___\/\___\
//
//Device: UltraScale
//Design Name: AXI Slave
//Purpose:
// Description: 
// MC does not support up to 256 beats per transaction to support an AXI INCR 
// command directly.  Additionally for QOS purposes, larger transactions
// issued as many smaller transactions should improve QoS for the system.
// In the BL8 mode depending on the address offset ragged head or ragged tail
// need to be inserted into the data stream for writes and ignored for reads.
// In BL8 mode for transactions with odd length and even length transactions
// with an address offset an extra BL8 transaction will be issued. 
//
//Reference:
//Revision History:
//*****************************************************************************
`timescale 1ps/1ps
`default_nettype none

module ddr4_v2_2_0_axi_incr_cmd #
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
                    // Range: 2-4
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
localparam P_AXLEN_WIDTH = 8;
////////////////////////////////////////////////////////////////////////////////
// Wire and register declarations
////////////////////////////////////////////////////////////////////////////////
reg                         sel_first_r;
reg  [7:0]                  axlen_cnt;
reg  [C_AXI_ADDR_WIDTH-1:0] axaddr_incr;
reg                         int_next_pending_r;

wire                        sel_first;
wire                        addr_offset;
wire                        length_even;
wire [7:0]                  axlen_cnt_t;
wire [7:0]                  axlen_cnt_p;
wire [7:0]                  axlen_cnt_i;
wire [C_AXI_ADDR_WIDTH-1:0] axaddr_incr_t;
(* keep = "true" *) reg [C_AXI_ADDR_WIDTH-1:0] axaddr_incr_p;
wire [7:0]                  incr_cnt;
wire                        int_next_pending;
wire                        extra_cmd;

////////////////////////////////////////////////////////////////////////////////
// BEGIN RTL
////////////////////////////////////////////////////////////////////////////////
assign cmd_byte_addr = axaddr_incr_t;

generate
  if(C_MC_BURST_LEN == 1) begin
    assign addr_offset = 1'b0;
    assign length_even = 1'b1;
    assign axaddr_incr_t = axhandshake ? axaddr : axaddr_incr;

  end else begin
    // Figuring out if the address have an offset for padding data in BL8 case
    assign addr_offset = axaddr[C_AXSIZE];
    // The length could be odd which is an issue in BL8
    assign length_even = axlen[0];

    if(C_MC_RD_INST == 0) // axhandshake & next won't occur in same cycle in Write channel 2:1 mode
      assign axaddr_incr_t = axaddr_incr;
    else
      assign axaddr_incr_t = axhandshake ? axaddr : axaddr_incr;
  end
endgenerate

always @(*) begin
  axaddr_incr_p = axaddr_incr_t + (incr_cnt * C_MC_BURST_LEN); // spyglass disable W164a
end

always @(posedge clk) begin
  if(reset)
    axaddr_incr <= {C_AXI_ADDR_WIDTH{1'b0}};
  else if (axhandshake & ~next)
    axaddr_incr <= axaddr;
  else if(next)
    axaddr_incr <= axaddr_incr_p;
end

// figuring out how much to much to incr based on AXSIZE
assign incr_cnt = (C_AXSIZE == 2) ? 8'd4 : (C_AXSIZE == 3) ? 8'd8 :
       (C_AXSIZE == 4)? 8'd16 :(C_AXSIZE == 5) ? 8'd32 : 
       (C_AXSIZE == 6) ? 8'd64 :  (C_AXSIZE == 7) ? 8'd128 :8'd0;

// assign axlen_cnt_i = (C_MC_BURST_LEN == 1) ? axlen : (extra_cmd ? ((axlen >> 1) + 1'b1) : (axlen >> 1));
assign axlen_cnt_i = (C_MC_BURST_LEN == 1) ? axlen : (axlen >> 1);

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

assign extra_cmd = addr_offset & length_even;

assign next_pending = extra_cmd ? int_next_pending_r : int_next_pending;

assign int_next_pending = |axlen_cnt_t;

always @(posedge clk) begin
  if(reset)
    int_next_pending_r <= 1'b1;
  else if(extra_cmd & next)
    int_next_pending_r <= int_next_pending;
end

// last and ignore signals to data channel. These signals are used for
// BL8 to ignore and insert data for even len transactions with offset
// and odd len transactions
// For odd len transactions with no offset the last read is ignored and
// last write is masked
// For odd len transactions with offset the first read is ignored and
// first write is masked
// For even len transactions with offset the last & first read is ignored and
// last& first  write is masked
// For even len transactions no ingnores or masks. 

// Ignore logic for first transaction        
assign ignore_begin = sel_first ? addr_offset : 1'b0;

// Ignore logic for second transaction.    
assign ignore_end = next_pending ? 1'b0 : ~(length_even ^ addr_offset);

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

