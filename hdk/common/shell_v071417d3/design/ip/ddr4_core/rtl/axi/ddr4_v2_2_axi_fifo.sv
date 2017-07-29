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
//  /   /         Filename           : ddr4_v2_2_0_axi_fifo.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Apr 17 2014
//  \___\/\___\
//
//Device: UltraScale 
//Design Name: AXI Slave
//Purpose:
//    Synchronous, shallow FIFO that uses simple as a DP Memory.
//    This requires about 1/2 the resources as a Distributed RAM DPRAM 
//    implementation.
//
//    This FIFO will have the current data on the output when data is contained
//    in the FIFO.  When the FIFO is empty, the output data is invalid.
//
//Reference:
//Revision History:
//*****************************************************************************
//-----------------------------------------------
//
// MODULE:  axi_mc_fifo
//
// This is the simplest form of inferring the
// simple/SRL(16/32)CE in a Xilinx FPGA.
//
//-----------------------------------------------
`timescale 1ns / 100ps
`default_nettype none

module ddr4_v2_2_0_axi_fifo #
(
  parameter C_WIDTH  = 8,
  parameter C_AWIDTH = 4,
  parameter C_DEPTH  = 16
)
(
  input  wire               clk,       // Main System Clock  (Sync FIFO)
  input  wire               rst,       // FIFO Counter Reset (Clk
  input  wire               wr_en,     // FIFO Write Enable  (Clk)
  input  wire               rd_en,     // FIFO Read Enable   (Clk)
  input  wire [C_WIDTH-1:0] din,       // FIFO Data Input    (Clk)
  output wire [C_WIDTH-1:0] dout,      // FIFO Data Output   (Clk)
  output wire               a_full,
  output wire               full,      // FIFO FULL Status   (Clk)
  output wire               a_empty,
  output wire               empty      // FIFO EMPTY Status  (Clk)
);

///////////////////////////////////////
// FIFO Local Parameters
///////////////////////////////////////
localparam [C_AWIDTH:0] C_EMPTY = ~(0);
localparam [C_AWIDTH-1:0] C_EMPTY_PRE =  0;
localparam [C_AWIDTH-1:0] C_FULL  = C_DEPTH - 1;
localparam [C_AWIDTH-1:0] C_FULL_PRE  = C_DEPTH -2;
 
///////////////////////////////////////
// FIFO Internal Signals
///////////////////////////////////////
reg [C_WIDTH-1:0]  memory [C_DEPTH-1:0];
reg [C_AWIDTH:0] cnt_read;
reg [C_AWIDTH:0] next_cnt_read;

wire [C_AWIDTH:0] cnt_read_plus1;
wire [C_AWIDTH:0] cnt_read_minus1;
wire [C_AWIDTH-1:0] read_addr;

///////////////////////////////////////
// Main FIFO Array
///////////////////////////////////////
assign read_addr = cnt_read[C_AWIDTH-1:0];

assign dout  = memory[read_addr];

always @(posedge clk) begin : BLKSRL
integer i;
  if (wr_en) begin
    for (i = 0; i < C_DEPTH-1; i = i + 1) begin
      memory[i+1] <= memory[i];
    end
    memory[0] <= din;
  end
end

///////////////////////////////////////
// Read Index Counter
// Up/Down Counter
//  *** Notice that there is no ***
//  *** OVERRUN protection.     ***
///////////////////////////////////////
always @(posedge clk) begin
  if (rst) cnt_read <= C_EMPTY;
  else cnt_read <= next_cnt_read;
end

assign cnt_read_plus1 = cnt_read + 1'b1;
assign cnt_read_minus1 = cnt_read - 1'b1;

always @(*) begin
  next_cnt_read = cnt_read;
  if ( wr_en & !rd_en) next_cnt_read = cnt_read_plus1;
  else if (!wr_en &  rd_en) next_cnt_read = cnt_read_minus1;
end

///////////////////////////////////////
// Status Flags / Outputs
// These could be registered, but would
// increase logic in order to pre-decode
// FULL/EMPTY status.
///////////////////////////////////////
assign full  = (cnt_read == C_FULL);
assign empty = (cnt_read == C_EMPTY);
assign a_full  = (cnt_read == C_FULL_PRE);
assign a_empty = (cnt_read == C_EMPTY_PRE);

endmodule // axi_mc_fifo

`default_nettype wire

