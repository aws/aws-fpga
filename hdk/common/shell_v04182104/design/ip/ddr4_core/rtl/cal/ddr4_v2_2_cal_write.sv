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
//  /   /         Filename           : ddr4_v2_2_10_cal_write.sv
// /___/   /\     Date Last Modified : $Date: 2015/04/23 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                   ddr4_v2_2_10_cal_write module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ns/100ps

module ddr4_v2_2_10_cal_write # (parameter
   DBAW = 5
   ,DBYTES = 4
   ,MEM = "DDR4"
   ,RANKS = 1
   ,DM_DBI = "DM_NODBI"
   ,WL     = 9
   ,EARLY_WR_DATA = "OFF"
   ,EXTRA_CMD_DELAY  = 0
   ,ECC           = "OFF"
   ,TCQ        = 0.1
)(
    input clk
   ,input rst

   ,output    [DBYTES*4-1:0] mc_clb2phy_wrcs0_upp
   ,output    [DBYTES*4-1:0] mc_clb2phy_wrcs1_upp
   ,output    [DBYTES*4-1:0] mc_clb2phy_wrcs0_low
   ,output    [DBYTES*4-1:0] mc_clb2phy_wrcs1_low
   ,output    [DBYTES*4-1:0] mc_clb2phy_t_b_upp
   ,output    [DBYTES*4-1:0] mc_clb2phy_t_b_low
   ,output   [DBYTES*8-1:0] mcal_DMOut_n
   ,output [DBYTES*8*8-1:0] mcal_DQOut
   ,output            [7:0] mcal_DQSOut
   ,output       [DBAW-1:0] wrDataAddr
   ,output                  wrDataEn

   ,input            [1:0] casSlot
   ,input                  mccasSlot2
   ,input       [DBAW-1:0] winBuf
   ,input            [1:0] winRank
   ,input            [1:0] calRank
   ,input            [1:0] mcwinRank
   ,input                  wrCAS
   ,input                  calwrCAS
   ,input                  mcwrCAS
   ,input [DBYTES*8*8-1:0] DQOut
   ,input   [DBYTES*8-1:0] DMOut
   ,input      [DBYTES-1:0] cal_oe_dis_low // spyglass disable W498
   ,input      [DBYTES-1:0] cal_oe_dis_upp // spyglass disable W498
   ,input                  calDone
);

function [7:0] csoe;
   input [7:0] cur;
   input [1:0] sel;
   input       val;
   input       b;

if (val) case (sel)
   2'b00: csoe = { {8{b}}          };
   2'b01: csoe = { {7{b}}, cur[  4]};
   2'b10: csoe = { {6{b}}, cur[5:4]};
   2'b11: csoe = { {5{b}}, cur[6:4]};
endcase else csoe = { cur[7:4], cur[7:0] } >> 4;

endfunction


function [7:0] tboe;
   input [7:0] cur;
   input [1:0] sel;
   input       val;
   input       b;

if (val) case (sel)
   2'b00: tboe = { 3'b0, {5{b}}          };
   2'b01: tboe = { 2'b0, {5{b}}, cur[  4]};
   2'b10: tboe = { 1'b0, {5{b}}, cur[5:4]};
   2'b11: tboe = {       {5{b}}, cur[6:4]};
endcase else tboe = cur[7:0] >> 4;

endfunction

// This module implements a WRQ_MSB+1 lenght shift register called wrQ that times the generation
// of write path output enables (t_b), rank (wrcs), write buffer address (wrDataAddr and wrDataEn),
// and write data (mcal_DQOut).  The shift register operates in the fabric clock domain.
localparam WRQ_MSB = 13;

// The overall timing is set by local parameter ALL_WR_LATENCY which includes write latency WL
// (tCWL and additive latency) and any extra command path delay.  This timing value is in DRAM
// command clocks (tCK).  EXTRA_CMD_DELAY is needed in the following cases:
// EXTRA_CMD_DELAY     Case
// 1                   Single rank config with WL < 8 and fabric clock > 1/2 of max
// 1                   Multi rank config with WL < 12
// 2                   Multi rank config with WL < 8
localparam ALL_WR_LATENCY = WL + 4*EXTRA_CMD_DELAY;

// The total write latency calculated above is translated into a fabric cycle and tCK offset
// used in pushing new write CAS commands into the wrQ shift register.  These values are
// calculated for both casslot0 and casslot2.
localparam FABRIC_CASSLOT0 = (   ALL_WR_LATENCY       / 4 ) - 2;
localparam FABRIC_CASSLOT2 = ( ( ALL_WR_LATENCY + 2 ) / 4 ) - 2;
localparam OFFSET_CASSLOT0 =   ( ALL_WR_LATENCY     ) % 4;
localparam OFFSET_CASSLOT2 =   ( ALL_WR_LATENCY + 2 ) % 4;

integer i;

reg      [7:0] cs0;
reg      [7:0] cs1;
reg            wrDataVal;
reg      [7:0] oe_low;
reg      [7:0] oe_upp;
reg [DBAW+4:0] wrQ[0:WRQ_MSB]; // bit 0 wrCAS, 2:1 slot 4:3 rank, rest adr
reg [DBAW+4:0] wrQ_nxt[0:WRQ_MSB];
reg [DBAW+4:0] wrQ_out[0:WRQ_MSB];
reg           cal_oe_dis_low_dly;
reg           cal_oe_dis_upp_dly;


generate
if (RANKS == 1) begin
   assign mc_clb2phy_wrcs0_low = 4'b0;
   assign mc_clb2phy_wrcs0_upp = 4'b0;
   assign mc_clb2phy_wrcs1_low = 4'b0;
   assign mc_clb2phy_wrcs1_upp = 4'b0;
end else begin
   assign mc_clb2phy_wrcs0_low = {DBYTES{cs0[3:0]}};
   assign mc_clb2phy_wrcs0_upp = {DBYTES{cs0[3:0]}};
   assign mc_clb2phy_wrcs1_low = {DBYTES{cs1[3:0]}};
   assign mc_clb2phy_wrcs1_upp = {DBYTES{cs1[3:0]}};
end
endgenerate

// Output enable shift register fabric load cycle for cal and mc.  mccasSlot2 is timing critical.
reg  [3:0] oe_0_mux_cal;
wire [3:0] oe_0_mux_cal_nxt = calDone    ? FABRIC_CASSLOT0 : FABRIC_CASSLOT2;
wire [3:0] oe_fabric        = mccasSlot2 ? FABRIC_CASSLOT2 : oe_0_mux_cal;

// tCK offset for mc.  mccasSlot2 is timing critical.
wire [1:0] tck_offset = mccasSlot2 ? OFFSET_CASSLOT2 : OFFSET_CASSLOT0;

// Output enable shift register load value for cal and mc.  mcwrCAS and tck_offset are timing critical.
wire [DBAW+4:0] wrQ_cal_load_value = {winBuf,   calRank, OFFSET_CASSLOT2[1:0], 1'b1};
wire [DBAW+4:0] wrQ_mc_load_value  = {winBuf, mcwinRank,           tck_offset, 1'b1};

// Qualify calwrCAS with calDone to make sure it does not interrupt normal operation
wire wrQ_cal_load = calwrCAS & ~calDone;

always @(*) begin
                                      wrQ_nxt[WRQ_MSB]   = '0;
  for (i = 0; i < WRQ_MSB; i = i + 1) wrQ_nxt[i]         = wrQ[i + 1];
                    if (wrQ_cal_load) wrQ_nxt[oe_fabric] = wrQ_cal_load_value;
                    if (     mcwrCAS) wrQ_nxt[oe_fabric] = wrQ_mc_load_value;
end

assign mc_clb2phy_t_b_low = {DBYTES{oe_low[3:0]}};
assign mc_clb2phy_t_b_upp = {DBYTES{oe_upp[3:0]}};
always @(*) begin
  for (i = 0; i <=WRQ_MSB; i = i + 1) wrQ_out[i]        = ( ALL_WR_LATENCY > 7 ) ? wrQ[i] : wrQ_nxt[i];
end
assign wrDataAddr        = ( ECC == "ON" & ALL_WR_LATENCY >= 12 ) ? wrQ[1][DBAW+4:5] : ( ( ( EARLY_WR_DATA == "ON" ) | ( ALL_WR_LATENCY <= 7 ) ) ? wrQ_nxt[0][DBAW+4:5] : wrQ[0][DBAW+4:5] );
assign wrDataEn          = ( ( ECC == "ON" & ALL_WR_LATENCY >= 12 ) & calDone ) ? wrQ_out[1][0] : wrQ_out[0][0];
wire   wrDataEn_internal = wrQ_out[0][0];

always @(posedge clk) if (rst) begin
   cs0 <= 'b0;
   cs1 <= 'b0;
   oe_low <= 'b0;
   oe_upp <= 'b0;
   wrDataVal <= 1'b0;
   for (i = 0; i <= WRQ_MSB; i = i + 1) wrQ[i] <= 'b0;
end else begin
   wrDataVal <= #TCQ wrDataEn_internal;
   for (i = 0; i <= WRQ_MSB; i = i + 1) wrQ[i] <= #TCQ wrQ_nxt[i];
   if (calDone) begin
      oe_low <= #TCQ tboe(oe_low, wrQ_out[0][2:1], wrQ_out[0][0], 1'b1);
      oe_upp <= #TCQ tboe(oe_upp, wrQ_out[0][2:1], wrQ_out[0][0], 1'b1);
      cs0 <= #TCQ csoe(cs0, wrQ_out[1][2:1], wrQ_out[1][0], wrQ_out[1][3]);
      cs1 <= #TCQ csoe(cs1, wrQ_out[1][2:1], wrQ_out[1][0], wrQ_out[1][4]);
   end else begin
      oe_low <= #TCQ   tboe(oe_low, wrQ_out[0][2:1], wrQ_out[0][0], 1'b1)
                     & {8{~cal_oe_dis_low_dly}};
      oe_upp <= #TCQ   tboe(oe_upp, wrQ_out[0][2:1], wrQ_out[0][0], 1'b1)
                     & {8{~cal_oe_dis_upp_dly}};
      cs0 <= #TCQ {8{calRank[0]}};
      cs1 <= #TCQ {8{calRank[1]}};
   end
end

genvar bNum;
generate
   for (bNum = 0; bNum < DBYTES; bNum++) begin:genByte
      ddr4_v2_2_10_cal_wr_byte # (
        .TCQ   (TCQ)
        )
        u_ddr_mc_wr_byte (
          .clk (clk)
         ,.rst (rst)

         ,.mcal_DMOut_n (mcal_DMOut_n[bNum*8+:8])
         ,.mcal_DQOut   (mcal_DQOut[bNum*64+:64])

         ,.DQOut     (DQOut[bNum*64+:64])
         ,.DMOut     (DMOut[bNum*8+:8])
         ,.wrDataVal (wrDataVal)
         ,.wrOffset  (wrQ_out[0][2:1])
      );
   end
endgenerate

assign mcal_DQSOut = 8'b01010101;

// General purpose flops
always @(posedge clk) begin
 oe_0_mux_cal <= #TCQ oe_0_mux_cal_nxt;
 cal_oe_dis_low_dly <= #TCQ cal_oe_dis_low[0];
 cal_oe_dis_upp_dly <= #TCQ cal_oe_dis_upp[0];
end

//synopsys translate_off

`ifdef MEM_INTERNAL

// Asserts - When asserted high, an illegal condition has been detected and the test has failed.
// ---------------------------------------------------------------------------------------------

// Check ALL_WR_LATENCY greater than 63
wire a_mc_write_000_ovf = ALL_WR_LATENCY > 63;
always @(posedge clk) if (~rst) assert property (~a_mc_write_000_ovf);

`endif
//synopsys translate_on

endmodule


