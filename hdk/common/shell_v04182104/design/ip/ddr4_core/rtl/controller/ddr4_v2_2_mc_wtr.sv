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
//  /   /         Filename           : ddr4_v2_2_10_mc_wtr.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                   ddr4_v2_2_10_mc_wtr module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ns/100ps

module ddr4_v2_2_10_mc_wtr #(parameter
    tWTR_L = 9
   ,tWTR_S = 3
   ,LR_WIDTH = 1
   ,TCQ    = 0.1
)(
    input clk
   ,input rst

   ,output           wtr_okl
   ,output           wtr_oks
   ,output reg [1:0] prevGr
   ,output reg [LR_WIDTH-1:0] prevLR

   ,input       wrCAS
   ,input       casSlot2
   ,input [1:0] group
   ,input [LR_WIDTH-1:0] l_rank
   ,input [5:0] tCWL
);

// +5 tCK term covers rounding down and casSlot2.  -2 fabric clock covers the scheduler pipeline.
wire [6:0] tWTR_LTEMP = (tCWL + 6'd4 + tWTR_L + 6'd5) / 4;
wire [3:0] tWTR_LF    = ( ( tWTR_LTEMP - 2 ) > 0 ) ? ( tWTR_LTEMP[3:0] - 4'd2 ) : 5'd0; // spyglass disable W164a
wire [6:0] tWTR_STEMP = (tCWL + 6'd4 + tWTR_S + 6'd5) / 4;
wire [3:0] tWTR_SF    = ( ( tWTR_STEMP - 2 ) > 0 ) ? ( tWTR_STEMP[3:0] - 4'd2 ) : 5'd0; // spyglass disable W164a
// A "medium" tWTR is used in the corner case of back to back cas slot2 writes to different groups.
// This is used to cover the condition where tCCD_S+tWTR_S < tWTR_L.  This case needs to be
// covered since we only track the most recent write. To cover the case where the write previous
// to the most recent write has a tWTR_L that may not yet be safe, we pad up the tWTR_S counter.
wire [6:0] tWTR_MTEMP = (  tWTR_L > ( 6'd4 + tWTR_S ) ) ? ( (tCWL + 6'd4 + tWTR_S + 6'd5 + tWTR_L - 6'd4 - tWTR_S) / 4 ) : tWTR_STEMP;
wire [3:0] tWTR_MF    = ( ( tWTR_MTEMP - 2 ) > 0 ) ? ( tWTR_MTEMP[3:0] - 4'd2 ) : 4'd0; // spyglass disable W164a

reg [3:0] wtrl;
reg [3:0] wtrs;
reg       wtr_oklr;
reg       wtr_oksr;
reg       wrCAS_dly;
reg       casSlot2_dly;

assign wtr_okl = wtr_oklr & !wrCAS;
assign wtr_oks = wtr_oksr & !wrCAS;
wire [3:0]  tWTR_SF_selected = ( wrCAS_dly & casSlot2_dly & ~( group == prevGr ) ) ? tWTR_MF : tWTR_SF;

always @(posedge clk) if (rst) begin
   prevGr <= 2'b00;
   prevLR <= 'b0;
   wtr_oklr <= 1'b1;
   wtr_oksr <= 1'b1;
   wtrl <= 'b0;
   wtrs <= 'b0;
end else begin
   if (wtrl) wtrl <= #TCQ wtrl - 1'b1;
   if (wtrs) wtrs <= #TCQ wtrs - 1'b1;
   wtr_oklr <= #TCQ (wtrl <= 1);
   wtr_oksr <= #TCQ (wtrs <= 1);
   if (wrCAS) begin
      prevGr <= #TCQ group;
      prevLR <= #TCQ l_rank;
      wtrl <= #TCQ tWTR_LF;
      wtrs <= #TCQ tWTR_SF_selected;
      wtr_oklr <= #TCQ 1'b0;
      wtr_oksr <= #TCQ 1'b0;
   end
end

always @(posedge clk) begin
   wrCAS_dly    <= #TCQ wrCAS;
   casSlot2_dly <= #TCQ casSlot2;
end

//synopsys translate_off

`ifdef MEM_INTERNAL
// Events - When asserted high in a test that passes all verification checks, these coverage
//          properties indicate that a functional coverage event has been hit.
// ---------------------------------------------------------------------------------------------

// WTR_S can limit timing
wire   e_mc_wtr_000_wtr_s = wrCAS & ( tWTR_LF > tWTR_SF ) & ( | tWTR_SF );
always @(posedge clk) mc_wtr_000: if (~rst) cover property (e_mc_wtr_000_wtr_s);

// WTR_M corner case hit
wire   e_mc_wtr_001_wtr_m = wrCAS & wrCAS_dly & ~(group == prevGr);
always @(posedge clk) mc_wtr_001: if (~rst) cover property (e_mc_wtr_001_wtr_m);

// WTR_M corner case hit
wire   e_mc_wtr_002_wtr_m = wrCAS & wrCAS_dly & ~(group == prevGr) & ( tWTR_MF > tWTR_SF );
always @(posedge clk) mc_wtr_002: if (~rst) cover property (e_mc_wtr_002_wtr_m);


// Asserts - When asserted high, an illegal condition has been detected and the test has failed.
// ---------------------------------------------------------------------------------------------

// tWTR_L overflow
wire   a_mc_wtr_000_l = ( ( (tCWL + 6'd4 + tWTR_L + 6'd5) / 4 ) - 2 ) > 4'd15;
always @(posedge clk) if (~rst) assert property (~a_mc_wtr_000_l);

// tWTR_S overflow
wire   a_mc_wtr_001_s = ( ( (tCWL + 6'd4 + tWTR_S + 6'd5) / 4 ) - 2 ) > 4'd15;
always @(posedge clk) if (~rst) assert property (~a_mc_wtr_001_s);


`endif

//synopsys translate_on



endmodule


