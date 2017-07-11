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
//  /   /         Filename           : ddr4_v2_2_0_cal_rd_en.sv
// /___/   /\     Date Last Modified : $Date: 2015/04/23 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                   ddr4_v2_2_0_cal_rd_en module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ns/100ps

module ddr4_v2_2_0_cal_rd_en #(parameter
    RANKS = 1
   ,RL  = 11
   ,EXTRA_CMD_DELAY  = 0
   ,TCQ = 0.1
)(
    input clk
   ,input rst

   ,output [3:0] mc_clb2phy_rden
   ,output [3:0] mc_clb2phy_rdcs0
   ,output [3:0] mc_clb2phy_rdcs1

   ,input [1:0] casSlot       // spyglass disable W498
   ,input       mccasSlot2
   ,input       rdCAS
   ,input       calrdCAS
   ,input       mcrdCAS
   ,input [5:0] mCL0
   ,input [5:0] mCL1
   ,input [5:0] mCL2
   ,input [5:0] mCL3
   ,input [1:0] winRank
   ,input [1:0] calRank
   ,input [1:0] mcwinRank
   ,input       calDone
);

wire [5:0] mCL[0:3];
assign mCL[0] = mCL0;
assign mCL[1] = mCL1;
assign mCL[2] = mCL2;
assign mCL[3] = mCL3;

// This section generates the Gate enable mc_clb2phy_rden.
// This logic is used in calibration and during normal operation.
// Case 4'b0110 defines nominal timing where the trained mCL value equals RL.
// This logic supports mCL = RL - 3, to enable the Gate 3tCK earlier than nominal RL.
// Early gate enable is needed in Gate training, during normal operation
// if command delays are very low, and to compensate for extra Gate delay
// in the XiPhy that is allocated for VT tracking.  The logic also supports Gate
// enable 4tCK later than nominal to allow for command fly-by routing.
// The Gate enable can be further delayed to allow for extra command pipeline delays.
// The Gate enable supports RL as low as 7 with no extra command delays, but other
// blocks have higher low limits, so the minimum RL without extra command delays
// is expected to be RL=8.

reg                      [RL+12 + 4*EXTRA_CMD_DELAY :0] rdEn;
(* KEEP = "true" *) reg  [RL+12 + 4*EXTRA_CMD_DELAY :0] rdEn_nxt;
reg                      [18:0]                        rsMask[0:7];

function [18:0] rs2mask;
   input [3:0] diff;
   input       slot2;
case ({diff, slot2})
   5'b0_0000: rs2mask = 19'b000_0000_0000_0000_1111;
   5'b0_0001: rs2mask = 19'b000_0000_0000_0011_1100;
   5'b0_0010: rs2mask = 19'b000_0000_0000_0001_1110;
   5'b0_0011: rs2mask = 19'b000_0000_0000_0111_1000;
   5'b0_0100: rs2mask = 19'b000_0000_0000_0011_1100;
   5'b0_0101: rs2mask = 19'b000_0000_0000_1111_0000;
   5'b0_0110: rs2mask = 19'b000_0000_0000_0111_1000;
   5'b0_0111: rs2mask = 19'b000_0000_0001_1110_0000;
   5'b0_1000: rs2mask = 19'b000_0000_0000_1111_0000;
   5'b0_1001: rs2mask = 19'b000_0000_0011_1100_0000;
   5'b0_1010: rs2mask = 19'b000_0000_0001_1110_0000;
   5'b0_1011: rs2mask = 19'b000_0000_0111_1000_0000;
   5'b0_1100: rs2mask = 19'b000_0000_0011_1100_0000;
   5'b0_1101: rs2mask = 19'b000_0000_1111_0000_0000;
   5'b0_1110: rs2mask = 19'b000_0000_0111_1000_0000;
   5'b0_1111: rs2mask = 19'b000_0001_1110_0000_0000;
   5'b1_0000: rs2mask = 19'b000_0000_1111_0000_0000;
   5'b1_0001: rs2mask = 19'b000_0011_1100_0000_0000;
   5'b1_0010: rs2mask = 19'b000_0001_1110_0000_0000;
   5'b1_0011: rs2mask = 19'b000_0111_1000_0000_0000;
   5'b1_0100: rs2mask = 19'b000_0011_1100_0000_0000;
   5'b1_0101: rs2mask = 19'b000_1111_0000_0000_0000;
   5'b1_0110: rs2mask = 19'b000_0111_1000_0000_0000;
   5'b1_0111: rs2mask = 19'b001_1110_0000_0000_0000;
   5'b1_1000: rs2mask = 19'b000_1111_0000_0000_0000;
   5'b1_1001: rs2mask = 19'b011_1100_0000_0000_0000;
   5'b1_1010: rs2mask = 19'b001_1110_0000_0000_0000;
   5'b1_1011: rs2mask = 19'b111_1000_0000_0000_0000;
     default: rs2mask = 19'b000_0000_1000_0000_1111;
endcase
endfunction

always @(posedge clk) begin: blk1
   reg [3:0] rsNdx;
   for (rsNdx = 0; rsNdx <= 7; rsNdx = rsNdx + 1)
      rsMask[rsNdx] <= #TCQ rs2mask(mCL[rsNdx[2:1]] - (RL - 3), rsNdx[0]);
end

always @(*) if (rst) begin
   rdEn_nxt = 'b0;
end else begin
   rdEn_nxt =   (rdEn >> 4)
                | (rdCAS ? {rsMask[{winRank, casSlot[1]}], { (RL-6 + 4*EXTRA_CMD_DELAY) {1'b0}}}
                : 'b0);
end

always @(posedge clk)
   rdEn <= #TCQ rdEn_nxt;

assign mc_clb2phy_rden = rdEn[3:0];

///////////////////////////////////////////////////////////////////
// This logic is used during normal, multi-rank operation only. Durring cal or single
// rank operation this logic is bypassed and the output of this section is static.
// This section generates the read rank signals used by the XiPhy to select per rank
// cal values during read operations.

integer tck_index;
localparam rdcs_msb = RL + 8 + 4*EXTRA_CMD_DELAY;

reg  [rdcs_msb :0] rdcs0;
reg  [rdcs_msb :0] rdcs0_mc;
reg  [rdcs_msb :0] rdcs1;
reg  [rdcs_msb :0] rdcs1_mc;
reg  [6:0]           rdcs_rdcas_lsb_slot0;
reg                  calDone_dly;

// Extend newest cs (MSB) and shift out the oldest (low 4 LSBs)
wire [rdcs_msb :0] rdcs0_shift  = { { 4 { rdcs0[rdcs_msb] } }, rdcs0[ rdcs_msb : 4] };
wire [rdcs_msb :0] rdcs1_shift  = { { 4 { rdcs1[rdcs_msb] } }, rdcs1[ rdcs_msb : 4] };

// Create rdcs mask for the current rdcas
wire [6:0]         rdcs_rdcas_lsb_slot0_nxt  = { 1'b0, mCL0 } + 4*EXTRA_CMD_DELAY - 7'd7;
wire [rdcs_msb :0] rdcs_rdcas_mask_slot0     = { ( rdcs_msb + 1 ) { 1'b1 } } << rdcs_rdcas_lsb_slot0;
wire [rdcs_msb :0] rdcs_rdcas_mask           = rdcs_rdcas_mask_slot0 << 2*mccasSlot2;

// Merge the shifted rdcs and winRank based on the rdcs mask for the current rdcas
always @(*) begin
   for (tck_index = 0; tck_index <= rdcs_msb; tck_index = tck_index + 1) begin
     rdcs0_mc[tck_index] = ( mcrdCAS & rdcs_rdcas_mask[tck_index] ) ? mcwinRank[0] : rdcs0_shift[tck_index];
     rdcs1_mc[tck_index] = ( mcrdCAS & rdcs_rdcas_mask[tck_index] ) ? mcwinRank[1] : rdcs1_shift[tck_index];
   end
end

// Select mc or cal rdcs
wire [rdcs_msb :0] rdcs0_nxt = calDone_dly ? rdcs0_mc : { rdcs_msb+1 { calRank[0] } };
wire [rdcs_msb :0] rdcs1_nxt = calDone_dly ? rdcs1_mc : { rdcs_msb+1 { calRank[1] } };

// Final 4 bit rdcs output
assign mc_clb2phy_rdcs0 = rdcs0[3:0] & ~{ 4 { RANKS == 1 } };
assign mc_clb2phy_rdcs1 = rdcs1[3:0] & ~{ 4 { RANKS == 1 } };

// Flops
always @(posedge clk) begin
  rdcs_rdcas_lsb_slot0 <= #TCQ rdcs_rdcas_lsb_slot0_nxt;
  calDone_dly          <= #TCQ calDone;
end

// Reset flops
always @(posedge clk) if (rst) begin
  rdcs0 <= #TCQ '0;
  rdcs1 <= #TCQ '0;
end else begin
  rdcs0 <= #TCQ rdcs0_nxt;
  rdcs1 <= #TCQ rdcs1_nxt;
end


//synopsys translate_off

`ifdef MEM_INTERNAL
// Events - When asserted high in a test that passes all verification checks, these coverage
//          properties indicate that a functional coverage event has been hit.
// ---------------------------------------------------------------------------------------------

// Minimum mCL in normal operation
//wire   e_mc_rd_en_000 = ( ( mCL0 + 4*EXTRA_CMD_DELAY ) == 13 ) & calDone & ~( RANKS == 1 ) & rdCAS;
//always @(posedge clk) mc_rd_en_000: if (~rst) cover property (e_mc_rd_en_000);


// Asserts - When asserted high, an illegal condition has been detected and the test has failed.
// ---------------------------------------------------------------------------------------------

// Check for illegal rank switch in rdEn and rdcs.  rdEn gap must be at least 2tCK wide.  rdcs must be stable for 2tCK after rdEn de-assertion.
reg                      [RL+12 + 4*EXTRA_CMD_DELAY :0] a_rdEn;
reg                      [rdcs_msb :0]                 a_rdcs0_dly;
reg                      [rdcs_msb :0]                 a_rdcs1_dly;
reg                      [RL+12 + 4*EXTRA_CMD_DELAY :0] a_rdcs0;
wire                     [RL+12 + 4*EXTRA_CMD_DELAY :0] a_rdcs0_nxt = { rdcs0, a_rdcs0_dly[3:0] };
reg                      [RL+12 + 4*EXTRA_CMD_DELAY :0] a_rdcs1;
wire                     [RL+12 + 4*EXTRA_CMD_DELAY :0] a_rdcs1_nxt = { rdcs1, a_rdcs1_dly[3:0] };
wire                     [RL+12 + 4*EXTRA_CMD_DELAY -1 :0] a_rdEn_falling_edge = ~a_rdEn[RL+12 + 4*EXTRA_CMD_DELAY :1] & a_rdEn[RL+12 + 4*EXTRA_CMD_DELAY -1 :0];
reg                      [RL+12 + 4*EXTRA_CMD_DELAY -3 :0] a_rdEn_hold0_fail;
reg                      [RL+12 + 4*EXTRA_CMD_DELAY -3 :0] a_rdEn_hold1_fail;
reg                      [RL+12 + 4*EXTRA_CMD_DELAY -3 :0] a_rdEn_gap_fail;
always @(*) begin
   for (tck_index = 0; tck_index < RL+12 + 4*EXTRA_CMD_DELAY -2; tck_index = tck_index + 1) begin
     a_rdEn_hold0_fail[tck_index] = calDone & a_rdEn_falling_edge[tck_index] & ( ( a_rdcs0[tck_index] ^ a_rdcs0[tck_index+1] ) | ( a_rdcs0[tck_index] ^ a_rdcs0[tck_index+2] ) );
     a_rdEn_hold1_fail[tck_index] = calDone & a_rdEn_falling_edge[tck_index] & ( ( a_rdcs1[tck_index] ^ a_rdcs1[tck_index+1] ) | ( a_rdcs1[tck_index] ^ a_rdcs1[tck_index+2] ) );
     a_rdEn_gap_fail[tck_index]   = calDone & a_rdEn_falling_edge[tck_index] & a_rdEn[tck_index+2];
   end
end
always @(posedge clk) if (rst) begin
         a_rdEn      <= #TCQ '0;
         a_rdcs0_dly <= #TCQ '0;
         a_rdcs1_dly <= #TCQ '0;
         a_rdcs0     <= #TCQ '0;
         a_rdcs1     <= #TCQ '0;
end else begin
         a_rdEn      <= #TCQ rdEn;
         a_rdcs0_dly <= #TCQ rdcs0;
         a_rdcs1_dly <= #TCQ rdcs1;
         a_rdcs0     <= #TCQ a_rdcs0_nxt;
         a_rdcs1     <= #TCQ a_rdcs1_nxt;
end

// rdcs0 not held for 2tCK after end of burst
wire a_mc_rd_en_000_hld = calDone & ( | a_rdEn_hold0_fail ) & ( mCL0 > 6'b0 );
always @(posedge clk) if (~rst) assert property (~a_mc_rd_en_000_hld);

// rdcs1 not held for 2tCK after end of burst
wire a_mc_rd_en_001_hld = calDone & ( | a_rdEn_hold1_fail ) & ( mCL0 > 6'b0 );
always @(posedge clk) if (~rst) assert property (~a_mc_rd_en_001_hld);

// rdEn not held low for 2tCK after end of burst
wire a_mc_rd_en_002_hld = calDone & ( | a_rdEn_gap_fail ) & ( mCL0 > 6'b0 );
always @(posedge clk) if (~rst) assert property (~a_mc_rd_en_002_hld);

// mCL0 is less than RL-3
wire a_mc_rd_en_003_ovf = ( mCL0 < (RL - 3) ) & ( mCL0 > 6'b0 );
always @(posedge clk) if (~rst) assert property (~a_mc_rd_en_003_ovf);

// mCL1 is less than RL-3
wire a_mc_rd_en_004_ovf = ( mCL1 < (RL - 3) ) & ( mCL1 > 6'b0 );
always @(posedge clk) if (~rst) assert property (~a_mc_rd_en_004_ovf);

// mCL2 is less than RL-3
wire a_mc_rd_en_005_ovf = ( mCL2 < (RL - 3) ) & ( mCL2 > 6'b0 );
always @(posedge clk) if (~rst) assert property (~a_mc_rd_en_005_ovf);

// mCL3 is less than RL-3
wire a_mc_rd_en_006_ovf = ( mCL3 < (RL - 3) ) & ( mCL3 > 6'b0 );
always @(posedge clk) if (~rst) assert property (~a_mc_rd_en_006_ovf);


`endif
//synopsys translate_on

endmodule


