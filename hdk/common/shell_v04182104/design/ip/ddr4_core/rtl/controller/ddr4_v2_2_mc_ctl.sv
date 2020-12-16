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
//  /   /         Filename           : ddr4_v2_2_10_mc_ctl.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                   ddr4_v2_2_10_mc_ctl module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ns/100ps

module ddr4_v2_2_10_mc_ctl #(parameter
    RANKS = 1			   
   ,RANK_SLOT = 1
   ,RKBITS = 2
   ,RANK_SLAB = 4
   ,ABITS = 18
   ,BABITS = 2
   ,BGBITS = 2
   ,S_HEIGHT = 1
   ,LR_WIDTH = 1
   ,CKEBITS = 4
   ,COLBITS = 10
   ,CSBITS = 4
   ,ODTBITS = 4
   ,tCCD_3ds = 4         // read to read and write to write, to different group, at speed great than 1866 requires 5 nCK
   ,MR6      = 13'b0_1000_0000_0000
   ,MEM = "DDR4"
   ,NOP_ADD_LOW = 1'b1
   ,tCK         = 938
   ,CLAMSHELL = "OFF"
   ,REG_CTRL  = "OFF"

   ,ODTWR = 16'h8421
   ,ODTWRDEL = 5'd9
   ,ODTWRDUR = 4'd6
   ,ODTWRODEL = 5'd9
   ,ODTWRODUR = 4'd6

   ,ODTRD = 16'h0000
   ,ODTRDDEL = 5'd9
   ,ODTRDDUR = 4'd6
   ,ODTRDODEL = 5'd9
   ,ODTRDODUR = 4'd6

   ,ODTNOP = 4'b0000
   ,TCQ        = 0.1   
)(
    input clk
   ,input rst

   ,output reg           [7:0] mc_ACT_n
   ,output reg           [7:0] mc_CAS_n
   ,output reg           [7:0] mc_RAS_n
   ,output reg           [7:0] mc_WE_n
   ,output reg   [ABITS*8-1:0] mc_ADR
   ,output reg  [BABITS*8-1:0] mc_BA
   ,output reg  [BGBITS*8-1:0] mc_BG
   ,output reg [LR_WIDTH*8-1:0]mc_C
   ,output reg [CKEBITS*8-1:0] mc_CKE
   ,output reg  [CSBITS*8-1:0] mc_CS_n
   ,output     [ODTBITS*8-1:0] mc_ODT

   ,output reg        casSlot2
   ,output reg        tranSentC
   ,output reg        prevCmdAP

   ,input         [1:0] winBankAT
   ,input         [1:0] win_bank_cas
   ,input         [1:0] winBankPT
   ,input         [1:0] winGroupAT
   ,input         [1:0] win_group_cas
   ,input         [1:0] winGroupPT
   ,input               winAP
   ,input [COLBITS-1:0] winCol
   ,input               winAct
   ,input         [3:0] winPortC
   ,input         [3:0] winPortP
   ,input  [RKBITS-1:0] winRankA
   ,input  [RKBITS-1:0] win_rank_cas
   ,input  [RKBITS-1:0] winRankP
   ,input [LR_WIDTH-1:0] winLRankAT
   ,input [LR_WIDTH-1:0] win_l_rank_cas
   ,input [LR_WIDTH-1:0] winLRankPT
   ,input               winRead
   ,input   [ABITS-1:0] winRowA
   ,input               winWrite

   ,input               preIss
   ,input               refIss
   ,input               zqIss
   ,input               zqIssAll
   ,input  [RKBITS-1:0] refRank
   ,input [LR_WIDTH-1:0] refLRank
   ,input               per_cas_block_req

   ,input  int_sreIss
   ,input [RANKS-1:0] int_sreCkeDis
   ,input int_srxIss
);


// Parameter used to enforce 8 tCK spacing for rank switching
// for DDR speeds greater than 1866.
localparam LONG_RANK_SWITCH = ( tCK < 1070 ) & ( RANKS > 1 );

localparam 
    MRS = 3'b000
   ,REF = 3'b001
   ,PRE = 3'b010
   ,ACT = 3'b011
   ,WR  = 3'b100
   ,RD  = 3'b101
   ,ZQC = 3'b110
   ,NOP = 3'b111
;

localparam   tCCD_L   = ( MR6[12:10] <= 3'd2 ) ? 6 :
                        ( MR6[12:10] == 3'd3 ) ? 7 : 8;

wire [BABITS-1:0] winBankA;
wire [BABITS-1:0] winBankC;
wire [BABITS-1:0] winBankP;
wire [BGBITS-1:0] winGroupA;
wire [BGBITS-1:0] winGroupC;
wire [BGBITS-1:0] winGroupP;
wire [LR_WIDTH-1:0] winLRankA;
wire [LR_WIDTH-1:0] winLRankC;
wire [LR_WIDTH-1:0] winLRankP;

generate
   if (MEM == "DDR3") begin
      assign winBankA = {winGroupAT[0], winBankAT};
      assign winBankC =     {win_group_cas[0], win_bank_cas};
      assign winBankP = {winGroupPT[0], winBankPT};
      assign winGroupA = 'bx;
      assign winGroupC     = '0;
      assign winGroupP = 'bx;
      assign winLRankA = 'bx;
      assign winLRankC = 'bx;
      assign winLRankP = 'bx;
   end else begin
      if (BGBITS == 2) begin
         assign winBankA = winBankAT;
         assign winBankC     = win_bank_cas;
         assign winBankP = winBankPT;
         assign winGroupA = winGroupAT;
         assign winGroupC     = win_group_cas;
         assign winGroupP = winGroupPT;
         assign winLRankA = winLRankAT;
         assign winLRankC = win_l_rank_cas;
         assign winLRankP = winLRankPT;
      end else begin
         assign winBankA = winBankAT;
         assign winBankC     = win_bank_cas;
         assign winBankP = winBankPT;
         assign winGroupA = winGroupAT[0];
         assign winGroupC     = win_group_cas[0];
         assign winGroupP = winGroupPT[0];
         assign winLRankA = 'bx;
         assign winLRankC = 'bx;
         assign winLRankP = 'bx;
      end
   end
endgenerate

integer i;
integer bn;
integer rank_index;


reg [7:0] mc_ADRR[0:ABITS-1];
reg [7:0] mc_BAR[0:BABITS-1];
reg [7:0] mc_BGR[0:BGBITS-1];
reg [7:0] mc_CR[0:LR_WIDTH-1];
reg [7:0] mc_CKER[0:CKEBITS-1];
reg [7:0] mc_CS_nR[0:CSBITS-1];

always @(*) begin
   for (i = 0; i < ABITS; i++) mc_ADR[i*8+:8] = mc_ADRR[i];
   for (i = 0; i < BABITS; i++) mc_BA[i*8+:8] = mc_BAR[i];
   for (i = 0; i < BGBITS; i++) mc_BG[i*8+:8] = mc_BGR[i];
   for (i = 0; i < LR_WIDTH; i++) mc_C[i*8+:8] = mc_CR[i];
   for (i = 0; i < CKEBITS; i++) mc_CKE[i*8+:8] = mc_CKER[i];
   for (i = 0; i < CSBITS; i++) mc_CS_n[i*8+:8] = mc_CS_nR[i];
end

reg [7:0] d_mc_ACT_n;
reg [7:0] d_mc_RAS_n;
reg [7:0] d_mc_CAS_n;
reg [7:0] d_mc_WE_n;
reg [7:0] d_mc_ADRR[0:17];
reg [7:0] d_mc_BAR[0:BABITS-1];
reg [7:0] d_mc_BGR[0:BGBITS-1];
reg [7:0] d_mc_CR[0:LR_WIDTH-1];
reg [7:0] d_mc_CS_nR[0:CSBITS-1];
reg [7:0] d_mc_CKER[0:CKEBITS-1];

/*
always @(posedge clk) if (rst) begin
   mc_ACT_n <= 8'b11111111;
   mc_RAS_n <= 8'b11111111;
   mc_CAS_n <= 8'b11111111;
   mc_WE_n <= 8'b11111111;
   for (i = 0; i < CKEBITS; i++) mc_CKER[i] <= 8'b11111111;
   for (i = 0; i < CSBITS; i++) mc_CS_nR[i] <= 8'b11111111;
end else begin
   mc_ACT_n <= #TCQ d_mc_ACT_n;
   mc_RAS_n <= #TCQ d_mc_RAS_n;
   mc_CAS_n <= #TCQ d_mc_CAS_n;
   mc_WE_n <= #TCQ d_mc_WE_n;
   for (i = 0; i < ABITS; i++) mc_ADRR[i] <= #TCQ d_mc_ADRR[i];
   for (i = 0; i < BABITS; i++) mc_BAR[i] <= #TCQ d_mc_BAR[i];
   for (i = 0; i < BGBITS; i++) mc_BGR[i] <= #TCQ d_mc_BGR[i];
   for (i = 0; i < CKEBITS; i++) mc_CKER[i] <= #TCQ 8'b11111111;
   for (i = 0; i < CSBITS; i++) mc_CS_nR[i] <= #TCQ d_mc_CS_nR[i];
end
*/

always @(*) begin
   mc_ACT_n = d_mc_ACT_n;
   mc_RAS_n = d_mc_RAS_n;
   mc_CAS_n = d_mc_CAS_n;
   mc_WE_n = d_mc_WE_n;
   for (i = 0; i < ABITS; i++) mc_ADRR[i] = d_mc_ADRR[i];
   for (i = 0; i < BABITS; i++) mc_BAR[i] = d_mc_BAR[i];
   for (i = 0; i < BGBITS; i++) mc_BGR[i] = d_mc_BGR[i];
   for (i = 0; i < LR_WIDTH; i++) mc_CR[i] = d_mc_CR[i];
   for (i = 0; i < CKEBITS; i++) mc_CKER[i] = d_mc_CKER[i];
   for (i = 0; i < CSBITS; i++) begin
     if (CLAMSHELL == "ON") begin
       mc_CS_nR[i] = d_mc_CS_nR[i/2];
     end else begin
       mc_CS_nR[i] = d_mc_CS_nR[i];
     end
   end
end

reg       d_prevCAS;
reg [RKBITS-1:0] d_prevRank;
reg [BGBITS-1:0] d_prevGroup;
reg [LR_WIDTH-1:0] d_prevLRank;
reg       d_prevSlot2;
reg       d_prevCmdAP;

reg       prevCAS;
reg       prev2CAS;
reg [RKBITS-1:0] prevRank;
reg [BGBITS-1:0] prevGroup;
reg [LR_WIDTH-1:0] prevLRank;
reg       prevSlot2;

always @(posedge clk) if (rst) begin
   prevCAS <= #TCQ 1'b0;
   prev2CAS <= #TCQ 1'b0;
   prevRank <= #TCQ {RKBITS{1'b0}};
   prevGroup <= #TCQ '0;
   prevLRank <= #TCQ '0;
   prevSlot2 <= #TCQ 1'b0;
   prevCmdAP <= #TCQ 1'b0;
end else begin
   prevCAS <= #TCQ d_prevCAS;
   prev2CAS <= #TCQ prevCAS;
   prevRank <= #TCQ  d_prevRank;
   prevGroup <= #TCQ d_prevGroup;
   prevLRank <= #TCQ d_prevLRank;
   prevSlot2 <= #TCQ d_prevSlot2;
   prevCmdAP <= #TCQ d_prevCmdAP;
end

localparam RRI = ((RANK_SLOT == 4) && (REG_CTRL == "ON")) ? 0 : 1 ;  // Refresh Rank Index
localparam RR  = ((RANK_SLOT == 4) && (REG_CTRL == "ON")) ? 2 : 4 ;   // Refresf Rank to be compared
generate
always @(*) begin : blk
   reg [16:14] op;

   d_mc_ACT_n = 8'b11111111;
   d_mc_RAS_n = 8'b11111111;
   d_mc_CAS_n = 8'b11111111;
   d_mc_WE_n = 8'b11111111;
   d_prevCAS = 1'b0;
   d_prevRank = prevRank;
   d_prevGroup = prevGroup;
   d_prevLRank = prevLRank;
   d_prevSlot2 = prevSlot2;
   d_prevCmdAP = prevCmdAP;
   d_mc_ADRR[17]  = NOP_ADD_LOW ? '0 : 8'b11111111;
   for (i = 14; i < 17; i++)     d_mc_ADRR[i]  = 8'b11111111;
   for (i =  0; i < 14; i++)     d_mc_ADRR[i]  = NOP_ADD_LOW ? '0 : 8'b11111111;
   for (i =  0; i < BABITS; i++) d_mc_BAR[i]   = NOP_ADD_LOW ? '0 : 8'b11111111;
   for (i =  0; i < BGBITS; i++) d_mc_BGR[i]   = NOP_ADD_LOW ? '0 : 8'b11111111;
   for (i =  0; i < LR_WIDTH; i++) d_mc_CR[i]  = NOP_ADD_LOW ? '0 : 8'b11111111;
   //for (i = 0; i < CKEBITS; i++) d_mc_CKER[i]  = int_sreIss && (refRank == i) ? 8'b00111111 : // Change for SRE, only works for single rank
   for (i = 0; i < CKEBITS; i++) d_mc_CKER[i]  = int_sreIss && (refRank[RRI:0] == (i%RR)) ? 8'b00111111 :
	                                         int_sreCkeDis[i] ? 8'b00000000 : 
	                                         int_srxIss       ? 8'b11000000 :
  	                                                            8'b11111111; 
   for (i =  0; i < CSBITS; i++) d_mc_CS_nR[i] = 8'b11111111;

   casez ({winRead, winWrite})
      2'b01, 2'b10: begin
         d_prevRank = win_rank_cas;
         d_prevGroup = winGroupC;
         d_prevLRank = winLRankC;
         if (tranSentC) begin // spyglass disable STARC-2.7.1.3a     // else statement not needed due to defaults above
            op = winRead ? RD : WR;
            for (bn = 0; bn < ABITS; bn = bn + 1) d_mc_ADRR[bn] = 8'b0;
            for (bn = 0; bn < COLBITS; bn++) begin
               if      ( bn <=  9 ) d_mc_ADRR[bn]  [(casSlot2*4)+:2] = {2{winCol[bn]}}; // Column bits A9 to A0
               else if ( bn == 10 ) d_mc_ADRR[bn+1][(casSlot2*4)+:2] = {2{winCol[bn]}}; // Column bit A11
               else                 d_mc_ADRR[bn+2][(casSlot2*4)+:2] = {2{winCol[bn]}}; // Column bit A13
            end
            d_mc_ADRR[10][(casSlot2*4)+:2] = {2{winAP}};
            if (MEM == "DDR4") begin
               d_mc_ADRR[14] = 8'b11111111;
               d_mc_ADRR[15] = 8'b11111111;
               d_mc_ADRR[16] = 8'b11111111;
               d_mc_ADRR[14][(casSlot2*4)+:2] = {2{op[14]}};
               d_mc_ADRR[15][(casSlot2*4)+:2] = {2{op[15]}};
               d_mc_ADRR[16][(casSlot2*4)+:2] = {2{op[16]}};
            end
            d_mc_RAS_n[(casSlot2*4)+:2] = {2{op[16]}};
            d_mc_CAS_n[(casSlot2*4)+:2] = {2{op[15]}};
            d_mc_WE_n[(casSlot2*4)+:2] = {2{op[14]}};
            for (bn = 0; bn < BABITS; bn++) d_mc_BAR[bn][(casSlot2*4)+:2] = {2{winBankC[bn]}};
            for (bn = 0; bn < BGBITS; bn++) d_mc_BGR[bn][(casSlot2*4)+:2] = {2{winGroupC[bn]}};
            for (bn = 0; bn < LR_WIDTH; bn++) d_mc_CR[bn][(casSlot2*4)+:2] = {2{winLRankC[bn]}};
            d_mc_CS_nR[win_rank_cas] = casSlot2 ? {2'b11, 2'b00, 4'b1111}
                                                : {6'b111111, 2'b00};
            d_prevCAS = 1'b1;
            d_prevSlot2 = casSlot2;
            d_prevCmdAP = winAP;
         end
      end
      default:  // default covers case 2'b00.  case 2'b11 will never happen.
         casez (1'b1)
         preIss: begin
            op = PRE;
            for (bn = 0; bn < ABITS; bn++) d_mc_ADRR[bn][7:6] = {2{1'b1}};
            if (MEM == "DDR4") begin
               d_mc_ADRR[14][7:6] = {2{op[14]}};
               d_mc_ADRR[15][7:6] = {2{op[15]}};
               d_mc_ADRR[16][7:6] = {2{op[16]}};
            end
            d_mc_RAS_n[7:6] = {2{op[16]}};
            d_mc_CAS_n[7:6] = {2{op[15]}};
            d_mc_WE_n[7:6] = {2{op[14]}};
            for (bn = 0; bn < BABITS; bn++) d_mc_BAR[bn][7:6] = 2'b00;
            for (bn = 0; bn < BGBITS; bn++) d_mc_BGR[bn][7:6] = 2'b00;
            for (bn = 0; bn < LR_WIDTH; bn++) d_mc_CR[bn][7:6] = {2{refLRank[bn]}};
            d_mc_CS_nR[refRank][7:6] = 2'b00;
         end
         refIss,int_sreIss: begin
            op = REF;
            if (MEM == "DDR4") begin
              d_mc_ADRR[14][7:6] = {2{op[14]}};
              d_mc_ADRR[15][7:6] = {2{op[15]}};
              d_mc_ADRR[16][7:6] = {2{op[16]}};
            end
            d_mc_RAS_n[7:6] = {2{op[16]}};
            d_mc_CAS_n[7:6] = {2{op[15]}};
            d_mc_WE_n[7:6] = {2{op[14]}};
            for (bn = 0; bn < LR_WIDTH; bn++) d_mc_CR[bn][7:6] = {2{refLRank[bn]}};
	    if (!int_srxIss) begin // No CS activity for SRX
	      if (int_sreIss) begin
                for (i =  0; i < CSBITS; i++) begin
	          if (refRank[RRI:0] == (i%RR))
	            d_mc_CS_nR[i][7:6] = 2'b00;
                end
	      end else begin
	        d_mc_CS_nR[refRank][7:6] = 2'b00;
	      end
	    end
         end
         zqIss: begin
            op = ZQC;
            if (MEM == "DDR4") begin
              d_mc_ADRR[14][7:6] = {2{op[14]}};
              d_mc_ADRR[15][7:6] = {2{op[15]}};
              d_mc_ADRR[16][7:6] = {2{op[16]}};
            end
            d_mc_ADRR[10][7:6] = 2'b0;
            d_mc_RAS_n[7:6] = {2{op[16]}};
            d_mc_CAS_n[7:6] = {2{op[15]}};
            d_mc_WE_n[7:6] = {2{op[14]}};
            for (bn = 0; bn < LR_WIDTH; bn++) d_mc_CR[bn][7:6] = {2{refLRank[bn]}};
            for (rank_index = 0; rank_index < CSBITS; rank_index++) d_mc_CS_nR[rank_index][7:6] = ~{ 2 { zqIssAll } };
            d_mc_CS_nR[refRank][7:6] = 2'b00;
         end
      endcase
   endcase
   if (winAct) begin
      op = ACT;
      for (bn = 0; bn < ABITS; bn++) d_mc_ADRR[bn][3:2] = {2{winRowA[bn]}};
      for (bn = 0; bn < BABITS; bn++) d_mc_BAR[bn][3:2] = {2{winBankA[bn]}};
      for (bn = 0; bn < BGBITS; bn++) d_mc_BGR[bn][3:2] = {2{winGroupA[bn]}};
      for (bn = 0; bn < LR_WIDTH; bn++) d_mc_CR[bn][3:2] = {2{winLRankA[bn]}};
      d_mc_ACT_n[3:2] = 2'b00;
      d_mc_RAS_n[3:2] = {2{op[16]}};
      d_mc_CAS_n[3:2] = {2{op[15]}};
      d_mc_WE_n[3:2] = {2{op[14]}};
      d_mc_CS_nR[winRankA][3:2] = 2'b00;
   end
   if (winPortP != 4'b0000) begin
      op = PRE;
      for (bn = 0; bn < ABITS; bn++) d_mc_ADRR[bn][7:6] = {2{1'b0}};
      if (MEM == "DDR4") begin
         d_mc_ADRR[14][7:6] = {2{op[14]}};
         d_mc_ADRR[15][7:6] = {2{op[15]}};
         d_mc_ADRR[16][7:6] = {2{op[16]}};
      end
      d_mc_RAS_n[7:6] = {2{op[16]}};
      d_mc_CAS_n[7:6] = {2{op[15]}};
      d_mc_WE_n[7:6] = {2{op[14]}};
      for (bn = 0; bn < BABITS; bn++)
         d_mc_BAR[bn][7:6] = {2{winBankP[bn]}};
      for (bn = 0; bn < BGBITS; bn++)
         d_mc_BGR[bn][7:6] = {2{winGroupP[bn]}};
      for (bn = 0; bn < LR_WIDTH; bn++) 
         d_mc_CR[bn][7:6] = {2{winLRankP[bn]}};
      d_mc_CS_nR[winRankP][7:6] = 2'b00;
   end
end
endgenerate

// Periodic read FSM blocks read CAS for 3 cycles each interval in high BW workloads
wire winReadAllowed = winRead & ~per_cas_block_req;

// If the Rank changes, back to back CAS is not allowed.  In addition
// if the Group bit is unchanged, back to back CAS is not allowed
// and dead command cycles must be inserted.  The Group check is only
// needed with x16 DDR4.  With DDR3 there are no Groups, and with
// x4/x8 DDR4 the four Groups are always spread across four different
// Group FSMs. Normally 2 tCK dead cycles are inserted when back to back
// is not allowed. Rank switching above DDR1866 requires 4 dead cycles.
// The LONG_RANK_SWITCH parameter will block transactions with rank switches
// or same group from using casSlot2 so that rank switches are guaranteed
// to have 4 dead cycles.
wire rank_different          = (win_rank_cas  != prevRank);
wire lrank_different         = winLRankC != prevLRank;
wire group_unchanged         = ( (MEM == "DDR4") & (BGBITS == 1) ) ? (winGroupC == prevGroup) : 1'b0;
wire b2b_cas_not_allowed     = rank_different | group_unchanged;
wire wr_and_rank_different   = rank_different & winWrite;
wire tccdl_gt6_and_rank_same = ~rank_different & ( tCCD_L > 6 );
wire diff_lr_or_wr_and_rank_different = lrank_different | (rank_different & winWrite); 

always @(*) begin
   casSlot2 = 1'b0;
   tranSentC = 1'b0;
   casez ({winReadAllowed, winWrite})
     2'b10, 2'b01: 
       casez ({prevCAS, b2b_cas_not_allowed, prevSlot2})
         3'b0zz: begin
	    casSlot2  = LONG_RANK_SWITCH & (prev2CAS & prevSlot2);
	    tranSentC = 1'b1;
	 end
         3'b100: begin
            casSlot2 = (tCCD_3ds > 4) ? lrank_different : 1'b0;
            tranSentC = 1'b1;
         end
         3'b101: begin
            casSlot2 =  (tCCD_3ds > 4) ? ~diff_lr_or_wr_and_rank_different : ~wr_and_rank_different;
            tranSentC = (tCCD_3ds > 4) ? ~diff_lr_or_wr_and_rank_different : ~wr_and_rank_different;
         end
         3'b110: begin
            casSlot2  = ~wr_and_rank_different & ~tccdl_gt6_and_rank_same & ~LONG_RANK_SWITCH;
            tranSentC = ~wr_and_rank_different & ~tccdl_gt6_and_rank_same & ~LONG_RANK_SWITCH;
         end
         3'b111: tranSentC = 1'b0;
       endcase
     default: tranSentC = ~( winRead & per_cas_block_req );
   endcase
end

ddr4_v2_2_10_cal_mc_odt #( // MAN - name change
    .ODTWR     (ODTWR)
   ,.ODTWRDEL  (ODTWRDEL)
   ,.ODTWRDUR  (ODTWRDUR)
   ,.ODTWRODEL (ODTWRODEL)
   ,.ODTWRODUR (ODTWRODUR)

   ,.ODTRD     (ODTRD)
   ,.ODTRDDEL  (ODTRDDEL)
   ,.ODTRDDUR  (ODTRDDUR)
   ,.ODTRDODEL (ODTRDODEL)
   ,.ODTRDODUR (ODTRDODUR)

   ,.RANKS     (RANKS)
   ,.RNK_BITS  (RKBITS)
   ,.ODTNOP    (ODTNOP)
   ,.ODTBITS   (ODTBITS)
   ,.TCQ       (TCQ)
)u_ddr_mc_odt(
    .clk (clk)
   ,.rst (rst)

   ,.mc_ODT (mc_ODT)

   ,.casSlot2  (casSlot2)
   ,.rank      (win_rank_cas)
   ,.winRead   (winRead)
   ,.winWrite  (winWrite)
   ,.tranSentC (tranSentC)
);

//synopsys translate_off

`ifdef MEM_INTERNAL
// Events - When asserted high in a test that passes all verification checks, these coverage
//          properties indicate that a functional coverage event has been hit.
// ---------------------------------------------------------------------------------------------

// Read one cycle after write
reg    e_write_previous_cycle;
always @(posedge clk) e_write_previous_cycle  <= #TCQ ( winWrite & tranSentC );
wire   e_mc_ctl_000_wtr = winRead & tranSentC & e_write_previous_cycle;
always @(posedge clk) mc_ctl_000: if (~rst) cover property (e_mc_ctl_000_wtr);

// Write 6tCK after read
reg  [1:0] e_read_previous_cycle;
always @(posedge clk) e_read_previous_cycle  <= #TCQ { e_read_previous_cycle[0], ( winRead & tranSentC & casSlot2 ) };
wire   e_mc_ctl_001_rtw = winWrite & tranSentC & ~casSlot2 & e_read_previous_cycle[1];
always @(posedge clk) mc_ctl_001: if (~rst) cover property (e_mc_ctl_001_rtw);

// Read one cycle after read to different rank
reg [RKBITS-1:0] e_cas_rank_previous_cycle;
always    @(posedge clk) e_cas_rank_previous_cycle  <= #TCQ ( win_rank_cas );
wire      e_mc_ctl_002_rtr = winRead & tranSentC & e_read_previous_cycle & ~( win_rank_cas == e_cas_rank_previous_cycle );
always    @(posedge clk) mc_ctl_002: if (~rst) cover property (e_mc_ctl_002_rtr);

// Write two cycles after write to different rank
reg       e_write_previous_cycle_dly;
reg [RKBITS-1:0] e_cas_rank_previous_cycle_dly;
always    @(posedge clk) e_write_previous_cycle_dly <= #TCQ ( e_write_previous_cycle );
always    @(posedge clk) e_cas_rank_previous_cycle_dly  <= #TCQ ( e_cas_rank_previous_cycle );
wire      e_mc_ctl_003_wtw = winWrite & tranSentC & e_write_previous_cycle_dly & ~( win_rank_cas == e_cas_rank_previous_cycle_dly );
always    @(posedge clk) mc_ctl_003: if (~rst) cover property (e_mc_ctl_003_wtw);

// Write one cycle after write
wire      e_mc_ctl_004_wtw = winWrite & tranSentC & e_write_previous_cycle;
always    @(posedge clk) mc_ctl_004: if (~rst) cover property (e_mc_ctl_004_wtw);

// Read one cycle after read
wire      e_mc_ctl_005_rtr = winRead & tranSentC & e_read_previous_cycle;
always    @(posedge clk) mc_ctl_005: if (~rst) cover property (e_mc_ctl_005_rtr);

// Write on casslot2
wire      e_mc_ctl_006_w2 = winWrite & tranSentC & casSlot2;
always    @(posedge clk) mc_ctl_006: if (~rst) cover property (e_mc_ctl_006_w2);

// Read on casslot2
wire      e_mc_ctl_007_r2 = winRead & tranSentC & casSlot2;
always    @(posedge clk) mc_ctl_007: if (~rst) cover property (e_mc_ctl_007_r2);

// Read blocked by periodic FSM
wire      e_mc_ctl_008_r = winRead & per_cas_block_req;
always    @(posedge clk) mc_ctl_008: if (~rst) cover property (e_mc_ctl_008_r);

// Read issued
wire      e_mc_ctl_009_r = winRead & tranSentC;
always    @(posedge clk) mc_ctl_009: if (~rst) cover property (e_mc_ctl_009_r);

// Write issued
wire      e_mc_ctl_010_w = winWrite & tranSentC;
always    @(posedge clk) mc_ctl_010: if (~rst) cover property (e_mc_ctl_010_w);

// ReadA issued
wire      e_mc_ctl_011_ra = winRead & tranSentC & winAP;
always    @(posedge clk) mc_ctl_011: if (~rst) cover property (e_mc_ctl_011_ra);

// WriteA issued
wire      e_mc_ctl_012_wa = winWrite & tranSentC & winAP;
always    @(posedge clk) mc_ctl_012: if (~rst) cover property (e_mc_ctl_012_wa);

// Activate issued
wire      e_mc_ctl_013_act = winAct;
always    @(posedge clk) mc_ctl_013: if (~rst) cover property (e_mc_ctl_013_act);

// Precharge issued
wire      e_mc_ctl_014_pre = | winPortP;
always    @(posedge clk) mc_ctl_014: if (~rst) cover property (e_mc_ctl_014_pre);

// PrechargeAll issued
wire      e_mc_ctl_015_prea = preIss;
always    @(posedge clk) mc_ctl_015: if (~rst) cover property (e_mc_ctl_015_prea);

// Refresh issued
wire      e_mc_ctl_016_ref = refIss;
always    @(posedge clk) mc_ctl_016: if (~rst) cover property (e_mc_ctl_016_ref);

// ZQCS issued
wire      e_mc_ctl_017_zq = zqIss & ~zqIssAll;
always    @(posedge clk) mc_ctl_017: if (~rst) cover property (e_mc_ctl_017_zq);

// ZQCS issued to all ranks in parallel
wire      e_mc_ctl_018_zqa = zqIss & zqIssAll;
always    @(posedge clk) mc_ctl_018: if (~rst) cover property (e_mc_ctl_018_zqa);

// Read, Act, Pre issued in same fabric cycle
wire      e_mc_ctl_019_rdactpre = e_mc_ctl_009_r & e_mc_ctl_013_act & e_mc_ctl_014_pre & ~casSlot2;
always    @(posedge clk) mc_ctl_019: if (~rst) cover property (e_mc_ctl_019_rdactpre);

// Write, Act, Pre issued in same fabric cycle
wire      e_mc_ctl_020_wractpre = e_mc_ctl_010_w & e_mc_ctl_013_act & e_mc_ctl_014_pre & ~casSlot2;
always    @(posedge clk) mc_ctl_020: if (~rst) cover property (e_mc_ctl_020_wractpre);

// Read casslot2, Act, Pre issued in same fabric cycle
wire      e_mc_ctl_021_rdactpre2 = e_mc_ctl_009_r & e_mc_ctl_013_act & e_mc_ctl_014_pre & casSlot2;
always    @(posedge clk) mc_ctl_021: if (~rst) cover property (e_mc_ctl_021_rdactpre2);

// Write casslot2, Act, Pre issued in same fabric cycle
wire      e_mc_ctl_022_wractpre2 = e_mc_ctl_010_w & e_mc_ctl_013_act & e_mc_ctl_014_pre & casSlot2;
always    @(posedge clk) mc_ctl_022: if (~rst) cover property (e_mc_ctl_022_wractpre2);

// Back to back read or write and 3ds
wire      e_mc_ctl_023_3ds_b2b_wr = winWrite & tCCD_3ds > 4 & S_HEIGHT > 1 & lrank_different & prevCAS &
                                    ~b2b_cas_not_allowed & ~prevSlot2;
always    @(posedge clk) mc_ctl_023: if (~rst) cover property (e_mc_ctl_023_3ds_b2b_wr);

wire      e_mc_ctl_024_3ds_b2b_rd = winReadAllowed & tCCD_3ds > 4 & S_HEIGHT > 1 & lrank_different & prevCAS &
                                    ~b2b_cas_not_allowed & ~prevSlot2;
always    @(posedge clk) mc_ctl_024: if (~rst) cover property (e_mc_ctl_024_3ds_b2b_rd);

wire      e_mc_ctl_025_3ds_b2b_wr = winWrite & tCCD_3ds > 4 & S_HEIGHT > 1 & lrank_different & prevCAS &
                                    ~b2b_cas_not_allowed &  prevSlot2 & ~wr_and_rank_different;
always    @(posedge clk) mc_ctl_025: if (~rst) cover property (e_mc_ctl_025_3ds_b2b_wr);

wire      e_mc_ctl_026_3ds_b2b_rd = winReadAllowed & tCCD_3ds > 4 & S_HEIGHT > 1 & lrank_different & prevCAS &
                                    ~b2b_cas_not_allowed &  prevSlot2;
always    @(posedge clk) mc_ctl_026: if (~rst) cover property (e_mc_ctl_026_3ds_b2b_rd);


// Asserts - When asserted high, an illegal condition has been detected and the test has failed.
// ---------------------------------------------------------------------------------------------

// Read during periodic cas block
wire   a_mc_ctl_000_read = winRead & per_cas_block_req & tranSentC;
always @(posedge clk) if (~rst) assert property (~a_mc_ctl_000_read);

// Read and write arbitrating on same cycle
wire   a_mc_ctl_001_rd_wr = winRead & winWrite;
always @(posedge clk) if (~rst) assert property (~a_mc_ctl_001_rd_wr);

// Two tCK tCCD
reg    a_casslot2_sent_previous_cycle;
always @(posedge clk)  a_casslot2_sent_previous_cycle <= #TCQ ( ( winRead | winWrite ) & tranSentC & casSlot2 );
wire   a_mc_ctl_002_2ccd = ( winRead | winWrite ) & tranSentC & ~casSlot2 & a_casslot2_sent_previous_cycle;
always @(posedge clk) if (~rst) assert property (~a_mc_ctl_002_2ccd);

// Illegal four tCK tCCD - read to write or write to read with 4tCK spacing
reg    a_read_casslot0_sent_previous_cycle;
reg    a_read_casslot2_sent_previous_cycle;
reg    a_write_casslot0_sent_previous_cycle;
reg    a_write_casslot2_sent_previous_cycle;
always @(posedge clk)  a_read_casslot0_sent_previous_cycle <= #TCQ ( winRead & tranSentC & ~casSlot2 );
always @(posedge clk)  a_read_casslot2_sent_previous_cycle <= #TCQ ( winRead & tranSentC &  casSlot2 );
always @(posedge clk)  a_write_casslot0_sent_previous_cycle <= #TCQ ( winWrite & tranSentC & ~casSlot2 );
always @(posedge clk)  a_write_casslot2_sent_previous_cycle <= #TCQ ( winWrite & tranSentC &  casSlot2 );
wire   a_mc_ctl_003_4ccd = tranSentC
                           & ( ( winWrite & ~casSlot2 & a_read_casslot0_sent_previous_cycle )
                             | ( winWrite &  casSlot2 & a_read_casslot2_sent_previous_cycle )
                             | ( winRead  & ~casSlot2 & a_write_casslot0_sent_previous_cycle )
                             | ( winRead  &  casSlot2 & a_write_casslot2_sent_previous_cycle ) );
always @(posedge clk) if (~rst) assert property (~a_mc_ctl_003_4ccd);

// Illegal write after write - write to write to different ranks with less than 8tCK spacing.
reg       a_write_sent_previous_cycle;
reg [RKBITS-1:0] a_rank_previous_cycle;
always    @(posedge clk)  a_write_sent_previous_cycle <= #TCQ ( winWrite & tranSentC );
always    @(posedge clk)  a_rank_previous_cycle <= #TCQ ( win_rank_cas );
wire      a_mc_ctl_004_wtw = winWrite & tranSentC & a_write_sent_previous_cycle & ~( win_rank_cas == a_rank_previous_cycle );
always    @(posedge clk) if (~rst) assert property (~a_mc_ctl_004_wtw);

// Illegal read after read - 4tCK apart to different ranks.
wire      a_mc_ctl_005_rtr = winRead & tranSentC & ~( win_rank_cas == a_rank_previous_cycle )
                             & ( ( ~casSlot2 & a_read_casslot0_sent_previous_cycle )
                               | (  casSlot2 & a_read_casslot2_sent_previous_cycle ) );
always    @(posedge clk) if (~rst) assert property (~a_mc_ctl_005_rtr);

// Illegal read after read, or write after write, to different lr and tCCD_3ds > 4
wire      a_mc_ctl_006_ccd_3ds = tranSentC & lrank_different & tCCD_3ds > 4 & ~rank_different & S_HEIGHT > 1 & 
                                 ((~casSlot2 & winRead  & a_read_casslot0_sent_previous_cycle) |
                                  (~casSlot2 & winWrite & a_write_casslot0_sent_previous_cycle)|
                                  (winRead  & a_read_casslot2_sent_previous_cycle)             |
                                  (winWrite & a_write_casslot2_sent_previous_cycle));
always    @(posedge clk) if (~rst) assert property (~a_mc_ctl_006_ccd_3ds);

// Illegal rank/tCCD_L config
//wire   a_mc_ctl_007 = (CSBITS > 1) & (tCCD_L>6);
//always @(posedge clk) if (~rst) assert property (~a_mc_ctl_007);

// Illegal 3DS/tCCD_L config
wire   a_mc_ctl_008 = (S_HEIGHT > 1) & (tCCD_L>6);
always @(posedge clk) if (~rst) assert property (~a_mc_ctl_008);

`endif

//synopsys translate_on


endmodule


