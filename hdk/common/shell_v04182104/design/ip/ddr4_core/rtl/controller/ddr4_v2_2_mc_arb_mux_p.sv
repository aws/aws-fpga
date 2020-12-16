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
//  /   /         Filename           : ddr4_v2_2_10_mc.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                   ddr4_v2_2_10_mc_arb_mux_p module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ns/100ps

module ddr4_v2_2_10_mc_arb_mux_p #(parameter
    MEM = "DDR4"
   ,ABITS = 18
   ,S_HEIGHT = 1
   ,ALIAS_P_CNT = "ON"
   ,LR_WIDTH = 1
   ,TCQ = 0.1
   ,XTP_MODE = "RANK_GROUP_BANK"
   ,RKBITS = 2
   ,RANK_SLAB = 4
   ,tRAS = 33
   ,tRTP = 6
   ,tWR = 12
)(
    input clk
   ,input rst

   ,output [1:0] winBankP
   ,output [1:0] winGroupP
   ,output [LR_WIDTH-1:0] winLRankP
   ,output [3:0] winPortP
   ,output [RKBITS-1:0] winRankP
   ,output [3:0] tWTPF
   ,output [1:0] tRTPF
   ,output [3:0] tRASF

   ,input [7:0] cmdBankP
   ,input [7:0] cmdGroupP
   ,input [4*LR_WIDTH-1:0] cmdLRankP
   ,input [RKBITS*4-1:0] cmdRankP
   ,input [3:0] preReq
   ,input [5:0] tCWL
   ,input [1:0] winBankC
   ,input [1:0] winGroupC
   ,input [LR_WIDTH-1:0] winLRankC
   ,input [RKBITS-1:0] winRankC
   ,input       winRead
   ,input       winWrite
   ,input       rdCAS
   ,input       wrCAS
   ,input [1:0] winBankA
   ,input [1:0] winGroupA
   ,input [LR_WIDTH-1:0] winLRankA
   ,input [RKBITS-1:0] winRankA
   ,input       winAct

   ,output reg [3:0] preReqM
);

// These equations do not support additive latency.
// +2 tCK allows for rounding down and min 5 tCK CAS to PRE spacing, -2 fabric cycles for scheduler PRE pipeline.
wire [3:0] tWTP_TEMP = ( (tWR + 4 + tCWL + 2) / 4 ) - 2;
assign     tWTPF     = ( ( (tWR + 4 + tCWL + 2) / 4 ) - 2 > 0 ) ? tWTP_TEMP : 0;
wire [1:0] tRTP_TEMP = ( (tRTP + 2) / 4 ) - 2;                                   // spyglass disable W164c
assign     tRTPF     = ( ( (tRTP + 2) / 4 ) - 2 > 0 ) ? tRTP_TEMP : 0;
wire [3:0] tRAS_TEMP = ( (tRAS + 3) / 4 ) - 2;
assign     tRASF     = ( ( (tRAS + 3) / 4 ) - 2 > 0 ) ? tRAS_TEMP : 0;

integer i, j, k, l;

wire [LR_WIDTH-1:0] winLRankC_3ds;
wire [LR_WIDTH-1:0] winLRankA_3ds;
wire [4*LR_WIDTH-1:0] cmdLRankP_3ds;

localparam S_HEIGHT_ALIASED = (ALIAS_P_CNT == "ON") ? 1 : S_HEIGHT;

generate
  if (S_HEIGHT_ALIASED < 2) begin
    assign winLRankC_3ds = '0;
    assign winLRankA_3ds = '0;
    assign cmdLRankP_3ds = '0;
  end else begin
    assign winLRankC_3ds = winLRankC;
    assign winLRankA_3ds = winLRankA;
    assign cmdLRankP_3ds = cmdLRankP;
  end
endgenerate

reg [3:0] timerWTP[0:RANK_SLAB-1][S_HEIGHT_ALIASED-1:0][0:3][0:3]; // rank, l_rank, group and bank
reg [1:0] timerRTP[0:RANK_SLAB-1][S_HEIGHT_ALIASED-1:0][0:3][0:3]; // rank, l_rank, group and bank
reg [3:0] timerRAS[0:RANK_SLAB-1][S_HEIGHT_ALIASED-1:0][0:3][0:3]; // rank, l_rank, group and bank
reg       pre_safe[0:RANK_SLAB-1][S_HEIGHT_ALIASED-1:0][0:3][0:3]; // rank, l_rank, group and bank

generate
if (XTP_MODE == "RANK_GROUP_BANK") begin
// ======================================================================
// This section has safe counters for write to precharge and read
// to precharge on a per rank, per group, per bank basis.  This supports
// the most precharge scheduling freedom after a CAS command.
// ======================================================================
   always @(posedge clk) if (rst) begin
      for (i = 0; i <= RANK_SLAB-1; i = i + 1)
         for (j = 0; j <= S_HEIGHT_ALIASED-1; j = j + 1)
            for (k = 0; k <= 3; k = k + 1)
               for (l = 0; l <= 3; l = l + 1) begin
                  timerWTP[i][j][k][l] <= 'b0;
                  timerRTP[i][j][k][l] <= 'b0;
                  timerRAS[i][j][k][l] <= 'b0;
                  pre_safe[i][j][k][l] <= #TCQ 1'b0;
            end
   end else begin
      for (i = 0; i <= RANK_SLAB-1; i = i + 1)
         for (j = 0; j <= S_HEIGHT_ALIASED-1; j = j + 1)
            for (k = 0; k <= 3; k = k + 1)
               for (l = 0; l <= 3; l = l + 1) begin
                  if (timerWTP[i][j][k][l]) timerWTP[i][j][k][l] <= #TCQ timerWTP[i][j][k][l] - 4'b1;
                  if (timerRTP[i][j][k][l]) timerRTP[i][j][k][l] <= #TCQ timerRTP[i][j][k][l] - 2'b1;
                  if (timerRAS[i][j][k][l]) timerRAS[i][j][k][l] <= #TCQ timerRAS[i][j][k][l] - 4'b1;
                  pre_safe[i][j][k][l] <= #TCQ ( ( timerWTP[i][j][k][l] <= 4'd1 ) & ( timerRTP[i][j][k][l] <= 2'd1 ) & ( timerRAS[i][j][k][l] <= 4'd1 ) );
            end
      // Do not qualify with tranSentC since we cannot arbitrate for the same
      // Rank, Group, Bank on both a CAS and Precharge command in the same fabric cycle.
      // This will load the timer a cycle early if tranSentC de-asserts, but there will
      // be no functional effect.
      if (winWrite) timerWTP[winRankC][winLRankC_3ds][winGroupC][winBankC] <= #TCQ tWTPF;
      if (winRead)  timerRTP[winRankC][winLRankC_3ds][winGroupC][winBankC] <= #TCQ tRTPF;
      if (winAct)   timerRAS[winRankA][winLRankA_3ds][winGroupA][winBankA] <= #TCQ tRASF;
   end
   always @(*) begin
      preReqM[0] = preReq[0] & pre_safe[cmdRankP[RKBITS*1-1:RKBITS*0]][cmdLRankP_3ds[0*LR_WIDTH+:LR_WIDTH]][cmdGroupP[1:0]][cmdBankP[1:0]];
      preReqM[1] = preReq[1] & pre_safe[cmdRankP[RKBITS*2-1:RKBITS*1]][cmdLRankP_3ds[1*LR_WIDTH+:LR_WIDTH]][cmdGroupP[3:2]][cmdBankP[3:2]];
      preReqM[2] = preReq[2] & pre_safe[cmdRankP[RKBITS*3-1:RKBITS*2]][cmdLRankP_3ds[2*LR_WIDTH+:LR_WIDTH]][cmdGroupP[5:4]][cmdBankP[5:4]];
      preReqM[3] = preReq[3] & pre_safe[cmdRankP[RKBITS*4-1:RKBITS*3]][cmdLRankP_3ds[3*LR_WIDTH+:LR_WIDTH]][cmdGroupP[7:6]][cmdBankP[7:6]];
   end
end else begin
// ======================================================================
// This section has safe counters for write to precharge and read
// to precharge on a per rank basis only.  This blocks all precharge
// commands to a rank for tRTP or tWTP after a read or write CAS to
// that rank.  The output of this block is also used in the arb_c block
// to prevent a CAS and Precharge from being issued on consecutive cycles.
// ======================================================================
   reg [3:0] timerWR[0:RANK_SLAB-1]; // rank
   reg [3:0] rank_timerRTP[0:RANK_SLAB-1]; // rank
   always @(posedge clk) if (rst) begin
      for (i = 0; i <= RANK_SLAB-1; i = i + 1) begin
         timerWR[i] <= 'b0;
         rank_timerRTP[i] <= 'b0;
      end
   end else begin
      for (i = 0; i <= RANK_SLAB-1; i = i + 1) begin
         if (timerWR[i]) timerWR[i] <= #TCQ timerWR[i] - 1'b1;
         if (rank_timerRTP[i]) rank_timerRTP[i] <= #TCQ rank_timerRTP[i] - 1'b1;
      end
      if (wrCAS) timerWR[winRankC] <= #TCQ tWTPF;
      if (rdCAS) rank_timerRTP[winRankC] <= #TCQ tRTPF;
   end
   always @(*) begin
      preReqM[0] =    preReq[0]
                   && (timerWR[cmdRankP[RKBITS*1-1:RKBITS*0]] == 0) && !wrCAS
                   && (rank_timerRTP[cmdRankP[RKBITS*1-1:RKBITS*0]] == 0) && !rdCAS;
      preReqM[1] =    preReq[1]
                   && (timerWR[cmdRankP[RKBITS*2-1:RKBITS*1]] == 0) && !wrCAS
                   && (rank_timerRTP[cmdRankP[RKBITS*2-1:RKBITS*1]] == 0) && !rdCAS;
      preReqM[2] =    preReq[2]
                   && (timerWR[cmdRankP[RKBITS*3-1:RKBITS*2]] == 0) && !wrCAS
                   && (rank_timerRTP[cmdRankP[RKBITS*3-1:RKBITS*2]] == 0) && !rdCAS;
      preReqM[3] =    preReq[3]
                   && (timerWR[cmdRankP[RKBITS*4-1:RKBITS*3]] == 0) && !wrCAS
                   && (rank_timerRTP[cmdRankP[RKBITS*4-1:RKBITS*3]] == 0) && !rdCAS;
   end
end
endgenerate

ddr4_v2_2_10_mc_arb_p #(
   .TCQ (TCQ)
)u_ddr_mc_arb_p(
    .clk     (clk)
   ,.rst     (rst)

   ,.winPort (winPortP)

   ,.req     (preReqM)
);

wire [ABITS-1:0] winRow;

ddr4_v2_2_10_mc_cmd_mux_ap #(
   .ABITS (ABITS)
  ,.LR_WIDTH (LR_WIDTH)
  ,.RKBITS     (RKBITS)
  ,.RANK_SLAB  (RANK_SLAB)
)u_ddr_mc_cmd_mux_p(
    .winBank  (winBankP)
   ,.winGroup (winGroupP)
   ,.winLRank (winLRankP)
   ,.winRank  (winRankP)
   ,.winRow   (winRow)

   ,.cmdBank  (cmdBankP)
   ,.cmdGroup (cmdGroupP)
   ,.cmdLRank (cmdLRankP)
   ,.cmdRank  (cmdRankP)
   ,.cmdRow   ({ 4*ABITS { 1'b0 }})

   ,.sel      (winPortP)
);

//synopsys translate_off

`ifdef MEM_INTERNAL
// Events - When asserted high in a test that passes all verification checks, these coverage
//          properties indicate that a functional coverage event has been hit.
// ---------------------------------------------------------------------------------------------

// All Group FSMs arbitrating for a precharge
wire   e_mc_arb_mux_p_000_req = & preReq;
always @(posedge clk) mc_arb_mux_p_000: if (~rst) cover property (e_mc_arb_mux_p_000_req);

// All Group FSMs arbitrating for a precharge and they are all safe
wire   e_mc_arb_mux_p_001_req = & preReqM;
always @(posedge clk) mc_arb_mux_p_001: if (~rst) cover property (e_mc_arb_mux_p_001_req);

// Group 0 precharge blocked by wtp
wire   e_mc_arb_mux_p_002_wtp = preReq[0] & ~( timerWTP[cmdRankP[RKBITS*1-1:RKBITS*0]][cmdLRankP_3ds[0*LR_WIDTH+:LR_WIDTH]][cmdGroupP[1:0]][cmdBankP[1:0]] <= 4'd0 )
                                          &  ( timerRTP[cmdRankP[RKBITS*1-1:RKBITS*0]][cmdLRankP_3ds[0*LR_WIDTH+:LR_WIDTH]][cmdGroupP[1:0]][cmdBankP[1:0]] <= 2'd0 )
                                          &  ( timerRAS[cmdRankP[RKBITS*1-1:RKBITS*0]][cmdLRankP_3ds[0*LR_WIDTH+:LR_WIDTH]][cmdGroupP[1:0]][cmdBankP[1:0]] <= 4'd0 );
always @(posedge clk) mc_arb_mux_p_002: if (~rst) cover property (e_mc_arb_mux_p_002_wtp);

// Group 1 precharge blocked by rtp
wire   e_mc_arb_mux_p_003_rtp = preReq[1] &  ( timerWTP[cmdRankP[RKBITS*2-1:RKBITS*1]][cmdLRankP_3ds[1*LR_WIDTH+:LR_WIDTH]][cmdGroupP[3:2]][cmdBankP[3:2]] <= 4'd0 )
                                          & ~( timerRTP[cmdRankP[RKBITS*2-1:RKBITS*1]][cmdLRankP_3ds[1*LR_WIDTH+:LR_WIDTH]][cmdGroupP[3:2]][cmdBankP[3:2]] <= 2'd0 )
                                          &  ( timerRAS[cmdRankP[RKBITS*2-1:RKBITS*1]][cmdLRankP_3ds[1*LR_WIDTH+:LR_WIDTH]][cmdGroupP[3:2]][cmdBankP[3:2]] <= 4'd0 );
always @(posedge clk) mc_arb_mux_p_003: if (~rst) cover property (e_mc_arb_mux_p_003_rtp);

// Group 2 precharge blocked by ras
wire   e_mc_arb_mux_p_004_ras = preReq[2] &  ( timerWTP[cmdRankP[RKBITS*3-1:RKBITS*2]][cmdLRankP_3ds[2*LR_WIDTH+:LR_WIDTH]][cmdGroupP[5:4]][cmdBankP[5:4]] <= 4'd0 )
                                          &  ( timerRTP[cmdRankP[RKBITS*3-1:RKBITS*2]][cmdLRankP_3ds[2*LR_WIDTH+:LR_WIDTH]][cmdGroupP[5:4]][cmdBankP[5:4]] <= 2'd0 )
                                          & ~( timerRAS[cmdRankP[RKBITS*3-1:RKBITS*2]][cmdLRankP_3ds[2*LR_WIDTH+:LR_WIDTH]][cmdGroupP[5:4]][cmdBankP[5:4]] <= 4'd0 );
always @(posedge clk) mc_arb_mux_p_004: if (~rst) cover property (e_mc_arb_mux_p_004_ras);

// Group 3 precharge blocked by wtp and ras
wire   e_mc_arb_mux_p_005_ras = preReq[3] & ~( timerWTP[cmdRankP[RKBITS*4-1:RKBITS*3]][cmdLRankP_3ds[3*LR_WIDTH+:LR_WIDTH]][cmdGroupP[7:6]][cmdBankP[7:6]] <= 4'd0 )
                                          &  ( timerRTP[cmdRankP[RKBITS*4-1:RKBITS*3]][cmdLRankP_3ds[3*LR_WIDTH+:LR_WIDTH]][cmdGroupP[7:6]][cmdBankP[7:6]] <= 2'd0 )
                                          & ~( timerRAS[cmdRankP[RKBITS*4-1:RKBITS*3]][cmdLRankP_3ds[3*LR_WIDTH+:LR_WIDTH]][cmdGroupP[7:6]][cmdBankP[7:6]] <= 4'd0 );
always @(posedge clk) mc_arb_mux_p_005: if (~rst) cover property (e_mc_arb_mux_p_005_ras);

// Group 0 precharge blocked by rtp and ras
wire   e_mc_arb_mux_p_006_ras = preReq[0] &  ( timerWTP[cmdRankP[RKBITS*1-1:RKBITS*0]][cmdLRankP_3ds[0*LR_WIDTH+:LR_WIDTH]][cmdGroupP[1:0]][cmdBankP[1:0]] <= 4'd0 )
                                          & ~( timerRTP[cmdRankP[RKBITS*1-1:RKBITS*0]][cmdLRankP_3ds[0*LR_WIDTH+:LR_WIDTH]][cmdGroupP[1:0]][cmdBankP[1:0]] <= 2'd0 )
                                          & ~( timerRAS[cmdRankP[RKBITS*1-1:RKBITS*0]][cmdLRankP_3ds[0*LR_WIDTH+:LR_WIDTH]][cmdGroupP[1:0]][cmdBankP[1:0]] <= 4'd0 );
always @(posedge clk) mc_arb_mux_p_006: if (~rst) cover property (e_mc_arb_mux_p_006_ras);

// Group 2 precharge blocked by wtp and rtp and ras
wire   e_mc_arb_mux_p_007_ras = preReq[2] & ~( timerWTP[cmdRankP[RKBITS*3-1:RKBITS*2]][cmdLRankP_3ds[2*LR_WIDTH+:LR_WIDTH]][cmdGroupP[5:4]][cmdBankP[5:4]] <= 4'd0 )
                                          & ~( timerRTP[cmdRankP[RKBITS*3-1:RKBITS*2]][cmdLRankP_3ds[2*LR_WIDTH+:LR_WIDTH]][cmdGroupP[5:4]][cmdBankP[5:4]] <= 2'd0 )
                                          & ~( timerRAS[cmdRankP[RKBITS*3-1:RKBITS*2]][cmdLRankP_3ds[2*LR_WIDTH+:LR_WIDTH]][cmdGroupP[5:4]][cmdBankP[5:4]] <= 4'd0 );
always @(posedge clk) mc_arb_mux_p_007: if (~rst) cover property (e_mc_arb_mux_p_007_ras);

// Load wtp counter when write was not issued
wire   e_mc_arb_mux_p_008_wri = winWrite & ~wrCAS & ( tWTPF > 0 );
always @(posedge clk) mc_arb_mux_p_008: if (~rst) cover property (e_mc_arb_mux_p_008_wri);

// Load rtp counter when read was not issued
wire   e_mc_arb_mux_p_009_rd  = winRead & ~rdCAS & ( tRTPF > 0 );
always @(posedge clk) mc_arb_mux_p_009: if (~rst) cover property (e_mc_arb_mux_p_009_rd);


// Asserts - When asserted high, an illegal condition has been detected and the test has failed.
// ---------------------------------------------------------------------------------------------

// winPortP select one hot cold counter
integer group_index;
reg  [2:0] a_winPortP_count;
always @(*) begin
  a_winPortP_count = 3'b0;
  for (group_index = 0; group_index <= 3; group_index++) begin
    a_winPortP_count += winPortP[group_index];
  end
end

// winPortP one hot cold check failed
wire a_mc_arb_mux_p_000_1hc = ( a_winPortP_count > 3'b1 );
always @(posedge clk) if (~rst) assert property (~a_mc_arb_mux_p_000_1hc);

// tWTP overflow
wire a_mc_arb_mux_p_001_of = ( ( (tWR + 4 + tCWL + 2) / 4 ) - 2 ) > 15;
always @(posedge clk) if (~rst) assert property (~a_mc_arb_mux_p_001_of);

// tRTP overflow
wire a_mc_arb_mux_p_002_of = ( ( (tRTP + 2) / 4 ) - 2 ) > 3;
always @(posedge clk) if (~rst) assert property (~a_mc_arb_mux_p_002_of);

// tRAS overflow
wire a_mc_arb_mux_p_003_of = ( ( (tRAS + 3) / 4 ) - 2 ) > 15;
always @(posedge clk) if (~rst) assert property (~a_mc_arb_mux_p_003_of);


`endif

//synopsys translate_on



endmodule


