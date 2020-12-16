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
//  /   /         Filename           : ddr4_v2_2_10_mc_rd_wr.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                   ddr4_v2_2_10_mc_rd_wr module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ns/100ps

module ddr4_v2_2_10_mc_rd_wr #(parameter
    RDSLOT = 256
   ,WRSLOT = 128
   ,tWTR_L = 9
   ,tWTR_S = 3
   ,tRTW   = 4 // (RL + BL/2 - WL + 2CK + 3) / 4
   ,RKBITS = 2
   ,RANK_SLAB = 4
   ,S_HEIGHT = 1
   ,LR_WIDTH = 1
   ,STARVATION_EN = 1'b1
   ,STARVE_COUNT_WIDTH = 9
   ,TCQ    = 0.1
)(
    input        clk
   ,input        rst

   ,output     readMode

   ,output reg [3:0] rdReqT
   ,output reg [3:0] wrReqT

   ,input [7:0] cmdGroup
   ,input [4*LR_WIDTH-1:0] cmdLRank
   ,input [RKBITS*4-1:0] cmdRank
   ,input       rdCAS
   ,input [3:0] rdReq
   ,input [1:0] winGroup
   ,input [LR_WIDTH-1:0] winLRank
   ,input [3:0] winPort
   ,input [RKBITS-1:0] winRank
   ,input       wrCAS
   ,input       casSlot2
   ,input [3:0] wrReq
   ,input [5:0] tCWL
);


integer i;
integer g_index;

assign readMode = '0;

// Starvation signals
reg block_reads;
reg block_writes;
reg [3:0] read_req_starve;
reg [3:0] read_req_starve_nxt;
reg [STARVE_COUNT_WIDTH-1:0] read_req_starve_count[3:0];
reg [STARVE_COUNT_WIDTH-1:0] read_req_starve_count_nxt[3:0];
reg [3:0] write_req_starve;
reg [3:0] write_req_starve_nxt;
reg [STARVE_COUNT_WIDTH-1:0] write_req_starve_count[3:0];
reg [STARVE_COUNT_WIDTH-1:0] write_req_starve_count_nxt[3:0];
reg [3:0] read_req_ff;
reg [3:0] write_req_ff;

// Increment or reset saturating counters to track forward progress of each group FSM.
always @(*) begin
 for (g_index = 0; g_index < 4; g_index = g_index + 1) begin
   read_req_starve_count_nxt[g_index]  = read_req_ff[g_index]
                                       ? ( read_req_starve_count[g_index]  + { { STARVE_COUNT_WIDTH-1 { 1'b0 } }, ~read_req_starve[g_index] } )
                                       : '0;
   write_req_starve_count_nxt[g_index] = write_req_ff[g_index]
                                       ? ( write_req_starve_count[g_index] + { { STARVE_COUNT_WIDTH-1 { 1'b0 } }, ~write_req_starve[g_index] } )
                                       : '0;
 end
end

// Check which FSM counter has saturated due to starvation.
always @(*) begin
 for (g_index = 0; g_index < 4; g_index = g_index + 1) begin
   read_req_starve_nxt[g_index]  = & read_req_starve_count_nxt[g_index];
   write_req_starve_nxt[g_index] = & write_req_starve_count_nxt[g_index];
 end
end

// Block based on starvation bits.
wire block_reads_nxt  = | write_req_starve;
wire block_writes_nxt = | read_req_starve;
wire [3:0] rdReq_starve = STARVATION_EN ? ( rdReq & ~{ 4 {  block_reads } } ) : rdReq;
wire [3:0] wrReq_starve = STARVATION_EN ? ( wrReq & ~{ 4 { block_writes } } ) : wrReq;

// Clear all starvation counters if reads and writes are starved at the same time.  This would cause deadlock.
wire [3:0] read_req_nxt  = rdReq & ~{ 4 { block_reads & block_writes } };
wire [3:0] write_req_nxt = wrReq & ~{ 4 { block_reads & block_writes } };




wire [RANK_SLAB-1:0] wtr_okl; // per rank
wire [RANK_SLAB-1:0] wtr_oks; // per rank
wire [1:0] prevGrW[0:RANK_SLAB-1];
wire [LR_WIDTH-1:0] prevLRW[0:RANK_SLAB-1];

genvar wtr;
generate
   for (wtr = 0; wtr <= RANK_SLAB-1; wtr = wtr + 1) begin:wtrs
      ddr4_v2_2_10_mc_wtr #(
          .tWTR_L (tWTR_L)
         ,.tWTR_S (tWTR_S)
         ,.LR_WIDTH(LR_WIDTH)
         ,.TCQ    (TCQ)
      ) u_ddr_mc_wtr (
          .clk (clk)
         ,.rst (rst)

         ,.wtr_okl (wtr_okl[wtr])
         ,.wtr_oks (wtr_oks[wtr])
         ,.prevGr  (prevGrW[wtr])
         ,.prevLR  (prevLRW[wtr])

         ,.wrCAS (wrCAS & (winRank == wtr))
         ,.casSlot2 (casSlot2)
         ,.group (winGroup)
         ,.l_rank(winLRank)
         ,.tCWL  (tCWL)
      );
   end
endgenerate


always @(*) begin
  for (i = 0; i <= 3; i = i + 1) begin 
    if (rdReq_starve[i]) begin:chkR
      if (S_HEIGHT > 1) begin
        if (prevGrW[cmdRank[i*RKBITS+:RKBITS]] == cmdGroup[i*2+:2] & prevLRW[cmdRank[i*RKBITS+:RKBITS]] == cmdLRank[i*LR_WIDTH+:LR_WIDTH])
          rdReqT[i] = wtr_okl[cmdRank[i*RKBITS+:RKBITS]];
        else 
          rdReqT[i] = wtr_oks[cmdRank[i*RKBITS+:RKBITS]];
      end else begin
        if (prevGrW[cmdRank[i*RKBITS+:RKBITS]] == cmdGroup[i*2+:2])
          rdReqT[i] = wtr_okl[cmdRank[i*RKBITS+:RKBITS]];
        else 
          rdReqT[i] = wtr_oks[cmdRank[i*RKBITS+:RKBITS]];
      end
    end else 
      rdReqT[i] = 1'b0;
  end // for
end // always


// +5 tCK term covers rounding down and casSlot2.  -2 fabric clocks covers the scheduler pipeline.
wire [2:0] tRTW_TEMP = ( tRTW + 5 ) / 4;                                        // spyglass disable W164c
wire [2:0] tRTW_F    = ( ( tRTW_TEMP - 2 ) > 0 ) ? ( tRTW_TEMP - 3'd2 ) : 3'd0; // spyglass disable W164a

reg       rtw_okr;
reg [2:0] rtw;
wire      rtw_ok = rtw_okr & !rdCAS;

always @(posedge clk) if (rst) begin
   rtw_okr <= 1'b1;
   rtw <= 'b0;
end else begin
   if (rtw) rtw <= #TCQ rtw - 3'b1;
   rtw_okr <= #TCQ (rtw <= 1);
   if (rdCAS) begin
      rtw <= #TCQ tRTW_F;
      rtw_okr <= #TCQ 1'b0;
   end
end

always @(*) for (i = 0; i <= 3; i = i + 1) if (wrReq_starve[i]) begin:chkW
   wrReqT[i] = rtw_ok;
end else wrReqT[i] = 1'b0;

// Flops for starvation logic
always @(posedge clk) if (rst) begin
  block_reads              <= #TCQ '0;
  read_req_ff              <= #TCQ '0;
  read_req_starve          <= #TCQ '0;
  block_writes             <= #TCQ '0;
  write_req_ff             <= #TCQ '0;
  write_req_starve         <= #TCQ '0;
  for (g_index = 0; g_index < 4; g_index = g_index + 1) read_req_starve_count[g_index]  <= #TCQ '0;
  for (g_index = 0; g_index < 4; g_index = g_index + 1) write_req_starve_count[g_index] <= #TCQ '0;
end else begin
  block_reads              <= #TCQ block_reads_nxt;
  read_req_ff              <= #TCQ read_req_nxt;
  read_req_starve          <= #TCQ read_req_starve_nxt;
  block_writes             <= #TCQ block_writes_nxt;
  write_req_ff             <= #TCQ write_req_nxt;
  write_req_starve         <= #TCQ write_req_starve_nxt;
  for (g_index = 0; g_index < 4; g_index = g_index + 1) read_req_starve_count[g_index]  <= #TCQ read_req_starve_count_nxt[g_index];
  for (g_index = 0; g_index < 4; g_index = g_index + 1) write_req_starve_count[g_index] <= #TCQ write_req_starve_count_nxt[g_index];
end

//synopsys translate_off

`ifdef MEM_INTERNAL
// Events - When asserted high in a test that passes all verification checks, these coverage
//          properties indicate that a functional coverage event has been hit.
// ---------------------------------------------------------------------------------------------

// Read from group 0 one cycle after write to rank0 blocked by wtr_s
reg    e_wrcas_previous_cycle_rank0;
always @(posedge clk) e_wrcas_previous_cycle_rank0 <= #TCQ (wrCAS & (winRank == 2'b0));
wire   e_mc_rd_wr_000_wtr_s = rdReq[0] & (cmdRank[0*RKBITS+:RKBITS] == 2'b0) & (S_HEIGHT < 2)           // current read group 0 rank 0
                              & ~(prevGrW[ cmdRank[0*RKBITS+:RKBITS] ] == cmdGroup[0*2+:2])             // previous group in rank 0 different
                              & ~wtr_oks[ cmdRank[0*RKBITS+:RKBITS] ] & e_wrcas_previous_cycle_rank0;   // wtr_s not safe and write in previous cycle
always @(posedge clk) mc_rd_wr_000: if (~rst) cover property (e_mc_rd_wr_000_wtr_s);

// Read from group 3 one cycle after write to rank3 blocked by wtr_l
reg    e_wrcas_previous_cycle_rank3;
always @(posedge clk) e_wrcas_previous_cycle_rank3 <= #TCQ (wrCAS & (winRank == 2'b11));
wire   e_mc_rd_wr_001_wtr_l = rdReq[3] & (cmdRank[3*RKBITS+:RKBITS] == 2'b11) & (S_HEIGHT < 2)          // current read group 3 rank 3
                              &  (prevGrW[ cmdRank[3*RKBITS+:RKBITS] ] == cmdGroup[3*2+:2])             // previous group in rank 3 same
                              & ~wtr_okl[ cmdRank[3*RKBITS+:RKBITS] ] & e_wrcas_previous_cycle_rank3;   // wtr_l not safe and write in previous cycle
always @(posedge clk) mc_rd_wr_001: if (~rst) cover property (e_mc_rd_wr_001_wtr_l);

// Read after write with minimum wtr_s timing in group 1
reg       e_rdreq_blocked_previous_cycle_group1;
reg [1:0] e_rdreq_blocked_previous_cycle_group1_rank;
always @(posedge clk) e_rdreq_blocked_previous_cycle_group1      <= #TCQ ( rdReq[1] & ~rdReqT[1] );
always @(posedge clk) e_rdreq_blocked_previous_cycle_group1_rank <= #TCQ ( cmdRank[1*RKBITS+:RKBITS] );
wire   e_mc_rd_wr_002_wtr_s = rdReq[1] & rdReqT[1] & (S_HEIGHT < 2)                                 // current read safe
                              & e_rdreq_blocked_previous_cycle_group1                               // read blocked previous cycle
                              & ~(prevGrW[ cmdRank[1*RKBITS+:RKBITS] ] == cmdGroup[1*2+:2])                   // previous write group different
                              & ( cmdRank[1*RKBITS+:RKBITS] == e_rdreq_blocked_previous_cycle_group1_rank );  // current and previous read to same rank
always @(posedge clk) mc_rd_wr_002: if (~rst) cover property (e_mc_rd_wr_002_wtr_s);

// Read after write with minimum wtr_l timing in group 2
reg       e_rdreq_blocked_previous_cycle_group2;
reg [1:0] e_rdreq_blocked_previous_cycle_group2_rank;
always @(posedge clk) e_rdreq_blocked_previous_cycle_group2      <= #TCQ ( rdReq[2] & ~rdReqT[2] );
always @(posedge clk) e_rdreq_blocked_previous_cycle_group2_rank <= #TCQ ( cmdRank[2*RKBITS+:RKBITS] );
wire   e_mc_rd_wr_003_wtr_l = rdReq[2] & rdReqT[2] & (S_HEIGHT < 2)                                 // current read safe
                              & e_rdreq_blocked_previous_cycle_group2                               // read blocked previous cycle
                              &  (prevGrW[ cmdRank[2*RKBITS+:RKBITS] ] == cmdGroup[2*2+:2])                   // previous write group same
                              & ( cmdRank[2*RKBITS+:RKBITS] == e_rdreq_blocked_previous_cycle_group2_rank );  // current and previous read to same rank
always @(posedge clk) mc_rd_wr_003: if (~rst) cover property (e_mc_rd_wr_003_wtr_l);

// Read after write with minimum wtr to different ranks
wire   e_mc_rd_wr_004_wtr = wrCAS
                            & (   ( rdReqT[0] & ~(winRank == cmdRank[0*RKBITS+:RKBITS]) )
                                | ( rdReqT[1] & ~(winRank == cmdRank[1*RKBITS+:RKBITS]) )
                                | ( rdReqT[2] & ~(winRank == cmdRank[2*RKBITS+:RKBITS]) )
                                | ( rdReqT[3] & ~(winRank == cmdRank[3*RKBITS+:RKBITS]) ) );
always @(posedge clk) mc_rd_wr_004: if (~rst) cover property (e_mc_rd_wr_004_wtr);

// Write one cycle after read blocked by rdCAS
wire   e_mc_rd_wr_005_rtw = rdCAS & ( | wrReq ) & ~( | wrReqT ) & rtw_okr;
always @(posedge clk) mc_rd_wr_005: if (~rst) cover property (e_mc_rd_wr_005_rtw);

// Write after read with minimum timing
reg     e_wrreq_blocked_previous_cycle;
always @(posedge clk)  e_wrreq_blocked_previous_cycle <= #TCQ ( ( | wrReq ) & ~( | wrReqT ) );
wire   e_mc_rd_wr_006_rtw = ( | wrReq ) & ( | wrReqT ) & e_wrreq_blocked_previous_cycle;
always @(posedge clk) mc_rd_wr_006: if (~rst) cover property (e_mc_rd_wr_006_rtw);

// Write after read with minimum timing and delayed by rtw counter
reg     e_wrreq_blocked_previous_cycle_counter;
always @(posedge clk)  e_wrreq_blocked_previous_cycle_counter <= #TCQ ( ( | wrReq ) & ~( | wrReqT ) & ~rdCAS & ~rtw_okr );
wire   e_mc_rd_wr_007_rtw = ( | wrReq ) & ( | wrReqT ) & e_wrreq_blocked_previous_cycle_counter;
always @(posedge clk) mc_rd_wr_007: if (~rst) cover property (e_mc_rd_wr_007_rtw);

// Read after write to different LR's in 3ds blocked by wtr_oks
wire   e_mc_rd_wr_008_wtr = wrCAS & (S_HEIGHT > 1)
                            & (   ( rdReqT[0] & (winRank == cmdRank[0*RKBITS+:RKBITS]) & ~(winLRank == cmdLRank[0*LR_WIDTH+:LR_WIDTH]) )
                                | ( rdReqT[1] & (winRank == cmdRank[1*RKBITS+:RKBITS]) & ~(winLRank == cmdLRank[1*LR_WIDTH+:LR_WIDTH]) )
                                | ( rdReqT[2] & (winRank == cmdRank[2*RKBITS+:RKBITS]) & ~(winLRank == cmdLRank[2*LR_WIDTH+:LR_WIDTH]) )
                                | ( rdReqT[3] & (winRank == cmdRank[3*RKBITS+:RKBITS]) & ~(winLRank == cmdLRank[3*LR_WIDTH+:LR_WIDTH]) ));
always @(posedge clk) mc_rd_wr_008: if (~rst) cover property (e_mc_rd_wr_008_wtr);

// Read from group 3 one cycle after write to rank3 blocked by wtr_l in 3ds
wire   e_mc_rd_wr_009_wtr_l = rdReq[3] & (cmdRank[3*RKBITS+:RKBITS] == 2'b11) & (S_HEIGHT > 1)          // current read group 3 rank 3
                              &  (prevGrW[cmdRank[3*RKBITS+:RKBITS]] == cmdGroup[3*2+:2])               // previous group in rank 3 same
                              &  (prevLRW[cmdRank[3*RKBITS+:RKBITS]] == cmdLRank[3*LR_WIDTH+:LR_WIDTH]) // previous LR in rank 3 same 
                              & ~wtr_okl[cmdRank[3*RKBITS+:RKBITS]] & e_wrcas_previous_cycle_rank3;     // wtr_l not safe and write in previous cycle
always @(posedge clk) mc_rd_wr_009: if (~rst) cover property (e_mc_rd_wr_009_wtr_l);

// Read after write in group 1 blocked by wtr_l in 3ds
reg [1:0] e_wrcas_previous_win_rank;
always @(posedge clk) e_wrcas_previous_win_rank <= #TCQ (wrCAS) ? winRank : e_wrcas_previous_win_rank;
wire   e_mc_rd_wr_010_wtr_l = rdReq[1] & (cmdRank[1*RKBITS+:RKBITS] == e_wrcas_previous_win_rank) & (S_HEIGHT > 1)   // current read group 1 rank
                              &  (prevGrW[cmdRank[1*RKBITS+:RKBITS]] == cmdGroup[1*2+:2])                            // previous group is 1 for selected rank
                              &  (prevLRW[cmdRank[1*RKBITS+:RKBITS]] == cmdLRank[3*LR_WIDTH+:LR_WIDTH])              // previous LR is same for selected rank for group 1
                              & ~wtr_okl[cmdRank[1*RKBITS+:RKBITS]] & e_wrcas_previous_win_rank == cmdRank[1*RKBITS+:RKBITS];  // wtr_l not safe and write in previous cycle
always @(posedge clk) mc_rd_wr_010: if (~rst) cover property (e_mc_rd_wr_010_wtr_l);

// Asserts - When asserted high, an illegal condition has been detected and the test has failed.
// ---------------------------------------------------------------------------------------------

// Read one cycle after write to same rank
wire   a_mc_rd_wr_000_wtr = wrCAS
                            & (   ( rdReqT[0] & (winRank == cmdRank[0*RKBITS+:RKBITS]) )
                                | ( rdReqT[1] & (winRank == cmdRank[1*RKBITS+:RKBITS]) )
                                | ( rdReqT[2] & (winRank == cmdRank[2*RKBITS+:RKBITS]) )
                                | ( rdReqT[3] & (winRank == cmdRank[3*RKBITS+:RKBITS]) ) );
always @(posedge clk) if (~rst) assert property (~a_mc_rd_wr_000_wtr);

// Write one cycle after read
wire   a_mc_rd_wr_001_rtw = rdCAS & ( | wrReqT );
always @(posedge clk) if (~rst) assert property (~a_mc_rd_wr_001_rtw);

// tRTW overflow
wire   a_mc_rd_wr_002_rtw = ( ( tRTW + 5 ) / 4 ) > 7;
always @(posedge clk) if (~rst) assert property (~a_mc_rd_wr_002_rtw);


`endif

//synopsys translate_on

endmodule

