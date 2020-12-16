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
//  /   /         Filename           : ddr4_v2_2_10_mc_arb_c.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                   ddr4_v2_2_10_mc_arb_c module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ns/100ps

module ddr4_v2_2_10_mc_arb_c #(parameter
    TCQ = 0.1   
   ,RKBITS = 2
   ,RANK_SLAB = 4
   ,S_HEIGHT = 1
   ,LR_WIDTH = 1
   ,ORDERING  = "NORM"
)(
    input        clk
   ,input        rst

   ,output reg [1:0] winPortEnc
   ,output reg [3:0] winPort
   ,output reg       winRead
   ,output reg       winWrite
   ,output reg [1:0] win_bank_cas
   ,output reg [1:0] win_group_cas
   ,output     [LR_WIDTH-1:0] win_l_rank_cas
   ,output reg [RKBITS-1:0] win_rank_cas

   ,input  [3:0] cmdRmw
   ,input  [3:0] read
   ,input  [3:0] wrte
   ,input        tranSent
   ,input        useAdr
   ,input  [3:0] accept
   ,input        per_rd_accept

   ,input  [7:0] cmd_bank_cas
   ,input  [7:0] cmd_group_cas
   ,input  [4*LR_WIDTH-1:0] cmd_l_rank_cas
   ,input  [RKBITS*4-1:0] cmd_rank_cas
   ,input  [RKBITS*4-1:0] cmdRank
   ,input  [RKBITS*4-1:0] cmdRankP
   ,input  [3:0] preReqM
);

localparam STRICT_FULL_THRESH     = 20;
localparam STRICT_FIFO_DEPTH      = 32;
localparam STRICT_FIFO_PTR_WIDTH  =  5;

function [1:0] findWin;
   input       last;
   input [1:0] reqs;
casez (reqs)
   2'b01: findWin = 2'b01;
   2'b10: findWin = 2'b10;
   2'b11: findWin = last ? 2'b01 : 2'b10;
   default: findWin = 2'b00;
endcase
endfunction

// regs
reg       last;
reg       last10;
reg       last32;
reg       rdSlot;
reg [3:0] reqs; // wire-reg
reg [7:0] slotCnt;
reg [3:0] readM;
reg [3:0] wrteM;
reg [3:0] preMask;

// ------------------------------------------------------------
// Strict order
// ------------------------------------------------------------
// Each time a txn is accepted into a Group FSM, push the 4 bit
// Group accept vector into a FIFO.  The FIFO output will be
// used to determine which Group is allowed to issue a CAS.
reg  [3:0] strict_fifo[STRICT_FIFO_DEPTH-1:0];
reg  [3:0] strict_fifo_nxt[STRICT_FIFO_DEPTH-1:0];
reg  [STRICT_FIFO_PTR_WIDTH-1:0] strict_rptr;
reg  [STRICT_FIFO_PTR_WIDTH-1:0] strict_wptr;
reg  [STRICT_FIFO_PTR_WIDTH-1:0] strict_wptr2;
reg  [LR_WIDTH-1:0] win_l_rank_cas_int;
wire [3:0] win3210_strict;
wire [3:0] win3210_strict_rptr_en;

// Pop the strict order FIFO each time a CAS issues except when its
// an underfill read.
wire       strict_rptr_en      =  ( | win3210_strict_rptr_en ) & tranSent;
wire [STRICT_FIFO_PTR_WIDTH-1:0] strict_rptr_nxt     =  strict_rptr[STRICT_FIFO_PTR_WIDTH-1:0]                      // spyglass disable W164a
                                                        + { { STRICT_FIFO_PTR_WIDTH-1 { 1'b0 } }, strict_rptr_en };

// The order FIFO write port needs to be able to push 2 transactions at the same time.
// Group 0 can accept a periodic read on the same cycle that another Group can
// accept an NI txn.  The periodic read will be ordered after the NI txn.
wire       strict_wptr_en      =  ( ( | accept ) & useAdr ) | per_rd_accept;
wire       strict_wptr_en2     =  ( ( | accept ) & useAdr ) & per_rd_accept;
wire       strict_data_in_per  = ~( ( | accept ) & useAdr ) & per_rd_accept;
wire [STRICT_FIFO_PTR_WIDTH-1:0] strict_wptr_nxt     =  strict_wptr[STRICT_FIFO_PTR_WIDTH-1:0]                     // spyglass disable W164a
                                                        + { { STRICT_FIFO_PTR_WIDTH-2 { 1'b0 } }, strict_wptr_en2, ~strict_wptr_en2 & strict_wptr_en };
wire [STRICT_FIFO_PTR_WIDTH-1:0] strict_wptr2_nxt    =  strict_wptr_nxt[STRICT_FIFO_PTR_WIDTH-1:0] + { { STRICT_FIFO_PTR_WIDTH-1 { 1'b0 } }, 1'b1 };
wire [3:0] strict_fifo_data_in =  strict_data_in_per ? 4'b1 : accept;

always @(*) begin
  strict_fifo_nxt = strict_fifo;
  strict_fifo_nxt[ strict_wptr  ] = strict_wptr_en  ? strict_fifo_data_in : strict_fifo[ strict_wptr  ];
  strict_fifo_nxt[ strict_wptr2 ] = strict_wptr_en2 ?                4'b1 : strict_fifo[ strict_wptr2 ];
end

// Select strict arbitration winner based on order FIFO and available CAS requests.
// Pop the order FIFO based on the winner unless it is an underfill read.
wire [3:0] strict_fifo_output     = strict_fifo[ strict_rptr ];
assign     win3210_strict         = strict_fifo_output & ( readM | wrteM );
assign     win3210_strict_rptr_en = ( strict_fifo_output & ~cmdRmw & readM ) | ( strict_fifo_output & wrteM );

always @(posedge clk) if (rst) begin
  strict_rptr  <= #TCQ '0;
  strict_wptr  <= #TCQ '0;
  strict_wptr2 <= #TCQ '0;
end else begin
  strict_rptr  <= #TCQ strict_rptr_nxt;
  strict_wptr  <= #TCQ strict_wptr_nxt;
  strict_wptr2 <= #TCQ strict_wptr2_nxt;
end

always @(posedge clk) begin
  strict_fifo        <= #TCQ strict_fifo_nxt;
end


always @(*) begin
   preMask = 4'b0000; // ranks
   if (preReqM[0]) preMask[cmdRankP[RKBITS*1-1:RKBITS*0]] = 1'b1;
   if (preReqM[1]) preMask[cmdRankP[RKBITS*2-1:RKBITS*1]] = 1'b1;
   if (preReqM[2]) preMask[cmdRankP[RKBITS*3-1:RKBITS*2]] = 1'b1;
   if (preReqM[3]) preMask[cmdRankP[RKBITS*4-1:RKBITS*3]] = 1'b1;
end

always @(*) begin
   readM = read;
   if (preMask[cmdRank[RKBITS*1-1:RKBITS*0]]) readM[0] = 1'b0;
   if (preMask[cmdRank[RKBITS*2-1:RKBITS*1]]) readM[1] = 1'b0;
   if (preMask[cmdRank[RKBITS*3-1:RKBITS*2]]) readM[2] = 1'b0;
   if (preMask[cmdRank[RKBITS*4-1:RKBITS*3]]) readM[3] = 1'b0;
end

always @(*) begin
   wrteM = wrte;
   if (preMask[cmdRank[RKBITS*1-1:RKBITS*0]]) wrteM[0] = 1'b0;
   if (preMask[cmdRank[RKBITS*2-1:RKBITS*1]]) wrteM[1] = 1'b0;
   if (preMask[cmdRank[RKBITS*3-1:RKBITS*2]]) wrteM[2] = 1'b0;
   if (preMask[cmdRank[RKBITS*4-1:RKBITS*3]]) wrteM[3] = 1'b0;
end

always @(*) begin
   reqs = 4'b0;
   casez (1'b0)
      rdSlot: reqs = readM ? readM : wrteM;
      default: reqs = wrteM ? wrteM : readM;
   endcase
end

// wire-regs
reg [1:0] winner;
reg [1:0] w10;
reg [1:0] w32;
reg [3:0] win3210_reorder;

always @(*) begin
   w10 = findWin(last10, reqs[1:0]);
   w32 = findWin(last32, reqs[3:2]);
   winner = findWin(last, {|reqs[3:2], |reqs[1:0]});
   case (winner)
      2'b01:   win3210_reorder = {2'b00, w10};
      2'b10:   win3210_reorder = {w32, 2'b00};
      default: win3210_reorder = 4'b0000;
   endcase
end

// Select arbitration winner based on ordering mode
wire [3:0] win3210 = ( ORDERING == "STRICT" ) ? win3210_strict : win3210_reorder;

always @(posedge clk) if (rst) begin
   last <= 1'b0;
   last10 <= 1'b0;
   last32 <= 1'b0;
   rdSlot <= 1'b0;
   slotCnt <= 'b0;
   winPortEnc <= 2'b0;
   winPort <= 4'b0;
   winRead <= 1'b0;
   winWrite <= 1'b0;
   win_bank_cas  <= #TCQ 2'b0;
   win_group_cas <= #TCQ 2'b0;
   win_l_rank_cas_int <= #TCQ '0;
   win_rank_cas  <= #TCQ {RKBITS{1'b0}};
end else begin:arbing
   reg       nRdSlot;
   reg [7:0] nSlotCnt;
   nRdSlot = rdSlot;
   nSlotCnt = slotCnt - 1'b1;
   if (tranSent) casez (win3210)
      4'bzzz1: begin
         last <= #TCQ 1'b0;
         last10 <= #TCQ 1'b0;
         winPortEnc <= #TCQ 2'd0;
         winPort <= #TCQ win3210;
         {winRead, winWrite} <= #TCQ {readM[0], wrteM[0]};
         win_bank_cas        <= #TCQ cmd_bank_cas[1:0];
         win_group_cas       <= #TCQ cmd_group_cas[1:0];
         win_l_rank_cas_int  <= #TCQ cmd_l_rank_cas[0*LR_WIDTH+:LR_WIDTH];
         win_rank_cas        <= #TCQ cmd_rank_cas[RKBITS*1-1:RKBITS*0];
      end
      4'bzz1z: begin
         last <= #TCQ 1'b0;
         last10 <= #TCQ 1'b1;
         winPortEnc <= #TCQ 2'd1;
         winPort <= #TCQ win3210;
         {winRead, winWrite} <= #TCQ {readM[1], wrteM[1]};
         win_bank_cas        <= #TCQ cmd_bank_cas[3:2];
         win_group_cas       <= #TCQ cmd_group_cas[3:2];
         win_l_rank_cas_int  <= #TCQ cmd_l_rank_cas[1*LR_WIDTH+:LR_WIDTH];
         win_rank_cas        <= #TCQ cmd_rank_cas[RKBITS*2-1:RKBITS*1];
      end
      4'bz1zz: begin
         last <= #TCQ 1'b1;
         last32 <= #TCQ 1'b0;
         winPortEnc <= #TCQ 2'd2;
         winPort <= #TCQ win3210;
         {winRead, winWrite} <= #TCQ {readM[2], wrteM[2]};
         win_bank_cas        <= #TCQ cmd_bank_cas[5:4];
         win_group_cas       <= #TCQ cmd_group_cas[5:4];
         win_l_rank_cas_int  <= #TCQ cmd_l_rank_cas[2*LR_WIDTH+:LR_WIDTH];
         win_rank_cas        <= #TCQ cmd_rank_cas[RKBITS*3-1:RKBITS*2];
      end
      4'b1zzz: begin
         last <= #TCQ 1'b1;
         last32 <= #TCQ 1'b1;
         winPortEnc <= #TCQ 2'd3;
         winPort <= #TCQ win3210;
         {winRead, winWrite} <= #TCQ {readM[3], wrteM[3]};
         win_bank_cas        <= #TCQ cmd_bank_cas[7:6];
         win_group_cas       <= #TCQ cmd_group_cas[7:6];
         win_l_rank_cas_int  <= #TCQ cmd_l_rank_cas[3*LR_WIDTH+:LR_WIDTH];
         win_rank_cas        <= #TCQ cmd_rank_cas[RKBITS*4-1:RKBITS*3];
      end
      default:begin
         winPortEnc <= #TCQ 2'd0;
         winPort <= #TCQ 4'b0000;
         {winRead, winWrite} <= #TCQ 2'b0;
         win_bank_cas        <= #TCQ 2'b0;
         win_group_cas       <= #TCQ 2'b0;
         win_l_rank_cas_int  <= #TCQ '0;
         win_rank_cas        <= #TCQ {RKBITS{1'b0}};
      end
   endcase
   rdSlot <= #TCQ nRdSlot;
   slotCnt <= #TCQ nSlotCnt;
end

generate
  if (S_HEIGHT > 1)
    assign win_l_rank_cas = win_l_rank_cas_int;
  else
    assign win_l_rank_cas = '0;
endgenerate

//synopsys translate_off

`ifdef MEM_INTERNAL
// Events - When asserted high in a test that passes all verification checks, these coverage
//          properties indicate that a functional coverage event has been hit.
// ---------------------------------------------------------------------------------------------

// Strict fifo half full
wire   e_mc_arb_c_000_str = ( ( strict_wptr - strict_rptr ) > STRICT_FULL_THRESH/2 ) & ( ORDERING == "STRICT" );
always @(posedge clk) mc_arb_a_000: if (~rst) cover property (e_mc_arb_c_000_str);

// Strict fifo 4 below full
wire   e_mc_arb_c_001_str = ( ( strict_wptr - strict_rptr ) == ( STRICT_FULL_THRESH - 4 ) ) & ( ORDERING == "STRICT" );
always @(posedge clk) mc_arb_a_001: if (~rst) cover property (e_mc_arb_c_001_str);

// Strict fifo 3 below full
wire   e_mc_arb_c_002_str = ( ( strict_wptr - strict_rptr ) == ( STRICT_FULL_THRESH - 3 ) ) & ( ORDERING == "STRICT" );
always @(posedge clk) mc_arb_a_002: if (~rst) cover property (e_mc_arb_c_002_str);

// Strict fifo 2 below full
wire   e_mc_arb_c_003_str = ( ( strict_wptr - strict_rptr ) == ( STRICT_FULL_THRESH - 2 ) ) & ( ORDERING == "STRICT" );
always @(posedge clk) mc_arb_a_003: if (~rst) cover property (e_mc_arb_c_003_str);

// Strict fifo 1 below full
wire   e_mc_arb_c_004_str = ( ( strict_wptr - strict_rptr ) == ( STRICT_FULL_THRESH - 1 ) ) & ( ORDERING == "STRICT" );
always @(posedge clk) mc_arb_a_004: if (~rst) cover property (e_mc_arb_c_004_str);

// Strict fifo full
wire   e_mc_arb_c_005_str = ( ( strict_wptr - strict_rptr ) == ( STRICT_FULL_THRESH ) ) & ( ORDERING == "STRICT" );
always @(posedge clk) mc_arb_a_005: if (~rst) cover property (e_mc_arb_c_005_str);

// System transaction and periodic read pushed into strict fifo on the same cycle
wire   e_mc_arb_c_006_str = strict_wptr_en & strict_wptr_en2 & ( ORDERING == "STRICT" );
always @(posedge clk) mc_arb_a_006: if (~rst) cover property (e_mc_arb_c_006_str);

// Strict fifo pop blocked due to RMW
wire   e_mc_arb_c_007_str = ( strict_fifo_output & cmdRmw & readM ) & tranSent & ( ORDERING == "STRICT" );
always @(posedge clk) mc_arb_a_007: if (~rst) cover property (e_mc_arb_c_007_str);

// Delay win3210 for comparison to winPort
reg  [3:0] win3210_dly;
always @(posedge clk) begin
  win3210_dly <= #TCQ win3210;
end

// winRead held due to tranSent de-assertion
wire   e_mc_arb_c_008_hld = ( | winPort ) & ( | win3210_dly ) & ( | ( winPort ^ win3210_dly ) ) & winRead;
always @(posedge clk) mc_arb_a_008: if (~rst) cover property (e_mc_arb_c_008_hld);

// winWrite held due to tranSent de-assertion
wire   e_mc_arb_c_009_hld = ( | winPort ) & ( | win3210_dly ) & ( | ( winPort ^ win3210_dly ) ) & winWrite;
always @(posedge clk) mc_arb_a_009: if (~rst) cover property (e_mc_arb_c_009_hld);



// Asserts - When asserted high, an illegal condition has been detected and the test has failed.
// ---------------------------------------------------------------------------------------------

// Illegal cas command in strict mode due to empty ordering fifo.
wire a_mc_arb_c_000_ill = ( | ( readM | wrteM ) ) & ( strict_wptr == strict_rptr ) & tranSent & ( ORDERING == "STRICT" );
always @(posedge clk) if (~rst) assert property (~a_mc_arb_c_000_ill);

// Strict fifo overflow
wire [STRICT_FIFO_PTR_WIDTH-1:0] a_strict_ptr_diff = ( strict_wptr - strict_rptr );
wire a_mc_arb_c_001_of = ( a_strict_ptr_diff >= ( STRICT_FULL_THRESH + 1 ) ) & ( ORDERING == "STRICT" );
always @(posedge clk) if (~rst) assert property (~a_mc_arb_c_001_of);

// System transaction and periodic read both target Group FSM 0 in strict mode
wire a_mc_arb_c_002_per = strict_wptr_en2 & ( accept == 4'b1 ) & ( ORDERING == "STRICT" );
always @(posedge clk) if (~rst) assert property (~a_mc_arb_c_002_per);

// Winner select one hot cold counter
integer group_index;
reg  [2:0] a_win3210_count;
always @(*) begin
  a_win3210_count = 3'b0;
  for (group_index = 0; group_index <= 3; group_index++) begin
    a_win3210_count += win3210[group_index];
  end
end

// Winner one hot cold check failed in strict mode
wire a_mc_arb_c_003_1hc = tranSent & ( a_win3210_count > 3'b1 ) & ( ORDERING == "STRICT" );
always @(posedge clk) if (~rst) assert property (~a_mc_arb_c_003_1hc);

// Winner one hot cold check failed in normal mode
wire a_mc_arb_c_004_1hc = ( a_win3210_count > 3'b1 ) & ~( ORDERING == "STRICT" );
always @(posedge clk) if (~rst) assert property (~a_mc_arb_c_004_1hc);

// At least one Group FSM arbitrating for both read and write
wire a_mc_arb_c_005_grp = | ( readM & wrteM );
always @(posedge clk) if (~rst) assert property (~a_mc_arb_c_005_grp);



`endif

//synopsys translate_on


endmodule


