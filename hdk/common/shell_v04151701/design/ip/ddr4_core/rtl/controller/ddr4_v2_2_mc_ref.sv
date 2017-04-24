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
//  /   /         Filename           : ddr4_v2_2_0_mc_ref.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                   ddr4_v2_2_0_mc_ref module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ns/100ps

module ddr4_v2_2_0_mc_ref #(parameter
    NUMREF = 1
   ,RANKS  = 1
   ,RANK_SLOT = 1
   ,LR_WIDTH = 3
   ,S_HEIGHT = 8
   ,tREFI  = 1300
   ,tRFC   = 27
   ,tRFC_dlr = 9
   ,tRP    = 15
   ,tWR    = 12
   ,ZQINTVL = 58960
   ,tZQCS   = 128
   ,TCQ    = 0.1
   ,REG_CTRL  = "OFF"
   ,PARTIAL_RECONFIG = "Enable"
)(
    input clk
   ,input rst

   ,output           preIss
   ,output           refIss
   ,output           zqIss
   ,output           zqIssAll
   ,output     [1:0] refRank
   ,output [LR_WIDTH-1:0] refLRank
   ,output           refReq
   ,output           ref_ack
   ,output           zq_ack

   ,input       calDone
   ,input [3:0] refOK
   ,input [5:0] tCWL
   ,input       per_block_ref
   ,input       ref_req
   ,input       zq_req

   ,input       sre_req
   ,output reg  sre_ack
   ,input       ui_busy
   ,input [3:0] txn_fifo_empty
   ,input [3:0] cas_fifo_empty
   ,output      mc_block_req
   ,output reg  int_sreIss
   ,output reg  [RANKS-1:0] int_sreCkeDis
   ,input       stop_gate_tracking_ack
   ,output      stop_gate_tracking_req
   ,input       srx_cke0_release
   ,input       srx_req
   ,output      cmd_complete
   ,output reg  int_srxIss
   ,output reg  [2:0] dbg_sre_sm_ps
   ,output reg  [3:0] dbg_refSt
   ,output reg  [7:0] mcCKt
   ,output reg  [7:0] mcCKc
);

function [1:0] nextRank;
   input [1:0] rank;
   nextRank = ((rank + 1) == RANKS) ? 0 : (rank + 1'b1);
endfunction

function [LR_WIDTH-1:0] nextLRank;
   input [LR_WIDTH-1:0] l_rank;
   nextLRank = ((l_rank + 1) == S_HEIGHT) ? 0 : (l_rank + 1'b1);
endfunction

reg  [9:0] cntr;
reg  [3:0] refs;
reg  [3:0] refSt;
reg  [3:0] retSt;
reg [14:0] refi[RANKS-1:0];
reg        int_refReq;
reg        int_preIss;
reg        int_refIss;
reg        int_zqIss;
reg  [1:0] int_refRank;
reg  [LR_WIDTH-1:0] int_refLRank;

// ZQCS signals
reg  [1:0]       zq_rank;
reg  [15:0]      zq_intvl_count;
reg  [RANKS-1:0] zq_pending;

// USER_MODE signals
reg        ref_req_ff;
reg        zq_req_ff;
reg  [3:0] user_fsm;
reg  [3:0] user_fsm_nxt;
reg  [9:0] um_wait_cntr;
reg  [9:0] um_wait_cntr_init;
reg        um_wait_cntr_start;
reg        um_ref_req;
reg        set_um_ref_req;
reg        clear_um_ref_req;
reg        um_pre_iss_nxt;
reg        um_pre_iss;
reg        um_ref_iss_nxt;
reg        um_ref_iss;
reg        init_um_rank_cntr;
reg        inc_um_rank_cntr;
reg [1:0]  um_rank_cntr;
reg        init_um_l_rank_cntr;
reg        inc_um_l_rank_cntr;
reg [LR_WIDTH-1:0]  um_l_rank_cntr;
reg        um_ref_ack;
reg        um_ref_ack_nxt;
reg        um_zq_ack;
reg        um_zq_ack_nxt;
reg        um_zq_iss;
reg        um_zq_iss_nxt;
reg        um_zq_iss_all;
reg        um_zq_iss_all_nxt;

localparam tREFIFR = tREFI/(4*RANKS);

localparam tREFIF = (tREFIFR*RANKS)-1;

localparam USER_MODE = (tREFI == 0);

localparam ZQINTVLREF = (USER_MODE == 1)
                        ? 0 
			: (( ZQINTVL/tREFI <     2 ) ? 2 :
                           ( ZQINTVL/tREFI > 65535 ) ? 65535 : ZQINTVL/tREFI) ;

localparam ALL_RANKS = 1'b1;

localparam tSTAG = tRFC/2;

localparam
    stRST  = 4'b0000
   ,stTWDL = 4'b0001
   ,stREQ  = 4'b0010
   ,stWAIT = 4'b0011
   ,stPRE  = 4'b0100
   ,stREF  = 4'b0101
   ,stRFC  = 4'b0110
   ,stRFCE = 4'b0111
   ,stZQ   = 4'b1000
   ,stSRE  = 4'b1001 // SRE state. Will loop through this state until all Ranks are in SR.
   ,stSR   = 4'b1010 // SR state. After SRE is issued, internal refresh machine will be stuck in this state
   ,stSRX  = 4'b1011
   ,stERR  = 4'b1111
;

localparam
   UM_IDLE       = 4'd0
  ,UM_ACK_WAIT   = 4'd1
  ,UM_WR_WAIT    = 4'd2
  ,UM_PRE        = 4'd3
  ,UM_PRE_CHECK  = 4'd4
  ,UM_PRE_WAIT   = 4'd5
  ,UM_REF        = 4'd6
  ,UM_REF_CHECK  = 4'd7
  ,UM_STAG_WAIT  = 4'd8
  ,UM_TRFC_WAIT  = 4'd9
  ,UM_ZQ         = 4'd10
  ,UM_ZQ_CHECK   = 4'd11
  ,UM_ZQ_WAIT    = 4'd12
  ,UM_ZQ_ALL     = 4'd13
  ,UM_TZQCS_WAIT = 4'd14
;

// Per rank pending refresh counter
reg  [RANKS-1:0]  inc_pend_ref;
reg  [3:0]        pend_ref[RANKS-1:0];

localparam tRFCWAIT_TEMP = ( tRFC + 3 ) / 4;
localparam tRFCWAIT      = ( ( tRFCWAIT_TEMP - 8 ) > 0 ) ? ( tRFCWAIT_TEMP - 8 ) : 0;
localparam tRPWAIT_TEMP  = ( tRP + 3 ) / 4;
localparam tRPWAIT       = ( ( tRPWAIT_TEMP - 2 ) > 0 ) ? ( tRPWAIT_TEMP - 2 ) : 0;
wire [6:0] tWRWAIT_temp  = ( tCWL + 6'd4 + tWR[5:0] + 6'd3) / 4;
wire [9:0] tWRWAIT       = ( ( tWRWAIT_temp - 7'd4 ) > '0 ) ? { 3'b0, ( tWRWAIT_temp - 7'd4 ) } : '0;
wire [9:0] tZQCSF        = ( tZQCS + 3 ) / 4;  // spyglass disable W164c

integer i;

// ==================================================================
// Clock stopped power down mode for RCD
// ==================================================================
localparam TCKOFF = 15;  //tCKoff = 5 + CLA(max. 4)
localparam TCKEV  = 15;  //tCKEV = max 8
reg [3:0] tckoff_timer;
reg [3:0] tckev_timer;
wire sre_issued;
reg  sre_issued_r;
wire sre_tckoff_ok;
reg  sre_tckoff_ok_r;
wire sre_tckev_ok;

always @(posedge clk)
  sre_issued_r <= #TCQ sre_issued;
always @(posedge clk) begin
  if (rst)
    tckoff_timer <= 4'b0;
  else if (sre_issued && (!sre_issued_r))
    tckoff_timer <= TCKOFF-1;
  else if (tckoff_timer > 0)
    tckoff_timer <= tckoff_timer-1;
end
assign sre_tckoff_ok = (tckoff_timer == 0) ? sre_issued_r : 0 ;

always @(posedge clk)
  sre_tckoff_ok_r <= #TCQ sre_tckoff_ok;
always @(posedge clk) begin
  if (rst)
    tckev_timer <= 4'b0;
  else if (sre_tckoff_ok && (!sre_tckoff_ok_r))
    tckev_timer <= TCKEV-1;
  else if (tckev_timer > 0)
    tckev_timer <= tckev_timer-1;
end
assign sre_tckev_ok = (tckev_timer == 0) ? sre_tckoff_ok_r : 0 ;

// Driving sre_ack and memory clocks
assign sre_ack = ((REG_CTRL == "ON") && (PARTIAL_RECONFIG == "Enable")) ? sre_tckev_ok : sre_issued ;
always @(posedge clk) begin
  if (sre_tckoff_ok && (PARTIAL_RECONFIG == "Enable")) begin
    mcCKt <= #TCQ 8'b0;
    mcCKc <= #TCQ 8'b0;
  end else begin
    mcCKt <= #TCQ 8'b01010101;
    mcCKc <= #TCQ 8'b10101010;
  end
end

   // ==================================================================
   // Self Refresh support
   // ==================================================================
   // This new code is added for IBM Self Refresh support.
   // When Self Refresh Entry (SRE) request is received, the request is flopped.
   // When the next scheduled refresh is issued, the refresh command is modified to SRE.
   // Note: SRE is supporting single rank design only.
   localparam SRE_SM_IDLE     = 3'd0;
   localparam SRE_SM_REQ      = 3'd1;
   localparam SRE_SM_VT_STOP  = 3'd2;
   localparam SRE_SM_MC_CHK   = 3'd3;
   localparam SRE_SM_REF_REQ  = 3'd4;
   localparam SRE_SM_ISS      = 3'd5;
   localparam SRE_SM_WAIT     = 3'd6;
   localparam SRE_SM_DONE     = 3'd7;
   
   reg [2:0] sre_sm_ps;
   reg [2:0] sre_sm_ns;
   reg [4:0] ui_mc_idle_cnt;
   reg [4:0] sre_wait_cnt;
   
   // Added for IBM Self Refresh. Denote MC does not have outstanding transaction in txn fifo nor cas fifo
   reg      mc_busy; 
   reg      ui_busy_r;
   reg [3:0] txn_fifo_empty_r;
   reg [3:0] cas_fifo_empty_r;
   reg      sre_req_r;
   reg      sre_req_lpulse;

   // Creating a long pulse for the self-refresh request
   always @(posedge clk) begin
      sre_req_r <= #TCQ sre_req;
      if (rst)
         sre_req_lpulse <= #TCQ 1'b0;
      else if (~sre_req_r & sre_req)
         sre_req_lpulse <= #TCQ 1'b1;
   end

   wire arc_SRE_SM_IDLE_REQ        = sre_req_lpulse;
   wire arc_SRE_SM_REQ_VT_STOP     = stop_gate_tracking_ack;
   wire arc_SRE_SM_VT_STOP_MC_CHK  = ~mc_busy;
   wire arc_SRE_SM_MC_CHK_REF_REQ  = & ui_mc_idle_cnt;
   wire arc_SRE_SM_REF_REQ_ISS     = (refSt == stREQ);
   wire arc_SRE_SM_ISS_WAIT        = (refSt == stSR);
   wire arc_SRE_SM_WAIT_DONE       = & sre_wait_cnt;
   wire arc_SRE_SM_DONE_IDLE       = srx_req | srx_cke0_release;
   
   assign cmd_complete = arc_SRE_SM_VT_STOP_MC_CHK;

   always @(posedge clk) begin
      if (rst) begin
	 ui_busy_r        <= #TCQ 'h0;
	 txn_fifo_empty_r <= #TCQ 'h0;
	 cas_fifo_empty_r <= #TCQ 'h0;
	 mc_busy          <= #TCQ 'h0;
      end
      else begin
	 ui_busy_r        <= #TCQ ui_busy;
	 txn_fifo_empty_r <= #TCQ txn_fifo_empty;
	 cas_fifo_empty_r <= #TCQ cas_fifo_empty;      
	 mc_busy <= #TCQ !(&txn_fifo_empty_r) || !(&cas_fifo_empty_r) || ui_busy_r;
      end
   end

   always @(posedge clk) begin
      if (rst) begin
	 sre_sm_ps <= #TCQ SRE_SM_IDLE;
      end
      else begin
	 sre_sm_ps <= #TCQ sre_sm_ns;
      end
   end

   always @(*) begin
      casez (sre_sm_ps)
	SRE_SM_IDLE: begin
	   sre_sm_ns = arc_SRE_SM_IDLE_REQ ? SRE_SM_REQ : SRE_SM_IDLE;
	end
	SRE_SM_REQ: begin
	   sre_sm_ns = arc_SRE_SM_REQ_VT_STOP ? SRE_SM_VT_STOP : SRE_SM_REQ;
	end
	SRE_SM_VT_STOP: begin
	   sre_sm_ns = arc_SRE_SM_VT_STOP_MC_CHK ? SRE_SM_MC_CHK : SRE_SM_VT_STOP;
	end
	SRE_SM_MC_CHK: begin
	   sre_sm_ns = arc_SRE_SM_MC_CHK_REF_REQ ? SRE_SM_REF_REQ : SRE_SM_MC_CHK;
	end
	SRE_SM_REF_REQ: begin
	   sre_sm_ns = arc_SRE_SM_REF_REQ_ISS ? SRE_SM_ISS : SRE_SM_REF_REQ;
	end
	SRE_SM_ISS: begin
	   sre_sm_ns = arc_SRE_SM_ISS_WAIT ? SRE_SM_WAIT : SRE_SM_ISS;
	end
	SRE_SM_WAIT: begin
	   sre_sm_ns = arc_SRE_SM_WAIT_DONE ? SRE_SM_DONE : SRE_SM_WAIT;
	end
	SRE_SM_DONE: begin
	   sre_sm_ns = arc_SRE_SM_DONE_IDLE ? SRE_SM_IDLE : SRE_SM_DONE;
	end
	default: begin
	   sre_sm_ns = SRE_SM_DONE;
	end
      endcase
   end

   //assign mc_block_req           = sre_req_bk || (sre_sm_ps != SRE_SM_IDLE);
   assign mc_block_req           = 0 ;
   assign stop_gate_tracking_req = (sre_sm_ps != SRE_SM_IDLE);
   //assign sre_ack                = arc_SRE_SM_WAIT_DONE;
   assign sre_issued             = arc_SRE_SM_WAIT_DONE;

   always @(posedge clk) begin
      if (rst || mc_busy || srx_cke0_release) begin
	 ui_mc_idle_cnt <= #TCQ 'h0;
      end
      else if ((sre_sm_ps == SRE_SM_MC_CHK) && (ui_mc_idle_cnt != 5'b11111)) begin
	    ui_mc_idle_cnt <= #TCQ ui_mc_idle_cnt + 'h1;
      end
   end   

   always @(posedge clk) begin
      if (rst || (sre_sm_ps == SRE_SM_IDLE) || srx_cke0_release) begin
	 sre_wait_cnt <= #TCQ 'h0;
      end
      else if ((sre_sm_ps == SRE_SM_WAIT) && (sre_wait_cnt != 5'b11111)) begin
	    sre_wait_cnt <= #TCQ sre_wait_cnt + 'h1;
      end
   end   

   assign dbg_sre_sm_ps = sre_sm_ps;
   assign dbg_refSt     = refSt;
   
// ==================================================================
// Internal Periodic Refresh and ZQCS
// ==================================================================
// The refresh block has two modes, USER_MODE and internal periodic refresh/ZQ.
// In USER_MODE refreshes and ZQCS insertion is determined by input signals at the NI.
// In internal periodic mode refreshes and ZQCS are inserted when free running
// timers expire.  There is a separe FSM for each mode to control the refresh/ZQ flow.


// ==================================================================
// Outputs - Select between USER_MODE and Internal Periodic Signals
// ==================================================================
assign refReq      = USER_MODE ? um_ref_req   : int_refReq;
assign preIss      = USER_MODE ? um_pre_iss   : int_preIss;
assign refIss      = USER_MODE ? um_ref_iss   : int_refIss;
assign zqIss       = USER_MODE ? um_zq_iss    : int_zqIss;
assign zqIssAll    = um_zq_iss_all;
assign refRank     = USER_MODE ? um_rank_cntr : int_refRank;
assign refLRank    = USER_MODE ? um_l_rank_cntr : int_refLRank;
assign ref_ack     = um_ref_ack;
assign zq_ack      = um_zq_ack;



// ==================================================================
// Handshake with periodic read module and refresh interval counters
// ==================================================================
// If the periodic read module wants to inject a txn into a Group FSM, it will
// first attempt to prevent the refresh FSMs from asserting refReq.  If refReq
// asserts anyway, the periodic module will wait for refReq to de-assert and
// then try to block refReq again.
// The internal periodic refresh logic will count any tREFI intervals that elapse
// while refReq is blocked and service the refreshes when the block is de-asserted.
// To make sure that refresh intervals are not missed, the interval counter and pending refresh
// counter is implented separately from the refresh FSMs.

// Free running per rank refresh interval counter.
// Reset values staggered.  Decrements continuously after calDone assertion.
// Disabled in USER_MODE.
reg  [14:0]       refi_nxt[RANKS-1:0];
reg  [RANKS-1:0]  inc_pend_ref_due;
reg  [RANKS-1:0]  inc_pend_ref_nxt;
reg  [RANKS-1:0]  err_pend_ref;

// Per rank pending refresh counter.  Increment when refresh interval counter reaches zero and
// decrement when the precharge command in the refresh flow is issued.
reg  [4:0]  pend_ref_nxt [RANKS-1:0];

always @(*) begin
   for (i = 0; i < RANKS; i = i + 1)  inc_pend_ref_due[i] = ~USER_MODE & ( refi[i] == '0 );
   for (i = 0; i < RANKS; i = i + 1)  inc_pend_ref_nxt[i] = inc_pend_ref_due[i] & ~( & pend_ref[i] );
   for (i = 0; i < RANKS; i = i + 1)  err_pend_ref[i]     = inc_pend_ref_due[i] &  ( & pend_ref[i] );
   for (i = 0; i < RANKS; i = i + 1)  refi_nxt[i]         = { 15 { ~USER_MODE } } & ( ( refi[i] == '0 ) ? tREFIF : ( refi[i] - { 14'b0, calDone } ) );
   for (i = 0; i < RANKS; i = i + 1)  pend_ref_nxt[i]     = (refSt == stSRE || refSt == stSR) ? 5'd2 : 
	    ( pend_ref[i] + { 3'b0, inc_pend_ref[i] } ) - { 3'b0, ( int_refRank == i ) & int_preIss & (~|int_refLRank)};
end

// Refresh interval and pending refresh flops
always @(posedge clk) begin
  if (rst || srx_cke0_release) begin
    for (i = 0; i < RANKS; i = i + 1) refi[i]      <= #TCQ ( (i+1)*tREFIFR);
    for (i = 0; i < RANKS; i = i + 1) pend_ref[i]  <= #TCQ '0;
                                      inc_pend_ref <= #TCQ '0;
  end else begin
    for (i = 0; i < RANKS; i = i + 1) refi[i]      <= #TCQ refi_nxt[i];
    for (i = 0; i < RANKS; i = i + 1) pend_ref[i]  <= #TCQ pend_ref_nxt[i][3:0];
                                      inc_pend_ref <= #TCQ inc_pend_ref_nxt;
  end
end

// ==================================================================
// ZQCS interval and pending counters 
// ==================================================================
// When not in USER_MODE, this section will generate staggard ZQCS,
// evenly spaced to each rank over the programmed ZQCS interval.
// The ZQCS interval is counted in refresh commands.  The local parameter
// ZQINTVLREF is the number of refreshes between ZQCS to the same rank.
// The output of this section is a per rank ZQCS pending flag.
// The refresh FSM will check the flag for the current refRank
// after refreshes are complete and issue a ZQCS if needed.

// ZQCS interval counter:
// Count down the number of refreshes between ZQCS.  Decrement the
// count when a refresh issues to any rank, and re-load the count
// when a ZQCS issues.  By counting refreshes to all ranks, and
// starting with a count equal to the number of refreshes between
// ZQCS to the same rank, we get the right spacing between ZQCS
// commands in a single rank config and for all multiple rank
// configs.
wire        zq_intvl_count_dec  = int_refIss;
wire        zq_intvl_load       = ~( | zq_intvl_count );
wire [15:0] zq_intvl_count_nxt  = zq_intvl_load                      // spyglass disable W164a
                                  ? { 1'b0, ZQINTVLREF[15:0] }
                                  : ( zq_intvl_count - { 15'b0, zq_intvl_count_dec } );

// ZQCS rank pointer:
// Increment the ZQCS rank pointer each time a ZQCS issues.
wire       wrap_zq_rank = ( zq_rank == (RANKS-1) ) & int_zqIss;
wire [1:0] zq_rank_nxt  = wrap_zq_rank ? '0 : ( zq_rank + { 1'b0, int_zqIss } ); // spyglass disable W164a

// Pending ZQCS pending tracker:
// Set the ZQCS pending flag for the current ZQCS rank pointer
// when the interval counter re-loads.  Clear the flag when
// when ZQCS issues to the refRank.
reg  [RANKS-1:0] set_zq_pending;
reg  [RANKS-1:0] clear_zq_pending;
always @(*) begin
  set_zq_pending                  = 4'b0;
  set_zq_pending  [ zq_rank ]     = zq_intvl_load;
  clear_zq_pending                = 4'b0;
  clear_zq_pending[ int_refRank ] = int_zqIss;
end
wire [RANKS-1:0] zq_pending_nxt   = ( zq_pending | set_zq_pending ) & ~( clear_zq_pending );




// ==================================================================
// Internal Periodic Refresh/ZQ FSM
// ==================================================================


always @(posedge clk) if (rst) begin
   int_preIss <= 1'b0;
   int_refIss <= 1'b0;
   int_sreIss <= 1'b0;
   int_sreCkeDis <= 4'b0;
   int_srxIss <= 1'b0;
   int_zqIss  <= 1'b0;
   int_refRank <= 2'b00;
   int_refLRank <= '0;
   int_refReq <= 1'b0;
   retSt <= 4'bxxxx;
   refSt <= stRST;
end else begin
   int_preIss <= #TCQ 1'b0;
   int_refIss <= #TCQ 1'b0;
   int_sreIss <= #TCQ 1'b0;
   //int_sreCkeDis <= #TCQ 4'b0;
   int_srxIss <= 1'b0;
   int_zqIss  <= #TCQ 1'b0;
   if (cntr) cntr <= #TCQ cntr - 1'b1;
   casez (refSt)
      stRST: begin
         if (calDone & ~USER_MODE) refSt <= #TCQ stREQ;
      end
      stTWDL: if (cntr == 0) refSt <= #TCQ retSt;
      // Start internal mode refresh flow unless blocked by periodic read or if
      // any group FSM is already asserting the refOK handshake.  Need to avoid looking
      // at a stale refOK signal after leaving stREQ.
      stREQ: if ( ( pend_ref[int_refRank] > 0 ) & ~per_block_ref & ~( | refOK ) ) begin
         int_refReq <= #TCQ 1'b1;
         refSt <= #TCQ stWAIT;
      end
      stWAIT: begin
         cntr <= #TCQ tWRWAIT;
         retSt <= #TCQ stPRE;
         if (refOK == 4'b1111) refSt <= #TCQ stTWDL;
      end
      stPRE: begin
         if (nextLRank(int_refLRank) == 0) begin 
           cntr <= #TCQ tRPWAIT;
           refs <= #TCQ NUMREF;
           retSt <= #TCQ stREF;
           refSt <= #TCQ stTWDL;
         end else begin 
           refSt <= #TCQ stPRE;
         end
         int_preIss <= #TCQ 1'b1;
         int_refLRank <= #TCQ nextLRank(int_refLRank);
      end
      stREF: begin
         if (nextLRank(int_refLRank) == 0) begin 
           // The last refresh before exiting does not wait the full tRFC to allow for handshake inefficiencies.
           // It is not known in the stREF state if ZQCS is required or not, so the stRFCE state will complete tRFC
           // if a ZQCS needs to be scheduled.
           cntr <= #TCQ sre_req_lpulse ? ((tRFC+3)/4) : ((refs == 1) ? tRFCWAIT : ((tRFC+3)/4));  // spyglass disable W164c
           refs <= #TCQ refs - 1'b1;
           retSt <= #TCQ (refs == 1) ? stRFCE : stREF;
         end else begin
           cntr <= #TCQ (tRFC_dlr + 3) / 4; // spyglass disable W164c
           retSt <= #TCQ stREF;
         end
         int_refIss <= #TCQ 1'b1;
	 //int_sreIss <= #TCQ (sre_sm_ps == SRE_SM_ISS);
         //refSt <= #TCQ (sre_sm_ps == SRE_SM_ISS) ? stSRE : stTWDL;
         refSt <= #TCQ stTWDL;
         int_refLRank <= #TCQ nextLRank(int_refLRank);
      end
     stSRE: begin
	if ((RANK_SLOT == 4) && (REG_CTRL == "ON")) begin
	  int_sreCkeDis <= #TCQ int_sreCkeDis | (1'b1 << int_refRank) | (1'b1 << (int_refRank+2'b10));
	  refSt <= #TCQ & (int_sreCkeDis | (1'b1 << int_refRank) | (1'b1 << (int_refRank+2'b10))) ? stSR : stREQ;
	end else begin
	  int_sreCkeDis <= #TCQ int_sreCkeDis | (1'b1 << int_refRank);
	  refSt <= #TCQ & (int_sreCkeDis | (1'b1 << int_refRank)) ? stSR : stREQ;
	end
	int_refRank <= #TCQ nextRank(int_refRank);
     end
     stSR: begin
       if (calDone) begin
         refSt <= #TCQ srx_req ? stSRX: 
                       srx_cke0_release ? stRST: 
                       stSR;
         int_sreCkeDis <= #TCQ srx_cke0_release ? 4'b0 : int_sreCkeDis;
       end else begin
         refSt <= #TCQ stRST;
         int_sreCkeDis <= #TCQ 4'b0;
       end
     end
     stSRX: begin
         cntr <= #TCQ tRFC << 1;
         int_refReq <= #TCQ 1'b0;
         int_refIss <= #TCQ 1'b1;
	 int_srxIss <= #TCQ 1'b1;
	 int_sreCkeDis <= #TCQ 4'b0;
	 refs  <= #TCQ 'h1;
         retSt <= #TCQ stREF;
         refSt <= #TCQ stTWDL;	 
     end
      stRFCE: begin
         if (zq_pending[int_refRank]) begin
           // Complete tRFC and go to the ZQCS state.
           cntr  <= #TCQ 9'd10;
           retSt <= #TCQ stZQ;
           refSt <= #TCQ stTWDL;
         end else begin
           // No ZQCS required to exit the refresh flow.  Controller handshakes and pipeline delays
           // will ensure that any remaining tRFC wait time is covered.
           refSt <= #TCQ stRFC;
         end
      end
      stZQ: begin
         cntr  <= #TCQ tZQCSF;
         retSt <= #TCQ stRFC;
         int_zqIss <= #TCQ 1'b1;
         refSt <= #TCQ stTWDL;
      end
      stRFC: begin
         int_refReq <= #TCQ 1'b0;
	 if (sre_sm_ps == SRE_SM_ISS) begin
           refSt <= #TCQ stSRE;
	   int_sreIss <= #TCQ 1;
	 end else begin
           refSt <= #TCQ stREQ;
	   int_sreIss <= #TCQ 0;
           int_refRank <= #TCQ nextRank(int_refRank);
	 end
      end
      default: refSt <= #TCQ stERR;
   endcase
end


// ==================================================================
// USER_MODE Refresh/ZQ FSM and Logic
// ==================================================================

// USER_MODE Input signal capture
// Clear with ack signal when user flow completes
wire ref_req_nxt = ~um_ref_ack_nxt & ( ref_req_ff | ref_req );
wire zq_req_nxt  = ~um_zq_ack_nxt  & ( zq_req_ff  | zq_req );

// USER_MODE NI block signal
wire um_ref_req_nxt = ~clear_um_ref_req & ( um_ref_req | set_um_ref_req );

// USER_MODE rank counter.  Used for both refresh and ZQCS.
wire [1:0] um_rank_cntr_nxt = init_um_rank_cntr ? '0 : ( um_rank_cntr + { 1'b0, inc_um_rank_cntr } ); // spyglass disable W164a

// USER_MODE logical rank counter. Used for refresh
wire [LR_WIDTH-1:0] um_l_rank_cntr_nxt = init_um_l_rank_cntr ? '0 : ( um_l_rank_cntr + { 1'b0, inc_um_l_rank_cntr } ); 

// USER_MODE wait counter.  General purpose counter to tRFC, tZQCS, etc...
wire [9:0] um_wait_cntr_nxt = um_wait_cntr_start ? { 1'b0, um_wait_cntr_init } : ( um_wait_cntr - { 9'b0, | um_wait_cntr } ); // spyglass disable W164a

// USER_MODE Refresh and ZQCS FSM
always @(*) begin
  user_fsm_nxt = user_fsm;
  set_um_ref_req = 1'b0;
  init_um_rank_cntr = 1'b0;
  inc_um_rank_cntr = 1'b0;
  init_um_l_rank_cntr = 1'b0;
  inc_um_l_rank_cntr = 1'b0;
  um_wait_cntr_init = '0;
  um_wait_cntr_start = 1'b0;
  um_pre_iss_nxt = 1'b0;
  um_ref_iss_nxt   = 1'b0;
  um_ref_ack_nxt = 1'b0;
  um_zq_ack_nxt = 1'b0;
  um_zq_iss_nxt    = 1'b0;
  um_zq_iss_all_nxt    = 1'b0;
  clear_um_ref_req = 1'b0;

  casez (user_fsm)
    UM_IDLE: begin
      // Start user mode refresh or zqcs unless blocked by periodic read or if
      // any group FSM is already asserting the refOK handshake.  Need to avoid looking
      // at a stale refOK signal after leaving IDLE.
      if ( (ref_req_ff | zq_req_ff) & ~per_block_ref & ~( | refOK ) & USER_MODE ) begin
        set_um_ref_req = 1'b1;
        init_um_rank_cntr = 1'b1;
        init_um_l_rank_cntr = 1'b1;
        user_fsm_nxt = UM_ACK_WAIT;
      end
    end
    UM_ACK_WAIT: begin
      if (refOK == 4'b1111) begin
        um_wait_cntr_start = 1'b1;
        um_wait_cntr_init  = tWRWAIT;
        user_fsm_nxt = UM_WR_WAIT;
      end
    end
    UM_WR_WAIT: begin
      if ( ~ ( | um_wait_cntr ) ) begin
        user_fsm_nxt = UM_PRE;
      end
    end
    UM_PRE: begin
      um_pre_iss_nxt   = 1'b1;
      user_fsm_nxt = UM_PRE_CHECK;
    end
    UM_PRE_CHECK: begin
      if (um_rank_cntr == (RANKS-1) & um_l_rank_cntr == (S_HEIGHT-1)) begin
        um_wait_cntr_start = 1'b1;
        um_wait_cntr_init  = tRPWAIT;
        user_fsm_nxt       = UM_PRE_WAIT;
      end else if (um_l_rank_cntr == (S_HEIGHT-1)) begin
        inc_um_rank_cntr   = 1'b1;
        init_um_l_rank_cntr = 1'b1;
        user_fsm_nxt       = UM_PRE;
      end else begin
        inc_um_l_rank_cntr = 1'b1;
        user_fsm_nxt       = UM_PRE;
      end
    end
    UM_PRE_WAIT: begin
      if ( ~( | um_wait_cntr ) & ref_req_ff ) begin
        user_fsm_nxt = UM_REF;
        init_um_rank_cntr = 1'b1;
        init_um_l_rank_cntr = 1'b1;
      end else if ( ~( | um_wait_cntr ) & zq_req_ff & ~ALL_RANKS ) begin
        user_fsm_nxt = UM_ZQ;
        init_um_rank_cntr = 1'b1;
      end else if ( ~( | um_wait_cntr ) & zq_req_ff &  ALL_RANKS ) begin
        user_fsm_nxt = UM_ZQ_ALL;
      end
    end
    UM_REF: begin
      um_ref_iss_nxt   = 1'b1;
      user_fsm_nxt = UM_REF_CHECK;
    end
    UM_REF_CHECK: begin
      if (um_rank_cntr == (RANKS-1) & um_l_rank_cntr == (S_HEIGHT-1)) begin
        um_wait_cntr_start = 1'b1;
        um_wait_cntr_init  = (tRFC + 3) / 4; // spyglass disable W164c
        user_fsm_nxt       = UM_TRFC_WAIT;
      end else if (um_l_rank_cntr == (S_HEIGHT-1)) begin
        inc_um_rank_cntr   = 1'b1;
        init_um_l_rank_cntr = 1'b1;
        um_wait_cntr_start = 1'b1;
        um_wait_cntr_init  = (tSTAG + 3) / 4; // spyglass disable W164c
        user_fsm_nxt       = UM_STAG_WAIT;
      end else begin
        inc_um_l_rank_cntr = 1'b1;
        um_wait_cntr_start = 1'b1;
        um_wait_cntr_init  = (tRFC_dlr + 3) / 4; // spyglass disable W164c
        user_fsm_nxt       = UM_STAG_WAIT;
      end
    end
    UM_STAG_WAIT: begin
      if ( ~ ( | um_wait_cntr ) ) begin
        user_fsm_nxt = UM_REF;
      end
    end
    UM_TRFC_WAIT: begin
      if ( ~( | um_wait_cntr ) & ~zq_req_ff ) begin
        user_fsm_nxt = UM_IDLE;
        um_ref_ack_nxt = 1'b1;
        clear_um_ref_req = 1'b1;
      end else if ( ~( | um_wait_cntr ) & zq_req_ff & ~ALL_RANKS ) begin
        user_fsm_nxt = UM_ZQ;
        init_um_rank_cntr = 1'b1;
        um_ref_ack_nxt = 1'b1;
      end else if ( ~( | um_wait_cntr ) & zq_req_ff &  ALL_RANKS ) begin
        user_fsm_nxt = UM_ZQ_ALL;
        um_ref_ack_nxt = 1'b1;
      end
    end
    UM_ZQ: begin
      um_zq_iss_nxt    = 1'b1;
      user_fsm_nxt = UM_ZQ_CHECK;
    end
    UM_ZQ_CHECK: begin
      if (um_rank_cntr == (RANKS-1) ) begin
        um_wait_cntr_start = 1'b1;
        um_wait_cntr_init  = (tZQCS+3)/4;
        user_fsm_nxt       = UM_TZQCS_WAIT;
      end else begin
        inc_um_rank_cntr   = 1'b1;
        um_wait_cntr_start = 1'b1;
        um_wait_cntr_init  = (tZQCS+3)/4;
        user_fsm_nxt       = UM_ZQ_WAIT;
      end
    end
    UM_ZQ_WAIT: begin
      if ( ~ ( | um_wait_cntr ) ) begin
        user_fsm_nxt = UM_ZQ;
      end
    end
    UM_ZQ_ALL: begin
      um_zq_iss_nxt          = 1'b1;
      um_zq_iss_all_nxt      = 1'b1;
      um_wait_cntr_start = 1'b1;
      um_wait_cntr_init  = (tZQCS+3)/4;
      user_fsm_nxt       = UM_TZQCS_WAIT;
    end
    UM_TZQCS_WAIT: begin
      if ( ~ ( | um_wait_cntr ) ) begin
        user_fsm_nxt = UM_IDLE;
        clear_um_ref_req = 1'b1;
        um_zq_ack_nxt = 1'b1;
      end
    end
    default: begin
      user_fsm_nxt = UM_IDLE;
      clear_um_ref_req = 1'b1;
    end
  endcase

end //always

// General reset flops
always @(posedge clk) begin
  if (rst) begin
    user_fsm <= #TCQ '0;
    um_ref_req <= #TCQ 1'b0;
    um_wait_cntr <= #TCQ '0;
    um_rank_cntr <= #TCQ '0;
    um_l_rank_cntr <= #TCQ '0;
    ref_req_ff <= #TCQ 1'b0;
    zq_req_ff <= #TCQ 1'b0;
    zq_rank        <= #TCQ 2'b0;
    zq_intvl_count <= #TCQ ZQINTVLREF;
    zq_pending     <= #TCQ 4'b0;
  end
  else begin
    user_fsm <= #TCQ user_fsm_nxt;
    um_ref_req <= #TCQ um_ref_req_nxt;
    um_wait_cntr <= um_wait_cntr_nxt;
    um_rank_cntr <= #TCQ um_rank_cntr_nxt;
    um_l_rank_cntr <= #TCQ um_l_rank_cntr_nxt;
    ref_req_ff <= #TCQ ref_req_nxt;
    zq_req_ff <= #TCQ zq_req_nxt;
    zq_rank        <= #TCQ zq_rank_nxt;
    zq_intvl_count <= #TCQ zq_intvl_count_nxt;
    zq_pending     <= #TCQ zq_pending_nxt;
  end
end

// Non-Reset flops
always @(posedge clk) begin
    um_pre_iss <= #TCQ um_pre_iss_nxt;
    um_ref_iss <= #TCQ um_ref_iss_nxt;
    um_zq_iss <= #TCQ um_zq_iss_nxt;
    um_zq_iss_all <= #TCQ um_zq_iss_all_nxt;
    um_ref_ack <= #TCQ um_ref_ack_nxt;
    um_zq_ack <= #TCQ um_zq_ack_nxt;
end

//synopsys translate_off
reg [7*8-1:0] ref_st_name;

always @(*) begin
  casez (refSt)
    stRST  : ref_st_name = "stRST";  // spyglass disable W164c
    stTWDL : ref_st_name = "stTWDL"; // spyglass disable W164c
    stREQ  : ref_st_name = "stREQ";  // spyglass disable W164c
    stWAIT : ref_st_name = "stWAIT"; // spyglass disable W164c
    stPRE  : ref_st_name = "stPRE";  // spyglass disable W164c
    stREF  : ref_st_name = "stREF";  // spyglass disable W164c
    stRFC  : ref_st_name = "stRFC";  // spyglass disable W164c
    stRFCE : ref_st_name = "stRFCE"; // spyglass disable W164c
    stZQ   : ref_st_name = "stZQ";   // spyglass disable W164c
    stERR  : ref_st_name = "stERR";  // spyglass disable W164c
    default: ref_st_name = "REF_ERR";
  endcase
end // always

reg [13*8-1:0] user_fsm_name;

always @(*) begin
  casez (user_fsm)
    UM_IDLE      : user_fsm_name = "UM_IDLE";      // spyglass disable W164c
    UM_ACK_WAIT  : user_fsm_name = "UM_ACK_WAIT";  // spyglass disable W164c
    UM_WR_WAIT   : user_fsm_name = "UM_WR_WAIT";   // spyglass disable W164c
    UM_PRE       : user_fsm_name = "UM_PRE";       // spyglass disable W164c
    UM_PRE_CHECK : user_fsm_name = "UM_PRE_CHECK"; // spyglass disable W164c
    UM_PRE_WAIT  : user_fsm_name = "UM_PRE_WAIT";  // spyglass disable W164c
    UM_REF       : user_fsm_name = "UM_REF";       // spyglass disable W164c
    UM_REF_CHECK : user_fsm_name = "UM_REF_CHECK"; // spyglass disable W164c
    UM_STAG_WAIT : user_fsm_name = "UM_STAG_WAIT"; // spyglass disable W164c
    UM_TRFC_WAIT : user_fsm_name = "UM_TRFC_WAIT"; // spyglass disable W164c
    UM_ZQ        : user_fsm_name = "UM_ZQ";        // spyglass disable W164c
    UM_ZQ_CHECK  : user_fsm_name = "UM_ZQ_CHECK";  // spyglass disable W164c
    UM_ZQ_WAIT   : user_fsm_name = "UM_ZQ_WAIT";   // spyglass disable W164c
    UM_ZQ_ALL    : user_fsm_name = "UM_ZQ_ALL";    // spyglass disable W164c
    UM_TZQCS_WAIT: user_fsm_name = "UM_TZQCS_WAIT";
    default      : user_fsm_name = "USER_REF_ERR"; // spyglass disable W164c
  endcase
end // always

`ifdef MEM_INTERNAL
// Events - When asserted high in a test that passes all verification checks, these coverage
//          properties indicate that a functional coverage event has been hit.
// ---------------------------------------------------------------------------------------------

// Refresh issued
wire   e_mc_ref_000 = refIss;
always @(posedge clk) mc_ref_000: if (~rst) cover property (e_mc_ref_000);

// ZQCS issued
wire   e_mc_ref_001 = zqIss;
always @(posedge clk) mc_ref_001: if (~rst) cover property (e_mc_ref_001);

// Refresh issued in user mode to rank 0
wire   e_mc_ref_002 = USER_MODE & refIss & ( refRank == 2'd0 );
always @(posedge clk) mc_ref_002: if (~rst) cover property (e_mc_ref_002);

// Refresh issued in user mode to rank 3
wire   e_mc_ref_003 = USER_MODE & refIss & ( refRank == 2'd3 );
always @(posedge clk) mc_ref_003: if (~rst) cover property (e_mc_ref_003);

// Refresh issued in internal mode to rank 0
wire   e_mc_ref_004 = ~USER_MODE & refIss & ( refRank == 2'd0 );
always @(posedge clk) mc_ref_004: if (~rst) cover property (e_mc_ref_004);

// Refresh issued in internal mode to rank 3
wire   e_mc_ref_005 = ~USER_MODE & refIss & ( refRank == 2'd3 );
always @(posedge clk) mc_ref_005: if (~rst) cover property (e_mc_ref_005);

// ZQCS issued in user mode
wire   e_mc_ref_006 = USER_MODE & zqIss;
always @(posedge clk) mc_ref_006: if (~rst) cover property (e_mc_ref_006);

// ZQCS issued in internal mode to rank 0
wire   e_mc_ref_007 = ~USER_MODE & zqIss & ( refRank == 2'd0 );
always @(posedge clk) mc_ref_007: if (~rst) cover property (e_mc_ref_007);

// ZQCS issued in internal mode to rank 3
wire   e_mc_ref_008 = ~USER_MODE & zqIss & ( refRank == 2'd3 );
always @(posedge clk) mc_ref_008: if (~rst) cover property (e_mc_ref_008);

// Refresh blocked by periodic read.
wire   e_mc_ref_009 = ( refSt == stREQ ) & ( pend_ref[int_refRank] > 0 ) & per_block_ref;
always @(posedge clk) mc_ref_009: if (~rst) cover property (e_mc_ref_009);

// Refresh and periodic read due on same cycle
reg  e_per_block_ref_dly;
reg  e_pend_ref_dly;
wire e_pend_ref_dly_nxt = ( pend_ref[int_refRank] > 0 );
always @(posedge clk) begin
  e_per_block_ref_dly <= #TCQ per_block_ref;
  e_pend_ref_dly      <= #TCQ e_pend_ref_dly_nxt;
end
wire   e_mc_ref_010 = ( refSt == stREQ ) & ( pend_ref[int_refRank] > 0 ) & per_block_ref
                      & ~e_pend_ref_dly_nxt & ~e_pend_ref_dly;
always @(posedge clk) mc_ref_010: if (~rst) cover property (e_mc_ref_010);

// Periodic request while refresh in progress
wire   e_mc_ref_011 = ~( refSt == stREQ ) & ~( refSt == stRST ) & per_block_ref;
always @(posedge clk) mc_ref_011: if (~rst) cover property (e_mc_ref_011);

// Single internal refresh requested
wire   e_mc_ref_012 = ( refSt == stPRE ) & ( NUMREF == 1 );
always @(posedge clk) mc_ref_012: if (~rst) cover property (e_mc_ref_012);

// Multiple internal refreshes requested
wire   e_mc_ref_013 = ( refSt == stPRE ) & ( NUMREF > 1 );
always @(posedge clk) mc_ref_013: if (~rst) cover property (e_mc_ref_013);

// User mode refresh blocked by periodic read
wire   e_mc_ref_014 = ( user_fsm == UM_IDLE ) & ref_req_ff & per_block_ref & USER_MODE;
always @(posedge clk) mc_ref_014: if (~rst) cover property (e_mc_ref_014);

// User mode zqcs blocked by periodic read
wire   e_mc_ref_015 = ( user_fsm == UM_IDLE ) & zq_req_ff & per_block_ref & USER_MODE;
always @(posedge clk) mc_ref_015: if (~rst) cover property (e_mc_ref_015);

// User mode refresh and periodic read request on same cycle
reg  e_ref_req_ff_dly;
reg  e_zq_req_ff_dly;
always @(posedge clk) begin
  e_ref_req_ff_dly <= #TCQ ref_req_ff;
  e_zq_req_ff_dly  <= #TCQ zq_req_ff;
end
wire   e_mc_ref_016 = ( user_fsm == UM_IDLE ) & ref_req_ff & per_block_ref & USER_MODE
                      & ~e_ref_req_ff_dly & ~e_per_block_ref_dly;
always @(posedge clk) mc_ref_016: if (~rst) cover property (e_mc_ref_016);

// User mode zqcs and periodic read request on same cycle
wire   e_mc_ref_017 = ( user_fsm == UM_IDLE ) & zq_req_ff & per_block_ref & USER_MODE
                      & ~e_zq_req_ff_dly & ~e_per_block_ref_dly;
always @(posedge clk) mc_ref_017: if (~rst) cover property (e_mc_ref_017);

// User ref and zq requested on same cycle
wire   e_mc_ref_018 = ( user_fsm == UM_IDLE ) & ref_req_ff & zq_req_ff & ~e_ref_req_ff_dly & ~e_zq_req_ff_dly & USER_MODE;
always @(posedge clk) mc_ref_018: if (~rst) cover property (e_mc_ref_018);

// User ref requested while zqcs in progress
wire   e_mc_ref_019 = ~( user_fsm == UM_IDLE ) & ref_req_ff & zq_req_ff & ~e_ref_req_ff_dly & e_zq_req_ff_dly & USER_MODE;
always @(posedge clk) mc_ref_019: if (~rst) cover property (e_mc_ref_019);

// User zq requested while ref in progress
wire   e_mc_ref_020 = ~( user_fsm == UM_IDLE ) & ref_req_ff & zq_req_ff & e_ref_req_ff_dly & ~e_zq_req_ff_dly & USER_MODE;
always @(posedge clk) mc_ref_020: if (~rst) cover property (e_mc_ref_020);

// User mode precharge to zqcs without refresh
wire   e_mc_ref_021 = ( user_fsm == UM_PRE_WAIT ) & ( user_fsm_nxt == UM_ZQ_ALL ) & USER_MODE;
always @(posedge clk) mc_ref_021: if (~rst) cover property (e_mc_ref_021);

// User mode refresh on cycle wait expires interrupts zqcs
wire   e_mc_ref_022 = ( user_fsm == UM_PRE_WAIT ) & ~( | um_wait_cntr ) & ref_req_ff & ~e_ref_req_ff_dly & USER_MODE;
always @(posedge clk) mc_ref_022: if (~rst) cover property (e_mc_ref_022);

// User mode refresh without zqcs
wire   e_mc_ref_023 = ( user_fsm == UM_TRFC_WAIT ) & ~( | um_wait_cntr ) & ~zq_req_ff & USER_MODE;
always @(posedge clk) mc_ref_023: if (~rst) cover property (e_mc_ref_023);

// User mode refresh with zqcs on the cycle just before returning to idle
wire   e_mc_ref_024 = ( user_fsm == UM_TRFC_WAIT ) & ~( | um_wait_cntr ) & zq_req_ff & ~e_zq_req_ff_dly & USER_MODE;
always @(posedge clk) mc_ref_024: if (~rst) cover property (e_mc_ref_024);

// User mode refresh with zqcs on the cycle just when returning to idle
wire   e_mc_ref_025 = ( user_fsm == UM_TRFC_WAIT ) & ~( | um_wait_cntr ) & ~zq_req_ff & zq_req_nxt & USER_MODE;
always @(posedge clk) mc_ref_025: if (~rst) cover property (e_mc_ref_025);

// Internal refresh with at least 2 refreshes pending
wire   e_mc_ref_027 = ~USER_MODE & ( pend_ref[0] >= 2 ) & refIss;
always @(posedge clk) mc_ref_027: if (~rst) cover property (e_mc_ref_027);

// Refresh issued in user mode to LR = 8
wire   e_mc_ref_028 = USER_MODE & refIss & ( refLRank == 3'd8 ) & ( S_HEIGHT == 8 );
always @(posedge clk) mc_ref_028: if (~rst) cover property (e_mc_ref_028);

// Refresh issued in internal mode to LR = 8
wire   e_mc_ref_029 = ~USER_MODE & refIss & ( refLRank == 3'd8 ) & ( S_HEIGHT == 8 );
always @(posedge clk) mc_ref_029: if (~rst) cover property (e_mc_ref_029);

// Asserts - When asserted high, an illegal condition has been detected and the test has failed.
// ---------------------------------------------------------------------------------------------

// Number of internal refresh requests too high
wire   a_mc_ref_000 = ( refSt == stPRE ) & ( NUMREF > 15 );
always @(posedge clk) if (~rst) assert property (~a_mc_ref_000);

// tZQCSF out of range
wire   a_mc_ref_001 = ( (tZQCS + 3) / 4 ) > 1023;
always @(posedge clk) if (~rst) assert property (~a_mc_ref_001);

// User ref or zqcs request in internal mode
wire   a_mc_ref_002 = ( ref_req_ff | zq_req_ff ) & ~USER_MODE;
always @(posedge clk) if (~rst) assert property (~a_mc_ref_002);

// Illegal refOK de-assertion
reg  [3:0] refOK_dly;
always @(posedge clk) begin
  refOK_dly <= #TCQ refOK;
end
wire [3:0] refOK_fall = ~refOK & refOK_dly;
wire       refOK_deassert = | refOK_fall;
wire   a_mc_ref_003 = ( ( ~(refSt == stREQ) & ~(refSt == stSR) & ~USER_MODE ) | ( ~( user_fsm == UM_IDLE ) & USER_MODE ) ) & refOK_deassert;
always @(posedge clk) if (~rst) assert property (~a_mc_ref_003);

// Illegal refReq
reg refReq_dly;
always @(posedge clk) begin
  refReq_dly <= #TCQ refReq;
end
wire   a_mc_ref_004 = refReq & ~refReq_dly & ( | refOK );
always @(posedge clk) if (~rst) assert property (~a_mc_ref_004);

// Illegal user requests
wire   a_mc_ref_005 = ~calDone & ( ref_req | zq_req );
always @(posedge clk) if (~rst) assert property (~a_mc_ref_005);

// tREFI overflow
wire   a_mc_ref_006 = tREFIF > 65536;
always @(posedge clk) if (~rst) assert property (~a_mc_ref_006);

// Pending refresh overflow
wire   a_mc_ref_007 = inc_pend_ref_due[0] &  ( & pend_ref[0] );
always @(posedge clk) if (~rst) assert property (~a_mc_ref_007);

// tWRWAIT overflow
wire a_mc_ref_008 = ((tCWL + 4 + tWR + 3) / 4) > 128;
always @(posedge clk) if (~rst) assert property (~a_mc_ref_008);


`endif
//synopsys translate_on

endmodule


