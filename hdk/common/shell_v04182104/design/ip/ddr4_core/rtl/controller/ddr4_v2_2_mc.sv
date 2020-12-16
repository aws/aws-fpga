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
// \   \  /  \    Date Created       : Tue May 13 2014
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                   ddr4_v2_2_10_mc module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ns/100ps

module ddr4_v2_2_10_mc # (parameter
    ABITS   = 18
   ,BABITS  = 2
   ,BGBITS  = 2
   ,CKEBITS = 4
   ,COLBITS = 10
   ,S_HEIGHT = 1
   ,LR_WIDTH = 1
   ,ALIAS_PAGE = "OFF"
   ,ALIAS_P_CNT = "OFF"
   ,CSBITS  = 4
   ,ODTBITS = 4
   ,MEM     = "DDR4"
   ,DQ_WIDTH      = 32
   ,DQS_WIDTH     = 4
   ,DM_WIDTH = 8
   ,PAYLOAD_WIDTH = 64
   ,PAYLOAD_DM_WIDTH = 64
   ,ECC_WIDTH     = 8
   ,ECC           = "OFF"
   ,ADDR_FIFO_WIDTH = 30
   ,DBAW    = 5
   ,RANKS   = 1
   ,RKBITS = (RANKS <= 4) ? 2 : 3
   ,RANK_SLAB = (RANKS <= 4) ? 4 : 8
   ,RANK_SLOT = 1
   ,ORDERING  = "NORM"
   ,TXN_FIFO_BYPASS = "ON"
   ,TXN_FIFO_PIPE   = "OFF"
   ,PER_RD_PERF     = 1'b1
   ,CAS_FIFO_BYPASS = "ON"
   ,NOP_ADD_LOW     = 1'b0
   ,STARVATION_EN = 1'b1
   ,STARVE_COUNT_WIDTH = 9
   ,DDR4_CLAMSHELL = "OFF"
   ,MEM_CONFIG = "COMPONENT"
   ,REG_CTRL   = "OFF"
   ,PARTIAL_RECONFIG = "Enable"

   ,tCK    = 938
   ,tFAW   = 20
   ,tFAW_dlr = 16
   ,tRTW   = 4
   ,tWTR_L = 13
   ,tWTR_S = 13
   ,tRFC   = 27
   ,tRFC_dlr = 9
   ,tREFI  = 1300
   ,ZQINTVL = 10400
   ,tZQCS   = 128
   ,tRP    = 15
   ,tRRD_L = 4
   ,tRRD_S = 4
   ,tRRD_dlr = 4
   ,tRAS   = 39
   ,tRCD   = 15
   ,tRTP   = 6
   ,tWR    = 12
   ,tCCD_3ds = 4
   ,MR6      = 13'b0_1000_0000_0000

   ,NUMREF = 1
   ,PER_RD_INTVL = 32'd0

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

   ,ODTNOP = 16'h0000
   ,nCK_PER_CLK = 4
   ,TCQ        = 0.1
)(
    input clk
   ,input rst
   ,input calDone

   ,output            [7:0] mcCKt
   ,output            [7:0] mcCKc
   ,output            [7:0] mc_ACT_n
   ,output            [7:0] mc_RAS_n
   ,output            [7:0] mc_CAS_n
   ,output            [7:0] mc_WE_n
   ,output    [ABITS*8-1:0] mc_ADR
   ,output   [BABITS*8-1:0] mc_BA
   ,output   [BGBITS*8-1:0] mc_BG
   ,output [LR_WIDTH*8-1:0] mc_C
   ,output  [CKEBITS*8-1:0] mc_CKE
   ,output   [CSBITS*8-1:0] mc_CS_n
   ,output  [ODTBITS*8-1:0] mc_ODT

   ,output            [1:0] casSlot
   ,output                  casSlot2
   ,output                  rdCAS
   ,output                  wrCAS
   ,output       [DBAW-1:0] winBuf
   ,output                  winInjTxn
   ,output                  winRmw
   ,output                  gt_data_ready
   ,output   [RKBITS-1:0]   win_rank_cas

   ,output                  accept
   ,output                  accept_ns
   ,output                  ref_ack
   ,output                  zq_ack

   ,output     [DQ_WIDTH*8-1:0]             wr_data_mc2phy
   ,output     [DM_WIDTH*8-1:0]             wr_data_mask_mc2phy
   ,output     [PAYLOAD_WIDTH*8-1:0]        rd_data_mc2ni
   ,output     [DBAW-1:0]                   rd_data_addr_mc2ni
   ,output                                  rd_data_en_mc2ni
   ,output                                  rd_data_end_mc2ni
   ,output     [ADDR_FIFO_WIDTH-1:0]        ecc_err_addr
   ,output     [2*nCK_PER_CLK-1:0]          eccSingle
   ,output     [2*nCK_PER_CLK-1:0]          eccMultiple
   ,output     [DQ_WIDTH*8-1:0]             rd_data_phy2mc // ecc log format
   ,input [DQ_WIDTH/8-1:0]                  fi_xor_we
   ,input [DQ_WIDTH-1:0]                    fi_xor_wrdata
   ,input                                   fi_xor_wrdata_en

   ,input      [2*nCK_PER_CLK-1:0]          raw_not_ecc
   ,input                                   correct_en
   ,input                                   rmw_rd_done
   ,input      [PAYLOAD_WIDTH*8-1:0]        wr_data_ni2mc
   ,input      [PAYLOAD_DM_WIDTH*8-1:0]     wr_data_mask_ni2mc
   ,input      [DBAW-1:0]                   wr_data_addr_phy2mc
   ,input      [DQ_WIDTH*8-1:0]             rd_data_phy2mc_xif
   ,input      [DBAW-1:0]                   rd_data_addr_phy2mc
   ,input                                   rd_data_en_phy2mc
   ,input                                   rd_data_end_phy2mc

   ,input     [BABITS-1:0] bank
   ,input     [BGBITS-1:0] group
   ,input            [2:0] lr
   ,input            [2:0] cmd
   ,input                  ap
   ,input    [COLBITS-1:0] col
   ,input       [DBAW-1:0] dBufAdr
   ,input                  hiPri
   ,input   [RKBITS-1:0]   rank
   ,input      [ABITS-1:0] row
   ,input                  size
   ,input                  useAdr
   ,input                  ref_req
   ,input                  zq_req

   ,input            [5:0] tCWL
   ,input                  per_rd_done

   // IBM SR
   ,input                  sre_req
   ,output                 sre_ack
   ,input                  ui_busy
   ,output                 mc_block_req
   ,input                  stop_gate_tracking_ack
   ,output                 stop_gate_tracking_req
   ,output                 cmd_complete
   ,input                  srx_cke0_release
   ,input                  srx_req
   ,output [31:0]          dbg_out
);


wire  [3:0] tWTPF;
wire  [1:0] tRTPF;
wire  [3:0] tRASF;
wire  [1:0] ba;
wire  [1:0] bagr;
wire  [1:0] group_fsm_select;
wire  [3:0] cmdAP;
wire  [3:0] grAccept;
wire  [3:0] grAccept_ns;
wire        preIss;
wire        readMode;
wire        refIss;
wire        zqIss;
wire        zqIssAll;
wire  [3:0] txn_fifo_full;
wire  [3:0] cas_fifo_full;
wire  [3:0] refOK;
wire  [RKBITS-1:0] refRank;
wire        refReq;
wire  [3:0] actReq;
wire  [3:0] actReqT;
wire  [3:0] preReq;
wire  [3:0] preReqM;
wire  [3:0] rdReq;
wire  [3:0] rdReqT;
wire  [3:0] wrReq;
wire  [3:0] wrReqT;
wire  [1:0] winGroupA;
wire  [1:0] winGroupC;
wire  [1:0] winGroupP;
wire  [7:0] readSlot;
wire  [7:0] writeSlot;
wire        tranSentC;
wire  [RKBITS-1:0] winRankA;
wire  [RKBITS-1:0] winRankC;
wire  [RKBITS-1:0] winRankP;
wire        winAP;
wire        winSize;
wire        winAct;
wire  [3:0] winPortA;
wire  [1:0] winPortEncC;
wire  [RANK_SLAB-1:0] act_rank_update;
wire  [3:0] act_winPort_nxt;
wire  [1:0] win_bank_cas;
wire  [1:0] win_group_cas;
wire  [3:0] winPortC;
wire  [3:0] winPortP;
wire        winRead;
wire        winWrite;
wire  [7:0] cmd_bank_cas;
wire  [7:0] cmdBank;
wire  [7:0] cmdBankP;
wire  [3:0] cmdHiPri;
wire  [7:0] cmd_group_cas;
wire  [7:0] cmdGroup;
wire  [7:0] cmdGroupP;
wire  [RKBITS*4-1:0] cmd_rank_cas;
wire  [RKBITS*4-1:0] cmdRank;
wire  [RKBITS*4-1:0] cmdRankP;
wire  [3:0] cmdSize;
wire  [1:0] winBankA;
wire  [1:0] winBankC;
wire  [1:0] winBankP;
wire     [ABITS-1:0] winRowA;
wire    [DBAW*4-1:0] cmdBuf;
wire   [COLBITS-1:0] winCol;
wire   [4*ABITS-1:0] cmdRow;
wire   [4*ABITS-1:0] cmd_row_cas;
wire [4*COLBITS-1:0] cmdCol;
wire [4*LR_WIDTH-1:0] cmdLRank;
wire [4*LR_WIDTH-1:0] cmdLRankP;
wire [4*LR_WIDTH-1:0] cmd_l_rank_cas;
wire [LR_WIDTH-1:0]  win_l_rank_cas;
wire [LR_WIDTH-1:0]  winLRankC;
wire [LR_WIDTH-1:0]  winLRankA;
wire [LR_WIDTH-1:0]  winLRankP;
wire [LR_WIDTH-1:0]  refLRank;

// Periodic reads
wire                 per_block_ref;           // Periodic module blocking refresh
wire                 per_rd_req;
wire [3:0]           per_rd_req_vec;
wire                 per_cas_block_req;
   // spyglass disable_block W498
wire [3:0]           per_rd_accept;
   // spyglass enable_block W498
wire [3:0]           cmdInjTxn;
wire [3:0]           cmdRmw;

wire [LR_WIDTH-1:0] l_rank;
   
// Added for IBM Self Refresh. Denote MC does not have outstanding transaction in txn fifo nor cas fifo
wire [3:0] txn_fifo_empty;
wire [3:0] cas_fifo_empty;
wire       int_sreIss;
wire [RANKS-1:0] int_sreCkeDis;
wire 	  int_srxIss;
wire 	  prevCmdAP;

wire [2:0] dbg_sre_sm_ps;
wire [3:0] dbg_refSt;
wire       dbg_mc_ref_rst;
wire       dbg_mc_periodic_rst;

(* keep = "TRUE" *) reg rst_r1;

always @(posedge clk)
  rst_r1 <= rst;

assign dbg_out = {24'b0, calDone, dbg_refSt[3:0], dbg_sre_sm_ps[2:0]};
assign dbg_mc_ref_rst      = 1'b0;
assign dbg_mc_periodic_rst = 1'b0;
   
assign accept = |grAccept;
assign accept_ns = |grAccept_ns;
assign casSlot = casSlot2 ? 2'b10 : 2'b00;
assign rdCAS = winRead & tranSentC;
assign wrCAS = winWrite & tranSentC;

// Map Bank and Group address bits to the Group FSMs (group_fsm_select).
// Also map Bank/Group to signals used for indexing the page table (ba)
// and for selecting tCCD_S/_L, tRRD_S/_L, and tWTR_S/_L timing (bagr).
generate
   if (MEM == "DDR3") begin
      assign ba = bank[1:0];
      assign bagr = { 1'b0, bank[2] };
      assign group_fsm_select = bank[2:1];
      assign l_rank = 'b0;
   end else begin
      if (BGBITS == 2) begin
         assign ba = bank;
         assign bagr = group;
         assign group_fsm_select = group;
      end else begin
         assign ba = bank[1:0];
         assign bagr = {1'b0, group};
         assign group_fsm_select = {group, bank[0]};
      end
      if (S_HEIGHT < 2) begin
         assign l_rank = 'b0;
      end else begin
         assign l_rank = lr[LR_WIDTH-1:0];
      end
   end
endgenerate

genvar bg;
generate
   for (bg = 0; bg <= 3; bg = bg + 1) begin:bgr
      assign per_rd_req_vec[bg] = per_rd_req & (bg == 0); // Only inject periodic read into Group 0 FSM
      ddr4_v2_2_10_mc_group #(
          .ABITS   (ABITS)
         ,.COLBITS (COLBITS)
         ,.DBAW    (DBAW)
         ,.ALIAS_PAGE(ALIAS_PAGE)
         ,.S_HEIGHT(S_HEIGHT)
         ,.LR_WIDTH(LR_WIDTH)
         ,.MEM     (MEM)
         ,.tRCD    (tRCD)
         ,.tRP     (tRP)
         ,.RKBITS          (RKBITS)
         ,.RANK_SLAB       (RANK_SLAB)
         ,.TXN_FIFO_BYPASS (TXN_FIFO_BYPASS)
         ,.TXN_FIFO_PIPE   (TXN_FIFO_PIPE)
         ,.PER_RD_PERF     (PER_RD_PERF)
         ,.CAS_FIFO_BYPASS (CAS_FIFO_BYPASS)
         ,.TCQ     (TCQ)
      )u_ddr_mc_group(
          .clk      (clk)
         ,.rst      (rst)

         ,.calDone  (calDone)
         ,.id       (bg[1:0])
         ,.group_fsm_select (group_fsm_select)

         ,.accept   (grAccept[bg])
         ,.accept_ns(grAccept_ns[bg])
         ,.actReq   (actReq[bg])
         ,.preReq   (preReq[bg])
         ,.rdReq    (rdReq[bg])
         ,.wrReq    (wrReq[bg])

         ,.cmd_bank_cas   (cmd_bank_cas[bg*2+:2])
         ,.cmdBank  (cmdBank[bg*2+:2])
         ,.cmdBankP (cmdBankP[bg*2+:2])
         ,.cmdBuf   (cmdBuf[bg*DBAW+:DBAW])
         ,.cmdInjTxn (cmdInjTxn[bg])
         ,.cmdRmw    (cmdRmw[bg])
         ,.cmdAP    (cmdAP[bg])
         ,.cmdCol   (cmdCol[bg*COLBITS+:COLBITS])
         ,.cmd_group_cas  (cmd_group_cas[bg*2+:2])
         ,.cmdGroupP(cmdGroupP[bg*2+:2])
         ,.cmdGroup (cmdGroup[bg*2+:2])
         ,.cmdHiPri (cmdHiPri[bg])
         ,.cmd_rank_cas   (cmd_rank_cas[bg*RKBITS+:RKBITS])
         ,.cmd_l_rank_cas (cmd_l_rank_cas[bg*LR_WIDTH+:LR_WIDTH])
         ,.cmdRank  (cmdRank[bg*RKBITS+:RKBITS])
         ,.cmdRankP (cmdRankP[bg*RKBITS+:RKBITS])
         ,.cmdLRank (cmdLRank[bg*LR_WIDTH+:LR_WIDTH])
         ,.cmdLRankP(cmdLRankP[bg*LR_WIDTH+:LR_WIDTH])
         ,.cmdRow   (cmdRow[bg*ABITS+:ABITS])
         ,.cmd_row_cas    (cmd_row_cas[bg*ABITS+:ABITS])
         ,.cmdSize  (cmdSize[bg*1+:1])

         ,.clrReq   (winPortA[bg] | winPortP[bg] | (winPortC[bg] && tranSentC))
         ,.act_won  (winPortA[bg])
         ,.pre_won  (winPortP[bg])
         ,.cas_won  (winPortC[bg] && tranSentC)
         ,.winInjTxn (winInjTxn)

         ,.bank     (ba)
         ,.cmd      (cmd)
         ,.ap       (ap)
         ,.col      (col)
         ,.dBufAdr  (dBufAdr)
         ,.group    (bagr)
         ,.l_rank   (l_rank)
         ,.hiPri    (hiPri)
         ,.rank     (rank)
         ,.row      (row)
         ,.size     (size)
         ,.useAdr   (useAdr)
         ,.tWTPF    (tWTPF)
         ,.tRTPF    (tRTPF)
         ,.tRASF    (tRASF)

         ,.refOK    (refOK[bg])
         ,.per_rd_accept (per_rd_accept[bg])

         ,.readMode (readMode)
         ,.refRank  (refRank)
         ,.refLRank (refLRank)
         ,.refReq   (refReq)
         ,.per_rd_req (per_rd_req_vec[bg])

         ,.rmw_rd_done         (rmw_rd_done)
         ,.rd_data_addr_phy2mc (rd_data_addr_phy2mc)

         ,.txn_fifo_empty      (txn_fifo_empty[bg])
         ,.cas_fifo_empty      (cas_fifo_empty[bg])
         ,.txn_fifo_full       (txn_fifo_full[bg])
         ,.cas_fifo_full       (cas_fifo_full[bg])
      );
   end
endgenerate

ddr4_v2_2_10_mc_act_timer #(
    .tFAW   (tFAW)
   ,.tFAW_dlr(tFAW_dlr)
   ,.tRRD_L (tRRD_L)
   ,.tRRD_S (tRRD_S)
   ,.tRRD_dlr(tRRD_dlr)
   ,.BGBITS  (BGBITS)
   ,.S_HEIGHT(S_HEIGHT)
   ,.LR_WIDTH(LR_WIDTH)
   ,.RKBITS          (RKBITS)
   ,.RANK_SLAB       (RANK_SLAB)
   ,.MEM     (MEM)
   ,.TCQ    (TCQ)   
)u_ddr_mc_act_timer(
    .clk     (clk)
   ,.rst     (rst_r1)

   ,.actReqT (actReqT)

   ,.actReq  (actReq)
   ,.cmdRank (cmdRank)
   ,.cmdLRank (cmdLRank)
   ,.winPort (winPortA)
   ,.winRank (winRankA)
   ,.winLRank (winLRankA) 
   ,.act_winPort_nxt (act_winPort_nxt)
   ,.act_rank_update (act_rank_update)
);

ddr4_v2_2_10_mc_arb_a # (
    .TCQ (TCQ)
   ,.RKBITS    (RKBITS)
   ,.RANK_SLAB (RANK_SLAB)
)u_ddr_mc_arb_a(
    .clk     (clk)
   ,.rst     (rst_r1)

   ,.winAct  (winAct)
   ,.winPort (winPortA)
   ,.act_rank_update (act_rank_update)
   ,.act_winPort_nxt (act_winPort_nxt)

   ,.cmdRank (cmdRank)
   ,.req     (actReqT)
);

ddr4_v2_2_10_mc_rd_wr #(
    .RDSLOT (256)
   ,.WRSLOT (128)
   ,.tWTR_L (tWTR_L)
   ,.tWTR_S (tWTR_S)
   ,.tRTW   (tRTW)
   ,.RKBITS    (RKBITS)
   ,.RANK_SLAB (RANK_SLAB)
   ,.S_HEIGHT (S_HEIGHT)
   ,.LR_WIDTH (LR_WIDTH)
   ,.STARVATION_EN      (STARVATION_EN)
   ,.STARVE_COUNT_WIDTH (STARVE_COUNT_WIDTH)
   ,.TCQ    (TCQ)
)u_ddr_mc_rd_wr(
    .clk    (clk)
   ,.rst    (rst_r1)

   ,.readMode (readMode)
   ,.rdReqT   (rdReqT)
   ,.wrReqT   (wrReqT)

   ,.cmdGroup (cmd_group_cas)
   ,.cmdLRank (cmd_l_rank_cas)
   ,.cmdRank  (cmd_rank_cas)
   ,.rdCAS    (rdCAS)
   ,.rdReq    (rdReq)
   ,.winGroup (winGroupC)
   ,.winLRank (winLRankC)
   ,.winPort  (winPortC)
   ,.winRank  (winRankC)
   ,.wrCAS    (wrCAS)
   ,.casSlot2 (casSlot2)
   ,.wrReq    (wrReq)
   ,.tCWL     (tCWL)
);

ddr4_v2_2_10_mc_arb_c #(
    .TCQ       (TCQ)
    ,.RKBITS    (RKBITS)
    ,.RANK_SLAB (RANK_SLAB)
    ,.S_HEIGHT (S_HEIGHT)
    ,.LR_WIDTH (LR_WIDTH)
    ,.ORDERING (ORDERING)
)u_ddr_mc_arb_c(
    .clk      (clk)
   ,.rst      (rst_r1)

   ,.winPortEnc  (winPortEncC)
   ,.winPort     (winPortC)
   ,.winRead     (winRead)
   ,.winWrite    (winWrite)
   ,.win_bank_cas  (win_bank_cas)
   ,.win_group_cas (win_group_cas)
   ,.win_l_rank_cas(win_l_rank_cas)
   ,.win_rank_cas  (win_rank_cas)

   ,.cmdRmw   (cmdRmw)
   ,.read     (rdReqT)
   ,.wrte     (wrReqT)
   ,.tranSent (tranSentC)
   ,.useAdr   (useAdr)
   ,.accept   (grAccept)
   ,.per_rd_accept (per_rd_accept[0])

   ,.cmd_bank_cas   (cmd_bank_cas)
   ,.cmd_group_cas  (cmd_group_cas)
   ,.cmd_l_rank_cas (cmd_l_rank_cas)
   ,.cmd_rank_cas   (cmd_rank_cas)
   ,.cmdRank  (cmdRank)
   ,.cmdRankP (cmdRankP)
   ,.preReqM  (4'b0)
);

ddr4_v2_2_10_mc_arb_mux_p #(
    .MEM   (MEM)
   ,.ABITS (ABITS)
   ,.ALIAS_P_CNT (ALIAS_P_CNT)
   ,.S_HEIGHT (S_HEIGHT)
   ,.LR_WIDTH (LR_WIDTH)
   ,.RKBITS    (RKBITS)
   ,.RANK_SLAB (RANK_SLAB)
   ,.TCQ   (TCQ)
   ,.tRAS  (tRAS)
   ,.tRTP  (tRTP)
   ,.tWR   (tWR)
)u_ddr_mc_arb_mux_p(
    .clk     (clk)
   ,.rst     (rst_r1)

   ,.winBankP  (winBankP)
   ,.winGroupP (winGroupP)
   ,.winLRankP (winLRankP)
   ,.winPortP  (winPortP)
   ,.winRankP  (winRankP)
   ,.tWTPF     (tWTPF)
   ,.tRTPF     (tRTPF)
   ,.tRASF     (tRASF)
   ,.cmdBankP  (cmdBankP)
   ,.cmdGroupP (cmdGroupP)
   ,.cmdLRankP (cmdLRankP)
   ,.cmdRankP  (cmdRankP)
   ,.preReq    (preReq)
   ,.tCWL      (tCWL)
   ,.winBankC  (winBankC)
   ,.winGroupC (winGroupC)
   ,.winLRankC (winLRankC)
   ,.winRankC  (winRankC)
   ,.winRead   (winRead)
   ,.winWrite  (winWrite)
   ,.rdCAS     (rdCAS)
   ,.wrCAS     (wrCAS)
   ,.winBankA  (winBankA)
   ,.winGroupA (winGroupA)
   ,.winLRankA (winLRankA)
   ,.winRankA  (winRankA)
   ,.winAct    (winAct)

   ,.preReqM   (preReqM)
);

ddr4_v2_2_10_mc_ctl #(
    .RANKS   (RANKS)
   ,.RANK_SLOT (RANK_SLOT)
   ,.RKBITS    (RKBITS)
   ,.RANK_SLAB (RANK_SLAB)
   ,.ABITS   (ABITS)
   ,.BABITS  (BABITS)
   ,.BGBITS  (BGBITS)
   ,.S_HEIGHT (S_HEIGHT)
   ,.LR_WIDTH(LR_WIDTH)
   ,.CKEBITS (CKEBITS)
   ,.COLBITS (COLBITS)
   ,.CSBITS  (CSBITS)
   ,.ODTBITS (ODTBITS)
   ,.tCCD_3ds(tCCD_3ds)
   ,.MR6     (MR6)
   ,.MEM     (MEM)
   ,.NOP_ADD_LOW (NOP_ADD_LOW)
   ,.tCK         (tCK)
   ,.CLAMSHELL (DDR4_CLAMSHELL)
   ,.REG_CTRL  (REG_CTRL)

   ,.ODTWR     (ODTWR)
   ,.ODTWRDEL  (ODTWRDEL)
   ,.ODTWRDUR  (ODTWRDUR)
   ,.ODTWRODEL (ODTWRODEL)
   ,.ODTWRODUR (ODTWRODUR)

   ,.ODTRD     (ODTRD)
   ,.ODTRDDEL  (ODTRDDEL)
   ,.ODTRDDUR  (ODTRDDUR)
   ,.ODTRDODEL (ODTRDODEL)
   ,.ODTRDODUR (ODTRDODUR)
   ,.TCQ     (TCQ)
)u_ddr_mc_ctl(
    .clk       (clk)
   ,.rst       (rst_r1)

   ,.casSlot2  (casSlot2)
   ,.tranSentC (tranSentC)
   ,.prevCmdAP (prevCmdAP)

   ,.winBankAT  (winBankA)
   ,.win_bank_cas (win_bank_cas)
   ,.winBankPT  (winBankP)
   ,.winGroupAT (winGroupA)
   ,.win_group_cas (win_group_cas)
   ,.winGroupPT (winGroupP)
   ,.winAP      (winAP)
   ,.winCol     (winCol)
   ,.winAct     (winAct)
   ,.winPortC   (winPortC)
   ,.winPortP   (winPortP)
   ,.winRankA   (winRankA)
   ,.win_rank_cas (win_rank_cas)
   ,.winRankP   (winRankP)
   ,.winLRankAT  (winLRankA)
   ,.win_l_rank_cas (win_l_rank_cas)
   ,.winLRankPT  (winLRankP)
   ,.winRead    (winRead)
   ,.winRowA    (winRowA)
   ,.winWrite   (winWrite)

   ,.mc_ACT_n   (mc_ACT_n)
   ,.mc_RAS_n   (mc_RAS_n)
   ,.mc_CAS_n   (mc_CAS_n)
   ,.mc_WE_n    (mc_WE_n)
   ,.mc_ADR     (mc_ADR)
   ,.mc_BA      (mc_BA)
   ,.mc_BG      (mc_BG)
   ,.mc_C       (mc_C)
   ,.mc_CKE     (mc_CKE)
   ,.mc_CS_n    (mc_CS_n)
   ,.mc_ODT     (mc_ODT)

   ,.preIss     (preIss)
   ,.refIss     (refIss)
   ,.zqIss      (zqIss)
   ,.zqIssAll   (zqIssAll)
   ,.refRank    (refRank)
   ,.refLRank   (refLRank)
   ,.per_cas_block_req (per_cas_block_req)
   ,.int_sreIss (int_sreIss)
   ,.int_sreCkeDis (int_sreCkeDis)
   ,.int_srxIss (int_srxIss)
);

ddr4_v2_2_10_mc_cmd_mux_ap #(
    .ABITS (ABITS)
   ,.RKBITS    (RKBITS)
   ,.RANK_SLAB (RANK_SLAB)
   ,.LR_WIDTH (LR_WIDTH)
)u_ddr_mc_cmd_mux_a(
    .winBank  (winBankA)
   ,.winGroup (winGroupA)
   ,.winLRank (winLRankA)
   ,.winRank  (winRankA)
   ,.winRow   (winRowA)

   ,.cmdBank  (cmdBank)
   ,.cmdGroup (cmdGroup)
   ,.cmdLRank (cmdLRank)
   ,.cmdRank  (cmdRank)
   ,.cmdRow   (cmdRow)

   ,.sel      (winPortA)
);

ddr4_v2_2_10_mc_cmd_mux_c #(
    .COLBITS (COLBITS)
   ,.RKBITS    (RKBITS)
   ,.RANK_SLAB (RANK_SLAB)
   ,.LR_WIDTH (LR_WIDTH)
   ,.DBAW    (DBAW)
)u_ddr_mc_cmd_mux_c(
    .winBank   (winBankC)
   ,.winBuf    (winBuf)
   ,.winInjTxn (winInjTxn)
   ,.winRmw    (winRmw)
   ,.winAP     (winAP)
   ,.winCol    (winCol)
   ,.winGroup  (winGroupC)
   ,.winLRank  (winLRankC)
   ,.winRank   (winRankC)
   ,.winSize   (winSize)

   ,.cmdBank  (cmd_bank_cas)
   ,.cmdBuf   (cmdBuf)
   ,.cmdInjTxn (cmdInjTxn)
   ,.cmdRmw    (cmdRmw)
   ,.cmdAP    (cmdAP)
   ,.cmdCol   (cmdCol)
   ,.cmdGroup (cmd_group_cas)
   ,.cmdLRank (cmd_l_rank_cas)
   ,.cmdRank  (cmd_rank_cas)
   ,.cmdSize  (cmdSize)

   ,.sel      (winPortC)
);

ddr4_v2_2_10_mc_ref #(
    .NUMREF     (NUMREF)
   ,.RANKS      (RANKS)
   ,.RANK_SLOT  (RANK_SLOT)
   ,.RKBITS     (RKBITS)
   ,.RANK_SLAB  (RANK_SLAB)
   ,.S_HEIGHT   (S_HEIGHT)
   ,.LR_WIDTH   (LR_WIDTH)
   ,.tREFI      (tREFI)
   ,.tRFC       (tRFC)
   ,.tRFC_dlr   (tRFC_dlr)
   ,.tRP        (tRP)
   ,.tWR        (tWR)
   ,.ZQINTVL    (ZQINTVL)
   ,.tZQCS      (tZQCS)
   ,.TCQ        (TCQ)
   ,.REG_CTRL   (REG_CTRL)
   ,.PARTIAL_RECONFIG (PARTIAL_RECONFIG)
)u_ddr_mc_ref(
    .clk                    (clk)
   ,.rst                    (rst_r1 | dbg_mc_ref_rst)

   ,.preIss                 (preIss)
   ,.refIss                 (refIss)
   ,.zqIss                  (zqIss)
   ,.zqIssAll               (zqIssAll)
   ,.refRank                (refRank)
   ,.refLRank               (refLRank)
   ,.refReq                 (refReq)
   ,.ref_ack                (ref_ack)
   ,.zq_ack                 (zq_ack)
   ,.prevCmdAP              (prevCmdAP)

   ,.mcCKt                  (mcCKt)
   ,.mcCKc                  (mcCKc)
   ,.calDone                (calDone)
   ,.refOK                  (refOK)
   ,.tCWL                   (tCWL)
   ,.per_block_ref          (per_block_ref)
   ,.ref_req                (ref_req)
   ,.zq_req                 (zq_req)
   ,.sre_req                (sre_req)
   ,.sre_ack                (sre_ack)
   ,.ui_busy                (ui_busy)
   ,.txn_fifo_empty         (txn_fifo_empty)
   ,.cas_fifo_empty         (cas_fifo_empty)
   ,.mc_block_req           (mc_block_req)
   ,.sreIss                 (int_sreIss)
   ,.sreCkeDis              (int_sreCkeDis)
   ,.stop_gate_tracking_ack (stop_gate_tracking_ack)
   ,.stop_gate_tracking_req (stop_gate_tracking_req)
   ,.cmd_complete           (cmd_complete)
   ,.srx_cke0_release       (srx_cke0_release)
   ,.srx_req                (srx_req)
   ,.int_srxIss             (int_srxIss)
   ,.dbg_sre_sm_ps          (dbg_sre_sm_ps)
   ,.dbg_refSt              (dbg_refSt)
);

wire [31:0] periodic_config = ( PER_RD_INTVL == 0 ) ? 32'b0 : { 30'b0, calDone, calDone };
wire [31:0] periodic_interval_config = PER_RD_INTVL;
wire        non_per_rd_cas = rdCAS & ~winInjTxn;
reg         stop_prd_reads;
reg         sre_req_r;
reg         sre_req_rEdge;

// Detecting the rising edge of the self-refresh request
always @(posedge clk) begin
   sre_req_r <= #TCQ sre_req;
   if (rst_r1)
      sre_req_rEdge <= #TCQ 1'b0;
   else if (~sre_req_r & sre_req)
      sre_req_rEdge <= #TCQ 1'b1;
end

// Need to stop the periodic reads after self-refresh entry
always @ (posedge clk) begin
  if (rst_r1)
    stop_prd_reads <= #TCQ 0;
  else if (sre_req_rEdge && calDone)
    if ((&txn_fifo_empty) && (&cas_fifo_empty) && (!ui_busy))
      stop_prd_reads <= #TCQ 1;
end

ddr4_v2_2_10_mc_periodic #(
    .TCQ    (TCQ)
)u_ddr_mc_periodic(
    .clk    (clk)
   ,.rst    (rst_r1 | dbg_mc_periodic_rst | stop_prd_reads)
     // Outputs
   ,.per_rd_req         (per_rd_req)
   ,.per_cas_block_req  (per_cas_block_req)
   ,.per_block_ref      (per_block_ref)
   ,.gt_data_ready      (gt_data_ready)
     // Inputs
   ,.periodic_config          (periodic_config)
   ,.periodic_interval_config (periodic_interval_config)
   ,.rdCAS                    (non_per_rd_cas)
   ,.refReq                   (refReq)
   ,.per_rd_done              (per_rd_done)
   ,.per_rd_accept            (per_rd_accept[0])
);

ddr4_v2_2_10_mc_ecc #(
    .PAYLOAD_WIDTH       (PAYLOAD_WIDTH)
   ,.PAYLOAD_DM_WIDTH    (PAYLOAD_DM_WIDTH)
   ,.ECC_WIDTH           (ECC_WIDTH)
   ,.ADDR_FIFO_WIDTH     (ADDR_FIFO_WIDTH)
   ,.S_HEIGHT            (S_HEIGHT)
   ,.LR_WIDTH            (LR_WIDTH)
   ,.DQ_WIDTH            (DQ_WIDTH)
   ,.DQS_WIDTH           (DQ_WIDTH/8)
   ,.DM_WIDTH            (DM_WIDTH)
   ,.nCK_PER_CLK         (nCK_PER_CLK)
   ,.DATA_BUF_ADDR_WIDTH (DBAW)
   ,.ECC                 (ECC)
   ,.MEM                 (MEM)
   ,.ABITS               (ABITS)
   ,.COLBITS             (COLBITS)
   ,.RKBITS              (RKBITS)
   ,.TCQ                 (TCQ)
)u_ddr_mc_ecc(
    .clk    (clk)
   ,.rst    (rst_r1)
   ,.winPortEncC         (winPortEncC)
   ,.non_per_rd_cas      (non_per_rd_cas)
   ,.cmdRmw              (cmdRmw)
   ,.cmdRank             (cmd_rank_cas)
   ,.cmdLRank            (cmd_l_rank_cas)
   ,.cmdRow              (cmd_row_cas)
   ,.cmdCol              (cmdCol)
   ,.cmdBank             (cmd_bank_cas)
   ,.cmdGroup            (cmd_group_cas)
   ,.wr_data_ni2mc       (wr_data_ni2mc)
   ,.wr_data_mask_ni2mc  (wr_data_mask_ni2mc)
   ,.wr_data_addr_phy2mc (wr_data_addr_phy2mc)
   ,.raw_not_ecc         (raw_not_ecc)
   ,.correct_en          (correct_en)
   ,.rmw_rd_done         (rmw_rd_done)
   ,.rd_data_phy2mc_xif  (rd_data_phy2mc_xif)
   ,.rd_data_addr_phy2mc (rd_data_addr_phy2mc)
   ,.rd_data_en_phy2mc   (rd_data_en_phy2mc)
   ,.rd_data_end_phy2mc  (rd_data_end_phy2mc)
   ,.wr_data_mc2phy      (wr_data_mc2phy)
   ,.wr_data_mask_mc2phy (wr_data_mask_mc2phy)
   ,.rd_data_mc2ni       (rd_data_mc2ni)
   ,.rd_data_addr_mc2ni  (rd_data_addr_mc2ni)
   ,.rd_data_en_mc2ni    (rd_data_en_mc2ni)
   ,.rd_data_end_mc2ni   (rd_data_end_mc2ni)
   ,.ecc_err_addr        (ecc_err_addr)
   ,.eccSingle           (eccSingle)
   ,.eccMultiple         (eccMultiple)
   ,.rd_data_phy2mc_cw_order (rd_data_phy2mc)
   ,.fi_xor_we           (fi_xor_we)
   ,.fi_xor_wrdata       (fi_xor_wrdata)
   ,.fi_xor_wrdata_en    (fi_xor_wrdata_en)
);

//synopsys translate_off

`ifdef MEM_INTERNAL
// Events - When asserted high in a test that passes all verification checks, these coverage
//          properties indicate that a functional coverage event has been hit.
// ---------------------------------------------------------------------------------------------

reg  [1:0]  e_calDone_dly;
reg  [63:0] e_new_txn_shift;
wire [63:0] e_new_txn_shift_nxt = { e_new_txn_shift[62:0], useAdr & accept };
reg  [31:0] e_cas_issued;
wire [31:0] e_cas_issued_nxt = { e_cas_issued[30:0], rdCAS | wrCAS };
reg  [4:0]  e_rmw_cmd_dly;
wire [4:0]  e_rmw_cmd_dly_nxt = { e_rmw_cmd_dly[3:0], ( cmd == 3'b011 ) };
reg  [ABITS-1:0] e_row_dly;
reg  [COLBITS-1:0] e_col_dly;
reg  [LR_WIDTH:0] e_lr_dly;
reg  [31:0] e_group_fsm_select_0_shift;
wire [31:0] e_group_fsm_select_0_shift_nxt = { e_group_fsm_select_0_shift[30:0], ( group_fsm_select == 2'b0 ) };
always @(posedge clk) begin
  e_calDone_dly   <= #TCQ { e_calDone_dly[0], calDone };
  e_new_txn_shift <= #TCQ e_new_txn_shift_nxt;
  e_cas_issued    <= #TCQ e_cas_issued_nxt;
  e_rmw_cmd_dly   <= #TCQ e_rmw_cmd_dly_nxt;
  e_row_dly       <= #TCQ row;
  e_col_dly       <= #TCQ col;
  e_lr_dly       <= #TCQ {1'b0, lr[LR_WIDTH-1:0]} + 1;
  e_group_fsm_select_0_shift <= #TCQ e_group_fsm_select_0_shift_nxt;
end

// Transaction accepted on earliest possible cycle after calDone assertion
wire   e_mc_000 = ~e_calDone_dly[1] & e_calDone_dly & useAdr & accept;
always @(posedge clk) mc_000: if (~rst_r1) cover property (e_mc_000);

// 12 transactions accepted in a row
wire   e_mc_001 = & e_new_txn_shift[11:0];
always @(posedge clk) mc_001: if (~rst_r1) cover property (e_mc_001);

// 16 transactions accepted in a row
wire   e_mc_002 = & e_new_txn_shift[15:0];
always @(posedge clk) mc_002: if (~rst_r1) cover property (e_mc_002);

// 32 transactions accepted in a row
wire   e_mc_003 = & e_new_txn_shift[31:0];
always @(posedge clk) mc_003: if (~rst_r1) cover property (e_mc_003);

// 64 transactions accepted in a row
wire   e_mc_004 = & e_new_txn_shift[63:0];
always @(posedge clk) mc_004: if (~rst_r1) cover property (e_mc_004);

// 3 group fsm txn fifos full
wire   e_mc_005 = & txn_fifo_full[2:0];
always @(posedge clk) mc_005: if (~rst_r1) cover property (e_mc_005);

// 4 group fsm txn fifos full
wire   e_mc_006 = & txn_fifo_full[3:0];
always @(posedge clk) mc_006: if (~rst_r1) cover property (e_mc_006);

// 2 group fsm cas fifos full
wire   e_mc_007 = & cas_fifo_full[1:0];
always @(posedge clk) mc_007: if (~rst_r1) cover property (e_mc_007);

// 3 group fsm cas fifos full
wire   e_mc_008 = & cas_fifo_full[2:0];
always @(posedge clk) mc_008: if (~rst_r1) cover property (e_mc_008);

// 4 group fsm cas fifos full
wire   e_mc_009 = & cas_fifo_full[3:0];
always @(posedge clk) mc_009: if (~rst_r1) cover property (e_mc_009);

// 4 rmw accepted in a row
wire   e_mc_011 = ( & e_new_txn_shift[3:0] ) & ( & e_rmw_cmd_dly[4:1] );
always @(posedge clk) mc_011: if (~rst_r1) cover property (e_mc_011);

// Max row bit set
wire   e_mc_012 = useAdr & accept & e_row_dly[ABITS-1];
always @(posedge clk) mc_012: if (~rst_r1) cover property (e_mc_012);

// Max supported row bit set
wire   e_mc_013 = useAdr & accept & e_row_dly[ABITS-1] & ( ABITS == 18 );
always @(posedge clk) mc_013: if (~rst_r1) cover property (e_mc_013);

// All supported row bits set
wire   e_mc_014 = useAdr & accept & ( & e_row_dly ) & ( ABITS == 18 );
always @(posedge clk) mc_014: if (~rst_r1) cover property (e_mc_014);

// Only FSM0 used for 32 fabric cycles
wire   e_mc_015 = ( | e_new_txn_shift[31:0] ) & ( & e_group_fsm_select_0_shift[31:0] ) & ( | e_cas_issued[31:16] );
always @(posedge clk) mc_015: if (~rst_r1) cover property (e_mc_015);

// Max supported col bit set (4G DDR3)
wire   e_mc_016 = useAdr & accept & e_col_dly[COLBITS-1] & ( COLBITS == 11 ) & ( MEM == "DDR3" );
always @(posedge clk) mc_016: if (~rst_r1) cover property (e_mc_016);

// Max supported col bit set (8G DDR3)
wire   e_mc_017 = useAdr & accept & e_col_dly[COLBITS-1] & ( COLBITS == 12 ) & ( MEM == "DDR3" );
always @(posedge clk) mc_017: if (~rst_r1) cover property (e_mc_017);

// Max supported col bit set (DDR4)
wire   e_mc_018 = useAdr & accept & e_col_dly[COLBITS-1] & ( COLBITS == 10 ) & ( MEM == "DDR4" );
always @(posedge clk) mc_018: if (~rst_r1) cover property (e_mc_018);

// Max supported lr set (DDR4 & 3DS)
wire   e_mc_019 = useAdr & accept & e_lr_dly[LR_WIDTH] & ( LR_WIDTH == 3 ) & ( MEM == "DDR4" );
always @(posedge clk) mc_019: if (~rst_r1) cover property (e_mc_019);

// Asserts - When asserted high, an illegal condition has been detected and the test has failed.
// ---------------------------------------------------------------------------------------------

// Transaction accepted before calDone assertion
wire   a_mc_000 = ~calDone & ( accept | accept_ns );
always @(posedge clk) if (~rst_r1) assert property (~a_mc_000);

// calDone de-assertion
wire   a_mc_001 = ~calDone & e_calDone_dly[0];
always @(posedge clk) if (~rst_r1) assert property (~a_mc_001);

// Incorrect 3ds stack height
wire a_mc_002 = (S_HEIGHT == 3) | (S_HEIGHT == 5) | (S_HEIGHT == 6) | (S_HEIGHT == 7);
always @(posedge clk) if (~rst_r1) assert property (~a_mc_002);

`endif

//synopsys translate_on





endmodule


