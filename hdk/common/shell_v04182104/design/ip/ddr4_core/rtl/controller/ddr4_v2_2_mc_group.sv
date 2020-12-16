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
//  /   /         Filename           : ddr4_v2_2_10_mc_group.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                   ddr4_v2_2_10_mc_group module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ns/100ps

module ddr4_v2_2_10_mc_group # (parameter
    ABITS = 18
   ,COLBITS = 10
   ,DBAW = 5
   ,ALIAS_PAGE = "ON"
   ,S_HEIGHT = 1
   ,LR_WIDTH = 1
   ,MEM = "DDR4"
   ,tRCD = 15
   ,tRP = 15
   ,RKBITS = 2
   ,RANK_SLAB = 4
   ,TXN_FIFO_BYPASS = "ON"
   ,TXN_FIFO_PIPE   = "OFF"
   ,PER_RD_PERF     = 1'b1
   ,CAS_FIFO_BYPASS = "ON"
   ,TCQ = 0.1
)(
    input            clk
   ,input            rst

   ,input            calDone
   ,input      [1:0] id
   ,input      [1:0] group_fsm_select

   ,output            accept_ns
   ,output reg        accept
   ,output reg        actReq
   ,output reg        preReq
   ,output reg        rdReq
   ,output reg        wrReq

   ,input            clrReq
   ,input            act_won
   ,input            pre_won
   ,input            cas_won
   ,input            winInjTxn

   ,output reg         [1:0] cmd_bank_cas
   ,output reg         [1:0] cmdBank
   ,output reg         [1:0] cmdBankP
   ,output reg               cmdAP
   ,output reg [COLBITS-1:0] cmdCol
   ,output reg    [DBAW-1:0] cmdBuf
   ,output reg               cmdInjTxn
   ,output reg               cmdRmw
   ,output reg         [1:0] cmd_group_cas
   ,output reg         [1:0] cmdGroup
   ,output reg         [1:0] cmdGroupP
   ,output reg [RKBITS-1:0]  cmd_rank_cas
   ,output reg   [LR_WIDTH-1:0] cmd_l_rank_cas
   ,output reg [RKBITS-1:0]  cmdRank
   ,output reg [RKBITS-1:0]  cmdRankP
   ,output reg   [LR_WIDTH-1:0] cmdLRank
   ,output reg   [LR_WIDTH-1:0] cmdLRankP
   ,output reg               cmdHiPri
   ,output reg   [ABITS-1:0] cmdRow
   ,output reg   [ABITS-1:0] cmd_row_cas
   ,output reg               cmdSize

   ,input         [1:0] bank
   ,input         [2:0] cmd
   ,input               ap
   ,input [COLBITS-1:0] col
   ,input    [DBAW-1:0] dBufAdr
   ,input         [1:0] group
   ,input [LR_WIDTH-1:0]l_rank
   ,input               hiPri
   ,input [RKBITS-1:0]  rank
   ,input   [ABITS-1:0] row
   ,input               size
   ,input               useAdr
   ,input         [3:0] tWTPF
   ,input         [1:0] tRTPF
   ,input         [3:0] tRASF

   ,output reg          refOK
   ,output reg          per_rd_accept

   ,input               readMode
   ,input [RKBITS-1:0]  refRank
   ,input [LR_WIDTH-1:0]refLRank
   ,input               refReq
   ,input               per_rd_req

   ,input                              rmw_rd_done
   ,input [DBAW-1:0]                   rd_data_addr_phy2mc

   ,output reg          txn_fifo_empty
   ,output reg          cas_fifo_empty
   ,output reg          txn_fifo_full
   ,output reg          cas_fifo_full
);


// Pad fifo width to nibble align ap + cmd + LR_WIDTH + ABITS + COLBITS + rank + group + bank;
localparam TXN_FIFO_WIDTH = (S_HEIGHT > 1) ? 53 : 49;
localparam PER_RD_FIELD   = (S_HEIGHT > 1) ? 52 : 48;
localparam AP_FIELD       = (S_HEIGHT > 1) ? 51 : 47;
localparam CMD_MSB        = (S_HEIGHT > 1) ? 50 : 46;
localparam CMD_LSB        = (S_HEIGHT > 1) ? 48 : 44;
localparam LR_UNUSED_MSB  = 47;
localparam LR_MSB         = 46;
localparam LR_LSB         = 44;
localparam ROW_MSB        = 43;
localparam ROW_LSB        = 24;
localparam COL_MSB        = 23;
localparam COL_LSB        =  8;
localparam WSPACE_MSB     =  7;
localparam RANK_MSB       =  4 + RKBITS - 1;
localparam RANK_LSB       =  4;
localparam GROUP_MSB      =  3;
localparam GROUP_LSB      =  2;
localparam BANK_MSB       =  1;
localparam BANK_LSB       =  0;
localparam TXN_FIFO_DEPTH = 4;
localparam TXN_FIFO_FULL_THRESHOLD = TXN_FIFO_DEPTH - 2;
localparam TXN_FIFO_PWIDTH = 2;
localparam CAS_FIFO_DEPTH = 4;
localparam CAS_FIFO_FULL_THRESHOLD = CAS_FIFO_DEPTH - 2;
localparam CAS_FIFO_PWIDTH = 2;

// The parameter ALIAS_PAGE allows two options for page table configuration
//
// Option 1 (ALIAS_PAGE == "ON"):
// the page address within the page table will be concatination of Logical
// Rank address and Row address. The number of page table entries will be 
// number_of_physical_ranks * number_of_banks.
// This option should result in better timing for when number of logical ranks
// and physical ranks are high.
//
// Option 2 (ALIAS_PAGE == "OFF"):
// the page address within the page table will be equal to Row address.
// The number of page table entries will be 
// number_of_physical_ranks * number_of_logical_ranks * number_of_banks.
// This option will result in worse timing than option 1, and should be used
// for cases with low number of physical and logical ranks.
wire [LR_WIDTH-1:0] cmdLRank_3ds;
wire [LR_WIDTH-1:0] refLRank_3ds;
wire [LR_WIDTH-1:0] cmd_l_rank_cas_3ds;
wire [LR_WIDTH-1:0] cmd_l_rank_cas_nxt_3ds;
wire [LR_WIDTH-1:0] cmd_l_rank_cas_nxt;

localparam S_HEIGHT_ALIASED = (ALIAS_PAGE == "ON") ? 1        : S_HEIGHT;
localparam LR_WIDTH_ALIASED = (ALIAS_PAGE == "ON") ? LR_WIDTH : 0;

wire [LR_WIDTH_ALIASED+ABITS-1:0] cmd_lrank_row;
wire [LR_WIDTH_ALIASED+ABITS-1:0] cmd_lrank_row_cas;

(* keep = "TRUE" *) reg rst_r1;

always @(posedge clk)
  rst_r1 <= rst;

generate
  if (S_HEIGHT_ALIASED < 2 & LR_WIDTH_ALIASED == 0) begin
    assign cmdLRank_3ds = '0;
    assign refLRank_3ds = '0;
    assign cmd_l_rank_cas_3ds = '0;
    assign cmd_l_rank_cas_nxt_3ds = '0;
    assign cmd_lrank_row = cmdRow;
    assign cmd_lrank_row_cas = cmd_row_cas;
  end else if (S_HEIGHT_ALIASED < 2) begin
    assign cmdLRank_3ds = '0;
    assign refLRank_3ds = '0;
    assign cmd_l_rank_cas_3ds = '0;
    assign cmd_l_rank_cas_nxt_3ds = '0;
    assign cmd_lrank_row = {cmdLRank, cmdRow};
    assign cmd_lrank_row_cas = {cmd_l_rank_cas, cmd_row_cas};
  end else begin
    assign cmdLRank_3ds = cmdLRank;
    assign refLRank_3ds = refLRank;
    assign cmd_l_rank_cas_3ds = cmd_l_rank_cas;
    assign cmd_l_rank_cas_nxt_3ds = cmd_l_rank_cas_nxt;
    assign cmd_lrank_row = cmdRow;
    assign cmd_lrank_row_cas = cmd_row_cas;
  end
endgenerate

reg [3:0] trcd_cntr             [RANK_SLAB-1:0][S_HEIGHT_ALIASED-1:0][3:0];
reg [3:0] trcd_cntr_nxt         [RANK_SLAB-1:0][S_HEIGHT_ALIASED-1:0][3:0];
reg       trcd_cntr_is_zero     [RANK_SLAB-1:0][S_HEIGHT_ALIASED-1:0][3:0];
reg       trcd_cntr_is_zero_nxt [RANK_SLAB-1:0][S_HEIGHT_ALIASED-1:0][3:0];
reg [4:0] trp_cntr;
reg       trp_cntr_is_zero;
reg [3:0] tras_cntr_rb          [RANK_SLAB-1:0][S_HEIGHT_ALIASED-1:0][3:0];
reg [3:0] tras_cntr_rb_nxt      [RANK_SLAB-1:0][S_HEIGHT_ALIASED-1:0][3:0];
reg [2:0] cmdCmd;
reg       actReqR;
reg       set_act_req;
reg       gr_state_act_wait;
reg       preReqR;
reg       set_pre_req;
reg       rdReqR;
reg       set_rd_req;
reg       set_rd_rmw;
reg       wrReqR;
reg       set_wr_req;
reg [2:0] grSt, grSt_nxt;
reg [2:0] gr_cas_state;
reg [2:0] gr_cas_state_nxt;
reg       cas_state_wait;
reg       cas_state_rmw_wrwait;
reg [2:0] cmd_cmd_cas;
reg       gr_fsm_idle;
reg       issue_cas;
reg       issue_cas_dly;

localparam PAGE_STATUS_BITS = 2;

// pageInfo definition
// upper bits - page
// bit  1     - Autoprecharge in progress
// bit  0     - page open
reg [LR_WIDTH_ALIASED+ABITS+PAGE_STATUS_BITS-1:0] pageInfo     [0:RANK_SLAB-1][S_HEIGHT_ALIASED-1:0][0:3]; // [rank_index][logical_rank_index][bank_index]
reg [LR_WIDTH_ALIASED+ABITS+PAGE_STATUS_BITS-1:0] pageInfo_nxt [0:RANK_SLAB-1][S_HEIGHT_ALIASED-1:0][0:3];
reg [LR_WIDTH_ALIASED+ABITS+PAGE_STATUS_BITS-1:0] pageInfo_ref [0:RANK_SLAB-1][S_HEIGHT_ALIASED-1:0][0:3];
reg [LR_WIDTH_ALIASED+ABITS+PAGE_STATUS_BITS-1:0] pageInfo_act [0:RANK_SLAB-1][S_HEIGHT_ALIASED-1:0][0:3];
reg [LR_WIDTH_ALIASED+ABITS+PAGE_STATUS_BITS-1:0] pageInfo_exp [0:RANK_SLAB-1][S_HEIGHT_ALIASED-1:0][0:3];

// Autoprecharge timers
reg [4:0]     ap_cntr             [0:RANK_SLAB-1][S_HEIGHT_ALIASED-1:0][0:3]; // [rank_index][logical_rank_index][bank_index]
reg [4:0]     ap_cntr_nxt         [0:RANK_SLAB-1][S_HEIGHT_ALIASED-1:0][0:3];
reg [4:0]     ap_cntr_dec         [0:RANK_SLAB-1][S_HEIGHT_ALIASED-1:0][0:3];
reg           ap_cntr_zero        [0:RANK_SLAB-1][S_HEIGHT_ALIASED-1:0][0:3];
reg           ap_cntr_zero_nxt    [0:RANK_SLAB-1][S_HEIGHT_ALIASED-1:0][0:3];
reg           ap_cntr_expired     [0:RANK_SLAB-1][S_HEIGHT_ALIASED-1:0][0:3];
reg           ap_cntr_expired_nxt [0:RANK_SLAB-1][S_HEIGHT_ALIASED-1:0][0:3];
reg [4:0]     ap_load_value;

// Flops to time periodic read injection without corrupting NI traffic
reg  periodic_read_block;
reg  periodic_read_block_dly1;
reg  periodic_read_block_dly2;
reg  periodic_read_block_dly3;

// Flops to time when to force the FSMs back to idle to allow refreshes to make progress
reg ref_req_dly1;
reg ref_req_dly2;
reg ref_req_dly3;
reg ref_req_dly4;

// Flop to block the NI for a periodic read or refresh
reg  periodic_read_or_ref_block;

// Flop the read return for a RMW read
reg  underfill_done;

// Head of line blocking fifo signals
reg  [TXN_FIFO_WIDTH-1:0]  txn_fifo    [TXN_FIFO_DEPTH-1:0];
reg  [TXN_FIFO_WIDTH-1:0]  txn_fifo_nxt[TXN_FIFO_DEPTH-1:0];
reg  [TXN_FIFO_PWIDTH-1:0] txn_fifo_wptr;
reg  [TXN_FIFO_PWIDTH-1:0] txn_fifo_rptr;
reg  [TXN_FIFO_WIDTH-1:0]  txn_fifo_output;
reg  [DBAW-1:0]            buf_fifo    [TXN_FIFO_DEPTH-1:0];
reg  [DBAW-1:0]            buf_fifo_nxt[TXN_FIFO_DEPTH-1:0];
reg                        select_periodic_read;
reg                        periodic_read_push_safe;
reg  [TXN_FIFO_WIDTH-1:0]  periodic_read_address;

// CAS fifo signals
reg  [TXN_FIFO_WIDTH-1:0]  cas_pend_fifo    [CAS_FIFO_DEPTH-1:0];
reg  [TXN_FIFO_WIDTH-1:0]  cas_pend_fifo_nxt[CAS_FIFO_DEPTH-1:0];
reg  [CAS_FIFO_PWIDTH-1:0] cas_fifo_wptr;
reg  [CAS_FIFO_PWIDTH-1:0] cas_fifo_rptr;
reg  [DBAW-1:0]            cas_dbuf_fifo    [CAS_FIFO_DEPTH-1:0];
reg  [DBAW-1:0]            cas_dbuf_fifo_nxt[CAS_FIFO_DEPTH-1:0];
reg  [CAS_FIFO_DEPTH-1:0]  cas_fifo_valid;
reg  [CAS_FIFO_DEPTH-1:0]  cas_fifo_wptr_decode;
reg  [CAS_FIFO_DEPTH-1:0]  cas_fifo_rptr_decode;
reg  [CAS_FIFO_DEPTH-1:0]  cas_pend_cam;
reg  [CAS_FIFO_DEPTH-1:0]  cas_pend_ap_status;

localparam
    grIDLE         = 3'b000
   ,grACCEPT       = 3'b001
   ,grPREWAIT      = 3'b010
   ,grACTWAIT      = 3'b011
   ,grACT          = 3'b100
   ,grAUTOPRE      = 3'b101
   ,grCASFSM       = 3'b110
;

localparam
    CAS_IDLE       = 3'b000
   ,CAS_WAIT       = 3'b001
   ,RMW_RDWAIT     = 3'b010
   ,RMW_DATAWAIT   = 3'b011
   ,RMW_WRWAIT     = 3'b100
;

localparam
    NATRD          = 3'b001
   ,NATWR          = 3'b000
   ,NATRMW         = 3'b011
;

// tRCD minimum spacing is 2 fabric cycles due to group FSM design and scheduler pipeline design. tRP min spacing is 3 fabric cycles.
// When the tRCD or tRP in fabric cycles is <= to their min spacing, no additional delay is needed and the tRCDF and tRPF parameters are set to zero.
localparam
    tRCDF_TEMP       = (tRCD + 4)/4 - 2             // +4 tCK allows for rounding down and 3 tCK of Act slot1 to CAS slot0 spacing
   ,tRCDF            = tRCDF_TEMP > 0 ? tRCDF_TEMP : 0
   ,tRCDFLVALUE_TEMP = tRCDF_TEMP
   ,tRCDFLVALUE      = tRCDFLVALUE_TEMP > 0 ? tRCDFLVALUE_TEMP : 0
   ,tRPF_TEMP        = (tRP  + 5)/4 - 3             // +5 tCK allows for rounding down and 2 tCK of Pre slot3 to Act slot1 spacing
   ,tRPF             = tRPF_TEMP > 0  ? tRPF_TEMP  : 0
;


// ===========================================
// Head of line unblocking FIFO. begin
// ===========================================


// Use a delayed version of per_rd_req to push the txn fifo when the NI is blocked and the fifo is not full
wire        periodic_read_push_safe_nxt = ~txn_fifo_full & periodic_read_block_dly3;
wire        select_periodic_read_nxt = ~periodic_read_push_safe & periodic_read_push_safe_nxt;
wire        per_rd_accept_nxt = select_periodic_read;

// Increment the txn wptr if we accept and receive useAdr.
// Address is pushed into the txn fifo the cycle before the wptr_nxt increments.
wire                       inc_txn_fifo_wptr_accept_useadr = ( accept & useAdr ) & calDone;
wire                       inc_txn_fifo_wptr               = inc_txn_fifo_wptr_accept_useadr | select_periodic_read;
wire [TXN_FIFO_PWIDTH-1:0] txn_fifo_wptr_nxt               = txn_fifo_wptr + { { TXN_FIFO_PWIDTH-1 { 1'b0 } }, inc_txn_fifo_wptr }; // spyglass disable W164a

// Store dBufAdr the cycle after the address is stored
wire       buf_fifo_push     = inc_txn_fifo_wptr;

// Write into the TXN FIFO. Input can be normal traffic or a periodic read.
// The source for periodic reads is selected for best performance or improved timing with parameter PER_RD_PERF.
wire [TXN_FIFO_WIDTH-1:0] txn_out_or_per; // Best performance. PER_RD_PERF = 1.
wire [TXN_FIFO_WIDTH-1:0] txn_inp_or_per; // Best timing.      PER_RD_PERF = 0.
 
// Txn fifo input assignments for both performance and timing options
wire fsm_not_target = ~( group_fsm_select == id );
assign txn_out_or_per[ PER_RD_FIELD : CMD_LSB  ] = select_periodic_read_nxt ? periodic_read_address[ PER_RD_FIELD : CMD_LSB  ] : { 1'b0, ap, cmd };
assign txn_inp_or_per[ PER_RD_FIELD : CMD_LSB  ] = select_periodic_read_nxt ? { 1'b1, 1'b0, NATRD }                            : { 1'b0, ap, cmd };
generate
  if (S_HEIGHT > 1) begin
        assign txn_out_or_per[ LR_UNUSED_MSB: LR_LSB   ] =   select_periodic_read_nxt                    ? periodic_read_address[       LR_UNUSED_MSB: LR_LSB ] : l_rank; // spyglass disable W164b W164c
        assign txn_inp_or_per[ LR_UNUSED_MSB: LR_LSB   ] = ( select_periodic_read_nxt | fsm_not_target ) ? txn_fifo[txn_fifo_wptr_nxt][ LR_UNUSED_MSB: LR_LSB ] : l_rank; // spyglass disable W164b W164c
  end
endgenerate
assign txn_out_or_per[ ROW_MSB     : ROW_LSB  ] =   select_periodic_read_nxt                    ? periodic_read_address[       ROW_MSB    : ROW_LSB  ] : row; // spyglass disable W164b W164c
assign txn_inp_or_per[ ROW_MSB     : ROW_LSB  ] = ( select_periodic_read_nxt | fsm_not_target ) ? txn_fifo[txn_fifo_wptr_nxt][ ROW_MSB    : ROW_LSB  ] : row; // spyglass disable W164b W164c
assign txn_out_or_per[ COL_MSB     : COL_LSB  ] =   select_periodic_read_nxt                    ? periodic_read_address[       COL_MSB    : COL_LSB  ] : col; // spyglass disable W164b W164c
assign txn_inp_or_per[ COL_MSB     : COL_LSB  ] =   select_periodic_read_nxt                    ? txn_fifo[txn_fifo_wptr_nxt][ COL_MSB    : COL_LSB  ] : col; // spyglass disable W164b W164c
assign txn_out_or_per[ WSPACE_MSB  : RANK_LSB ] =   select_periodic_read_nxt                    ? periodic_read_address[       WSPACE_MSB : RANK_LSB ] : rank; // spyglass disable W164b W164c
assign txn_inp_or_per[ WSPACE_MSB  : RANK_LSB ] = ( select_periodic_read_nxt | fsm_not_target ) ? txn_fifo[txn_fifo_wptr_nxt][ WSPACE_MSB : RANK_LSB ] : rank; // spyglass disable W164b W164c
assign txn_out_or_per[ GROUP_MSB   : BANK_LSB ] =   select_periodic_read_nxt                    ? periodic_read_address[       GROUP_MSB  : BANK_LSB ] : { group, bank };
assign txn_inp_or_per[ GROUP_MSB   : BANK_LSB ] = ( select_periodic_read_nxt | fsm_not_target ) ? txn_fifo[txn_fifo_wptr_nxt][ GROUP_MSB  : BANK_LSB ] : { group, bank };

// Select the txn fifo input for performance or timing
wire [TXN_FIFO_WIDTH-1:0] txn_fifo_input = PER_RD_PERF ? txn_out_or_per : txn_inp_or_per;

always @(*) begin
  txn_fifo_nxt                    = txn_fifo;
  txn_fifo_nxt[txn_fifo_wptr_nxt] = txn_fifo_input;
  buf_fifo_nxt                    = buf_fifo;
  buf_fifo_nxt[txn_fifo_wptr]     = buf_fifo_push ? dBufAdr : buf_fifo[txn_fifo_wptr];
end

// Issue accept_ns to the UI when the FIFO is not full and the group_fsm_select is a match
wire txn_fifo_full_nxt  = (txn_fifo_wptr - txn_fifo_rptr) >= TXN_FIFO_FULL_THRESHOLD[TXN_FIFO_PWIDTH-1:0];
wire txn_fifo_accept_ns = ~txn_fifo_full_nxt & ( group_fsm_select == id ) & calDone;
assign accept_ns        = txn_fifo_accept_ns & ~periodic_read_or_ref_block;

// Increment the txn rptr on issue_cas or with a one cycle pipeline to improve timing.
wire                       inc_txn_fifo_rptr   = ( TXN_FIFO_PIPE == "ON" ) ? issue_cas_dly : issue_cas;
wire [TXN_FIFO_PWIDTH-1:0] txn_fifo_rptr_nxt   = txn_fifo_rptr + { { TXN_FIFO_PWIDTH-1 { 1'b0 } }, inc_txn_fifo_rptr }; // spyglass disable W164a

// Generate fifo empty signal and flop for timing.
wire                       txn_fifo_empty_nxt  = txn_fifo_wptr_nxt == txn_fifo_rptr_nxt;

// Flop txn fifo output.
wire [TXN_FIFO_WIDTH-1:0]  txn_fifo_output_nxt = txn_fifo_nxt[txn_fifo_rptr_nxt];

// Read FIFO
wire               fifo_output_per     = txn_fifo_output[ PER_RD_FIELD ];
wire               fifo_output_ap      = txn_fifo_output[ AP_FIELD ];
wire [2:0]         fifo_output_cmd     = txn_fifo_output[ CMD_MSB   : CMD_LSB   ];
wire [ABITS-1:0]   fifo_output_row     = txn_fifo_output[ ROW_MSB   : ROW_LSB   ]; // spyglass disable W164a
wire [COLBITS-1:0] fifo_output_col     = txn_fifo_output[ COL_MSB   : COL_LSB   ]; // spyglass disable W164a
wire [RKBITS-1:0]  fifo_output_rank    = txn_fifo_output[ RANK_MSB  : RANK_LSB  ];
wire [1:0]         fifo_output_group   = txn_fifo_output[ GROUP_MSB : GROUP_LSB ];
wire [1:0]         fifo_output_bank    = txn_fifo_output[ BANK_MSB  : BANK_LSB  ];
wire [LR_WIDTH-1:0]fifo_output_l_rank;
generate
  if (S_HEIGHT > 1) begin
    assign fifo_output_l_rank  = txn_fifo_output[ LR_MSB    : LR_LSB    ]; // spyglass disable W164a
  end else begin
    assign fifo_output_l_rank  = 'b0;
  end
endgenerate
wire [DBAW-1:0]    fifo_output_dBufAdr = buf_fifo_nxt[txn_fifo_rptr];

always @(*) begin
     cmdBank  = fifo_output_bank;
     cmdCmd   = fifo_output_cmd;
     cmdHiPri = '0;
     cmdRank  = fifo_output_rank;
     cmdRow   = fifo_output_row;
     cmdLRank = fifo_output_l_rank;
     cmdSize  = 1'b1;
     cmdGroup = fifo_output_group;
end

// When Logical Rank aliasing is turned on the page contains Logical_Rank and
// Row. When Logical Rank aliasing is turned off, the page contains Row only
wire [LR_WIDTH_ALIASED+ABITS-1:0] page;
wire        open;
wire        ap_in_prog;

// ===========================================
// Head of line unblocking FIFO.  end
// ===========================================


// Sticky flops to capture read and write command requests
wire rd_req_nxt                = ( rdReqR | set_rd_req ) & ~cas_won;
wire rd_rmw_nxt                = ( cmdRmw | set_rd_rmw ) & ~cas_won;
wire wr_req_nxt                = ( wrReqR | set_wr_req ) & ~cas_won;

// Sticky flops to capture precharge and activate command requests
wire       pre_req_nxt         = ( preReqR | set_pre_req ) & ~pre_won;
wire [1:0] pre_bank_nxt        = set_pre_req ? cmdBank  : cmdBankP;
wire [RKBITS-1:0] pre_rank_nxt = set_pre_req ? cmdRank  : cmdRankP;

// When Logical Rank aliasing is turned on the precharge logical rank comes
// from the page table. When Logical Rank aliasing is turned off the precharge 
// logical rank comes from the command since the logical rank is not present in
// the page table.
wire [LR_WIDTH-1:0] pre_l_rank_nxt;

generate
  if (ALIAS_PAGE == "ON")
    assign pre_l_rank_nxt = (set_pre_req) ? page[LR_WIDTH_ALIASED+ABITS-1:ABITS]:
                                            cmdLRankP;
  else
    assign pre_l_rank_nxt = (set_pre_req) ? cmdLRank : 
                                            cmdLRankP;
endgenerate

wire [1:0] pre_group_nxt       = set_pre_req ? cmdGroup : cmdGroupP;
wire       act_req_nxt         = ( actReqR | set_act_req ) & ~act_won;

// Drop command requests when this mc_group wins
always @(*) begin
   actReq = act_won ? 1'b0 : actReqR;
   preReq = pre_won ? 1'b0 : preReqR;
   rdReq  = cas_won ? 1'b0 : rdReqR;
   wrReq  = cas_won ? 1'b0 : wrReqR;
end



integer rank_index;
integer lr_index;
integer bank_index;
integer fifo_entry;

assign {page, ap_in_prog, open} = pageInfo      [cmdRank][cmdLRank_3ds][cmdBank];

generate
always @(*) begin
  for (fifo_entry = 0; fifo_entry < CAS_FIFO_DEPTH; fifo_entry++) begin
    if (ALIAS_PAGE == "OFF" && S_HEIGHT > 1)
      cas_pend_cam     [fifo_entry] = { cmdRank, cmdBank } == { cas_pend_fifo[fifo_entry][RANK_MSB:RANK_LSB], cas_pend_fifo[fifo_entry][1:0] } &
                                      cmdLRank == cas_pend_fifo[fifo_entry][LR_LSB+LR_WIDTH-1:LR_LSB];
    else
      cas_pend_cam     [fifo_entry] = { cmdRank, cmdBank } == { cas_pend_fifo[fifo_entry][RANK_MSB:RANK_LSB], cas_pend_fifo[fifo_entry][1:0] };

    cas_pend_ap_status [fifo_entry] = cas_pend_fifo[fifo_entry][ AP_FIELD ];
  end
end
endgenerate

wire [CAS_FIFO_DEPTH-1:0] cas_pend_vec    = cas_pend_cam & cas_fifo_valid;
wire                      cas_pend        = | cas_pend_vec;
wire [CAS_FIFO_DEPTH-1:0] cas_pend_ap_vec = cas_pend_cam & cas_fifo_valid & cas_pend_ap_status;
wire                      cas_pend_ap     = | cas_pend_ap_vec;

// Capture the address for the last Activate command for use with periodic reads.
// The objective is to issue periodic reads to open pages to minimize the efficiency reduction due to periodic reads.
wire [TXN_FIFO_WIDTH-1:0] periodic_read_address_nxt;

generate
  if (S_HEIGHT > 1)
    assign periodic_read_address_nxt = set_act_req ? { 1'b1, 1'b0, NATRD, txn_fifo_output[ LR_UNUSED_MSB : BANK_LSB ] } : periodic_read_address;
  else
    assign periodic_read_address_nxt = set_act_req ? { 1'b1, 1'b0, NATRD, txn_fifo_output[ ROW_MSB : BANK_LSB ] } : periodic_read_address;
endgenerate

// Set flag to block the NI and inject a periodic read.  Clear the flag when the read is injected.
wire periodic_read_block_nxt = ~select_periodic_read & ( per_rd_req | periodic_read_block );

// Generate a delayed version of per_rd_req used for pushing the periodic read into the txn fifo.
// Clear all stages of the delay pipeline when the read is injected.
wire periodic_read_block_dly1_nxt = periodic_read_block      & ~select_periodic_read;
wire periodic_read_block_dly2_nxt = periodic_read_block_dly1 & ~select_periodic_read;
wire periodic_read_block_dly3_nxt = periodic_read_block_dly2 & ~select_periodic_read;

// Set flag to block the NI for a periodic read or refresh request
wire periodic_read_or_ref_block_nxt = periodic_read_block | periodic_read_block_nxt | refReq;

// Refreshes can make progress when the FSMs are at idle and the NI has been blocked. This guarantees the head of line fifo is empty.
wire ref_ok_nxt         = gr_fsm_idle & cas_fifo_empty & ref_req_dly4;

// Clear the refRank page table entries when refReq and refOK are asserted.  This allows for the refresh FSM to change refRank and refresh more than one rank.
wire ref_rank_clear = refReq & refOK;

// Signal to start processing a new transaction.  Processing can be delayed by a cycle if the page status is stale due to the addition
// of a cycle in the pipeline from issue_cas to cmdRank/Bank/Row for timing.  The txn_fifo_empty bypass can also be disabled for timing.
wire       page_status_stale    = ( TXN_FIFO_PIPE   == "ON" ) & issue_cas_dly;
wire       bypass_txn_available = ( TXN_FIFO_BYPASS == "ON" ) & inc_txn_fifo_wptr_accept_useadr;
wire       new_txn_available    = ~page_status_stale & ( ~txn_fifo_empty | bypass_txn_available );


always @(*) begin
   grSt_nxt = grSt;
   gr_fsm_idle = 1'b0;
   issue_cas = 1'b0;
   set_pre_req = 1'b0;
   set_act_req = 1'b0;
   gr_state_act_wait = 1'b0;
   casez (grSt)
      grIDLE: begin
         gr_fsm_idle = 1'b1;
         if (ref_req_dly4) begin
         end else begin
            if (calDone && ( ( group_fsm_select == id ) | ~txn_fifo_empty ) ) begin
               grSt_nxt = grACCEPT;
            end
         end
      end
      grACCEPT: begin
         if ( new_txn_available & open & ( page==cmd_lrank_row ) & ~cas_fifo_full & ~cas_pend_ap ) begin
            // Page Hit.  Issue CAS and pop the txn fifo.
            issue_cas   = 1'b1;
            grSt_nxt = grACCEPT;
         end else if ( new_txn_available & open & ~( page==cmd_lrank_row ) & ~cas_pend ) begin
            // Page Miss.  Issue precharge
            set_pre_req = 1;
            grSt_nxt = grPREWAIT;
         end else if ( new_txn_available & ap_in_prog & ~cas_pend ) begin
            // Page Miss due to autoprecharge
            grSt_nxt = grAUTOPRE;
         end else if ( new_txn_available & ~open & ~cas_pend ) begin
            // Page Empty.  Issue activate
            set_act_req = 1'b1;
            grSt_nxt = grACTWAIT;
         end else if ( txn_fifo_empty & ref_req_dly4 ) begin
            // Maintenance command is due
            grSt_nxt = grIDLE;
         end else begin
            grSt_nxt = grACCEPT;
         end
      end
      grACTWAIT: begin
         gr_state_act_wait = 1'b1;
         if ( act_won  & ~cas_fifo_full ) begin
           issue_cas = 1'b1;
           grSt_nxt = grACCEPT;
         end else if ( act_won ) begin
           grSt_nxt = grCASFSM;
         end
      end
      grAUTOPRE: begin
         grSt_nxt = grACT;
      end
      grPREWAIT: if (pre_won) begin
         grSt_nxt = grACT;
      end
      grACT: begin
         if ( trp_cntr_is_zero ) begin
           set_act_req = 1'b1;
           grSt_nxt = grACTWAIT;
         end
      end
      grCASFSM: begin
         if ( ~cas_fifo_full ) begin
           issue_cas = 1'b1;
           grSt_nxt = grACCEPT;
         end
      end
      default: ; // error?
   endcase
end


// ===========================================
// CAS pending FIFO. begin
// ===========================================



// CAS fifo input signals are the txn fifo output ports
wire [TXN_FIFO_WIDTH-1:0]  cas_pend_fifo_input = txn_fifo_output;
wire [DBAW-1:0]            cas_dbuf_fifo_input = fifo_output_dBufAdr;

// Write into the fifo at the write pointer on every cycle
always @(*) begin
  cas_pend_fifo_nxt = cas_pend_fifo;
  cas_pend_fifo_nxt[cas_fifo_wptr] = cas_pend_fifo_input;
  cas_dbuf_fifo_nxt = cas_dbuf_fifo;
  cas_dbuf_fifo_nxt[cas_fifo_wptr] = cas_dbuf_fifo_input;
end

// Increment the write pointer when the txn fifo read pointer increments
wire                       cas_pend_fifo_push = issue_cas;
wire [CAS_FIFO_PWIDTH-1:0] cas_fifo_wptr_nxt = cas_fifo_wptr                                              // spyglass disable W164a
                                               + { { CAS_FIFO_PWIDTH-1 { 1'b0 }}, cas_pend_fifo_push };

// Increment the read pointer when a CAS wins, unless it is an underfill read
wire                       cas_pend_fifo_pop = ~( gr_cas_state == RMW_RDWAIT ) & cas_won;
wire [CAS_FIFO_PWIDTH-1:0] cas_fifo_rptr_nxt = cas_fifo_rptr                                              // spyglass disable W164a
                                               + { { CAS_FIFO_PWIDTH-1 { 1'b0 }}, cas_pend_fifo_pop };

// Full before all entries are used
wire                       cas_fifo_empty_nxt = cas_fifo_wptr_nxt == cas_fifo_rptr_nxt;
wire                       cas_fifo_full_nxt  = ( cas_fifo_wptr_nxt - cas_fifo_rptr_nxt ) >= CAS_FIFO_FULL_THRESHOLD[CAS_FIFO_PWIDTH-1:0];

// Track which CAS fifo entries are valid for CAM
always @(*) begin
  cas_fifo_wptr_decode = '0;
  cas_fifo_wptr_decode[cas_fifo_wptr] = 1'b1;
  cas_fifo_rptr_decode = '0;
  cas_fifo_rptr_decode[cas_fifo_rptr] = 1'b1;
end
wire [CAS_FIFO_DEPTH-1:0]  cas_fifo_valid_set = cas_fifo_wptr_decode & { CAS_FIFO_DEPTH { cas_pend_fifo_push } };
wire [CAS_FIFO_DEPTH-1:0]  cas_fifo_valid_clr = cas_fifo_rptr_decode & { CAS_FIFO_DEPTH { cas_pend_fifo_pop  } };
wire [CAS_FIFO_DEPTH-1:0]  cas_fifo_valid_nxt = ~cas_fifo_valid_clr & ( cas_fifo_valid_set | cas_fifo_valid );


// Read CAS FIFO
wire [TXN_FIFO_WIDTH-1:0]  cas_pend_fifo_output    = ( cas_fifo_empty & ( CAS_FIFO_BYPASS == "ON" ) ) ? cas_pend_fifo_input : cas_pend_fifo[cas_fifo_rptr];
wire                       cas_pend_output_per     = cas_pend_fifo_output[ PER_RD_FIELD ];
wire                       cas_pend_output_ap      = cas_pend_fifo_output[ AP_FIELD ];
wire [2:0]                 cas_pend_output_cmd     = cas_pend_fifo_output[ CMD_MSB   : CMD_LSB   ];
wire [ABITS-1:0]           cas_pend_output_row     = cas_pend_fifo_output[ ROW_MSB   : ROW_LSB   ]; // spyglass disable W164a
wire [COLBITS-1:0]         cas_pend_output_col     = cas_pend_fifo_output[ COL_MSB   : COL_LSB   ]; // spyglass disable W164a
wire [RKBITS-1:0]          cas_pend_output_rank    = cas_pend_fifo_output[ RANK_MSB  : RANK_LSB  ];
wire [1:0]                 cas_pend_output_group   = cas_pend_fifo_output[ GROUP_MSB : GROUP_LSB ];
wire [1:0]                 cas_pend_output_bank    = cas_pend_fifo_output[ BANK_MSB  : BANK_LSB  ];
wire [LR_WIDTH-1:0]        cas_pend_output_l_rank;
generate
  if (S_HEIGHT > 1)
    assign cas_pend_output_l_rank  = cas_pend_fifo_output[ LR_MSB    : LR_LSB    ]; // spyglass disable W164a
  else
    assign cas_pend_output_l_rank  = 'b0;
endgenerate
wire [DBAW-1:0]            cas_dbuf_output         = cas_dbuf_fifo[cas_fifo_rptr];

wire [1:0]         cmd_group_cas_nxt     = cas_pend_output_group;
wire [RKBITS-1:0]  cmd_rank_cas_nxt      = cas_pend_output_rank;
wire [1:0]         cmd_bank_cas_nxt      = cas_pend_output_bank;
wire [COLBITS-1:0] cmd_col_nxt           = cas_pend_output_col;
wire               cmd_ap_nxt            = cas_pend_output_ap;
wire [DBAW-1:0]    cmd_buf_nxt           = cas_dbuf_output;
wire [2:0]         cmd_cmd_nxt           = cas_pend_output_cmd;
wire [ABITS-1:0]   cmd_row_cas_nxt       = cas_pend_output_row;
assign             cmd_l_rank_cas_nxt    = cas_pend_output_l_rank;
wire               cmd_inj_txn_nxt       = cas_pend_output_per;

// ===========================================
// CAS pending FIFO. end
// ===========================================



always @(*) begin
   gr_cas_state_nxt = gr_cas_state;
   cas_state_wait       = 1'b0;
   cas_state_rmw_wrwait = 1'b0;
   set_rd_rmw           = 1'b0;
   set_rd_req           = 1'b0;
   set_wr_req           = 1'b0;
   casez (gr_cas_state)
      CAS_IDLE: begin
        if ( ( ( issue_cas & ( CAS_FIFO_BYPASS == "ON" ) ) | ~cas_fifo_empty ) & trcd_cntr_is_zero[cmd_rank_cas_nxt][cmd_l_rank_cas_nxt_3ds][cmd_bank_cas_nxt] & ( cmd_cmd_nxt==NATRMW ) ) begin
          set_rd_req       = 1'b1;
          set_rd_rmw       = 1'b1;
          gr_cas_state_nxt = RMW_RDWAIT;
        end else if ( ( ( issue_cas & ( CAS_FIFO_BYPASS == "ON" ) ) | ~cas_fifo_empty ) & trcd_cntr_is_zero[cmd_rank_cas_nxt][cmd_l_rank_cas_nxt_3ds][cmd_bank_cas_nxt] ) begin
          set_rd_req       = ( cmd_cmd_nxt == NATRD );
          set_wr_req       = ( cmd_cmd_nxt == NATWR );
          gr_cas_state_nxt = CAS_WAIT;
        end
      end
      CAS_WAIT: begin
        cas_state_wait = 1'b1;
        if (cas_won) begin
          gr_cas_state_nxt = CAS_IDLE;
        end
      end
      RMW_RDWAIT: begin
        if (cas_won) begin
          gr_cas_state_nxt = RMW_DATAWAIT;
        end
      end
      RMW_DATAWAIT: begin
        if (underfill_done) begin
          set_wr_req = 1'b1;
          gr_cas_state_nxt = RMW_WRWAIT;
        end
      end
      RMW_WRWAIT: begin
        cas_state_rmw_wrwait = 1'b1;
        if (cas_won) begin
          gr_cas_state_nxt = CAS_IDLE;
        end
      end
      default: ; // error?
   endcase
end


// A RMW underfill is done when a read return buffer matches the latched buffer.
// This logic assumes that buffer addresses for all outstanding read and partial
// writes are unique.
wire underfill_done_nxt = ( rd_data_addr_phy2mc == cmdBuf ) & rmw_rd_done;

// Load timers in the state where we wait for commands to win, otherwise count down.
wire [4:0] trp_cntr_nxt  = ( grSt == grPREWAIT ) ? tRPF  :                                 // spyglass disable W164c
                           ( grSt == grAUTOPRE ) ? ap_cntr[cmdRank][cmdLRank_3ds][cmdBank] : ( trp_cntr  - 5'b1 );

// Generate single flop for timer expired to minimize FSM logic.
wire trp_cntr_is_zero_nxt  = ~( | trp_cntr_nxt );

// Generate CAS to Activate timer load value.  Include remainder of tRAS time for current Rank and Bank.
wire [4:0] tWTPF_extend     = { 1'b0, tWTPF }     + 5'b1;
wire [4:0] tRTPF_extend     = { 3'b0, tRTPF }     + 5'b1;
wire [4:0] tras_cntr_extend = { 1'b0, tras_cntr_rb[cmd_rank_cas][cmd_l_rank_cas_3ds][cmd_bank_cas] };
wire [4:0] wr_ap_load_value = ( tras_cntr_extend >  tWTPF_extend ) ? tras_cntr_extend : tWTPF_extend;
wire [4:0] rd_ap_load_value = ( tras_cntr_extend >  tRTPF_extend ) ? tras_cntr_extend : tRTPF_extend;
wire [4:0] ap_load_value_nxt = wrReqR ? ( wr_ap_load_value + { 1'b0, tRPF } ) : ( rd_ap_load_value + { 1'b0, tRPF } );

// Track page open and CAS with autoprecharge to Activate time on a per Rank per Bank basis
always @(*) begin
  for (rank_index = 0; rank_index <= RANK_SLAB-1; rank_index++) begin
    for (lr_index = 0; lr_index <= S_HEIGHT_ALIASED-1; lr_index++) begin
      for (bank_index = 0; bank_index <= 3; bank_index++) begin

        // Track tRAS for each rankbank
        tras_cntr_rb_nxt        [rank_index][lr_index][bank_index] = ( grSt==grACTWAIT & rank_index==cmdRank & lr_index==cmdLRank_3ds & bank_index==cmdBank )         // spyglass disable W164a
                                                           ? tRASF
                                                                     : ( tras_cntr_rb[rank_index][lr_index][bank_index] - { 3'b0, | tras_cntr_rb[rank_index][lr_index][bank_index] } );

        // Track tRCD for each rankbank
        trcd_cntr_nxt        [rank_index][lr_index][bank_index] = ( grSt==grACTWAIT & ~act_won & rank_index==cmdRank & lr_index==cmdLRank_3ds & bank_index==cmdBank ) // spyglass disable W164c
                                                        ? tRCDFLVALUE
                                                                  : ( trcd_cntr[rank_index][lr_index][bank_index] - { 3'b0, ~trcd_cntr_is_zero[rank_index][lr_index][bank_index] } );
        trcd_cntr_is_zero_nxt[rank_index][lr_index][bank_index] = ~( | trcd_cntr_nxt[rank_index][lr_index][bank_index] );

        // Load or decrement the autoprecharge to activate counter for each rankbank
        ap_cntr_dec     [rank_index][lr_index][bank_index] = ap_cntr[rank_index][lr_index][bank_index] - { 4'b0, ~ap_cntr_zero[rank_index][lr_index][bank_index] }; // spyglass disable W164a
        ap_cntr_nxt     [rank_index][lr_index][bank_index] = ( ( cas_state_wait | cas_state_rmw_wrwait ) & cmdAP & rank_index==cmd_rank_cas & lr_index==cmd_l_rank_cas_3ds & bank_index==cmd_bank_cas )
                                                             ? ap_load_value : ap_cntr_dec[rank_index][lr_index][bank_index][4:0];

        // Detect when the autoprecharge counter hits zero
        ap_cntr_zero_nxt    [rank_index][lr_index][bank_index] = ~( | ap_cntr_nxt[rank_index][lr_index][bank_index] );
        ap_cntr_expired_nxt [rank_index][lr_index][bank_index] = ap_cntr_zero_nxt[rank_index][lr_index][bank_index] & ~ap_cntr_zero[rank_index][lr_index][bank_index];

        // Update the page table on refresh, activate, ap timer expired, and CAS with autoprecharge.
        // No update on explicit precharge needed since precharge and activate are atomic.
        // pageInfo = {page, ap_in_prog, open}
        pageInfo_ref    [rank_index][lr_index][bank_index] = ( grSt==grIDLE & ref_rank_clear & rank_index==refRank & lr_index==refLRank_3ds )
                                                             ? {cmd_lrank_row, 1'b0, 1'b0} : pageInfo    [rank_index][lr_index][bank_index];
        pageInfo_act    [rank_index][lr_index][bank_index] = ( gr_state_act_wait & rank_index==cmdRank & lr_index==cmdLRank_3ds & bank_index==cmdBank )
                                                             ? {cmd_lrank_row, 1'b0, 1'b1} : pageInfo_ref[rank_index][lr_index][bank_index];
        pageInfo_exp    [rank_index][lr_index][bank_index] = ( ap_cntr_expired[rank_index][lr_index][bank_index] )
                                                             ? {cmd_lrank_row, 1'b0, 1'b0} : pageInfo_act[rank_index][lr_index][bank_index];
        pageInfo_nxt    [rank_index][lr_index][bank_index] = ( ( cas_state_wait | cas_state_rmw_wrwait ) & cmdAP
                                                             & rank_index==cmd_rank_cas & lr_index==cmd_l_rank_cas_3ds & bank_index==cmd_bank_cas )
                                                             ? {cmd_lrank_row_cas, 1'b1, 1'b0} : pageInfo_exp[rank_index][lr_index][bank_index];
      end
    end
  end
end

always @(posedge clk) begin
  if (rst_r1) begin
    for (rank_index = 0; rank_index <= RANK_SLAB-1; rank_index++) begin
      for (lr_index = 0; lr_index <= S_HEIGHT_ALIASED-1; lr_index++) begin
      for (bank_index = 0; bank_index <= 3; bank_index++) begin
          pageInfo     [rank_index][lr_index][bank_index]   <= {LR_WIDTH_ALIASED+ABITS+PAGE_STATUS_BITS{1'b0}};
          ap_cntr      [rank_index][lr_index][bank_index]   <= 5'b0;
          ap_cntr_zero [rank_index][lr_index][bank_index]   <= 1'b0;
          trcd_cntr    [rank_index][lr_index][bank_index]   <= #TCQ 4'b0;
          tras_cntr_rb [rank_index][lr_index][bank_index]   <= #TCQ 4'b0;
        end
      end
    end
    periodic_read_block  <= #TCQ 1'b0;
    underfill_done       <= #TCQ 1'b0;
    trp_cntr             <= #TCQ 5'b0;
    for (fifo_entry = 0; fifo_entry < TXN_FIFO_DEPTH; fifo_entry++) txn_fifo[fifo_entry] <= #TCQ '0;
    txn_fifo_wptr        <= #TCQ '0;
    txn_fifo_rptr        <= #TCQ '0;
    cas_fifo_wptr        <= #TCQ '0;
    cas_fifo_rptr        <= #TCQ '0;
    rdReqR               <= #TCQ 1'b0;
    cmdRmw               <= #TCQ 1'b0;
    wrReqR               <= #TCQ 1'b0;
    gr_cas_state         <= #TCQ 3'b0;
    cmdInjTxn            <= #TCQ 1'b0;
    actReqR              <= #TCQ 1'b0;
    preReqR              <= #TCQ 1'b0;
    grSt                 <= #TCQ 3'b0;
    cmdBankP             <= #TCQ 2'b0;
    cmdGroupP            <= #TCQ 2'b0;
    cmdLRankP            <= #TCQ '0;
    cmdRankP             <= #TCQ {RKBITS{1'b0}};
    cmd_group_cas        <= #TCQ 2'b0;
    cmd_rank_cas         <= #TCQ {RKBITS{1'b0}};
    cmd_l_rank_cas       <= #TCQ '0;
    cmd_bank_cas         <= #TCQ 2'b0;
    cmdCol               <= #TCQ '0;
    cmdAP                <= #TCQ 1'b0;
    cmdBuf               <= #TCQ '0;
    cmd_cmd_cas          <= #TCQ '0;
    cmd_row_cas          <= #TCQ '0;
    periodic_read_address  <= #TCQ ( ( 1'b1 << PER_RD_FIELD ) | ( NATRD << CMD_LSB ) );
    cas_fifo_valid         <= #TCQ '0;
  end else begin
    for (rank_index = 0; rank_index <= RANK_SLAB-1; rank_index++) begin
      for (lr_index = 0; lr_index <= S_HEIGHT_ALIASED-1; lr_index++) begin
      for (bank_index = 0; bank_index <= 3; bank_index++) begin
          pageInfo     [rank_index][lr_index][bank_index]    <= #TCQ pageInfo_nxt     [rank_index][lr_index][bank_index];
          ap_cntr      [rank_index][lr_index][bank_index]    <= #TCQ ap_cntr_nxt      [rank_index][lr_index][bank_index];
          ap_cntr_zero [rank_index][lr_index][bank_index]    <= #TCQ ap_cntr_zero_nxt [rank_index][lr_index][bank_index];
          trcd_cntr    [rank_index][lr_index][bank_index]    <= #TCQ trcd_cntr_nxt    [rank_index][lr_index][bank_index];
          tras_cntr_rb [rank_index][lr_index][bank_index]    <= #TCQ tras_cntr_rb_nxt [rank_index][lr_index][bank_index];
        end
      end
    end
    periodic_read_block  <= #TCQ periodic_read_block_nxt;
    underfill_done       <= #TCQ underfill_done_nxt;
    trp_cntr             <= #TCQ trp_cntr_nxt;
    txn_fifo             <= #TCQ txn_fifo_nxt;
    txn_fifo_wptr        <= #TCQ txn_fifo_wptr_nxt;
    txn_fifo_rptr        <= #TCQ txn_fifo_rptr_nxt;
    cas_fifo_wptr        <= #TCQ cas_fifo_wptr_nxt;
    cas_fifo_rptr        <= #TCQ cas_fifo_rptr_nxt;
    rdReqR               <= #TCQ rd_req_nxt;
    cmdRmw               <= #TCQ rd_rmw_nxt;
    wrReqR               <= #TCQ wr_req_nxt;
    gr_cas_state         <= #TCQ gr_cas_state_nxt;
    cmdInjTxn            <= #TCQ cmd_inj_txn_nxt;
    actReqR              <= #TCQ act_req_nxt;
    preReqR              <= #TCQ pre_req_nxt;
    grSt                 <= #TCQ grSt_nxt;
    cmdBankP             <= #TCQ pre_bank_nxt;
    cmdGroupP            <= #TCQ pre_group_nxt;
    cmdLRankP            <= #TCQ pre_l_rank_nxt;
    cmdRankP             <= #TCQ pre_rank_nxt;
    cmd_group_cas        <= #TCQ cmd_group_cas_nxt;
    cmd_rank_cas         <= #TCQ cmd_rank_cas_nxt;
    cmd_l_rank_cas       <= #TCQ cmd_l_rank_cas_nxt;
    cmd_bank_cas         <= #TCQ cmd_bank_cas_nxt;
    cmdCol               <= #TCQ cmd_col_nxt;
    cmdAP                <= #TCQ cmd_ap_nxt;
    cmdBuf               <= #TCQ cmd_buf_nxt;
    cmd_cmd_cas          <= #TCQ cmd_cmd_nxt;
    cmd_row_cas          <= #TCQ cmd_row_cas_nxt;
    periodic_read_address  <= #TCQ periodic_read_address_nxt;
    cas_fifo_valid         <= #TCQ cas_fifo_valid_nxt;
  end
end


always @(posedge clk) begin
    for (rank_index = 0; rank_index <= RANK_SLAB-1; rank_index++) begin
      for (lr_index = 0; lr_index <= S_HEIGHT_ALIASED-1; lr_index++) begin
      for (bank_index = 0; bank_index <= 3; bank_index++) begin
          ap_cntr_expired  [rank_index][lr_index][bank_index]  <= #TCQ ap_cntr_expired_nxt  [rank_index][lr_index][bank_index];
          trcd_cntr_is_zero[rank_index][lr_index][bank_index]  <= #TCQ trcd_cntr_is_zero_nxt[rank_index][lr_index][bank_index];
        end
      end
    end
    trp_cntr_is_zero       <= #TCQ trp_cntr_is_zero_nxt;
    ap_load_value          <= #TCQ ap_load_value_nxt;
    txn_fifo_full          <= #TCQ txn_fifo_full_nxt;
    buf_fifo               <= #TCQ buf_fifo_nxt;
    txn_fifo_empty         <= #TCQ txn_fifo_empty_nxt;
    cas_pend_fifo          <= #TCQ cas_pend_fifo_nxt;
    cas_dbuf_fifo          <= #TCQ cas_dbuf_fifo_nxt;
    cas_fifo_empty         <= #TCQ cas_fifo_empty_nxt;
    cas_fifo_full          <= #TCQ cas_fifo_full_nxt;
    accept                 <= #TCQ accept_ns;
    per_rd_accept          <= #TCQ per_rd_accept_nxt;
    refOK                  <= #TCQ ref_ok_nxt;
    periodic_read_block_dly1 <= #TCQ periodic_read_block_dly1_nxt;
    periodic_read_block_dly2 <= #TCQ periodic_read_block_dly2_nxt;
    periodic_read_block_dly3 <= #TCQ periodic_read_block_dly3_nxt;
    periodic_read_push_safe  <= #TCQ periodic_read_push_safe_nxt;
    select_periodic_read     <= #TCQ select_periodic_read_nxt;
    periodic_read_or_ref_block  <= #TCQ periodic_read_or_ref_block_nxt;
    ref_req_dly1                <= #TCQ refReq;
    ref_req_dly2                <= #TCQ ref_req_dly1;
    ref_req_dly3                <= #TCQ ref_req_dly2;
    ref_req_dly4                <= #TCQ ref_req_dly3;
    txn_fifo_output             <= #TCQ txn_fifo_output_nxt;
    issue_cas_dly               <= #TCQ issue_cas;
end

//synopsys translate_off

`ifdef MEM_INTERNAL
// Events - When asserted high in a test that passes all verification checks, these coverage
//          properties indicate that a functional coverage event has been hit.
// ---------------------------------------------------------------------------------------------

// Both FIFOs full at the same time
wire   e_mc_group_000_fifos_full = txn_fifo_full & cas_fifo_full;
always @(posedge clk) mc_group_000: if (~rst_r1) cover property (e_mc_group_000_fifos_full);

// Precharge blocked by pending CAS to same rank and bank
wire   e_mc_group_001_pre_blocked = ( grSt == grACCEPT ) & new_txn_available & open & ~( page==cmd_lrank_row ) & cas_pend;
always @(posedge clk) mc_group_001: if (~rst_r1) cover property (e_mc_group_001_pre_blocked);

// Page hit blocked by pending CAS with autoprecharge to same rank and bank
wire   e_mc_group_002_cas_blocked = ( grSt == grACCEPT ) & new_txn_available & open & ( page==cmd_lrank_row ) & ~cas_fifo_full & cas_pend_ap;
always @(posedge clk) mc_group_002: if (~rst_r1) cover property (e_mc_group_002_cas_blocked);

// Page empty due to autoprecharge currently in progress to same rank and bank
wire   e_mc_group_003_act_due     = ( grSt == grACCEPT ) & new_txn_available & ap_in_prog & ~cas_pend;
always @(posedge clk) mc_group_003: if (~rst_r1) cover property (e_mc_group_003_act_due);

// Issue cas after waiting for cas fifo entry
wire   e_mc_group_004_cas_stalled = ( grSt == grACTWAIT ) & act_won & cas_fifo_full;
always @(posedge clk) mc_group_004: if (~rst_r1) cover property (e_mc_group_004_cas_stalled);

// Txn fifo greater than full level.  This can happen due to accept_ns to accept skid.
wire   e_mc_group_005_extra_full  = (txn_fifo_wptr - txn_fifo_rptr) > TXN_FIFO_FULL_THRESHOLD[TXN_FIFO_PWIDTH-1:0];
always @(posedge clk) mc_group_005: if (~rst_r1) cover property (e_mc_group_005_extra_full);

// Txn fifo empty and new transaction flows through.
wire   e_mc_group_006_txn_thru    = txn_fifo_empty & inc_txn_fifo_rptr & inc_txn_fifo_wptr;
always @(posedge clk) mc_group_006: if (~rst_r1) cover property (e_mc_group_006_txn_thru);

// Six transactions accepted in a row
reg  [255:0] e_accept_shift;
wire [255:0] e_accept_shift_nxt = { e_accept_shift[254:0], useAdr & accept };
always    @(posedge clk)  e_accept_shift <= #TCQ ( e_accept_shift_nxt );
wire   e_mc_group_007_txn6    =  & e_accept_shift[5:0];
always @(posedge clk) mc_group_007: if (~rst_r1) cover property (e_mc_group_007_txn6);

// Five transactions accepted in a row
wire   e_mc_group_008_txn5    =  & e_accept_shift[4:0];
always @(posedge clk) mc_group_008: if (~rst_r1) cover property (e_mc_group_008_txn5);

// Four transactions accepted in a row
wire   e_mc_group_009_txn4    =  & e_accept_shift[3:0];
always @(posedge clk) mc_group_009: if (~rst_r1) cover property (e_mc_group_009_txn4);

// Bursty traffic - 4 txns in a row, multiple times, but separated by large dead times
reg  [255:0] e_burst_shift;
wire [255:0] e_burst_shift_nxt = { e_burst_shift[254:0], e_mc_group_009_txn4 };
always    @(posedge clk)  e_burst_shift <= #TCQ ( e_burst_shift_nxt );
wire   e_mc_group_010_txn    =  ( | e_burst_shift[255:240] ) & ~( | e_accept_shift[230:150] )
                                & ( | e_burst_shift[140:120] ) & ~( | e_accept_shift[110:30] ) & ( | e_burst_shift[20:0] );
always @(posedge clk) mc_group_010: if (~rst_r1) cover property (e_mc_group_010_txn);

// Read write mix
reg  [2:0]  e_cmd_dly;
always    @(posedge clk)  e_cmd_dly <= #TCQ ( cmd );
reg  [5:0] e_read_shift;
wire [5:0] e_read_shift_nxt = { e_read_shift[4:0], useAdr & accept & ( e_cmd_dly == NATRD ) };
always    @(posedge clk)  e_read_shift <= #TCQ ( e_read_shift_nxt );
wire   e_mc_group_011_mix    =  ( & e_accept_shift[3:0] ) & ( e_read_shift[3:0] == 4'b0010 );
always @(posedge clk) mc_group_011: if (~rst_r1) cover property (e_mc_group_011_mix);

wire   e_mc_group_012_mix    =  ( & e_accept_shift[3:0] ) & ( e_read_shift[3:0] == 4'b1101 );
always @(posedge clk) mc_group_012: if (~rst_r1) cover property (e_mc_group_012_mix);

wire   e_mc_group_013_mix    =  ( & e_accept_shift[4:0] ) & ( e_read_shift[4:0] == 5'b00010 );
always @(posedge clk) mc_group_013: if (~rst_r1) cover property (e_mc_group_011_mix);

wire   e_mc_group_014_mix    =  ( & e_accept_shift[4:0] ) & ( e_read_shift[4:0] == 5'b11101 );
always @(posedge clk) mc_group_014: if (~rst_r1) cover property (e_mc_group_012_mix);

reg  [5:0] e_rmw_shift;
wire [5:0] e_rmw_shift_nxt = { e_rmw_shift[4:0], useAdr & accept & ( e_cmd_dly == NATRMW ) };
always    @(posedge clk)  e_rmw_shift <= #TCQ ( e_rmw_shift_nxt );
wire   e_mc_group_015_mix    =  ( & e_accept_shift[3:0] ) & ( e_rmw_shift[3:0] == 4'b1111 );
always @(posedge clk) mc_group_015: if (~rst_r1) cover property (e_mc_group_015_mix);

wire   e_mc_group_016_mix    =  ( & e_accept_shift[4:0] ) & ( e_rmw_shift[4:0] == 5'b01110 ) & ( e_read_shift[4:0] == 5'b10001 );
always @(posedge clk) mc_group_016: if (~rst_r1) cover property (e_mc_group_016_mix);

wire   e_mc_group_017_mix    =  ( & e_accept_shift[4:0] ) & ( e_rmw_shift[4:0] == 5'b01110 ) & ( e_read_shift[4:0] == 5'b00000 );
always @(posedge clk) mc_group_017: if (~rst_r1) cover property (e_mc_group_017_mix);

// Refresh closes open pages
reg [3:0] e_ref_rank_bank_closed_down;
always @(*) begin
    for (bank_index = 0; bank_index <= 3; bank_index++) begin
       e_ref_rank_bank_closed_down[bank_index] = ( pageInfo[refRank][refLRank_3ds][bank_index][0] ) & ref_rank_clear & ( grSt==grIDLE );
    end
end
wire   e_mc_group_018_ref    = | e_ref_rank_bank_closed_down;
always @(posedge clk) mc_group_018: if (~rst_r1) cover property (e_mc_group_018_ref);

// Refresh to rank with all banks open
wire   e_mc_group_019_ref    = & e_ref_rank_bank_closed_down;
always @(posedge clk) mc_group_019: if (~rst_r1) cover property (e_mc_group_019_ref);

// Refresh to multiple ranks
reg    e_ref_rank_clear_dly;
wire   e_ref_rank_clear_nxt = ref_rank_clear & ( grSt==grIDLE );
always    @(posedge clk) e_ref_rank_clear_dly  <= #TCQ ( e_ref_rank_clear_nxt );
reg [RKBITS-1:0] e_ref_rank_dly;
always    @(posedge clk) e_ref_rank_dly  <= #TCQ ( refRank );
wire   e_mc_group_020_ref    = e_ref_rank_clear_dly & ref_rank_clear & ( grSt==grIDLE ) & ~( e_ref_rank_dly == refRank );
always @(posedge clk) mc_group_020: if (~rst_r1) cover property (e_mc_group_020_ref);

// Refresh requested with busy group fsm
wire   e_mc_group_021_ref    = ~gr_fsm_idle & ~cas_fifo_empty & ref_req_dly4;
always @(posedge clk) mc_group_021: if (~rst_r1) cover property (e_mc_group_021_ref);

// Group idle and then two transactions accepted after refresh request
reg        e_group_accept;
wire       e_group_accept_nxt      = inc_txn_fifo_wptr_accept_useadr;
always     @(posedge clk) e_group_accept  <= #TCQ ( e_group_accept_nxt );
reg        e_group_idle_refreq;
wire       e_group_idle_refreq_nxt = ( grSt==grACCEPT ) & txn_fifo_empty
                                     & cas_fifo_empty & ( gr_cas_state == CAS_IDLE )
                                     & refReq & ~ref_req_dly1;
always     @(posedge clk) e_group_idle_refreq  <= #TCQ ( e_group_idle_refreq_nxt );
wire       e_mc_group_022_ref    = e_group_idle_refreq & e_group_accept;
always @(posedge clk) mc_group_022: if (~rst_r1) cover property (e_mc_group_022_ref);
wire       e_mc_group_022a_ref    = e_group_idle_refreq & e_group_accept & e_group_accept_nxt;
always @(posedge clk) mc_group_022a: if (~rst_r1) cover property (e_mc_group_022a_ref);


// Group idle and then two transactions accepted after periodic read request
reg        e_group_idle_per_rd_req;
wire       e_group_idle_per_rd_req_nxt = ( grSt==grACCEPT ) & txn_fifo_empty
                                       & cas_fifo_empty & ( gr_cas_state == CAS_IDLE )
                                       & per_rd_req & ~periodic_read_block;
always     @(posedge clk) e_group_idle_per_rd_req  <= #TCQ ( e_group_idle_per_rd_req_nxt );
wire       e_mc_group_023_per    = e_group_idle_per_rd_req & e_group_accept;
always @(posedge clk) mc_group_023: if (~rst_r1) cover property (e_mc_group_023_per);
wire       e_mc_group_023a_per    = e_group_idle_per_rd_req & e_group_accept & e_group_accept_nxt;
always @(posedge clk) mc_group_023a: if (~rst_r1) cover property (e_mc_group_023a_per);

// Periodic read push into the txn fifo delayed due to a full fifo
wire       e_mc_group_024_per    = txn_fifo_full & periodic_read_block_dly3;
always @(posedge clk) mc_group_024: if (~rst_r1) cover property (e_mc_group_024_per);

// All rankbanks open at the same time
reg e_all_pages_open;
reg [3:0] e_num_ap_in_prog;
always @(*) begin
  e_all_pages_open = 1'b1;
  e_num_ap_in_prog = 4'b0;
  for (rank_index = 0; rank_index <= RANK_SLAB-1; rank_index++) begin
    for (lr_index = 0; lr_index <= S_HEIGHT_ALIASED-1; lr_index++) begin
      for (bank_index = 0; bank_index <= 3; bank_index++) begin
        e_all_pages_open &= pageInfo[rank_index][lr_index][bank_index][0];
        e_num_ap_in_prog += pageInfo[rank_index][lr_index][bank_index][1];
      end
    end
  end
end
wire       e_mc_group_025_open    = e_all_pages_open;
always @(posedge clk) mc_group_025: if (~rst_r1) cover property (e_mc_group_025_open);

// At least 4 auto_precharges in progress at the same time
wire       e_mc_group_026_ap      = e_num_ap_in_prog >= 4'd4;
always @(posedge clk) mc_group_026: if (~rst_r1) cover property (e_mc_group_026_ap);

// Max row address open in rank 3 LR max bank 3 and min row address open in rank 0 lr 0 bank 0
wire       e_mc_group_027_row     =    ( & pageInfo[3][S_HEIGHT_ALIASED-1][3][PAGE_STATUS_BITS+:ABITS] ) & pageInfo[3][0][3][0]
                                    & ~( | pageInfo[0][0                 ][0][PAGE_STATUS_BITS+:ABITS] ) & pageInfo[0][0][0][0]
                                    &  ( ABITS == 18 );
always @(posedge clk) mc_group_027: if (~rst_r1) cover property (e_mc_group_027_row);

// Periodic read is page miss
wire       e_mc_group_028_per     = pre_won & fifo_output_per;
always @(posedge clk) mc_group_028: if (~rst_r1) cover property (e_mc_group_028_per);

// Read with autoprecharge and explicit precharge on same fabric cycle
wire       e_mc_group_029_pre     = pre_won & cas_won & rdReqR & cmdAP;
always @(posedge clk) mc_group_029: if (~rst_r1) cover property (e_mc_group_029_pre);

// Write with autoprecharge and explicit precharge on same fabric cycle
wire       e_mc_group_030_pre     = pre_won & cas_won & wrReqR & cmdAP;
always @(posedge clk) mc_group_030: if (~rst_r1) cover property (e_mc_group_030_pre);

// Act and CAS in the same cycle
wire       e_mc_group_031_cas     = act_won & cas_won;
always @(posedge clk) mc_group_031: if (~rst_r1) cover property (e_mc_group_031_cas);

// RMW read
wire       e_mc_group_032_rmw     = cmdRmw & cas_won & rdReqR;
always @(posedge clk) mc_group_032: if (~rst_r1) cover property (e_mc_group_032_rmw);

// RMW write without autoprecharge
wire       e_mc_group_033_rmw     = cas_won & cas_state_rmw_wrwait & ~cmdAP;
always @(posedge clk) mc_group_033: if (~rst_r1) cover property (e_mc_group_033_rmw);

// RMW write with autoprecharge
wire       e_mc_group_034_rmw     = cas_won & cas_state_rmw_wrwait & cmdAP;
always @(posedge clk) mc_group_034: if (~rst_r1) cover property (e_mc_group_034_rmw);

// Precharge with tRPF at zero
wire       e_mc_group_035_trp     = ( tRPF == 0 ) & ( grSt == grPREWAIT );
always @(posedge clk) mc_group_035: if (~rst_r1) cover property (e_mc_group_035_trp);

// Activate timing limited by non-zero tRPF
wire       e_mc_group_036_trp     = ( tRPF > 0 ) & ( grSt == grACT ) & ~trp_cntr_is_zero;
always @(posedge clk) mc_group_036: if (~rst_r1) cover property (e_mc_group_036_trp);

// Activate with tRCDFLVALUE at zero and cas fifo not full
wire       e_mc_group_037_trcd    = ( tRCDFLVALUE == 0 ) & ( grSt == grACTWAIT ) & act_won & ~cas_fifo_full;
always @(posedge clk) mc_group_037: if (~rst_r1) cover property (e_mc_group_037_trcd);

// CAS timing limited by non-zero tRCDFLVALUE
wire       e_mc_group_038_trcd    = ( tRCDFLVALUE > 0 ) & ( gr_cas_state == CAS_IDLE ) & ( issue_cas | ~cas_fifo_empty ) & ~trcd_cntr_is_zero[cmd_rank_cas_nxt][cmd_l_rank_cas_nxt_3ds][cmd_bank_cas_nxt];
always @(posedge clk) mc_group_038: if (~rst_r1) cover property (e_mc_group_038_trcd);

// tRAS limiting AP done timer after read
wire       e_mc_group_039_tras    = ( tras_cntr_extend >  tRTPF_extend ) & ( cas_state_wait | cas_state_rmw_wrwait ) & cmdAP;
always @(posedge clk) mc_group_039: if (~rst_r1) cover property (e_mc_group_039_tras);

// tRAS limiting AP done timer after write
wire       e_mc_group_040_tras    = ( tras_cntr_extend >  tWTPF_extend ) & ( cas_state_wait | cas_state_rmw_wrwait ) & cmdAP;
always @(posedge clk) mc_group_040: if (~rst_r1) cover property (e_mc_group_040_tras);

// tRTP limiting AP done timer after read
wire       e_mc_group_041_trtp    = ( tras_cntr_extend <  tRTPF_extend ) & ( cas_state_wait | cas_state_rmw_wrwait ) & cmdAP;
always @(posedge clk) mc_group_041: if (~rst_r1) cover property (e_mc_group_041_trtp);

// tWTP limiting AP done timer after write
wire       e_mc_group_042_twtp    = ( tras_cntr_extend <  tWTPF_extend ) & ( cas_state_wait | cas_state_rmw_wrwait ) & cmdAP;
always @(posedge clk) mc_group_042: if (~rst_r1) cover property (e_mc_group_042_twtp);

// Periodic read is page empty
wire       e_mc_group_043_per     = act_won & fifo_output_per;
always @(posedge clk) mc_group_043: if (~rst_r1) cover property (e_mc_group_043_per);

// Pre-charge & activate aliased LR
wire       pre_page_dly_nxt = pre_won & ( grSt == grPREWAIT );
reg        pre_page_dly;
always @(posedge clk) pre_page_dly <= #TCQ pre_page_dly_nxt;
wire       e_mc_group_044_pre_aliased_lr = ALIAS_PAGE == "ON" & S_HEIGHT > 1
                                           & pre_page_dly & ( grSt == grACT ) & ~( cmdLRankP == cmdLRank );
always @(posedge clk) mc_group_044: if (~rst_r1) cover property (e_mc_group_044_pre_aliased_lr);

// Pre-charge & activate non-aliased LR
wire       e_mc_group_045_pre_lr = ALIAS_PAGE == "OFF" & S_HEIGHT > 1
                                   & pre_page_dly & ( grSt == grACT ) & ( cmdLRankP == cmdLRank );
always @(posedge clk) mc_group_045: if (~rst_r1) cover property (e_mc_group_045_pre_lr);

// cas_pend_cam coverage in 3DS
integer cas_pend_num = 0;
reg     e_mc_group_046_all_cas_pend_set;
always @(*) begin
  if (cas_pend_cam[cas_pend_num] === 1'b1 & cas_fifo_valid[cas_pend_num] === 1'b1 & cas_pend_num < CAS_FIFO_DEPTH) cas_pend_num++;
  e_mc_group_046_all_cas_pend_set = (cas_pend_num == CAS_FIFO_DEPTH) & ALIAS_PAGE == "OFF" & S_HEIGHT > 1;
end
always @(posedge clk) mc_group_046: if (~rst_r1) cover property (e_mc_group_046_all_cas_pend_set);

// Asserts - When asserted high, an illegal condition has been detected and the test has failed.
// ---------------------------------------------------------------------------------------------

// Txn fifo overflow. Maximum allowed txn fifo pointer separation is depth - 1
wire   a_mc_group_000_txn_of      = (txn_fifo_wptr - txn_fifo_rptr) == (TXN_FIFO_DEPTH[TXN_FIFO_PWIDTH-1:0] -1) & inc_txn_fifo_wptr;
always @(posedge clk) if (~rst_r1) assert property (~a_mc_group_000_txn_of);

// Txn fifo underflow.
wire   a_mc_group_001_txn_uf      = txn_fifo_empty & inc_txn_fifo_rptr & ~inc_txn_fifo_wptr;
always @(posedge clk) if (~rst_r1) assert property (~a_mc_group_001_txn_uf);

// Cas fifo overflow.
wire   a_mc_group_002_cas_of      = cas_fifo_full & cas_pend_fifo_push;
always @(posedge clk) if (~rst_r1) assert property (~a_mc_group_002_cas_of);

// Cas fifo underflow.
wire   a_mc_group_003_cas_uf      = cas_fifo_empty & cas_pend_fifo_pop;
always @(posedge clk) if (~rst_r1) assert property (~a_mc_group_003_cas_uf);

// Non-aliased precharge and activate LR not matching
wire   a_mc_group_004_pre_lr = ALIAS_PAGE == "OFF" & S_HEIGHT > 1
                               & pre_page_dly & ( grSt == grACT ) & ~( cmdLRankP == cmdLRank );
always @(posedge clk) if (~rst_r1) assert property (~a_mc_group_004_pre_lr);

// Check for Page aliasing
wire   a_mc_group_005_p_alias = ALIAS_PAGE == "ON" & S_HEIGHT > 1
                                & ~(( cmd_lrank_row == {cmdLRank, cmdRow} ) & ( cmd_lrank_row_cas == {cmd_l_rank_cas, cmd_row_cas} ));
always @(posedge clk) if (~rst_r1) assert property (~a_mc_group_005_p_alias);

`endif


reg [71:0] stName;

always @(*) casez (grSt)
   grIDLE            : stName = "grIDLE";     // spyglass disable W164c
   grACCEPT          : stName = "grACCEPT";   // spyglass disable W164c
   grPREWAIT         : stName = "grPREWAIT";
   grACTWAIT         : stName = "grACTWAIT";
   grACT             : stName = "grACT";      // spyglass disable W164c
   grAUTOPRE         : stName = "grAUTOPRE";
   grCASFSM          : stName = "grCASFSM";   // spyglass disable W164c
   default           : stName = "ERROR";      // spyglass disable W164c
endcase

reg [95:0] stCASName;

always @(*) casez (gr_cas_state)
      CAS_IDLE       : stCASName = "CAS_IDLE";     // spyglass disable W164c
      CAS_WAIT       : stCASName = "CAS_WAIT";     // spyglass disable W164c
      RMW_RDWAIT     : stCASName = "CAS_RDWAIT";   // spyglass disable W164c
      RMW_DATAWAIT   : stCASName = "CAS_DATAWAIT";
      RMW_WRWAIT     : stCASName = "CAS_WRWAIT";   // spyglass disable W164c
      default        : stCASName = "ERROR";        // spyglass disable W164c
endcase

// Unroll multi-dimensional arrays for waveform viewing
wire       e_trcd_cntr_is_zero_0_0 = trcd_cntr_is_zero[0][0][0];
wire       e_trcd_cntr_is_zero_0_1 = trcd_cntr_is_zero[0][0][1];
wire       e_trcd_cntr_is_zero_0_2 = trcd_cntr_is_zero[0][0][2];
wire       e_trcd_cntr_is_zero_0_3 = trcd_cntr_is_zero[0][0][3];
wire [3:0] e_trcd_cntr_0_0         = trcd_cntr[0][0][0];
wire [3:0] e_trcd_cntr_0_1         = trcd_cntr[0][0][1];
wire [3:0] e_trcd_cntr_0_2         = trcd_cntr[0][0][2];
wire [3:0] e_trcd_cntr_0_3         = trcd_cntr[0][0][3];
wire [3:0] e_trcdf                 = tRCDF[3:0];
wire [3:0] e_trcdflvalue           = tRCDFLVALUE[3:0];
wire [7:0] e_trcd                  = tRCD[7:0];
wire [4:0] e_ap_cntr_0_0           = ap_cntr[0][0][0];
wire [4:0] e_ap_cntr_0_1           = ap_cntr[0][0][1];
wire [4:0] e_ap_cntr_0_2           = ap_cntr[0][0][2];
wire [4:0] e_ap_cntr_0_3           = ap_cntr[0][0][3];
wire [4:0] e_ap_cntr_1_0           = ap_cntr[1][0][0];
wire [4:0] e_ap_cntr_1_1           = ap_cntr[1][0][1];
wire [4:0] e_ap_cntr_1_2           = ap_cntr[1][0][2];
wire [4:0] e_ap_cntr_1_3           = ap_cntr[1][0][3];
wire [4:0] e_ap_cntr_2_0           = ap_cntr[2][0][0];
wire [4:0] e_ap_cntr_2_1           = ap_cntr[2][0][1];
wire [4:0] e_ap_cntr_2_2           = ap_cntr[2][0][2];
wire [4:0] e_ap_cntr_2_3           = ap_cntr[2][0][3];
wire [4:0] e_ap_cntr_3_0           = ap_cntr[3][0][0];
wire [4:0] e_ap_cntr_3_1           = ap_cntr[3][0][1];
wire [4:0] e_ap_cntr_3_2           = ap_cntr[3][0][2];
wire [4:0] e_ap_cntr_3_3           = ap_cntr[3][0][3];
wire [4:0] e_trp                   = tRP;
wire [4:0] e_trpf                  = tRPF; // spyglass disable W164c
//synopsys translate_on

endmodule

