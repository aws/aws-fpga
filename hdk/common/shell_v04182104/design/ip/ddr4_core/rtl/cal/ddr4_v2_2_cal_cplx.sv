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
//  /   /         Filename           : ddr4_v2_2_10_cal_cplx.sv
// /___/   /\     Date Last Modified : $Date: 2015/04/23 $
// \   \  /  \    Date Created       : Mon Jan 20 2014
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                   ddr4_v2_2_10_cal_cplx module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ps/1ps

module ddr4_v2_2_10_cal_cplx  #
  (
   parameter DBYTES       = 4, //Data Bytes
   parameter ABITS        = 18, //ADDRESS BITS
   parameter BABITS = 4,
   parameter BGBITS = 4,
   parameter CKEBITS =4,
   parameter CSBITS =2,
   parameter ODTBITS = 4,
   parameter MEM = "DDR4",
   parameter TCQ = 100,
   parameter CPLX_PAT_LENGTH = "LONG",
   parameter CLK_2TO1 = "TRUE",
   parameter EXTRA_CMD_DELAY = 0,
   parameter WL = 9
  )
  (
   input                           clk,
   input                           rst,                    //sync reset
   input       [31:0]              cplx_config,                             // spyglass disable W498
   input       [DBYTES*8*8-1:0]    cplx_DQIn,         // Read DQ input
   input                           cplx_DQIn_valid,   // Read DQ input valid
   output reg                      cplx_cal,
   output reg  [31:0]              cplx_status,
   output      [31:0]              cplx_err_log30,
   output      [31:0]              cplx_err_log74,
   output reg  [DBYTES*8*8-1:0]    cplx_DQOut,        // Write DQ output
   output reg  [DBYTES*8-1:0]      cplx_DMOut_n,      // Write DM output
   output reg  [ABITS-1:0]         cplx_ADR,
   output reg  [7:0]               cplx_RAS,
   output reg  [7:0]               cplx_CAS,
   output reg  [7:0]               cplx_WE,
   output reg  [7:0]               cplx_ACT_n,
   output reg  [BABITS-1:0]        cplx_BA,
   output reg  [BGBITS-1:0]        cplx_BG,
   output reg  [CKEBITS*8-1:0]     cplx_CKE,
   output reg  [CSBITS*8-1:0]      cplx_CS_n,
   output reg  [ODTBITS-1:0]       cplx_ODT,
   output reg  [7:0]               cplx_PAR,
   output reg                      cplx_issue_cas_rd,
   output reg                      cplx_issue_cas_wr,
   output reg [63:0]               cplx_expected_data
   );

localparam SHORT_PATTERN_MODE = CPLX_PAT_LENGTH == "SHORT";

// Complex Calibration
//reg  [10:0] cplx_state;
//reg  [10:0] cplx_state_nxt;
(* fsm_encoding = "sequential" *) reg  [3:0] cplx_state;
reg  [3:0] cplx_state_nxt;
reg         cplx_state_init;
reg         cplx_state_rd_cal_wr_start;
reg         cplx_state_rd_cal_rd_start;
reg         cplx_state_wr_cal_wr_start;
reg         cplx_state_wr_cal_rd_start;
reg         cplx_state_wr_cal_dm_start;
reg         cplx_state_update_logs;
reg  [6:0]  cplx_loops;
reg  [4:0]  cplx_config_byte_select;

// Complex Calibration FSM encoding
//localparam IDLE                 = 11'b000_0000_0001;
//localparam INIT                 = 11'b000_0000_0010;
//localparam RD_CAL_WR_START      = 11'b000_0000_0100;
//localparam RD_CAL_WR_WAIT_DONE  = 11'b000_0000_1000;
//localparam RD_CAL_RD_START      = 11'b000_0001_0000;
//localparam RD_CAL_RD_WAIT_DONE  = 11'b000_0010_0000;
//localparam WR_CAL_WR_START      = 11'b000_0100_0000;
//localparam WR_CAL_WR_WAIT_DONE  = 11'b000_1000_0000;
//localparam WR_CAL_RD_START      = 11'b001_0000_0000;
//localparam WR_CAL_RD_WAIT_DONE  = 11'b010_0000_0000;
//localparam UPDATE_LOGS          = 11'b100_0000_0000;


localparam IDLE                 = 4'b0000;
localparam INIT                 = 4'b0001;
localparam RD_CAL_WR_START      = 4'b0010;
localparam RD_CAL_WR_WAIT_DONE  = 4'b0011;
localparam RD_CAL_RD_START      = 4'b0100;
localparam RD_CAL_RD_WAIT_DONE  = 4'b0101;
localparam WR_CAL_WR_START      = 4'b0110;
localparam WR_CAL_WR_WAIT_DONE  = 4'b0111;
localparam WR_CAL_DM_START      = 4'b1000;
localparam WR_CAL_DM_WAIT_DONE  = 4'b1001;
localparam WR_CAL_RD_START      = 4'b1010;
localparam WR_CAL_RD_WAIT_DONE  = 4'b1011;
localparam UPDATE_LOGS          = 4'b1100;

//localparam SEQ_FSM_WIDTH        = 16;
localparam SEQ_FSM_WIDTH        = 4;
// Burst Sequence
(* fsm_encoding = "sequential" *)reg  [SEQ_FSM_WIDTH-1:0] seq_state;
reg  [SEQ_FSM_WIDTH-1:0] seq_state_nxt;

reg                      seq_state_init_row;
reg                      seq_state_init_col;
reg                      seq_state_init_bg;
reg                      seq_state_issue_act;
reg                      seq_state_issue_cas;
reg                      seq_state_issue_prea;
reg                      seq_state_inc_bg;
reg                      seq_state_inc_row;
reg                      seq_state_done;
reg  [4:0]               seq_timer;

// Complex Calibration FSM encoding
//localparam SEQ_IDLE             = 16'b0000_0000_0000_0001;
//localparam SEQ_INIT_ROW         = 16'b0000_0000_0000_0010;
//localparam SEQ_INIT_COL         = 16'b0000_0000_0000_0100;
//localparam SEQ_ISSUE_ACT        = 16'b0000_0000_0000_1000;
//localparam SEQ_ACT_WAIT         = 16'b0000_0000_0001_0000;
//localparam SEQ_INC_BG           = 16'b0000_0000_0010_0000;
//localparam SEQ_INIT_BG          = 16'b0000_0000_0100_0000;
//localparam SEQ_ISSUE_CAS        = 16'b0000_0000_1000_0000;
//localparam SEQ_GAP_WAIT         = 16'b0000_0001_0000_0000;
//localparam SEQ_CAS_WAIT         = 16'b0000_0010_0000_0000;
//localparam SEQ_INIT_PREA        = 16'b0000_0100_0000_0000;
//localparam SEQ_ISSUE_PREA       = 16'b0000_1000_0000_0000;
//localparam SEQ_PREA_WAIT        = 16'b0001_0000_0000_0000;
//localparam SEQ_INC_PREA         = 16'b0010_0000_0000_0000;
//localparam SEQ_INC_ROW          = 16'b0100_0000_0000_0000;
//localparam SEQ_DONE             = 16'b1000_0000_0000_0000;


localparam SEQ_IDLE             = 4'b0000;
localparam SEQ_INIT_ROW         = 4'b0001;
localparam SEQ_INIT_COL         = 4'b0010;
localparam SEQ_ISSUE_ACT        = 4'b0011;
localparam SEQ_ACT_WAIT         = 4'b0100;
localparam SEQ_INC_BG           = 4'b0101;
localparam SEQ_INIT_BG          = 4'b0110;
localparam SEQ_ISSUE_CAS        = 4'b0111;
localparam SEQ_GAP_WAIT         = 4'b1000;
localparam SEQ_CAS_WAIT         = 4'b1001;
localparam SEQ_INIT_PREA        = 4'b1010;
localparam SEQ_ISSUE_PREA       = 4'b1011;
localparam SEQ_PREA_WAIT        = 4'b1100;
localparam SEQ_INC_PREA         = 4'b1101;
localparam SEQ_INC_ROW          = 4'b1110;
localparam SEQ_DONE             = 4'b1111;

// Address Counters
reg  [2:0]    seq_row;
wire [2:0]    max_seq_row = SHORT_PATTERN_MODE ? 3'd0 : 3'd7;
reg  [1:0]    seq_bg;
wire [1:0]    max_seq_bg = SHORT_PATTERN_MODE ? 2'd0 : 2'd3;
reg  [5:0]    seq_col;

// Calibration phase flags
reg           cas_is_read;
reg           cas_is_bursty;
reg           cas_uses_dm;

// CAS phase burst control
wire [4:0]    max_burst_index = SHORT_PATTERN_MODE ? 5'd1 : 5'd23;
reg  [4:0]    burst_index;
reg  [4:0]    burst_count;
wire [4:0]    burst_size_array[22:0];

// Command bus
reg           cplx_ACT_cmd;
reg           cplx_RAS_cmd;
reg           cplx_CAS_cmd;
reg           cplx_WE_cmd;
reg           cplx_CS_n_cmd;
reg  [BABITS-1:0]   cplx_BA_cmd;
reg  [BGBITS-1:0]   cplx_BG_cmd;
reg  [ABITS-1:0]    cplx_ADR_cmd;

// Data
wire [DBYTES*8*8-1:0] cplx_data;
wire [63:0]           cplx_data_byte;
reg  [63:0]           cplx_dqin_byte_103;
reg                   cplx_dqin_valid_101;
reg                   cplx_dqin_valid_102;
reg                   cplx_dqin_valid_103;
reg  [63:0]           cplx_error_accum;
reg  [63:0]           cplx_data_byte_103;
reg  [15:0]           wr_cas_delay_line_ff;
reg  [4:0]            outstanding_reads;

// Config
reg  [3:0]            cplx_config_chip_select;  // spyglass disable W498


//******************************************************************************
// Configuration and Status Registers
//******************************************************************************

// Config register definition
// bit    definition
// 0      start       - set by uB, cleared by complex cal fsm
// 1      write_cal   - Write calibration when set, otherwise read calibration
// 3:2    rank_select - Decodes to CS
// 8:4    byte_select - Which byte to walk the victim pattern across
// 15:9   max_loops   - Number of times to repeat the burst sequence
// 16     dm_cal_en   - Enable DM cal on write calibration

// Config bits
wire                  cplx_config_start       = cplx_config[0];
wire                  cplx_config_write_cal   = cplx_config[1];
wire [1:0]            cplx_config_rank_select = cplx_config[3:2];

(* KEEP = "true" *) wire [4:0]            cplx_config_byte_select_nxt; // keep data bus part select in range
assign cplx_config_byte_select_nxt = ( cplx_config[8:4] < DBYTES ) ? cplx_config[8:4] : '0; // keep data bus part select in range
wire [6:0]            cplx_config_max_loops   = SHORT_PATTERN_MODE ? 7'b1 : cplx_config[15:9];
wire                  cplx_config_dm_cal_en   = cplx_config[16];

// Decode rank select to CS
always @(*) begin
  cplx_config_chip_select = '0;
  cplx_config_chip_select[ cplx_config_rank_select ] = 1'b1;
end


// Status bits
// bit    definition
// 0      busy        - set when the config start bit is set, cleared by hardware when error logs are ready to read
// 31     done        - set by hardware when the error logs are ready to read, cleared when the config start bit is set
wire [31:0] cplx_status_nxt =   ~{ cplx_config[0], 30'b0, cplx_state_update_logs }
                              &  ( cplx_status | { cplx_state_update_logs,
                                                   30'b0,
                                                   cplx_config[0] } );
wire      cplx_status_busy  = cplx_status[0];

// Output assignments.  Not currently used in addr_decode
wire  [CKEBITS*8-1:0]     cplx_CKE_nxt     = '0;
wire  [7:0]               cplx_PAR_nxt     = '0;



//******************************************************************************
// Sequence Burst Counter
//******************************************************************************

// Set up the size of each CAS burst count
assign        burst_size_array[ 0] = 5'd1;
assign        burst_size_array[ 1] = 5'd2;
assign        burst_size_array[ 2] = 5'd3;
assign        burst_size_array[ 3] = 5'd4;
assign        burst_size_array[ 4] = 5'd5;
assign        burst_size_array[ 5] = 5'd6;
assign        burst_size_array[ 6] = 5'd1;
assign        burst_size_array[ 7] = 5'd2;
assign        burst_size_array[ 8] = 5'd3;
assign        burst_size_array[ 9] = 5'd4;
assign        burst_size_array[10] = 5'd5;
assign        burst_size_array[11] = 5'd6;
assign        burst_size_array[12] = 5'd3;
assign        burst_size_array[13] = 5'd4;
assign        burst_size_array[14] = 5'd5;
assign        burst_size_array[15] = 5'd7;
assign        burst_size_array[16] = 5'd8;
assign        burst_size_array[17] = 5'd9;
assign        burst_size_array[18] = 5'd10;
assign        burst_size_array[19] = 5'd12;
assign        burst_size_array[20] = 5'd13;
assign        burst_size_array[21] = 5'd14;
assign        burst_size_array[22] = cplx_config_write_cal ? 5'd30 : 5'd22;

// Burst mode, index, and count indicate when it is time for a gap between CAS bursts.
// In bursty mode, each time the count is down to 1 a gap is inserted.
// In gapless mode, we only insert a gap when the count is down to 1 and the index is at its max.
// When the count is down to 1 and the index is at its max the CAS phase of the sequence is complete.

wire         burst_count_down_to_one = burst_count   <= 5'd1;
wire         burst_index_at_max      = burst_index   >= max_burst_index;
wire         last_cas                = burst_count_down_to_one & seq_state_issue_cas & burst_index_at_max;
wire         seq_gap                 = burst_count_down_to_one & seq_state_issue_cas & cas_is_bursty;

// Reset the burst index when the column counter is reset to prepare for cycling through all bursts.
// Increment the burst index whenever the burst count is loaded.
// This prepares the index for the next time the count is loaded.
// Load the burst count from the burst size array entry pointed to by the index.
// Load the burst count at the start of CAS phase and each time the burst count is down to 1 in the issue CAS state.
// Decrement the burst count each time a CAS is issued.

wire         load_burst_count    = seq_state_init_bg | ( burst_count_down_to_one & seq_state_issue_cas );
wire [4:0]   burst_index_nxt     = seq_state_init_col ? 6'b0 : burst_index + { 4'b0, load_burst_count };  // spyglass disable W164a

wire [4:0]   limited_burst_index = burst_index_at_max ? ( max_burst_index - 5'd1 )  // keep index in range
                                                      : burst_index;
wire [4:0]   burst_count_nxt     = load_burst_count   ? { 1'b0, burst_size_array[ limited_burst_index ] } // spyglass disable W164a
                                                      : ( burst_count - { 4'b0, seq_state_issue_cas } );


//******************************************************************************
// Address Counters
//******************************************************************************

// Row is the outer most loop in the sequence FSM
wire [2:0]    seq_row_nxt = seq_state_init_row ? 4'b0 : ( seq_row + { 2'b0, seq_state_inc_row } ); // spyglass disable W164a

// Bank Group is incremented for both Activate and CAS commands
wire          inc_bg      = seq_state_inc_bg | seq_state_issue_cas;
wire [1:0]    seq_bg_nxt  = seq_state_init_bg  ? 3'b0 : ( seq_bg  + { 1'b0, inc_bg } );  // spyglass disable W164a

// Column is incremented when a CAS is issued and the Bank Group counter rolls over
wire          inc_col     = seq_state_issue_cas & ( seq_bg == max_seq_bg );
wire [5:0]    seq_col_nxt = seq_state_init_col ? 7'b0 : ( seq_col + { 5'b0, inc_col } );  // spyglass disable W164a


//******************************************************************************
// Track Phases of Calibration
//******************************************************************************

// Set a flag at the start of a read sequence and clear at the start of a write sequence
wire cas_is_read_nxt     =  ~( cplx_state_rd_cal_wr_start | cplx_state_wr_cal_wr_start )
                           & ( cplx_state_rd_cal_rd_start | cplx_state_wr_cal_rd_start | cas_is_read );

// Indicate if a CAS is a read or write
wire seq_state_issue_wr  = seq_state_issue_cas & ~cas_is_read;
wire seq_state_issue_rd  = seq_state_issue_cas &  cas_is_read;

// Indicate to addr_decode that rdCAS or wrCAS should be generated
wire                cplx_issue_cas_wr_nxt = seq_state_issue_wr;
wire                cplx_issue_cas_rd_nxt = seq_state_issue_rd;


// Set a flag at the start of a bursty sequence and clear at the start of a gapless sequence
wire cas_is_bursty_nxt   =  ~( cplx_state_rd_cal_wr_start | cplx_state_wr_cal_rd_start )
                           & ( cplx_state_rd_cal_rd_start | cplx_state_wr_cal_wr_start | cas_is_bursty );


// Set a flag to enable DM in write and read phase
wire cas_uses_dm_nxt    =  ~( cplx_state_wr_cal_wr_start | cplx_state_rd_cal_wr_start )
                          & ( cplx_state_wr_cal_dm_start | cas_uses_dm );


//******************************************************************************
// Command/Address Outputs
//******************************************************************************

// MUX row and column onto address bus
wire [ABITS-1:0]    cplx_ADR_cmd_nxt = seq_state_issue_act ? { { ABITS-3 { 1'b0 } }, seq_row }
                                                           : { { ABITS-9 { 1'b0 } }, seq_col, 3'b0 };
wire [ABITS-1:0]    cplx_ADR_nxt     = cplx_ADR_cmd;

// Drive bank group onto group and bank busses to cover ddr4 and ddr3
wire [BABITS-1:0]   cplx_BA_cmd_nxt  = { BABITS { 1'b0 } } | seq_bg;
wire [BGBITS-1:0]   cplx_BG_cmd_nxt  = { BABITS { 1'b0 } } | seq_bg;
wire [BABITS-1:0]   cplx_BA_nxt      = cplx_BA_cmd;
wire [BGBITS-1:0]   cplx_BG_nxt      = cplx_BG_cmd;


// Positive logic DDR command bus
wire                cplx_ACT_cmd_nxt;
wire                cplx_RAS_cmd_nxt;
wire                cplx_CAS_cmd_nxt;
wire                cplx_WE_cmd_nxt;
generate
if ( MEM == "DDR4" ) begin
  assign              cplx_ACT_cmd_nxt = seq_state_issue_act                                              ; 
  assign              cplx_RAS_cmd_nxt = seq_state_issue_act |                        seq_state_issue_prea;                        
  assign              cplx_CAS_cmd_nxt = seq_state_issue_act | seq_state_issue_cas                        ;
  assign              cplx_WE_cmd_nxt  = seq_state_issue_act | seq_state_issue_wr   | seq_state_issue_prea; 
end
else begin
  assign              cplx_ACT_cmd_nxt = 1'b0;
  assign              cplx_RAS_cmd_nxt = seq_state_issue_act |                        seq_state_issue_prea;
  assign              cplx_CAS_cmd_nxt =                       seq_state_issue_cas                        ;
  assign              cplx_WE_cmd_nxt  =                       seq_state_issue_wr   | seq_state_issue_prea;
end
endgenerate

// Negative logic DDR command bus
wire [7:0]          cplx_RAS_nxt     = { 1'b1, { 2 { ~cplx_RAS_cmd   }}, 5'b1111_1 };
wire [7:0]          cplx_CAS_nxt     = { 1'b1, { 2 { ~cplx_CAS_cmd   }}, 5'b1111_1 };
wire [7:0]          cplx_WE_nxt      = { 1'b1, { 2 { ~cplx_WE_cmd    }}, 5'b1111_1 };
wire [7:0]          cplx_ACT_n_nxt   = { 1'b1, { 2 { ~cplx_ACT_cmd   }}, 5'b1111_1 };

// Negative logic DDR CS bus
wire                cplx_CS_n_cmd_nxt  = ~( seq_state_issue_act | seq_state_issue_cas | seq_state_issue_prea );

wire [CSBITS*8-1:0] cplx_CS_n_nxt;
generate
  genvar i1;
  for (i1 = 0; i1 < CSBITS; i1 = i1 + 1)
  assign            cplx_CS_n_nxt[i1*8 +:8] =  { 1'b1, { 2 { ~cplx_config_chip_select[i1] | cplx_CS_n_cmd }}, 5'b1111_1 };
endgenerate

// Simple ODT pattern - assert in write phase, de-assert in read phase.
// For single rank, assert ODT to the target rank.
// For multi-rank, assert ODT to a non-target rank.
wire  [3:0]             cplx_ODT_rank_en = ( ODTBITS == 1 ) ? 4'b1 :
                                           ( cplx_config_chip_select[0] ) ? 4'b0010 :
                                           ( cplx_config_chip_select[1] ) ? 4'b0001 :
                                           ( cplx_config_chip_select[2] ) ? 4'b1000 : 4'b0100;
wire  [ODTBITS-1:0]     cplx_ODT_nxt     = { ODTBITS { ~cas_is_read } } & cplx_ODT_rank_en[ODTBITS-1:0];

//******************************************************************************
// Data Outputs
//******************************************************************************

// The DM pattern equals DQ[0] barrel shifted by 1 bit.
// There is no specific SI reason for this DM pattern. Similar but not exactly the
// same as DQ[0].
wire  [DBYTES*8-1:0]      cplx_dm = { DBYTES { { cplx_data_byte[0], cplx_data_byte[7:1] } } };

wire  [DBYTES*8*8-1:0]    cplx_DQOut_nxt   = cplx_cal ? ( { DBYTES*8*8 { cas_uses_dm } } ^ cplx_data ) : '0; // Invert write data on write phase with DM
wire  [DBYTES*8-1:0]      cplx_DMOut_n_nxt = cplx_cal ? ( { DBYTES*8   { cas_uses_dm } } & cplx_dm )   : '0; // Enable write mask on write phase with DM


//******************************************************************************
// Complex Calibration FSM
//******************************************************************************

always @(*) begin

  cplx_state_nxt             = cplx_state;
  cplx_state_init            = 1'b0;
  cplx_state_rd_cal_wr_start = 1'b0;
  cplx_state_rd_cal_rd_start = 1'b0;
  cplx_state_wr_cal_wr_start = 1'b0;
  cplx_state_wr_cal_dm_start = 1'b0;
  cplx_state_wr_cal_rd_start = 1'b0;
  cplx_state_update_logs     = 1'b0;

  casez (cplx_state)
    IDLE: begin
      if (cplx_config_start) cplx_state_nxt = INIT;
    end
    INIT: begin
      cplx_state_init = 1'b1;
      if (cplx_config_write_cal) cplx_state_nxt = WR_CAL_WR_START;
      else                       cplx_state_nxt = RD_CAL_WR_START;
    end

    // Read Calibration

    RD_CAL_WR_START: begin
      cplx_state_rd_cal_wr_start = 1'b1;
      cplx_state_nxt = RD_CAL_WR_WAIT_DONE;
    end
    RD_CAL_WR_WAIT_DONE: begin
      if (seq_state_done) cplx_state_nxt = RD_CAL_RD_START;
    end
    RD_CAL_RD_START: begin
      cplx_state_rd_cal_rd_start = 1'b1;
      cplx_state_nxt = RD_CAL_RD_WAIT_DONE;
    end
    RD_CAL_RD_WAIT_DONE: begin
      if (seq_state_done & ( cplx_loops >= cplx_config_max_loops ) ) cplx_state_nxt = UPDATE_LOGS;
      if (seq_state_done & ( cplx_loops <  cplx_config_max_loops ) ) cplx_state_nxt = RD_CAL_RD_START;
    end

    // Write Calibration

    // Write data pattern without data mask
    WR_CAL_WR_START: begin
      cplx_state_wr_cal_wr_start = 1'b1;
      cplx_state_nxt = WR_CAL_WR_WAIT_DONE;
    end
    WR_CAL_WR_WAIT_DONE: begin
      if (seq_state_done & ~cplx_config_dm_cal_en) cplx_state_nxt = WR_CAL_RD_START;
      if (seq_state_done &  cplx_config_dm_cal_en) cplx_state_nxt = WR_CAL_DM_START;
    end

    // Write data pattern with data mask
    WR_CAL_DM_START: begin
      cplx_state_wr_cal_dm_start = 1'b1;
      cplx_state_nxt = WR_CAL_DM_WAIT_DONE;
    end
    WR_CAL_DM_WAIT_DONE: begin
      if (seq_state_done) cplx_state_nxt = WR_CAL_RD_START;
    end

    WR_CAL_RD_START: begin
      cplx_state_wr_cal_rd_start = 1'b1;
      cplx_state_nxt = WR_CAL_RD_WAIT_DONE;
    end
    WR_CAL_RD_WAIT_DONE: begin
      if (seq_state_done & ( cplx_loops >= cplx_config_max_loops ) ) cplx_state_nxt = UPDATE_LOGS;
      if (seq_state_done & ( cplx_loops <  cplx_config_max_loops ) ) cplx_state_nxt = WR_CAL_WR_START;
    end

    // Update status logs

    UPDATE_LOGS: begin
      cplx_state_update_logs = 1'b1;
      cplx_state_nxt = IDLE;
    end
    default: begin
      cplx_state_nxt = IDLE;
    end
  endcase

end //always

// Complex Calibration Repeat Loop Counter
wire       cplx_loops_inc = cplx_state_wr_cal_rd_start | cplx_state_rd_cal_rd_start;
wire [6:0] cplx_loops_nxt = cplx_state_init ? 8'd0 : ( cplx_loops + { 6'b0, cplx_loops_inc } ); // spyglass disable W164a

always @(posedge clk) begin
  if (rst) begin
    cplx_state <= #TCQ IDLE;
    cplx_loops <= #TCQ 7'b0;
  end
  else begin
    cplx_state <= #TCQ cplx_state_nxt;
    cplx_loops <= #TCQ cplx_loops_nxt;
  end
end


//******************************************************************************
// Burst Sequence FSM
//******************************************************************************

// Sequence Timer
wire       seq_timer_load       = seq_state_issue_act | seq_state_issue_cas | seq_state_issue_prea;
wire [4:0] seq_timer_load_value = seq_state_issue_act ? 5'd4 : 5'd28;
wire       seq_timer_expired    = ~( | seq_timer );
wire       seq_timer_dec        = ~seq_timer_expired;
wire [4:0] seq_timer_nxt        = seq_timer_load ? { 1'b0, seq_timer_load_value } : ( seq_timer - { 4'b0, seq_timer_dec } );  // spyglass disable W164a

always @(*) begin

  seq_state_nxt             = seq_state;
  seq_state_init_row        = 1'b0;
  seq_state_init_col        = 1'b0;
  seq_state_init_bg         = 1'b0;
  seq_state_issue_act       = 1'b0;
  seq_state_issue_cas       = 1'b0;
  seq_state_issue_prea      = 1'b0;
  seq_state_inc_bg          = 1'b0;
  seq_state_inc_row         = 1'b0;
  seq_state_done            = 1'b0;

  casez (seq_state)
    SEQ_IDLE: begin
      if ( cplx_state_rd_cal_wr_start |
           cplx_state_rd_cal_rd_start |
           cplx_state_wr_cal_wr_start |
           cplx_state_wr_cal_dm_start |
           cplx_state_wr_cal_rd_start ) seq_state_nxt = SEQ_INIT_ROW;
    end
    SEQ_INIT_ROW: begin
      seq_state_init_row = 1'b1;
      seq_state_nxt = SEQ_INIT_COL;
    end
    SEQ_INIT_COL: begin
      seq_state_init_col = 1'b1;
      seq_state_init_bg  = 1'b1;
      seq_state_nxt = SEQ_ISSUE_ACT;
    end
    SEQ_ISSUE_ACT: begin
      seq_state_issue_act = 1'b1;
      seq_state_nxt = SEQ_ACT_WAIT;
    end
    SEQ_ACT_WAIT: begin
      if ( seq_timer_expired & ( seq_bg >= max_seq_bg ) ) seq_state_nxt = SEQ_INIT_BG;
      if ( seq_timer_expired & ( seq_bg <  max_seq_bg ) ) seq_state_nxt = SEQ_INC_BG;
    end
    SEQ_INC_BG: begin
      seq_state_inc_bg = 1'b1;
      seq_state_nxt = SEQ_ISSUE_ACT;
    end
    SEQ_INIT_BG: begin
      seq_state_init_bg = 1'b1;
      seq_state_nxt = SEQ_ISSUE_CAS;
    end
    SEQ_ISSUE_CAS: begin
      seq_state_issue_cas = 1'b1;
      if      ( last_cas ) seq_state_nxt = SEQ_CAS_WAIT;
      else if ( seq_gap )  seq_state_nxt = SEQ_GAP_WAIT;
    end
    SEQ_GAP_WAIT: begin
      if ( seq_timer_expired ) seq_state_nxt = SEQ_ISSUE_CAS;
    end
    SEQ_CAS_WAIT: begin
      if ( seq_timer_expired ) seq_state_nxt = SEQ_INIT_PREA;
    end
    SEQ_INIT_PREA: begin
      seq_state_init_bg = 1'b1;
      seq_state_nxt = SEQ_ISSUE_PREA;
    end
    SEQ_ISSUE_PREA: begin
      seq_state_issue_prea = 1'b1;
      seq_state_nxt = SEQ_PREA_WAIT;
    end
    SEQ_PREA_WAIT: begin
      if ( seq_timer_expired & ( seq_bg  <  max_seq_bg ) )  seq_state_nxt = SEQ_INC_PREA;
      else if ( seq_timer_expired & ( seq_row >= max_seq_row ) ) seq_state_nxt = SEQ_DONE;
      else if ( seq_timer_expired & ( seq_row <  max_seq_row ) ) seq_state_nxt = SEQ_INC_ROW;
    end
    SEQ_INC_PREA: begin
      seq_state_inc_bg = 1'b1;
      seq_state_nxt = SEQ_ISSUE_PREA;
    end
    SEQ_INC_ROW: begin
      seq_state_inc_row = 1'b1;
      seq_state_nxt = SEQ_INIT_COL;
    end
    SEQ_DONE: begin
      seq_state_done = 1'b1;
      seq_state_nxt = SEQ_IDLE;
    end
    default: begin
      seq_state_nxt = SEQ_IDLE;
    end
  endcase

end //always

always @(posedge clk) begin
  if (rst) begin
    seq_state <= #TCQ SEQ_IDLE;
    seq_timer <= #TCQ 5'b0;
  end
  else begin
    seq_state <= #TCQ seq_state_nxt;
    seq_timer <= #TCQ seq_timer_nxt;
  end
end


//******************************************************************************
// Complex pattern BRAM
//******************************************************************************

// Count outstanding reads.  Increment counter when a read CAS issues and
// decrement when the BRAM address is incremented for the next read compare.
wire       inc_rd_addr_for_rd_cmp = ( | outstanding_reads ) & cplx_dqin_valid_101;
wire [4:0] outstanding_reads_nxt  = seq_state_init_col                                            // spyglass disable W164a
                                    ? 6'b0
                                    : ( ( outstanding_reads + { 4'b0, seq_state_issue_rd } )
                                                            - { 4'b0, inc_rd_addr_for_rd_cmp } );

// Shift register to generate early equivalent of wrDataEn.
// The signal from ddr_mc_write.sv comes too late.
wire [5:0]  wr_casslot2_delay  = 4*EXTRA_CMD_DELAY + WL[5:0] + 6'd2;     // spyglass disable W498
wire [3:0]  wr_cas_delay_index = wr_casslot2_delay[5:2] - 4'd2;   // spyglass disable W164a
wire [15:0] wr_cas_delay_line_nxt = { wr_cas_delay_line_ff[14:0], seq_state_issue_wr };
wire       early_wrDataEn = wr_cas_delay_line_ff[wr_cas_delay_index];

// Increment the BRAM address when valid read data is available or when write data is ready to issue
wire                  inc_rd_addr = inc_rd_addr_for_rd_cmp | early_wrDataEn;

// Reset rd_addr each time a new CAS sequence starts
wire                  reset_rd_addr = seq_state_init_col;

// Each different row address corresponds to a different victim lane
wire [2:0]            victim_sel    = seq_row;

// Software selects the byte to test
wire [4:0]            byte_cnt      = cplx_config_byte_select;

// Unused output of ddr_cal_cplx_data
wire [7:0]            rd_addr;

ddr4_v2_2_10_cal_cplx_data # (
    .TCQ            (TCQ),
    .DQS_CNT_WIDTH  (5),
    .DBYTES         (DBYTES),
    .VCCO_PAT_EN    (1),
    .VCCAUX_PAT_EN  (1),
    .ISI_PAT_EN     (1),
    .FIXED_VICTIM   ("FALSE"),
    .SHORT_PATTERN_MODE (SHORT_PATTERN_MODE)
) u_ddr_cal_cplx_data (
     .clk_i         (clk),
     .rst_i         (rst),
     // Inputs
     .reset_rd_addr (reset_rd_addr),
     .inc_rd_addr   (inc_rd_addr),
     .victim_sel    (victim_sel),
     .byte_cnt      (byte_cnt),
     // Outputs
     .cplx_data      (cplx_data),
     .cplx_data_byte (cplx_data_byte),
     .rd_addr        (rd_addr)
  );


//******************************************************************************
// Error Logs
//******************************************************************************


// Data Format
//                  DQ[ DBYTES*8-1 ]            DQ[1]     DQ[0]
//        DBYTES*8*8-1....DBYTES*8*8-8  ...   15....8    7....0
//                  F3....R0            ...   F3....R0  F3....R0

// Select the byte for comparison
wire [63:0] cplx_dqin_byte_102 = cplx_DQIn[ cplx_config_byte_select*64 +:64];

// Invert expected data based on how DM was used in the write phase
wire [63:0] cplx_data_byte_102 = cplx_data_byte ^ (  ~{  8 {     cplx_dm } }
                                                    & { 64 { cas_uses_dm } } );

// Compare the bytes and accumulate errors
wire [63:0] cplx_dqin_error_103  = { 64 { cplx_dqin_valid_103 } } & ( cplx_data_byte_103 ^ cplx_dqin_byte_103 );
wire [63:0] cplx_error_accum_nxt = cplx_state_init ? '0 : ( cplx_dqin_error_103 | cplx_error_accum );

// Assign outputs
assign      cplx_err_log30 = cplx_error_accum[31: 0];
assign      cplx_err_log74 = cplx_error_accum[63:32];

//******************************************************************************
// Flops
//******************************************************************************

// General reset flops
always @(posedge clk) begin
  if (rst) begin
    cas_is_read   <= #TCQ 1'b0;
    cas_is_bursty <= #TCQ 1'b0;
    seq_row       <= #TCQ 3'b0;
    seq_bg        <= #TCQ 2'b0;
    seq_col       <= #TCQ 6'b0;
    burst_index   <= #TCQ 5'b0;
    burst_count   <= #TCQ 5'b0;
    cplx_status   <= #TCQ 32'b0;
    cplx_error_accum  <= #TCQ 64'b0;
    outstanding_reads <= #TCQ 5'b0;
    cas_uses_dm       <= #TCQ '0;
  end
  else begin
    cas_is_read   <= #TCQ cas_is_read_nxt;
    cas_is_bursty <= #TCQ cas_is_bursty_nxt;
    seq_row       <= #TCQ seq_row_nxt;
    seq_bg        <= #TCQ seq_bg_nxt;
    seq_col       <= #TCQ seq_col_nxt;
    burst_index   <= #TCQ burst_index_nxt;
    burst_count   <= #TCQ burst_count_nxt;
    cplx_status   <= #TCQ cplx_status_nxt;
    cplx_error_accum <= #TCQ cplx_error_accum_nxt;
    outstanding_reads <= #TCQ outstanding_reads_nxt;
    cas_uses_dm       <= #TCQ cas_uses_dm_nxt;
  end
end

// General non-reset flops
always @(posedge clk) begin
  cplx_DQOut    <= #TCQ cplx_DQOut_nxt;
  cplx_DMOut_n  <= #TCQ cplx_DMOut_n_nxt;
  cplx_RAS      <= #TCQ cplx_RAS_nxt;
  cplx_CAS      <= #TCQ cplx_CAS_nxt;
  cplx_WE       <= #TCQ cplx_WE_nxt;
  cplx_ACT_n    <= #TCQ cplx_ACT_n_nxt;
  cplx_ADR      <= #TCQ cplx_ADR_nxt;
  cplx_BA       <= #TCQ cplx_BA_nxt;
  cplx_BG       <= #TCQ cplx_BG_nxt;
  cplx_CKE      <= #TCQ cplx_CKE_nxt;
  cplx_CS_n     <= #TCQ cplx_CS_n_nxt;
  cplx_ODT      <= #TCQ cplx_ODT_nxt;
  cplx_PAR      <= #TCQ cplx_PAR_nxt;
  cplx_cal      <= #TCQ cplx_status_busy; // flop for timing
  cplx_dqin_byte_103  <= #TCQ cplx_dqin_byte_102;
  cplx_dqin_valid_101 <= #TCQ cplx_DQIn_valid;
  cplx_dqin_valid_102 <= #TCQ inc_rd_addr_for_rd_cmp;
  cplx_dqin_valid_103 <= #TCQ cplx_dqin_valid_102;
  cplx_data_byte_103  <= #TCQ cplx_data_byte_102;
  cplx_issue_cas_wr   <= #TCQ cplx_issue_cas_wr_nxt;
  cplx_issue_cas_rd   <= #TCQ cplx_issue_cas_rd_nxt;
  cplx_CS_n_cmd       <= #TCQ cplx_CS_n_cmd_nxt;
  cplx_ACT_cmd        <= #TCQ cplx_ACT_cmd_nxt;
  cplx_RAS_cmd        <= #TCQ cplx_RAS_cmd_nxt;
  cplx_CAS_cmd        <= #TCQ cplx_CAS_cmd_nxt;
  cplx_WE_cmd         <= #TCQ cplx_WE_cmd_nxt;
  cplx_BA_cmd         <= #TCQ cplx_BA_cmd_nxt;
  cplx_BG_cmd         <= #TCQ cplx_BG_cmd_nxt;
  cplx_ADR_cmd        <= #TCQ cplx_ADR_cmd_nxt;
  wr_cas_delay_line_ff <= #TCQ wr_cas_delay_line_nxt;
  cplx_config_byte_select <= #TCQ cplx_config_byte_select_nxt;
end

always @ (posedge clk)
begin
  if (cplx_dqin_valid_102)
    cplx_expected_data <= #TCQ cplx_data_byte_102;
  else
    cplx_expected_data <= #TCQ cplx_expected_data;
end


//******************************************************************************
// FSM ASCII Variables
//******************************************************************************

//synthesis translate_off

// Check for wr_casslot2_delay overflow
wire a_ddr_cal_cplx_001_ovf = (4*EXTRA_CMD_DELAY + WL + 2) > 63;
always @(posedge clk) if (~rst) assert property (~a_ddr_cal_cplx_001_ovf);

reg [151:0] cplx_state_name;
always @(*) casez (cplx_state)
  IDLE                 : cplx_state_name = "IDLE";
  INIT                 : cplx_state_name = "INIT";
  RD_CAL_WR_START      : cplx_state_name = "RD_CAL_WR_START";
  RD_CAL_WR_WAIT_DONE  : cplx_state_name = "RD_CAL_WR_WAIT_DONE";
  RD_CAL_RD_START      : cplx_state_name = "RD_CAL_RD_START";
  RD_CAL_RD_WAIT_DONE  : cplx_state_name = "RD_CAL_RD_WAIT_DONE";
  WR_CAL_WR_START      : cplx_state_name = "WR_CAL_WR_START";
  WR_CAL_WR_WAIT_DONE  : cplx_state_name = "WR_CAL_WR_WAIT_DONE";
  WR_CAL_DM_START      : cplx_state_name = "WR_CAL_DM_START";
  WR_CAL_DM_WAIT_DONE  : cplx_state_name = "WR_CAL_DM_WAIT_DONE";
  WR_CAL_RD_START      : cplx_state_name = "WR_CAL_RD_START";
  WR_CAL_RD_WAIT_DONE  : cplx_state_name = "WR_CAL_RD_WAIT_DONE";
  UPDATE_LOGS          : cplx_state_name = "UPDATE_LOGS";
  default              : cplx_state_name = "BAD_STATE";
endcase

reg [125:0] seq_state_name;
always @(*) casez (seq_state)
  SEQ_IDLE             : seq_state_name = "SEQ_IDLE";
  SEQ_INIT_ROW         : seq_state_name = "SEQ_INIT_ROW";
  SEQ_INIT_COL         : seq_state_name = "SEQ_INIT_COL";
  SEQ_ISSUE_ACT        : seq_state_name = "SEQ_ISSUE_ACT";
  SEQ_ACT_WAIT         : seq_state_name = "SEQ_ACT_WAIT";
  SEQ_INC_BG           : seq_state_name = "SEQ_INC_BG";
  SEQ_INIT_BG          : seq_state_name = "SEQ_INIT_BG";
  SEQ_ISSUE_CAS        : seq_state_name = "SEQ_ISSUE_CAS";
  SEQ_GAP_WAIT         : seq_state_name = "SEQ_GAP_WAIT";
  SEQ_CAS_WAIT         : seq_state_name = "SEQ_CAS_WAIT";
  SEQ_INIT_PREA        : seq_state_name = "SEQ_INIT_PREA";
  SEQ_ISSUE_PREA       : seq_state_name = "SEQ_ISSUE_PREA";
  SEQ_PREA_WAIT        : seq_state_name = "SEQ_PREA_WAIT";
  SEQ_INC_PREA         : seq_state_name = "SEQ_INC_PREA";
  SEQ_INC_ROW          : seq_state_name = "SEQ_INC_ROW";
  SEQ_DONE             : seq_state_name = "SEQ_DONE";
  default              : seq_state_name = "BAD_SEQ_STATE";
endcase
//synthesis translate_on

endmodule




