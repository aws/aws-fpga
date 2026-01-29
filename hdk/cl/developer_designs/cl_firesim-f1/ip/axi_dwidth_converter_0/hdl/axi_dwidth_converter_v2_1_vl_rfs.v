// -- (c) Copyright 2010 - 2011 Xilinx, Inc. All rights reserved.
// --
// -- This file contains confidential and proprietary information
// -- of Xilinx, Inc. and is protected under U.S. and 
// -- international copyright and other intellectual property
// -- laws.
// --
// -- DISCLAIMER
// -- This disclaimer is not a license and does not grant any
// -- rights to the materials distributed herewith. Except as
// -- otherwise provided in a valid license issued to you by
// -- Xilinx, and to the maximum extent permitted by applicable
// -- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// -- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// -- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// -- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// -- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// -- (2) Xilinx shall not be liable (whether in contract or tort,
// -- including negligence, or under any other theory of
// -- liability) for any loss or damage of any kind or nature
// -- related to, arising under or in connection with these
// -- materials, including for any direct, or any indirect,
// -- special, incidental, or consequential loss or damage
// -- (including loss of data, profits, goodwill, or any type of
// -- loss or damage suffered as a result of any action brought
// -- by a third party) even if such damage or loss was
// -- reasonably foreseeable or Xilinx had been advised of the
// -- possibility of the same.
// --
// -- CRITICAL APPLICATIONS
// -- Xilinx products are not designed or intended to be fail-
// -- safe, or for use in any application requiring fail-safe
// -- performance, such as life-support or safety devices or
// -- systems, Class III medical devices, nuclear facilities,
// -- applications related to the deployment of airbags, or any
// -- other applications that could lead to death, personal
// -- injury, or severe property or environmental damage
// -- (individually and collectively, "Critical
// -- Applications"). Customer assumes the sole risk and
// -- liability of any use of Xilinx products in Critical
// -- Applications, subject only to applicable laws and
// -- regulations governing limitations on product liability.
// --
// -- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// -- PART OF THIS FILE AT ALL TIMES.
//-----------------------------------------------------------------------------
//
// Description: Address Down-Sizer
//
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   a_downsizer
//     axic_fifo
//       fifo_gen
//         fifo_coregen
//
//--------------------------------------------------------------------------
`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_dwidth_converter_v2_1_12_a_downsizer #
  (
   parameter         C_FAMILY                         = "none", 
                       // FPGA Family. Current version: virtex6 or spartan6.
   parameter integer C_AXI_PROTOCOL = 0,         // Protocol of SI and MI (0=AXI4, 1=AXI3, 2=AXI4LITE).
   parameter integer C_AXI_ID_WIDTH                   = 1, 
                       // Width of all ID signals on SI and MI side of converter.
                       // Range: 1 - 32.
   parameter integer C_SUPPORTS_ID                    = 0, 
                       // 0 = No (SI is single-threaded), 1 = Yes (Converter stalls when ID changes).
   parameter integer C_AXI_ADDR_WIDTH                 = 32, 
                       // Width of all ADDR signals on SI and MI side of converter.
                       // Range: 32.
   parameter integer C_S_AXI_DATA_WIDTH               = 64,
                       // Width of s_axi_wdata and s_axi_rdata.
                       // Range: 64, 128, 256, 512, 1024.
   parameter integer C_M_AXI_DATA_WIDTH               = 32,
                       // Width of m_axi_wdata and m_axi_rdata. 
                       // Assume always smaller than C_S_AXI_DATA_WIDTH.
                       // Range: 32, 64, 128, 256, 512.
                       // S_DATA_WIDTH = M_DATA_WIDTH not allowed.
   parameter integer C_AXI_CHANNEL                    = 0,
                       // 0 = AXI AW Channel.
                       // 1 = AXI AR Channel.
   parameter integer C_MAX_SPLIT_BEATS              = 256,
                       // Max burst length after transaction splitting.
                       // Range: 0 (no splitting), 1 (convert to singles), 16, 256.
   parameter integer C_MAX_SPLIT_BEATS_LOG            = 8,
   parameter integer C_S_AXI_BYTES_LOG                = 3,
                       // Log2 of number of 32bit word on SI-side.
   parameter integer C_M_AXI_BYTES_LOG                = 2,
                       // Log2 of number of 32bit word on MI-side.
   parameter integer C_RATIO_LOG                      = 1
                       // Log2 of Up-Sizing ratio for data.
   )
  (
   // Global Signals
   input  wire                                                    ARESET,
   input  wire                                                    ACLK,

   // Command Interface (W/R)
   output wire                              cmd_valid,
   output wire                              cmd_split,
   output wire                              cmd_mirror,
   output wire                              cmd_fix,
   output wire [C_S_AXI_BYTES_LOG-1:0]      cmd_first_word, 
   output wire [C_S_AXI_BYTES_LOG-1:0]      cmd_offset,
   output wire [C_S_AXI_BYTES_LOG-1:0]      cmd_mask,
   output wire [C_M_AXI_BYTES_LOG:0]        cmd_step,
   output wire [3-1:0]                      cmd_size,
   output wire [8-1:0]                      cmd_length,
   input  wire                              cmd_ready,
   output wire [C_AXI_ID_WIDTH-1:0]         cmd_id,
   
   // Command Interface (B)
   output wire                              cmd_b_valid,
   output wire                              cmd_b_split,
   output wire [8-1:0]                      cmd_b_repeat,
   input  wire                              cmd_b_ready,
   
   // Slave Interface Write Address Ports
   input  wire [C_AXI_ID_WIDTH-1:0]            S_AXI_AID,
   input  wire [C_AXI_ADDR_WIDTH-1:0]          S_AXI_AADDR,
   input  wire [8-1:0]                         S_AXI_ALEN,
   input  wire [3-1:0]                         S_AXI_ASIZE,
   input  wire [2-1:0]                         S_AXI_ABURST,
   input  wire [2-1:0]                         S_AXI_ALOCK,
   input  wire [4-1:0]                         S_AXI_ACACHE,
   input  wire [3-1:0]                         S_AXI_APROT,
   input  wire [4-1:0]                         S_AXI_AREGION,
   input  wire [4-1:0]                         S_AXI_AQOS,
   input  wire                                                   S_AXI_AVALID,
   output wire                                                   S_AXI_AREADY,

   // Master Interface Write Address Port
   output wire [C_AXI_ADDR_WIDTH-1:0]          M_AXI_AADDR,
   output wire [8-1:0]                         M_AXI_ALEN,
   output wire [3-1:0]                         M_AXI_ASIZE,
   output wire [2-1:0]                         M_AXI_ABURST,
   output wire [2-1:0]                         M_AXI_ALOCK,
   output wire [4-1:0]                         M_AXI_ACACHE,
   output wire [3-1:0]                         M_AXI_APROT,
   output wire [4-1:0]                         M_AXI_AREGION,
   output wire [4-1:0]                         M_AXI_AQOS,
   output wire                                                   M_AXI_AVALID,
   input  wire                                                   M_AXI_AREADY
   );

   
  /////////////////////////////////////////////////////////////////////////////
  // Variables for generating parameter controlled instances.
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Local params
  /////////////////////////////////////////////////////////////////////////////
  
  // Decode the native transaction size on the SI-side interface.
  localparam [3-1:0] C_S_AXI_NATIVE_SIZE = (C_S_AXI_DATA_WIDTH == 1024) ? 3'b111 :
                                           (C_S_AXI_DATA_WIDTH ==  512) ? 3'b110 :
                                           (C_S_AXI_DATA_WIDTH ==  256) ? 3'b101 :
                                           (C_S_AXI_DATA_WIDTH ==  128) ? 3'b100 :
                                           (C_S_AXI_DATA_WIDTH ==   64) ? 3'b011 :
                                           (C_S_AXI_DATA_WIDTH ==   32) ? 3'b010 :
                                           (C_S_AXI_DATA_WIDTH ==   16) ? 3'b001 :
                                           3'b000;
  
  // Decode the native transaction size on the MI-side interface.
  localparam [3-1:0] C_M_AXI_NATIVE_SIZE = (C_M_AXI_DATA_WIDTH == 1024) ? 3'b111 :
                                           (C_M_AXI_DATA_WIDTH ==  512) ? 3'b110 :
                                           (C_M_AXI_DATA_WIDTH ==  256) ? 3'b101 :
                                           (C_M_AXI_DATA_WIDTH ==  128) ? 3'b100 :
                                           (C_M_AXI_DATA_WIDTH ==   64) ? 3'b011 :
                                           (C_M_AXI_DATA_WIDTH ==   32) ? 3'b010 :
                                           (C_M_AXI_DATA_WIDTH ==   16) ? 3'b001 :
                                           3'b000;
  
  // Help constant to generate mask signals.
  localparam [C_AXI_ADDR_WIDTH+8-1:0]      C_DOUBLE_LEN = {{C_AXI_ADDR_WIDTH{1'b0}}, 8'b1111_1111};
  
  // Constants for burst types.
  localparam [2-1:0] C_FIX_BURST         = 2'b00;
  localparam [2-1:0] C_INCR_BURST        = 2'b01;
  localparam [2-1:0] C_WRAP_BURST        = 2'b10;
  
  // Depth for command FIFO.
  localparam integer C_FIFO_DEPTH_LOG    = 5;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Functions
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Internal signals
  /////////////////////////////////////////////////////////////////////////////
  
  // Access decoding related signals.
  wire                                access_is_fix;
  wire                                access_is_incr;
  wire                                access_is_wrap;
  wire [C_AXI_ADDR_WIDTH+16-1:0]      alen_help_vector;
  reg  [C_S_AXI_BYTES_LOG-1:0]        size_mask;
  reg  [C_AXI_ADDR_WIDTH-1:0]         split_addr_mask;
  reg  [C_S_AXI_BYTES_LOG+8-1:0]      full_downsized_len;
  wire [8-1:0]                        downsized_len;
  reg                                 legal_wrap_len;
  reg  [8-1:0]                        fix_len;
  reg  [8-1:0]                        unalignment_addr;
  reg  [C_AXI_ADDR_WIDTH-1:0]         burst_mask;
  wire [C_AXI_ADDR_WIDTH-1:0]         masked_addr;
  wire [C_AXI_ADDR_WIDTH-1:0]         burst_unalignment;
  wire [8-1:0]                        wrap_unaligned_len;
  reg  [8-1:0]                        wrap_rest_len;
  wire [C_S_AXI_BYTES_LOG+8-1:0]      num_transactions;
  wire                                access_fit_mi_side;
  wire                                si_full_size;
  wire                                fix_need_to_split;
  wire                                incr_need_to_split;
  wire                                wrap_need_to_split;
  wire [C_AXI_ADDR_WIDTH-1:0]         pre_mi_addr;
  reg  [C_AXI_ADDR_WIDTH-1:0]         next_mi_addr;
  reg                                 split_ongoing = 1'b0;
  reg  [8-1:0]                        pushed_commands = 8'b0;
  wire                                need_to_split;
  
  // Access decoding related signals for internal pipestage.
  reg                                 access_is_fix_q = 1'b0;
  reg                                 access_is_incr_q = 1'b0;
  reg                                 access_is_wrap_q = 1'b0;
  reg                                 access_fit_mi_side_q = 1'b0;
  reg                                 legal_wrap_len_q = 1'b0;
  reg                                 si_full_size_q = 1'b0;
  reg                                 fix_need_to_split_q = 1'b0;
  reg                                 incr_need_to_split_q = 1'b0;
  reg                                 wrap_need_to_split_q = 1'b0;
  wire                                need_to_split_q;
  reg  [C_AXI_ADDR_WIDTH-1:0]         split_addr_mask_q;
  reg  [C_S_AXI_BYTES_LOG+8-1:0]      num_transactions_q;
  reg  [8-1:0]                        wrap_unaligned_len_q;
  reg  [C_S_AXI_BYTES_LOG-1:0]        size_mask_q;
  reg  [8-1:0]                        downsized_len_q;
  reg  [8-1:0]                        fix_len_q;
  reg  [8-1:0]                        unalignment_addr_q;
  reg  [C_AXI_ADDR_WIDTH-1:0]         masked_addr_q;
  
  // Command buffer help signals.
  reg  [C_FIFO_DEPTH_LOG:0]           cmd_depth;
  reg                                 cmd_empty = 1'b0;
  reg  [C_AXI_ID_WIDTH-1:0]           queue_id;
  wire                                id_match;
  wire                                cmd_id_check;
  wire                                cmd_id_check_empty;
  wire                                s_ready;
  wire                                cmd_full;
  wire                                allow_new_cmd;
  wire                                cmd_push;
  reg                                 cmd_push_block = 1'b0;
  reg  [C_FIFO_DEPTH_LOG:0]           cmd_b_depth;
  reg                                 cmd_b_empty_i = 1'b0;
  wire                                cmd_b_empty;
  wire                                cmd_b_full;
  wire                                cmd_b_push;
  reg                                 cmd_b_push_block = 1'b0;
  wire                                pushed_new_cmd;
  wire                                last_fix_split;
  wire                                last_incr_split;
  wire                                last_wrap_split;
  wire                                last_split;
  
  // Internal Command Interface signals (W/R).
  wire                                cmd_valid_i;
  wire                                cmd_fix_i;
  wire                                cmd_split_i;
  wire                                cmd_mirror_i;
  reg  [C_S_AXI_BYTES_LOG-1:0]        cmd_first_word_ii;
  wire [C_S_AXI_BYTES_LOG-1:0]        cmd_first_word_i;
  wire [C_S_AXI_BYTES_LOG-1:0]        cmd_offset_i;
  reg  [C_S_AXI_BYTES_LOG-1:0]        cmd_mask_i;
  reg  [C_S_AXI_BYTES_LOG-1:0]        cmd_mask_q;
  reg  [3-1:0]                        cmd_size_i;
  wire [3-1:0]                        cmd_size_ii;
  reg  [7-1:0]                        cmd_step_i;
  wire [8-1:0]                        cmd_length_i;
  reg  [8-1:0]                        base_len;
  reg  [8-1:0]                        compensation_len;
  
  // Internal Command Interface signals (B).
  wire                                cmd_b_split_i;
  reg  [8-1:0]                        cmd_b_repeat_i;
  
  // Throttling help signals.
  wire                                mi_stalling;
  reg                                 command_ongoing = 1'b0;
   
  // Internal SI-side signals.
  reg  [C_AXI_ID_WIDTH-1:0]           S_AXI_AID_Q;
  reg  [C_AXI_ADDR_WIDTH-1:0]         S_AXI_AADDR_Q;
  reg  [8-1:0]                        S_AXI_ALEN_Q;
  reg  [3-1:0]                        S_AXI_ASIZE_Q;
  reg  [2-1:0]                        S_AXI_ABURST_Q;
  reg  [2-1:0]                        S_AXI_ALOCK_Q;
  reg  [4-1:0]                        S_AXI_ACACHE_Q;
  reg  [3-1:0]                        S_AXI_APROT_Q;
  reg  [4-1:0]                        S_AXI_AREGION_Q;
  reg  [4-1:0]                        S_AXI_AQOS_Q;
  reg                                 S_AXI_AREADY_I = 1'b0;
  
  // Internal MI-side signals.
  reg  [C_AXI_ADDR_WIDTH-1:0]         M_AXI_AADDR_I;
  wire [8-1:0]                        M_AXI_ALEN_I;
  reg  [3-1:0]                        M_AXI_ASIZE_I;
  reg  [2-1:0]                        M_AXI_ABURST_I;
  reg  [2-1:0]                        M_AXI_ALOCK_I;
  wire [4-1:0]                        M_AXI_ACACHE_I;
  wire [3-1:0]                        M_AXI_APROT_I;
  wire [4-1:0]                        M_AXI_AREGION_I;
  wire [4-1:0]                        M_AXI_AQOS_I;
  wire                                M_AXI_AVALID_I;
  wire                                M_AXI_AREADY_I;
  
  reg [1:0] areset_d = 2'b0; // Reset delay register
  always @(posedge ACLK) begin
    areset_d <= {areset_d[0], ARESET};
  end
  
  /////////////////////////////////////////////////////////////////////////////
  // Capture SI-Side signals.
  //
  /////////////////////////////////////////////////////////////////////////////
  
  // Register SI-Side signals.
  always @ (posedge ACLK) begin
    if ( S_AXI_AREADY_I ) begin
      S_AXI_AID_Q     <= S_AXI_AID;
      S_AXI_AADDR_Q   <= S_AXI_AADDR;
      S_AXI_ALEN_Q    <= S_AXI_ALEN;
      S_AXI_ASIZE_Q   <= S_AXI_ASIZE;
      S_AXI_ABURST_Q  <= S_AXI_ABURST;
      S_AXI_ALOCK_Q   <= S_AXI_ALOCK;
      S_AXI_ACACHE_Q  <= S_AXI_ACACHE;
      S_AXI_APROT_Q   <= S_AXI_APROT;
      S_AXI_AREGION_Q <= S_AXI_AREGION;
      S_AXI_AQOS_Q    <= S_AXI_AQOS;
    end
  end
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Transfer SI-Side signals to internal Pipeline Stage.
  //
  /////////////////////////////////////////////////////////////////////////////
  always @ (posedge ACLK) begin
    if ( ARESET ) begin
      access_is_fix_q       <= 1'b0;
      access_is_incr_q      <= 1'b0;
      access_is_wrap_q      <= 1'b0;
      access_fit_mi_side_q  <= 1'b0;
      legal_wrap_len_q      <= 1'b0;
      si_full_size_q        <= 1'b0;
      fix_need_to_split_q   <= 1'b0;
      incr_need_to_split_q  <= 1'b0;
      wrap_need_to_split_q  <= 1'b0;
      split_addr_mask_q     <= {C_AXI_ADDR_WIDTH{1'b0}};
      num_transactions_q    <= {(C_S_AXI_BYTES_LOG+8){1'b0}};
      wrap_unaligned_len_q  <= 8'b0;
      cmd_mask_q            <= {C_S_AXI_BYTES_LOG{1'b0}};
      size_mask_q           <= {C_S_AXI_BYTES_LOG{1'b0}};
      downsized_len_q       <= 8'b0;
      fix_len_q             <= 8'b0;
      unalignment_addr_q    <= 8'b0;
      masked_addr_q         <= {C_AXI_ADDR_WIDTH{1'b0}};
    end else begin
      if ( S_AXI_AREADY_I ) begin
        access_is_fix_q       <= access_is_fix;
        access_is_incr_q      <= access_is_incr;
        access_is_wrap_q      <= access_is_wrap;
        access_fit_mi_side_q  <= access_fit_mi_side;
        legal_wrap_len_q      <= legal_wrap_len;
        si_full_size_q        <= si_full_size;
        fix_need_to_split_q   <= fix_need_to_split;
        incr_need_to_split_q  <= incr_need_to_split;
        wrap_need_to_split_q  <= wrap_need_to_split;
        split_addr_mask_q     <= split_addr_mask;
        num_transactions_q    <= num_transactions;
        wrap_unaligned_len_q  <= wrap_unaligned_len;
        cmd_mask_q            <= cmd_mask_i;
        size_mask_q           <= size_mask;
        downsized_len_q       <= downsized_len;
        fix_len_q             <= fix_len;
        unalignment_addr_q    <= unalignment_addr;
        masked_addr_q         <= masked_addr;
      end
    end
  end
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Decode the Incoming Transaction.
  // 
  // Decode transaction type and various mask and length data.
  // 
  // Generate mask for address bits that are used unused on SI-side to remove
  // sub transaction size unalignment from data multiplex control signals.
  // 
  // Generate mask to keep addressbit between SI-side width and width of 
  // current transaction, i.e. when SI-side > AxSIZE > MI-side. Mask is used 
  // to make sure that split INCR transactions are continued at the correct 
  // offset after split.
  // 
  // Generate mask for subsize WRAP that fit in MI-Side to make sure offset and
  // sub-size wrap position is correct. For example 8-bit in a 32-bit or wider
  // MI-Side.
  // 
  // Calculate MI-Side downsize length. Downsized length is equal to SI-Side
  // length for sub-sized transactions, i.e. AxSIZE <= MI-Side width. The 8 
  // least significant bits are used to determine the length of a transaction 
  // that doesn't need to be split and the length of the last transaction if it 
  // has been split. 
  // The most significant bits are used to determine the number of transactions
  // that has to be generated on the MI-Side.
  // 
  // Evaluate if current SI-Side WRAP length is a legal length on the MI-Side.
  // 
  // Calculate the length of a FIX transaction that needs to be translated into
  // a INCR on the MI-Side. I.e. for transactions with AxSIZE > MI-Side width.
  // 
  // Determine unalignment offset depending on transaction size so that it can 
  // be discarded on the MI-side. I.e. Unused data is removed to save cycles.
  // 
  // Calculate the address bits on the MI-Side that is covered by this burst 
  // transaction. This mask is used to generate WRAP base address and the 
  // length of the second half of a WRAP transaction that has to be split into 
  // two MI-Side INCR transactions.
  // 
  // Decode if the transaction fits on the MI-Side without needing to translate 
  // it. Also decode if the tranaction is of maximum SI-Side width.
  // 
  /////////////////////////////////////////////////////////////////////////////
  
  // Transaction burst type.
  assign access_is_fix   = ( S_AXI_ABURST == C_FIX_BURST );
  assign access_is_incr  = ( S_AXI_ABURST == C_INCR_BURST );
  assign access_is_wrap  = ( S_AXI_ABURST == C_WRAP_BURST );
  
  // Generate address bits used for SI-side transaction size.
  always @ *
  begin
    case (S_AXI_ASIZE)
      3'b000: size_mask = ~C_DOUBLE_LEN[8 +: C_M_AXI_BYTES_LOG]; // 1111111
      3'b001: size_mask = ~C_DOUBLE_LEN[7 +: C_M_AXI_BYTES_LOG]; // 1111110
      3'b010: size_mask = ~C_DOUBLE_LEN[6 +: C_M_AXI_BYTES_LOG]; // 1111100
      3'b011: size_mask = ~C_DOUBLE_LEN[5 +: C_M_AXI_BYTES_LOG]; // 1111000
      3'b100: size_mask = ~C_DOUBLE_LEN[4 +: C_M_AXI_BYTES_LOG]; // 1110000
      3'b101: size_mask = ~C_DOUBLE_LEN[3 +: C_M_AXI_BYTES_LOG]; // 1100000
      3'b110: size_mask = ~C_DOUBLE_LEN[2 +: C_M_AXI_BYTES_LOG]; // 1000000
      3'b111: size_mask = ~C_DOUBLE_LEN[1 +: C_M_AXI_BYTES_LOG]; // 0000000
    endcase
  end
  
  // Generate address mask for split transactions.
  always @ *
  begin
    case (S_AXI_ASIZE)
      3'b000: split_addr_mask = ~C_DOUBLE_LEN[8 +: C_AXI_ADDR_WIDTH]; // 1111111111111111
      3'b001: split_addr_mask = ~C_DOUBLE_LEN[7 +: C_AXI_ADDR_WIDTH]; // 1111111111111110
      3'b010: split_addr_mask = ~C_DOUBLE_LEN[6 +: C_AXI_ADDR_WIDTH]; // 1111111111111100
      3'b011: split_addr_mask = ~C_DOUBLE_LEN[5 +: C_AXI_ADDR_WIDTH]; // 1111111111111000
      3'b100: split_addr_mask = ~C_DOUBLE_LEN[4 +: C_AXI_ADDR_WIDTH]; // 1111111111110000
      3'b101: split_addr_mask = ~C_DOUBLE_LEN[3 +: C_AXI_ADDR_WIDTH]; // 1111111111100000
      3'b110: split_addr_mask = ~C_DOUBLE_LEN[2 +: C_AXI_ADDR_WIDTH]; // 1111111111000000
      3'b111: split_addr_mask = ~C_DOUBLE_LEN[1 +: C_AXI_ADDR_WIDTH]; // 1111111110000000
    endcase
  end
  
  // Help vector to determine the affected addressbits in the SI-side domain.
  // Also help to determine the length of downzized thransaction on the MI-side.
  assign alen_help_vector = {{C_AXI_ADDR_WIDTH-8{1'b0}}, S_AXI_ALEN, 8'hFF}; // 00000000LLLLLLLL11111111
  
  // Calculate the address bits that are affected when a complete wrap is detected.
  always @ *
  begin
    if ( access_is_wrap ) begin
      case (S_AXI_ASIZE)
        3'b000: cmd_mask_i  = alen_help_vector[8-0 +: C_S_AXI_BYTES_LOG]; // LLLLLLL
        3'b001: cmd_mask_i  = alen_help_vector[8-1 +: C_S_AXI_BYTES_LOG]; // LLLLLL1
        3'b010: cmd_mask_i  = alen_help_vector[8-2 +: C_S_AXI_BYTES_LOG]; // LLLLL11
        3'b011: cmd_mask_i  = alen_help_vector[8-3 +: C_S_AXI_BYTES_LOG]; // LLLL111
        3'b100: cmd_mask_i  = alen_help_vector[8-4 +: C_S_AXI_BYTES_LOG]; // LLL1111
        3'b101: cmd_mask_i  = alen_help_vector[8-5 +: C_S_AXI_BYTES_LOG]; // LL11111
        3'b110: cmd_mask_i  = alen_help_vector[8-6 +: C_S_AXI_BYTES_LOG]; // L111111
        3'b111: cmd_mask_i  = alen_help_vector[8-7 +: C_S_AXI_BYTES_LOG]; // 1111111
      endcase
    end else begin
      cmd_mask_i          = {C_S_AXI_BYTES_LOG{1'b1}};
    end
  end

  // Calculate the length of downzized transaction on the MI-side.
  always @ *
  begin
    if ( access_fit_mi_side ) begin
      full_downsized_len = alen_help_vector[8-0 +: C_S_AXI_BYTES_LOG + 8]; // 0000000LLLLLLLL
    end else begin
      case (S_AXI_ASIZE)
        3'b000: full_downsized_len = alen_help_vector[8+C_M_AXI_BYTES_LOG-0 +: C_S_AXI_BYTES_LOG + 8];  // Illegal setting.
        3'b001: full_downsized_len = alen_help_vector[8+C_M_AXI_BYTES_LOG-1 +: C_S_AXI_BYTES_LOG + 8];  // Illegal setting.
        3'b010: full_downsized_len = alen_help_vector[8+C_M_AXI_BYTES_LOG-2 +: C_S_AXI_BYTES_LOG + 8];  // Illegal setting.
        3'b011: full_downsized_len = alen_help_vector[8+C_M_AXI_BYTES_LOG-3 +: C_S_AXI_BYTES_LOG + 8];  // 000000LLLLLLLL1
        3'b100: full_downsized_len = alen_help_vector[8+C_M_AXI_BYTES_LOG-4 +: C_S_AXI_BYTES_LOG + 8];  // 000000LLLLLLLL1 - 00000LLLLLLLL11
        3'b101: full_downsized_len = alen_help_vector[8+C_M_AXI_BYTES_LOG-5 +: C_S_AXI_BYTES_LOG + 8];  // 000000LLLLLLLL1 - 0000LLLLLLLL111
        3'b110: full_downsized_len = alen_help_vector[8+C_M_AXI_BYTES_LOG-6 +: C_S_AXI_BYTES_LOG + 8];  // 000000LLLLLLLL1 - 000LLLLLLLL1111
        3'b111: full_downsized_len = alen_help_vector[8+C_M_AXI_BYTES_LOG-7 +: C_S_AXI_BYTES_LOG + 8];  // 000000LLLLLLLL1 - 00LLLLLLLL11111
      endcase
    end
  end
  
  // Extract the least significant part (that fit MI-side LEN).
  // AXI3 update
  assign downsized_len = full_downsized_len[C_MAX_SPLIT_BEATS_LOG-1:0];
  
  // Calculate if the current setting would fit a WRAP downsizing.
  always @ *
  begin
    if ( access_fit_mi_side ) begin
      legal_wrap_len = 1'b1;
    end else begin
      case (S_AXI_ASIZE)
        3'b000: legal_wrap_len = 1'b1;  // Illegal setting.
        3'b001: legal_wrap_len = 1'b1;  // Illegal setting.
        3'b010: legal_wrap_len = 1'b1;  // Illegal setting.
        3'b011: legal_wrap_len = S_AXI_ALEN < ( 16 * (2 ** C_M_AXI_NATIVE_SIZE) / (2 ** 3) );
        3'b100: legal_wrap_len = S_AXI_ALEN < ( 16 * (2 ** C_M_AXI_NATIVE_SIZE) / (2 ** 4) );
        3'b101: legal_wrap_len = S_AXI_ALEN < ( 16 * (2 ** C_M_AXI_NATIVE_SIZE) / (2 ** 5) );
        3'b110: legal_wrap_len = S_AXI_ALEN < ( 16 * (2 ** C_M_AXI_NATIVE_SIZE) / (2 ** 6) );
        3'b111: legal_wrap_len = S_AXI_ALEN < ( 16 * (2 ** C_M_AXI_NATIVE_SIZE) / (2 ** 7) );
      endcase
    end
  end
  
  // Length when converting a large FIX transaction into INCR.
  always @ *
  begin
    case (S_AXI_ASIZE)
      3'b000: fix_len = ( 8'h00 >> C_M_AXI_BYTES_LOG ); // 00000000
      3'b001: fix_len = ( 8'h01 >> C_M_AXI_BYTES_LOG ); // 00000000
      3'b010: fix_len = ( 8'h03 >> C_M_AXI_BYTES_LOG ); // 00000000
      3'b011: fix_len = ( 8'h07 >> C_M_AXI_BYTES_LOG ); // 00000000 - 00000001
      3'b100: fix_len = ( 8'h0F >> C_M_AXI_BYTES_LOG ); // 00000000 - 00000011
      3'b101: fix_len = ( 8'h1F >> C_M_AXI_BYTES_LOG ); // 00000000 - 00000111
      3'b110: fix_len = ( 8'h3F >> C_M_AXI_BYTES_LOG ); // 00000000 - 00001111
      3'b111: fix_len = ( 8'h7F >> C_M_AXI_BYTES_LOG ); // 00000001 - 00011111
    endcase
  end
  
  // Calculate unalignment address.
  always @ *
  begin
    case (S_AXI_ASIZE)
      3'b000: unalignment_addr  = 8'b0;
      3'b001: unalignment_addr  = {7'b0, ( S_AXI_AADDR[0 +: 1] >> C_M_AXI_BYTES_LOG )};
      3'b010: unalignment_addr  = {6'b0, ( S_AXI_AADDR[0 +: 2] >> C_M_AXI_BYTES_LOG )};
      3'b011: unalignment_addr  = {5'b0, ( S_AXI_AADDR[0 +: 3] >> C_M_AXI_BYTES_LOG )};
      3'b100: unalignment_addr  = {4'b0, ( S_AXI_AADDR[0 +: 4] >> C_M_AXI_BYTES_LOG )};
      3'b101: unalignment_addr  = {3'b0, ( S_AXI_AADDR[0 +: 5] >> C_M_AXI_BYTES_LOG )};
      3'b110: unalignment_addr  = {2'b0, ( S_AXI_AADDR[0 +: 6] >> C_M_AXI_BYTES_LOG )};
      3'b111: unalignment_addr  = {1'b0, ( S_AXI_AADDR[0 +: 7] >> C_M_AXI_BYTES_LOG )};
    endcase
  end
  
  // Mask for address bits that are inside burst address.
  always @ *
  begin
    case (S_AXI_ASIZE)
      3'b000: burst_mask  = alen_help_vector[8-0 +: C_AXI_ADDR_WIDTH]; // 0000000000000000LLLLLLLL
      3'b001: burst_mask  = alen_help_vector[8-1 +: C_AXI_ADDR_WIDTH]; // 000000000000000LLLLLLLL1
      3'b010: burst_mask  = alen_help_vector[8-2 +: C_AXI_ADDR_WIDTH]; // 00000000000000LLLLLLLL11
      3'b011: burst_mask  = alen_help_vector[8-3 +: C_AXI_ADDR_WIDTH]; // 0000000000000LLLLLLLL111
      3'b100: burst_mask  = alen_help_vector[8-4 +: C_AXI_ADDR_WIDTH]; // 000000000000LLLLLLLL1111
      3'b101: burst_mask  = alen_help_vector[8-5 +: C_AXI_ADDR_WIDTH]; // 00000000000LLLLLLLL11111
      3'b110: burst_mask  = alen_help_vector[8-6 +: C_AXI_ADDR_WIDTH]; // 0000000000LLLLLLLL111111
      3'b111: burst_mask  = alen_help_vector[8-7 +: C_AXI_ADDR_WIDTH]; // 000000000LLLLLLLL1111111
    endcase
  end
  
  // Mask address to get start WRAP boundary.
  assign masked_addr        = ( S_AXI_AADDR & ~burst_mask );
  
  // Calculate the burst WRAP LEN.
  // AXI3 update
  assign burst_unalignment  = ( ( S_AXI_AADDR & burst_mask ) >> C_M_AXI_BYTES_LOG );
  assign wrap_unaligned_len = burst_unalignment[0 +: 8];
  
  // Get number of transactions for downsized data.
  // AXI3 update
  assign num_transactions   = full_downsized_len >> C_MAX_SPLIT_BEATS_LOG;

  // Detect if the transaction can fit on MI-side untouched.
  assign access_fit_mi_side = ( S_AXI_ASIZE <= C_M_AXI_NATIVE_SIZE );
  assign si_full_size       = ( S_AXI_ASIZE == C_S_AXI_NATIVE_SIZE );
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Generate Command Information.
  // 
  // From the decode SI-side information determine if the transaction need to 
  // be split:
  // * FIX is always split when the don't fit MI-Side (AxSIZE > MI-Side width).
  // * INCR is split when the calculated downsized length has any of the most
  //   significant bits set.
  // * WRAP is split when it cannot downsized to a legal length, i.e. the 
  //   downsized lenght requires more that 16 data beats. And it doesn't fit the 
  //   natuaral MI_Side width. And it is unaligned.
  //   (An aligneded WRAP can always be translated into a INCR without splitting,
  //    it is the wrap offset that forces the split).
  // 
  // Keep track of when the splitting of a transaction has starts and ends. This 
  // is done by detecting the need for a split and keeping track of the number 
  // of commands issued so far. The command count is reset when last command has 
  // been forwarded (and the SI-side transaction is acknowledged).
  // 
  // Calculate the length of the second part of a split WRAP transaction.
  // 
  // Determine when the last command for a split is about to be generated. This
  // information is used to ackowledge the SI-Side transaction and also prepare
  // for the next transaction. This means that the only command for a 
  // transaction that doesn't need to be split is also considered the last (and
  // only) command.
  // 
  // Set that Read data should mirrored when transaction is smaller or equal to
  // MI-Side width.
  // 
  // Extract unalignement information to be able to extract and merge data
  // correctly in the W and R channels. 
  // * First MI-Side data extraction is always based on the SI-Side start address, 
  //   regardless of transaction type.
  // * WRAP and full size INCR transactions always start following split transactions
  //   at a SI-Side aligned boundary, i.e. 0.
  // * Split INCR that has AxSIZE less than SI-Side width has to adjust the data 
  //   extraction start with previously calculated address mask, i.e. to only use
  //   address bit defined by size difference between AxSIZE and SI-Side width.
  // 
  // Generate data extraction offset for small WRAP transactions.
  // 
  // Prepare address for next part of split transaction.
  // 
  /////////////////////////////////////////////////////////////////////////////
    
  // Detect when FIX must be split (and translate into INCR).
  assign fix_need_to_split  = access_is_fix & ~access_fit_mi_side &
                              ( C_MAX_SPLIT_BEATS > 0 );
  
  // Detect when INCR must be split.
  assign incr_need_to_split = access_is_incr & ( num_transactions != 0 ) &
                              ( C_MAX_SPLIT_BEATS > 0 );
  
  // Detect when WRAP must be split (and translate into INCR).
  assign wrap_need_to_split = access_is_wrap &
                              (~access_fit_mi_side & ~legal_wrap_len & ( wrap_unaligned_len != 0 )) &
                              ( C_MAX_SPLIT_BEATS > 0 );
  
  // Detect when a command has to be split.
  assign need_to_split_q    = ( fix_need_to_split_q | incr_need_to_split_q | wrap_need_to_split_q );
  
  // Handle progress of split transactions.
  always @ (posedge ACLK) begin
    if ( ARESET ) begin
      split_ongoing     <= 1'b0;
    end else begin
      if ( pushed_new_cmd ) begin
        split_ongoing     <= need_to_split_q & ~last_split;
      end
    end
  end
  
  // Keep track of number of transactions generated.
  always @ (posedge ACLK) begin
    if ( ARESET ) begin
      pushed_commands <= 8'b0;
    end else begin
      if ( S_AXI_AREADY_I ) begin
        pushed_commands <= 8'b0;
      end else if ( pushed_new_cmd ) begin
        pushed_commands <= pushed_commands + 8'b1;
      end
    end
  end
  
  // Generate the remaining LEN for split WRAP transaction.
  always @ (posedge ACLK) begin
    if ( ARESET ) begin
      wrap_rest_len <= 8'b0;
    end else begin
      wrap_rest_len <= wrap_unaligned_len_q - 8'b1;
    end
  end
  
  // Detect last part of a command, split or not.
  assign last_fix_split     = access_is_fix_q & ( ~fix_need_to_split_q | 
                                                ( fix_need_to_split_q & ( S_AXI_ALEN_Q[0 +: 4] == pushed_commands ) ) );
  assign last_incr_split    = access_is_incr_q & ( num_transactions_q   == pushed_commands );
  assign last_wrap_split    = access_is_wrap_q & ( ~wrap_need_to_split_q |
                                                 ( wrap_need_to_split_q & split_ongoing) );
  assign last_split         = last_fix_split | last_incr_split | last_wrap_split |
                              ( C_MAX_SPLIT_BEATS == 0 );
  
  // Only FIX that are small enough is concidered FIX.
  assign cmd_fix_i          = access_is_fix_q & access_fit_mi_side_q;
  
  // Assign Split signals.
  assign cmd_split_i        = need_to_split_q & ~last_split;
  assign cmd_b_split_i      = need_to_split_q & ~last_split;
  
  // Determine if data should be mirrored for Read.
  assign cmd_mirror_i       = ( access_fit_mi_side_q );
  
  // Get unalignment address bits (including aligning it inside covered area).
  always @ *
  begin
    if ( (split_ongoing & access_is_incr_q & si_full_size_q) | (split_ongoing & access_is_wrap_q) ) begin
      cmd_first_word_ii = {C_S_AXI_BYTES_LOG{1'b0}};
    end else if ( split_ongoing & access_is_incr_q ) begin
      cmd_first_word_ii = S_AXI_AADDR_Q[C_S_AXI_BYTES_LOG-1:0] & split_addr_mask_q[C_S_AXI_BYTES_LOG-1:0];
    end else begin
      cmd_first_word_ii = S_AXI_AADDR_Q[C_S_AXI_BYTES_LOG-1:0];
    end
  end
  assign cmd_first_word_i   = cmd_first_word_ii & cmd_mask_q & size_mask_q;
  
  // Offset is the bits that are outside of the Mask.
  assign cmd_offset_i       = cmd_first_word_ii & ~cmd_mask_q;
  
  // Calculate base for next address.
  assign pre_mi_addr        = ( M_AXI_AADDR_I & split_addr_mask_q & {{C_AXI_ADDR_WIDTH-C_M_AXI_BYTES_LOG{1'b1}}, {C_M_AXI_BYTES_LOG{1'b0}}} );
  always @ (posedge ACLK) begin
    if ( ARESET ) begin
      next_mi_addr  = {C_AXI_ADDR_WIDTH{1'b0}};
    end else if ( pushed_new_cmd ) begin
    // AXI3 update
      next_mi_addr  = pre_mi_addr + ( C_MAX_SPLIT_BEATS << C_M_AXI_BYTES_LOG );
    end
  end
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Translating Transaction.
  // 
  // Setup the number of MI-Side parts for the current transaction:
  // * FIX transactions that needs to be spit will have # of parts set by the
  //   length of the SI-Side transaction. 
  // * FIX with no need to split has 1 part (1:1).
  // * WRAP will be 1 part unless the length and unalignment requires a split, in
  //   which case the # of parts will be 2.
  // * INCR transactions will have the # of parts defined by the most significant
  //   bits of the true downsized length calculation.
  // 
  // Addreess has to be calculated for each part of a transaction on MI-Side:
  // * AxADDR is always used for the first part (and all types of transactions).
  // * WRAP has aligned wrap boundary as start address for second part.
  // * Split INCR transaction will increase address with maximum sized that can
  //   be covered by a MI-Side burst, i.e. 256 * 2^miBytes.
  // * FIX always use AxADDR for all parts, if split.
  // 
  // The length of a transaction part is calculated by a base length that is
  // depending on the type of transaction. This is the adjusted by unalignment
  // that this or previous parts have had.
  // 
  // Transactions that fit tha native MI-side will pass without altering 
  // AxSIZE and AxBURST. A transaction that is translated will always have the 
  // full MI-Side data width, i.e. AxSIZE is adjusted.
  // FIX and WRAP transactions that cannot fit on MI side will change type to
  // INCR and be split accordingly.
  // 
  /////////////////////////////////////////////////////////////////////////////
  
  // Generate the number of splits, to be able to coalesce responses in B & R channels.
  always @ *
  begin
    if ( fix_need_to_split_q ) begin
      cmd_b_repeat_i = {4'b0, S_AXI_ALEN_Q[0 +: 4]};
    end else if ( incr_need_to_split_q ) begin
      cmd_b_repeat_i = num_transactions_q;
    end else if ( wrap_need_to_split_q ) begin
      cmd_b_repeat_i = 8'b1;
    end else begin
      cmd_b_repeat_i = 8'b0;
    end
  end
  
  // Select new size or remaining size.
  always @ *
  begin
    if ( split_ongoing & access_is_incr_q ) begin
      M_AXI_AADDR_I = next_mi_addr;
    end else if ( split_ongoing & access_is_wrap_q ) begin
      M_AXI_AADDR_I = masked_addr_q;
    end else begin
      M_AXI_AADDR_I = S_AXI_AADDR_Q;
    end
  end
  
  // Generate the base length for each transaction.
  always @ *
  begin
    if ( access_fit_mi_side_q ) begin
      base_len = S_AXI_ALEN_Q;
      
    end else if ( ( access_is_wrap_q & legal_wrap_len_q ) | ( access_is_incr_q & ~incr_need_to_split_q ) |
                  ( access_is_wrap_q & ~split_ongoing ) | ( access_is_incr_q & incr_need_to_split_q & last_split ) ) begin
      base_len = downsized_len_q;
      
    end else if ( fix_need_to_split_q ) begin
      base_len = fix_len_q;
      
    end else if ( access_is_wrap_q & split_ongoing ) begin
      base_len = wrap_rest_len;
      
    end else begin
      // AXI3 update
      base_len = C_MAX_SPLIT_BEATS-1; 
      
    end
  end
  
  // Generate the compensation value for the transaction.
  always @ *
  begin
    if ( wrap_need_to_split_q & ~split_ongoing ) begin
      compensation_len = wrap_unaligned_len_q;
      
    end else if ( ( incr_need_to_split_q & ~split_ongoing ) | 
                  ( access_is_incr_q & ~incr_need_to_split_q & ~access_fit_mi_side_q ) |
                  ( fix_need_to_split_q ) ) begin
      compensation_len = unalignment_addr_q;
      
    end else begin
      compensation_len = 8'b0;
      
    end
  end
  
  // Generate the actual length.
  assign cmd_length_i = base_len - compensation_len; 
  assign M_AXI_ALEN_I = cmd_length_i;
  
  // Select directly forwarded or modified transaction.
  always @ *
  begin
    if ( ~access_fit_mi_side_q ) begin
      // SI to MI-side transaction translation.
      M_AXI_ASIZE_I  = C_M_AXI_NATIVE_SIZE;
      if ( access_is_fix_q | (access_is_wrap_q & ~legal_wrap_len_q) ) begin
        M_AXI_ABURST_I = C_INCR_BURST;
      end else begin
        M_AXI_ABURST_I = S_AXI_ABURST_Q;
      end
      
      // Command settings.
      cmd_size_i     = C_M_AXI_NATIVE_SIZE;
    end else begin
      // SI to MI-side transaction forwarding.
      M_AXI_ASIZE_I  = S_AXI_ASIZE_Q;
      M_AXI_ABURST_I = S_AXI_ABURST_Q;
      
      // Command settings.
      cmd_size_i     = S_AXI_ASIZE_Q;
    end
  end
  
  // Kill Exclusive for Split transactions.
  always @ *
  begin
    if ( need_to_split_q ) begin
      M_AXI_ALOCK_I = {S_AXI_ALOCK_Q[1], 1'b0};
    end else begin
      M_AXI_ALOCK_I = S_AXI_ALOCK_Q;
    end
  end
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Forward the command to the MI-side interface.
  // 
  //
  /////////////////////////////////////////////////////////////////////////////
  
  // Generate ready signal.
  // Move SI-side transaction to internal pipe stage.
  always @ (posedge ACLK) begin
    if (ARESET) begin
      command_ongoing <= 1'b0;
      S_AXI_AREADY_I <= 1'b0;
    end else begin
      if (areset_d == 2'b10) begin
        S_AXI_AREADY_I <= 1'b1;
      end else begin
        if ( S_AXI_AVALID & S_AXI_AREADY_I ) begin
          command_ongoing <= 1'b1;
          S_AXI_AREADY_I <= 1'b0;
        end else if ( pushed_new_cmd & last_split ) begin
          command_ongoing <= 1'b0;
          S_AXI_AREADY_I <= 1'b1;
        end 
      end
    end
  end
  
  assign S_AXI_AREADY   = S_AXI_AREADY_I;
  
  // Only allowed to forward translated command when command queue is ok with it.
  assign M_AXI_AVALID_I = allow_new_cmd & command_ongoing;
  
  // Detect when MI-side is stalling.
  assign mi_stalling    = M_AXI_AVALID_I & ~M_AXI_AREADY_I;
                          
  
  /////////////////////////////////////////////////////////////////////////////
  // Simple transfer of paramters that doesn't need to be adjusted.
  // 
  // ID     - Transaction still recognized with the same ID.
  // CACHE  - No need to change the chache features. Even if the modyfiable
  //          bit is overridden (forcefully) there is no need to let downstream
  //          component beleive it is ok to modify it further.
  // PROT   - Security level of access is not changed when upsizing.
  // REGION - Address region stays the same.
  // QOS    - Quality of Service remains the same.
  // 
  /////////////////////////////////////////////////////////////////////////////
  
  // Assign MI-Side.
  assign M_AXI_ACACHE_I   = S_AXI_ACACHE_Q;
  assign M_AXI_APROT_I    = S_AXI_APROT_Q;
  assign M_AXI_AREGION_I  = S_AXI_AREGION_Q;
  assign M_AXI_AQOS_I     = S_AXI_AQOS_Q;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Control command queue to W/R channel.
  //
  // It is allowed to continue pushing new commands as long as
  // * There is room in the queue(s).
  // * The ID is the same as previously queued. Since data is not reordered
  //   for the same ID it is ok to let them proceed.
  //   (It is only required to control ID for the AW/AR channels)
  //
  /////////////////////////////////////////////////////////////////////////////
  
  // Keep track of current ID in queue.
  always @ (posedge ACLK) begin
    if (ARESET) begin
      queue_id <= {C_AXI_ID_WIDTH{1'b0}};
    end else begin
      if ( cmd_push ) begin
        // Store ID (it will be matching ID or a "new beginning").
        queue_id <= S_AXI_AID_Q;
      end
    end
  end
  
  // Check ID to make sure this command is allowed.
  assign cmd_id = queue_id;  // output remains stable regardless of cmd_b handshake or queue.
  assign id_match       = ( C_SUPPORTS_ID == 0 ) | ( queue_id == S_AXI_AID_Q);
  assign cmd_id_check_empty = (C_AXI_CHANNEL == 0) ? cmd_b_empty : cmd_empty;
  assign cmd_id_check   = cmd_id_check_empty | id_match;
  
  // Check if it is allowed to push more commands (ID is allowed and there is room in the queue).
  assign allow_new_cmd  = (~cmd_full & ~cmd_b_full & cmd_id_check) | cmd_push_block;
  
  // Push new command when allowed and MI-side is able to receive the command.
  assign cmd_push       = M_AXI_AVALID_I & ~cmd_push_block;
  assign cmd_b_push     = M_AXI_AVALID_I & ~cmd_b_push_block & (C_AXI_CHANNEL == 0);
  
  // Block furter push until command has been forwarded to MI-side.
  always @ (posedge ACLK) begin
    if (ARESET) begin
      cmd_push_block <= 1'b0;
    end else begin
      if ( pushed_new_cmd ) begin
        cmd_push_block <= 1'b0;
      end else if ( cmd_push & mi_stalling ) begin
        cmd_push_block <= 1'b1;
      end 
    end
  end
  
  // Block further push until command has been forwarded to MI-side.
  always @ (posedge ACLK) begin
    if (ARESET) begin
      cmd_b_push_block <= 1'b0;
    end else begin
      if ( S_AXI_AREADY_I ) begin
        cmd_b_push_block <= 1'b0;
      end else if ( cmd_b_push ) begin
        cmd_b_push_block <= 1'b1;
      end 
    end
  end
  
  // Acknowledge command when we can push it into queue (and forward it).
  assign pushed_new_cmd = M_AXI_AVALID_I & M_AXI_AREADY_I;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Command Queue (W/R):
  // 
  // Instantiate a FIFO as the queue and adjust the control signals.
  //
  // Decode size to step before passing it along.
  //
  // When there is no need for bursts the command FIFO can be greatly reduced 
  // becase the following is always true:
  // * split = 0 (only single words)
  // * mirror = 1 (always mirror read data)
  // * length = 0
  // * nothing can be packed (i.e. no WRAP at all)
  //   * never any sub-size wraping => static offset (0) and mask (1)
  // 
  /////////////////////////////////////////////////////////////////////////////
  
  // Instantiated queue.
  axi_data_fifo_v2_1_11_axic_fifo #
  (
   .C_FAMILY(C_FAMILY),
   .C_FIFO_DEPTH_LOG(C_FIFO_DEPTH_LOG),
   .C_FIFO_WIDTH(1+1+1+C_S_AXI_BYTES_LOG+C_S_AXI_BYTES_LOG+C_S_AXI_BYTES_LOG+3+8+3),
   .C_FIFO_TYPE("lut")
   ) 
   cmd_queue
  (
   .ACLK(ACLK),
   .ARESET(ARESET),
   .S_MESG({cmd_fix_i, cmd_split_i, cmd_mirror_i, cmd_first_word_i, 
            cmd_offset_i, cmd_mask_q, cmd_size_i, cmd_length_i, S_AXI_ASIZE_Q}),
   .S_VALID(cmd_push),
   .S_READY(s_ready),
   .M_MESG({cmd_fix, cmd_split, cmd_mirror, cmd_first_word,  
            cmd_offset, cmd_mask, cmd_size_ii, cmd_length, cmd_size}),
   .M_VALID(cmd_valid_i),
   .M_READY(cmd_ready)
   );

  // Queue is concidered full when not ready.
  assign cmd_full   = ~s_ready;
  
  // Queue is empty when no data at output port.
  always @ (posedge ACLK) begin
    if (ARESET) begin
      cmd_empty <= 1'b1;
      cmd_depth <= {C_FIFO_DEPTH_LOG+1{1'b0}};
    end else begin
      if ( cmd_push & ~cmd_ready ) begin
        // Push only => Increase depth.
        cmd_depth <= cmd_depth + 1'b1;
        cmd_empty <= 1'b0;
      end else if ( ~cmd_push & cmd_ready ) begin
        // Pop only => Decrease depth.
        cmd_depth <= cmd_depth - 1'b1;
        cmd_empty <= ( cmd_depth == 1 );
      end
    end
  end
  
  // Assign external signal.
  assign cmd_valid  = cmd_valid_i;
  
  // Translate SI-side size to step for upsizer function.
  always @ *
  begin
    case (cmd_size_ii)
      3'b000: cmd_step_i = 7'b0000001;
      3'b001: cmd_step_i = 7'b0000010;
      3'b010: cmd_step_i = 7'b0000100;
      3'b011: cmd_step_i = 7'b0001000;
      3'b100: cmd_step_i = 7'b0010000;
      3'b101: cmd_step_i = 7'b0100000;
      3'b110: cmd_step_i = 7'b1000000;
      3'b111: cmd_step_i = 7'b0000000; // Illegal setting.
    endcase
  end
  
  // Get only the applicable bits in step.
  assign cmd_step = cmd_step_i[C_M_AXI_BYTES_LOG:0];
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Command Queue (B):
  // 
  // Add command queue for B channel only when it is AW channel and both burst
  // and splitting is supported.
  //
  // When turned off the command appears always empty.
  // 
  /////////////////////////////////////////////////////////////////////////////
  
  // Instantiated queue.
  generate
    if ( C_AXI_CHANNEL == 0 && C_MAX_SPLIT_BEATS > 0 ) begin : USE_B_CHANNEL
      
      wire                                cmd_b_valid_i;
      wire                                s_b_ready;
      
      axi_data_fifo_v2_1_11_axic_fifo #
      (
       .C_FAMILY(C_FAMILY),
       .C_FIFO_DEPTH_LOG(C_FIFO_DEPTH_LOG),
       .C_FIFO_WIDTH(1+8),
       .C_FIFO_TYPE("lut")
       ) 
       cmd_b_queue
      (
       .ACLK(ACLK),
       .ARESET(ARESET),
       .S_MESG({cmd_b_split_i, cmd_b_repeat_i}),
       .S_VALID(cmd_b_push),
       .S_READY(s_b_ready),
       .M_MESG({cmd_b_split, cmd_b_repeat}),
       .M_VALID(cmd_b_valid_i),
       .M_READY(cmd_b_ready)
       );
    
      // Queue is concidered full when not ready.
      assign cmd_b_full   = ~s_b_ready;
      
      // Queue is empty when no data at output port.
      always @ (posedge ACLK) begin
        if (ARESET) begin
          cmd_b_empty_i <= 1'b1;
          cmd_b_depth <= {C_FIFO_DEPTH_LOG+1{1'b0}};
        end else begin
          if ( cmd_b_push & ~cmd_b_ready ) begin
            // Push only => Increase depth.
            cmd_b_depth <= cmd_b_depth + 1'b1;
            cmd_b_empty_i <= 1'b0;
          end else if ( ~cmd_b_push & cmd_b_ready ) begin
            // Pop only => Decrease depth.
            cmd_b_depth <= cmd_b_depth - 1'b1;
            cmd_b_empty_i <= ( cmd_b_depth == 1 );
          end
        end
      end
      
      // Assign external signal.
      assign cmd_b_valid  = cmd_b_valid_i;
      assign cmd_b_empty = cmd_b_empty_i;
      
    end else begin : NO_B_CHANNEL
      
      // Assign external command signals.
      assign cmd_b_valid    = 1'b0;
      assign cmd_b_split    = 1'b0;
      assign cmd_b_repeat   = 8'b0;
   
      // Assign internal command FIFO signals.
      assign cmd_b_full     = 1'b0;
      assign cmd_b_empty    = 1'b1;
      
    end
  endgenerate
  
  
  /////////////////////////////////////////////////////////////////////////////
  // MI-side output handling
  // 
  /////////////////////////////////////////////////////////////////////////////
// TODO: registered?  
  assign M_AXI_AADDR    = M_AXI_AADDR_I;
  assign M_AXI_ALEN     = M_AXI_ALEN_I;
  assign M_AXI_ASIZE    = M_AXI_ASIZE_I;
  assign M_AXI_ABURST   = M_AXI_ABURST_I;
  assign M_AXI_ALOCK    = M_AXI_ALOCK_I;
  assign M_AXI_ACACHE   = M_AXI_ACACHE_I;
  assign M_AXI_APROT    = M_AXI_APROT_I;
  assign M_AXI_AREGION  = M_AXI_AREGION_I;
  assign M_AXI_AQOS     = M_AXI_AQOS_I;
  assign M_AXI_AVALID   = M_AXI_AVALID_I;
  assign M_AXI_AREADY_I = M_AXI_AREADY;
  
  
endmodule


// -- (c) Copyright 2010 - 2011 Xilinx, Inc. All rights reserved.
// --
// -- This file contains confidential and proprietary information
// -- of Xilinx, Inc. and is protected under U.S. and 
// -- international copyright and other intellectual property
// -- laws.
// --
// -- DISCLAIMER
// -- This disclaimer is not a license and does not grant any
// -- rights to the materials distributed herewith. Except as
// -- otherwise provided in a valid license issued to you by
// -- Xilinx, and to the maximum extent permitted by applicable
// -- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// -- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// -- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// -- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// -- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// -- (2) Xilinx shall not be liable (whether in contract or tort,
// -- including negligence, or under any other theory of
// -- liability) for any loss or damage of any kind or nature
// -- related to, arising under or in connection with these
// -- materials, including for any direct, or any indirect,
// -- special, incidental, or consequential loss or damage
// -- (including loss of data, profits, goodwill, or any type of
// -- loss or damage suffered as a result of any action brought
// -- by a third party) even if such damage or loss was
// -- reasonably foreseeable or Xilinx had been advised of the
// -- possibility of the same.
// --
// -- CRITICAL APPLICATIONS
// -- Xilinx products are not designed or intended to be fail-
// -- safe, or for use in any application requiring fail-safe
// -- performance, such as life-support or safety devices or
// -- systems, Class III medical devices, nuclear facilities,
// -- applications related to the deployment of airbags, or any
// -- other applications that could lead to death, personal
// -- injury, or severe property or environmental damage
// -- (individually and collectively, "Critical
// -- Applications"). Customer assumes the sole risk and
// -- liability of any use of Xilinx products in Critical
// -- Applications, subject only to applicable laws and
// -- regulations governing limitations on product liability.
// --
// -- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// -- PART OF THIS FILE AT ALL TIMES.
//-----------------------------------------------------------------------------
//
// Description: Write Data Response Down-Sizer
// Collect MI-side responses and set the SI-side response to the most critical
// level (in descending order):
//    DECERR, SLVERROR and OKAY.
// EXOKAY cannot occur for split transactions. 
//
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   wr_upsizer
//
//--------------------------------------------------------------------------
`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_dwidth_converter_v2_1_12_b_downsizer #
  (
   parameter         C_FAMILY                         = "none", 
                       // FPGA Family. Current version: virtex6 or spartan6.
   parameter integer C_AXI_ID_WIDTH                   = 1
                       // Width of all ID signals on SI and MI side of converter.
                       // Range: >= 1.
   )
  (
   // Global Signals
   input  wire                                                    ARESET,
   input  wire                                                    ACLK,

   // Command Interface
   input  wire                              cmd_valid,
   input  wire                              cmd_split,
   input  wire [8-1:0]                      cmd_repeat,
   output wire                              cmd_ready,
   input  wire [C_AXI_ID_WIDTH-1:0]         cmd_id,
   
   // Slave Interface Write Response Ports
   output wire [C_AXI_ID_WIDTH-1:0]           S_AXI_BID,
   output wire [2-1:0]                          S_AXI_BRESP,
   output wire                                                    S_AXI_BVALID,
   input  wire                                                    S_AXI_BREADY,

   // Master Interface Write Response Ports
   input  wire [2-1:0]                         M_AXI_BRESP,
   input  wire                                                   M_AXI_BVALID,
   output wire                                                   M_AXI_BREADY
   );
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Variables for generating parameter controlled instances.
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Local params
  /////////////////////////////////////////////////////////////////////////////
  
  // Constants for packing levels.
  localparam [2-1:0] C_RESP_OKAY        = 2'b00;
  localparam [2-1:0] C_RESP_EXOKAY      = 2'b01;
  localparam [2-1:0] C_RESP_SLVERROR    = 2'b10;
  localparam [2-1:0] C_RESP_DECERR      = 2'b11;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Functions
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Internal signals
  /////////////////////////////////////////////////////////////////////////////
  
  // Throttling help signals.
  wire                            cmd_ready_i;
  wire                            pop_mi_data;
  wire                            mi_stalling;
  
  // Repeat handling related.
  reg  [8-1:0]                    repeat_cnt_pre;
  reg  [8-1:0]                    repeat_cnt;
  wire [8-1:0]                    next_repeat_cnt;
  reg                             first_mi_word;
  wire                            last_word;
  
  // Ongoing split transaction.
  wire                            load_bresp;
  wire                            need_to_update_bresp;
  reg  [2-1:0]                    S_AXI_BRESP_ACC;
  
  // Internal signals for MI-side.
  wire                            M_AXI_BREADY_I;
  
  // Internal signals for SI-side.
  wire [C_AXI_ID_WIDTH-1:0]       S_AXI_BID_I;
  reg  [2-1:0]                    S_AXI_BRESP_I;
  wire                            S_AXI_BVALID_I;
  wire                            S_AXI_BREADY_I;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Handle interface handshaking:
  // 
  // The MI-side BRESP is popped when at once for split transactions, except 
  // for the last cycle that behaves like a "normal" transaction.
  // A "normal" BRESP is popped once the SI-side is able to use it,
  // 
  // 
  /////////////////////////////////////////////////////////////////////////////
  
  // Pop word from MI-side.
  assign M_AXI_BREADY_I = ~mi_stalling;
  assign M_AXI_BREADY   = M_AXI_BREADY_I;
  
  // Indicate when there is a BRESP available @ SI-side.
  assign S_AXI_BVALID_I = M_AXI_BVALID & last_word;
  
  // Get MI-side data.
  assign pop_mi_data    = M_AXI_BVALID & M_AXI_BREADY_I;
  
  // Signal that the command is done (so that it can be poped from command queue).
  assign cmd_ready_i    = cmd_valid & pop_mi_data & last_word;
  assign cmd_ready      = cmd_ready_i;
  
  // Detect when MI-side is stalling.
  assign mi_stalling    = (~S_AXI_BREADY_I & last_word);
                          
  
  /////////////////////////////////////////////////////////////////////////////
  // Handle the accumulation of BRESP.
  // 
  // Forward the accumulated or MI-side BRESP value depending on state:
  //  * MI-side BRESP is forwarded untouched when it is a non split cycle.
  //    (MI-side BRESP value is also used when updating the accumulated for
  //     the last access during a split access).
  //  * The accumulated BRESP is for a split transaction.
  // 
  // The accumulated BRESP register is updated for each MI-side response that 
  // is used.
  // 
  /////////////////////////////////////////////////////////////////////////////
  
  // Force load accumulated BRESPs to first value
  assign load_bresp           = (cmd_split & first_mi_word);
  
  // Update if more critical.
  assign need_to_update_bresp = ( M_AXI_BRESP > S_AXI_BRESP_ACC );
  
  // Select accumultated or direct depending on setting.
  always @ *
  begin
    if ( cmd_split ) begin
      if ( load_bresp || need_to_update_bresp ) begin
        S_AXI_BRESP_I = M_AXI_BRESP;
      end else begin
        S_AXI_BRESP_I = S_AXI_BRESP_ACC;
      end
    end else begin
      S_AXI_BRESP_I = M_AXI_BRESP;
    end
  end
  
  // Accumulate MI-side BRESP.
  always @ (posedge ACLK) begin
    if (ARESET) begin
      S_AXI_BRESP_ACC <= C_RESP_OKAY;
    end else begin
      if ( pop_mi_data ) begin
        S_AXI_BRESP_ACC <= S_AXI_BRESP_I;
      end
    end
  end
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Keep track of BRESP repeat counter.
  //
  // Last BRESP word is either:
  //  * The first and only word when not merging.
  //  * The last value when merging.
  // 
  // The internal counter is taken from the external command interface during
  // the first response when merging. The counter is updated each time a
  // BRESP is popped from the MI-side interface.
  // 
  /////////////////////////////////////////////////////////////////////////////
  
  // Determine last BRESP cycle.
  assign last_word  = ( ( repeat_cnt == 8'b0 ) & ~first_mi_word ) | 
                      ~cmd_split;
  
  // Select command reapeat or counted repeat value.
  always @ *
  begin
    if ( first_mi_word ) begin
      repeat_cnt_pre  =  cmd_repeat;
    end else begin
      repeat_cnt_pre  =  repeat_cnt;
    end
  end
  
  // Calculate next repeat counter value.
  assign next_repeat_cnt  = repeat_cnt_pre - 2'b01;
  
  // Keep track of the repeat count.
  always @ (posedge ACLK) begin
    if (ARESET) begin
      repeat_cnt    <= 8'b0;
      first_mi_word <= 1'b1;
    end else begin
      if ( pop_mi_data ) begin
        repeat_cnt    <= next_repeat_cnt;
        first_mi_word <= last_word;
      end
    end
  end
  
  
  /////////////////////////////////////////////////////////////////////////////
  // BID Handling
  /////////////////////////////////////////////////////////////////////////////
  
  assign S_AXI_BID_I  = cmd_id;
  
    /////////////////////////////////////////////////////////////////////////////
  // SI-side output handling
  /////////////////////////////////////////////////////////////////////////////
// TODO: registered?  
  assign S_AXI_BID      = S_AXI_BID_I;
  assign S_AXI_BRESP    = S_AXI_BRESP_I;
  assign S_AXI_BVALID   = S_AXI_BVALID_I;
  assign S_AXI_BREADY_I = S_AXI_BREADY;
  
  
endmodule


// -- (c) Copyright 2010 - 2011 Xilinx, Inc. All rights reserved.
// --
// -- This file contains confidential and proprietary information
// -- of Xilinx, Inc. and is protected under U.S. and 
// -- international copyright and other intellectual property
// -- laws.
// --
// -- DISCLAIMER
// -- This disclaimer is not a license and does not grant any
// -- rights to the materials distributed herewith. Except as
// -- otherwise provided in a valid license issued to you by
// -- Xilinx, and to the maximum extent permitted by applicable
// -- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// -- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// -- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// -- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// -- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// -- (2) Xilinx shall not be liable (whether in contract or tort,
// -- including negligence, or under any other theory of
// -- liability) for any loss or damage of any kind or nature
// -- related to, arising under or in connection with these
// -- materials, including for any direct, or any indirect,
// -- special, incidental, or consequential loss or damage
// -- (including loss of data, profits, goodwill, or any type of
// -- loss or damage suffered as a result of any action brought
// -- by a third party) even if such damage or loss was
// -- reasonably foreseeable or Xilinx had been advised of the
// -- possibility of the same.
// --
// -- CRITICAL APPLICATIONS
// -- Xilinx products are not designed or intended to be fail-
// -- safe, or for use in any application requiring fail-safe
// -- performance, such as life-support or safety devices or
// -- systems, Class III medical devices, nuclear facilities,
// -- applications related to the deployment of airbags, or any
// -- other applications that could lead to death, personal
// -- injury, or severe property or environmental damage
// -- (individually and collectively, "Critical
// -- Applications"). Customer assumes the sole risk and
// -- liability of any use of Xilinx products in Critical
// -- Applications, subject only to applicable laws and
// -- regulations governing limitations on product liability.
// --
// -- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// -- PART OF THIS FILE AT ALL TIMES.
//-----------------------------------------------------------------------------
//
// Description: Read Data Response Down-Sizer
// 
// 
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   r_downsizer
//
//--------------------------------------------------------------------------
`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_dwidth_converter_v2_1_12_r_downsizer #
  (
   parameter         C_FAMILY                         = "none", 
                       // FPGA Family. Current version: virtex6 or spartan6.
   parameter integer C_AXI_ID_WIDTH                   = 1, 
                       // Width of all ID signals on SI and MI side of converter.
                       // Range: >= 1.
   parameter integer C_S_AXI_DATA_WIDTH               = 64,
                       // Width of s_axi_wdata and s_axi_rdata.
                       // Range: 64, 128, 256, 512, 1024.
   parameter integer C_M_AXI_DATA_WIDTH               = 32,
                       // Width of m_axi_wdata and m_axi_rdata. 
                       // Assume always smaller than C_S_AXI_DATA_WIDTH.
                       // Range: 32, 64, 128, 256, 512.
                       // S_DATA_WIDTH = M_DATA_WIDTH not allowed.
   parameter integer C_S_AXI_BYTES_LOG                = 3,
                       // Log2 of number of 32bit word on SI-side.
   parameter integer C_M_AXI_BYTES_LOG                = 2,
                       // Log2 of number of 32bit word on MI-side.
   parameter integer C_RATIO_LOG                      = 1
                       // Log2 of Up-Sizing ratio for data.
   )
  (
   // Global Signals
   input  wire                                                    ARESET,
   input  wire                                                    ACLK,

   // Command Interface
   input  wire                              cmd_valid,
   input  wire                              cmd_split,
   input  wire                              cmd_mirror,
   input  wire                              cmd_fix,
   input  wire [C_S_AXI_BYTES_LOG-1:0]      cmd_first_word, 
   input  wire [C_S_AXI_BYTES_LOG-1:0]      cmd_offset,
   input  wire [C_S_AXI_BYTES_LOG-1:0]      cmd_mask,
   input  wire [C_M_AXI_BYTES_LOG:0]        cmd_step,
   input  wire [3-1:0]                      cmd_size,
   input  wire [8-1:0]                      cmd_length,
   output wire                              cmd_ready,
   input  wire [C_AXI_ID_WIDTH-1:0]         cmd_id,
   
   // Slave Interface Read Data Ports
   output wire [C_AXI_ID_WIDTH-1:0]           S_AXI_RID,
   output wire [C_S_AXI_DATA_WIDTH-1:0]     S_AXI_RDATA,
   output wire [2-1:0]                          S_AXI_RRESP,
   output wire                                                    S_AXI_RLAST,
   output wire                                                    S_AXI_RVALID,
   input  wire                                                    S_AXI_RREADY,

   // Master Interface Read Data Ports
   input  wire [C_M_AXI_DATA_WIDTH-1:0]    M_AXI_RDATA,
   input  wire [2-1:0]                         M_AXI_RRESP,
   input  wire                                                   M_AXI_RLAST,
   input  wire                                                   M_AXI_RVALID,
   output wire                                                   M_AXI_RREADY
   );

   
  /////////////////////////////////////////////////////////////////////////////
  // Variables for generating parameter controlled instances.
  /////////////////////////////////////////////////////////////////////////////
  
  // Generate variable for MI-side word lanes on SI-side.
  genvar word_cnt;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Local params
  /////////////////////////////////////////////////////////////////////////////
  
  // Constants for packing levels.
  localparam [2-1:0] C_RESP_OKAY        = 2'b00;
  localparam [2-1:0] C_RESP_EXOKAY      = 2'b01;
  localparam [2-1:0] C_RESP_SLVERROR    = 2'b10;
  localparam [2-1:0] C_RESP_DECERR      = 2'b11;
  
  // .
  localparam [24-1:0] C_DOUBLE_LEN       = 24'b0000_0000_0000_0000_1111_1111;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Functions
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Internal signals
  /////////////////////////////////////////////////////////////////////////////
  
  // Sub-word handling.
  reg                             first_word;
  reg  [C_S_AXI_BYTES_LOG-1:0]    current_word_1;
  reg  [C_S_AXI_BYTES_LOG-1:0]    current_word;
  wire [C_S_AXI_BYTES_LOG-1:0]    current_word_adjusted;
  wire [C_RATIO_LOG-1:0]          current_index;
  wire                            last_beat;
  wire                            last_word;
  wire                            new_si_word;
  reg  [C_S_AXI_BYTES_LOG-1:0]    size_mask;
  
  // Sub-word handling for the next cycle.
  wire [C_S_AXI_BYTES_LOG-1:0]    next_word;
  
  // Burst length handling.
  reg                             first_mi_word;
  reg  [8-1:0]                    length_counter_1;
  reg  [8-1:0]                    length_counter;
  wire [8-1:0]                    next_length_counter;
  
  // Loading of new rresp data.
  wire                            load_rresp;
  reg                             need_to_update_rresp;
  reg  [2-1:0]                    S_AXI_RRESP_ACC;
  
  // Detect start of MI word.
  wire                            first_si_in_mi;
  wire                            first_mi_in_si;
  
  // Throttling help signals.
  wire                            word_completed;
  wire                            cmd_ready_i;
  wire                            pop_si_data;
  wire                            pop_mi_data;
  wire                            si_stalling;
  
  // Internal MI-side control signals.
  wire                            M_AXI_RREADY_I;
   
  // Internal SI-side control signals.
  reg  [C_S_AXI_DATA_WIDTH-1:0]   S_AXI_RDATA_II;
  
  // Internal signals for SI-side.
  wire [C_AXI_ID_WIDTH-1:0]       S_AXI_RID_I;
  reg  [C_S_AXI_DATA_WIDTH-1:0]   S_AXI_RDATA_I;
  reg  [2-1:0]                    S_AXI_RRESP_I;
  wire                            S_AXI_RLAST_I;
  wire                            S_AXI_RVALID_I;
  wire                            S_AXI_RREADY_I;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Handle interface handshaking:
  //
  // 
  /////////////////////////////////////////////////////////////////////////////
  
  // Generate address bits used for SI-side transaction size.
  always @ *
  begin
    case (cmd_size)
      3'b000: size_mask = C_DOUBLE_LEN[8 +: C_S_AXI_BYTES_LOG];
      3'b001: size_mask = C_DOUBLE_LEN[7 +: C_S_AXI_BYTES_LOG];
      3'b010: size_mask = C_DOUBLE_LEN[6 +: C_S_AXI_BYTES_LOG];
      3'b011: size_mask = C_DOUBLE_LEN[5 +: C_S_AXI_BYTES_LOG];
      3'b100: size_mask = C_DOUBLE_LEN[4 +: C_S_AXI_BYTES_LOG];
      3'b101: size_mask = C_DOUBLE_LEN[3 +: C_S_AXI_BYTES_LOG];
      3'b110: size_mask = C_DOUBLE_LEN[2 +: C_S_AXI_BYTES_LOG];
      3'b111: size_mask = C_DOUBLE_LEN[1 +: C_S_AXI_BYTES_LOG];  // Illegal setting.
    endcase
  end
  
  // Detect when MI-side word is completely assembled.
  assign word_completed = ( cmd_fix ) |
                          ( cmd_mirror ) |
                          ( ~cmd_fix & ( ( next_word & size_mask ) == {C_S_AXI_BYTES_LOG{1'b0}} ) ) | 
                          ( ~cmd_fix & last_word );
  
  // Pop word from SI-side.
  assign M_AXI_RREADY_I =  cmd_valid & (S_AXI_RREADY_I | ~word_completed);
  assign M_AXI_RREADY   = M_AXI_RREADY_I;
  
  // Indicate when there is data available @ SI-side.
  assign S_AXI_RVALID_I = M_AXI_RVALID & word_completed & cmd_valid;
  
  // Get MI-side data.
  assign pop_mi_data    = M_AXI_RVALID & M_AXI_RREADY_I;
  
  // Get SI-side data.
  assign pop_si_data    = S_AXI_RVALID_I & S_AXI_RREADY_I;
  
  // Signal that the command is done (so that it can be poped from command queue).
  assign cmd_ready_i    = cmd_valid & pop_si_data & last_word;
  assign cmd_ready      = cmd_ready_i;
  
  // Detect when MI-side is stalling.
  assign si_stalling    = S_AXI_RVALID_I & ~S_AXI_RREADY_I;
                          
  
  /////////////////////////////////////////////////////////////////////////////
  // 
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Keep track of data extraction:
  // 
  // Current address is taken form the command buffer for the first data beat
  // to handle unaligned Read transactions. After this is the extraction 
  // address usually calculated from this point.
  // FIX transactions uses the same word address for all data beats. 
  // 
  // Next word address is generated as current word plus the current step 
  // size, with masking to facilitate sub-sized wraping. The Mask is all ones
  // for normal wraping, and less when sub-sized wraping is used.
  // 
  // The calculated word addresses (current and next) is offseted by the 
  // current Offset. For sub-sized transaction the Offset points to the least 
  // significant address of the included data beats. (The least significant 
  // word is not necessarily the first data to be extracted, consider WRAP).
  // Offset is only used for sub-sized WRAP transcation that are Complete.
  // 
  // First word is active during the first MI-side data beat.
  // 
  // First MI is set during the first MI-side data beat.
  //
  // The transaction length is taken from the command buffer combinatorialy
  // during the First MI cycle. For each generated MI word it is decreased 
  // until Last Beat is reached.
  // 
  // Last word is determined depending as the last MI-side word generated for 
  // the command (generated from the AW translation).
  // If burst aren't supported all MI-side words are concidered to be the last.
  //
  /////////////////////////////////////////////////////////////////////////////
  
  // Select if the offset comes from command queue directly or 
  // from a counter while when extracting multiple MI words per SI word
  always @ *
  begin
    if ( first_word | cmd_fix )
      current_word = cmd_first_word;
    else
      current_word = current_word_1;
  end
  
  // Calculate next word.
  assign next_word              = ( current_word + cmd_step ) & cmd_mask;
  
  // Calculate the word address with offset.
  assign current_word_adjusted  = current_word + cmd_offset;
  
  // Get the ratio bits (MI-side words vs SI-side words).
  assign current_index          = current_word_adjusted[C_S_AXI_BYTES_LOG-C_RATIO_LOG +: C_RATIO_LOG];
  
  // Prepare next word address.
  always @ (posedge ACLK) begin
    if (ARESET) begin
      first_word      <= 1'b1;
      current_word_1  <= 'b0;
    end else begin
      if ( pop_mi_data ) begin
        if ( M_AXI_RLAST ) begin
          // Prepare for next access.
          first_word <=  1'b1;
        end else begin
          first_word <=  1'b0;
        end
      
        current_word_1 <= next_word;
      end
    end
  end
  
  // Select command length or counted length.
  always @ *
  begin
    if ( first_mi_word )
      length_counter = cmd_length;
    else
      length_counter = length_counter_1;
  end
  
  // Calculate next length counter value.
  assign next_length_counter = length_counter - 1'b1;
  
  // Keep track of burst length.
  always @ (posedge ACLK) begin
    if (ARESET) begin
      first_mi_word    <= 1'b1;
      length_counter_1 <= 8'b0;
    end else begin
      if ( pop_mi_data ) begin
        if ( M_AXI_RLAST ) begin
          first_mi_word    <= 1'b1;
        end else begin
          first_mi_word    <= 1'b0;
        end
      
        length_counter_1 <= next_length_counter;
      end
    end
  end
  
  // Detect last beat in a burst.
  assign last_beat    = ( length_counter == 8'b0 );
  
  // Determine if this last word that shall be extracted from this SI-side word.
  assign last_word    = ( last_beat );
  
  // Detect new SI-side data word.
  assign new_si_word  = ( current_word == {C_S_AXI_BYTES_LOG{1'b0}} );
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Simple AXI signal forwarding:
  // 
  // LAST has to be filtered to remove any intermediate LAST (due to split 
  // trasactions).
  // 
  /////////////////////////////////////////////////////////////////////////////
  
  assign S_AXI_RID_I    = cmd_id;
  
  // Handle last flag, i.e. set for SI-side last word.
  assign S_AXI_RLAST_I  = M_AXI_RLAST & ~cmd_split;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Handle the accumulation of RRESP.
  // 
  // The accumulated RRESP register is updated for each MI-side response that 
  // is used in an SI-side word, i.e. the worst status for all included data
  // so far.
  // 
  /////////////////////////////////////////////////////////////////////////////
  
  // Detect first SI-side word per MI-side word.
  assign first_si_in_mi = cmd_mirror | 
                          first_mi_word |
                          ( ~cmd_mirror & ( ( current_word & size_mask ) == {C_S_AXI_BYTES_LOG{1'b0}} ) );
  
  // Force load accumulated RRESPs to first value or continously for non split.
  assign load_rresp     = first_si_in_mi;
  
  // Update if more critical.
  always @ *
  begin
    case (S_AXI_RRESP_ACC)
      C_RESP_EXOKAY:    need_to_update_rresp = ( M_AXI_RRESP == C_RESP_OKAY     |
                                                 M_AXI_RRESP == C_RESP_SLVERROR |
                                                 M_AXI_RRESP == C_RESP_DECERR );
      C_RESP_OKAY:      need_to_update_rresp = ( M_AXI_RRESP == C_RESP_SLVERROR |
                                                 M_AXI_RRESP == C_RESP_DECERR );
      C_RESP_SLVERROR:  need_to_update_rresp = ( M_AXI_RRESP == C_RESP_DECERR );
      C_RESP_DECERR:    need_to_update_rresp = 1'b0;
    endcase
  end
  
  // Select accumultated or direct depending on setting.
  always @ *
  begin
    if ( load_rresp || need_to_update_rresp ) begin
      S_AXI_RRESP_I = M_AXI_RRESP;
    end else begin
      S_AXI_RRESP_I = S_AXI_RRESP_ACC;
    end
  end
  
  // Accumulate MI-side RRESP.
  always @ (posedge ACLK) begin
    if (ARESET) begin
      S_AXI_RRESP_ACC <= C_RESP_OKAY;
    end else begin
      if ( pop_mi_data ) begin
        S_AXI_RRESP_ACC <= S_AXI_RRESP_I;
      end
    end
  end
  
    /////////////////////////////////////////////////////////////////////////////
  // Demultiplex data to form complete data word.
  // 
  /////////////////////////////////////////////////////////////////////////////
  
  // Registers and combinatorial data MI-word size mux.
  generate
    for (word_cnt = 0; word_cnt < (2 ** C_RATIO_LOG) ; word_cnt = word_cnt + 1) begin : WORD_LANE
        
      // Generate extended write data and strobe.
      always @ (posedge ACLK) begin
        if (ARESET) begin
          S_AXI_RDATA_II[word_cnt*C_M_AXI_DATA_WIDTH   +: C_M_AXI_DATA_WIDTH]   <= {C_M_AXI_DATA_WIDTH{1'b0}};
        end else begin
          if ( pop_si_data ) begin
            S_AXI_RDATA_II[word_cnt*C_M_AXI_DATA_WIDTH   +: C_M_AXI_DATA_WIDTH]   <= {C_M_AXI_DATA_WIDTH{1'b0}};
          end else if ( current_index == word_cnt & pop_mi_data ) begin
            S_AXI_RDATA_II[word_cnt*C_M_AXI_DATA_WIDTH   +: C_M_AXI_DATA_WIDTH]   <= M_AXI_RDATA;
          end
        end
      end
      
      // Select packed or extended data.
      always @ *
      begin
        // Multiplex data.
        if ( ( current_index == word_cnt ) | cmd_mirror ) begin
          S_AXI_RDATA_I[word_cnt*C_M_AXI_DATA_WIDTH +: C_M_AXI_DATA_WIDTH] = M_AXI_RDATA;
        end else begin
          S_AXI_RDATA_I[word_cnt*C_M_AXI_DATA_WIDTH +: C_M_AXI_DATA_WIDTH] = 
                        S_AXI_RDATA_II[word_cnt*C_M_AXI_DATA_WIDTH +: C_M_AXI_DATA_WIDTH];
        end
      end
      
    end // end for word_cnt
  endgenerate
      
  
  /////////////////////////////////////////////////////////////////////////////
  // SI-side output handling
  /////////////////////////////////////////////////////////////////////////////
  assign S_AXI_RREADY_I = S_AXI_RREADY;
  assign S_AXI_RVALID   = S_AXI_RVALID_I;
  assign S_AXI_RID      = S_AXI_RID_I;
  assign S_AXI_RDATA    = S_AXI_RDATA_I;
  assign S_AXI_RRESP    = S_AXI_RRESP_I;
  assign S_AXI_RLAST    = S_AXI_RLAST_I;
  
  
endmodule


// -- (c) Copyright 2010 - 2011 Xilinx, Inc. All rights reserved.
// --
// -- This file contains confidential and proprietary information
// -- of Xilinx, Inc. and is protected under U.S. and 
// -- international copyright and other intellectual property
// -- laws.
// --
// -- DISCLAIMER
// -- This disclaimer is not a license and does not grant any
// -- rights to the materials distributed herewith. Except as
// -- otherwise provided in a valid license issued to you by
// -- Xilinx, and to the maximum extent permitted by applicable
// -- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// -- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// -- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// -- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// -- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// -- (2) Xilinx shall not be liable (whether in contract or tort,
// -- including negligence, or under any other theory of
// -- liability) for any loss or damage of any kind or nature
// -- related to, arising under or in connection with these
// -- materials, including for any direct, or any indirect,
// -- special, incidental, or consequential loss or damage
// -- (including loss of data, profits, goodwill, or any type of
// -- loss or damage suffered as a result of any action brought
// -- by a third party) even if such damage or loss was
// -- reasonably foreseeable or Xilinx had been advised of the
// -- possibility of the same.
// --
// -- CRITICAL APPLICATIONS
// -- Xilinx products are not designed or intended to be fail-
// -- safe, or for use in any application requiring fail-safe
// -- performance, such as life-support or safety devices or
// -- systems, Class III medical devices, nuclear facilities,
// -- applications related to the deployment of airbags, or any
// -- other applications that could lead to death, personal
// -- injury, or severe property or environmental damage
// -- (individually and collectively, "Critical
// -- Applications"). Customer assumes the sole risk and
// -- liability of any use of Xilinx products in Critical
// -- Applications, subject only to applicable laws and
// -- regulations governing limitations on product liability.
// --
// -- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// -- PART OF THIS FILE AT ALL TIMES.
//-----------------------------------------------------------------------------
//
// Description: Write Data Down-Sizer
// Mirror data for simple accesses.
// Merge data for burst.
//
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   w_downsizer
//
//--------------------------------------------------------------------------
`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_dwidth_converter_v2_1_12_w_downsizer #
  (
   parameter         C_FAMILY                         = "none", 
                       // FPGA Family. Current version: virtex6 or spartan6.
   parameter integer C_S_AXI_DATA_WIDTH               = 64,
                       // Width of s_axi_wdata and s_axi_rdata.
                       // Range: 64, 128, 256, 512, 1024.
   parameter integer C_M_AXI_DATA_WIDTH               = 32,
                       // Width of m_axi_wdata and m_axi_rdata. 
                       // Assume always smaller than C_S_AXI_DATA_WIDTH.
                       // Range: 32, 64, 128, 256, 512.
                       // S_DATA_WIDTH = M_DATA_WIDTH not allowed.
   parameter integer C_S_AXI_BYTES_LOG                = 3,
                       // Log2 of number of 32bit word on SI-side.
   parameter integer C_M_AXI_BYTES_LOG                = 2,
                       // Log2 of number of 32bit word on MI-side.
   parameter integer C_RATIO_LOG                      = 1
                       // Log2 of Up-Sizing ratio for data.
   )
  (
   // Global Signals
   input  wire                                                    ARESET,
   input  wire                                                    ACLK,

   // Command Interface
   input  wire                              cmd_valid,
   input  wire                              cmd_mirror,
   input  wire                              cmd_fix,
   input  wire [C_S_AXI_BYTES_LOG-1:0]      cmd_first_word, 
   input  wire [C_S_AXI_BYTES_LOG-1:0]      cmd_offset,
   input  wire [C_S_AXI_BYTES_LOG-1:0]      cmd_mask,
   input  wire [C_M_AXI_BYTES_LOG:0]        cmd_step,
   input  wire [3-1:0]                      cmd_size,
   input  wire [8-1:0]                      cmd_length,
   output wire                              cmd_ready,
   
   // Slave Interface Write Data Ports
   input  wire [C_S_AXI_DATA_WIDTH-1:0]     S_AXI_WDATA,
   input  wire [C_S_AXI_DATA_WIDTH/8-1:0]   S_AXI_WSTRB,
   input  wire                                                    S_AXI_WLAST,
   input  wire                                                    S_AXI_WVALID,
   output wire                                                    S_AXI_WREADY,

   // Master Interface Write Data Ports
   output wire [C_M_AXI_DATA_WIDTH-1:0]    M_AXI_WDATA,
   output wire [C_M_AXI_DATA_WIDTH/8-1:0]  M_AXI_WSTRB,
   output wire                                                   M_AXI_WLAST,
   output wire                                                   M_AXI_WVALID,
   input  wire                                                   M_AXI_WREADY
   );

   
  /////////////////////////////////////////////////////////////////////////////
  // Local params
  /////////////////////////////////////////////////////////////////////////////
  
  // .
  localparam [24-1:0] C_DOUBLE_LEN       = 24'b0000_0000_0000_0000_1111_1111;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Internal signals
  /////////////////////////////////////////////////////////////////////////////

  // Sub-word handling.
  reg                             first_word;
  reg  [C_S_AXI_BYTES_LOG-1:0]    current_word_1;
  reg  [C_S_AXI_BYTES_LOG-1:0]    current_word;
  wire [C_S_AXI_BYTES_LOG-1:0]    current_word_adjusted;
  wire [C_RATIO_LOG-1:0]          current_index;
  wire                            last_beat;
  wire                            last_word;
  reg  [C_S_AXI_BYTES_LOG-1:0]    size_mask;
  
  // Sub-word handling for the next cycle.
  wire [C_S_AXI_BYTES_LOG-1:0]    next_word;
  
  // Burst length handling.
  reg                             first_mi_word;
  reg  [8-1:0]                    length_counter_1;
  reg  [8-1:0]                    length_counter;
  wire [8-1:0]                    next_length_counter;
  
  // Throttling help signals.
  wire                            word_completed;
  wire                            cmd_ready_i;
  wire                            pop_mi_data;
  wire                            mi_stalling;
  
  // Internal SI side control signals.
  wire                            S_AXI_WREADY_I;
  
  // Internal signals for MI-side.
  wire [C_M_AXI_DATA_WIDTH-1:0]   M_AXI_WDATA_I;
  wire [C_M_AXI_DATA_WIDTH/8-1:0] M_AXI_WSTRB_I;
  wire                            M_AXI_WLAST_I;
  wire                            M_AXI_WVALID_I;
  wire                            M_AXI_WREADY_I;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Handle interface handshaking:
  //
  // Determine if a SI-side word has been completely used. For FIX transactions
  // the SI-side word is used to extract a single data word. 
  // Otherwise is the SI-side word considered to be used when last MI-side beat
  // has been extracted or when the last (most significant) MI-side word has 
  // been extracted from the SI-side word.
  //
  // Data on the MI-side is available when data is being taken from SI-side.
  //
  // The command is popped from the command queue once the last beat on the 
  // MI-side has been ackowledged.
  // 
  /////////////////////////////////////////////////////////////////////////////
  
  // Generate address bits used for SI-side transaction size.
  always @ *
  begin
    case (cmd_size)
      3'b000: size_mask = C_DOUBLE_LEN[8 +: C_S_AXI_BYTES_LOG];
      3'b001: size_mask = C_DOUBLE_LEN[7 +: C_S_AXI_BYTES_LOG];
      3'b010: size_mask = C_DOUBLE_LEN[6 +: C_S_AXI_BYTES_LOG];
      3'b011: size_mask = C_DOUBLE_LEN[5 +: C_S_AXI_BYTES_LOG];
      3'b100: size_mask = C_DOUBLE_LEN[4 +: C_S_AXI_BYTES_LOG];
      3'b101: size_mask = C_DOUBLE_LEN[3 +: C_S_AXI_BYTES_LOG];
      3'b110: size_mask = C_DOUBLE_LEN[2 +: C_S_AXI_BYTES_LOG];
      3'b111: size_mask = C_DOUBLE_LEN[1 +: C_S_AXI_BYTES_LOG];  // Illegal setting.
    endcase
  end
  
  // Detect when SI-side word is completely used.
  assign word_completed = ( cmd_fix ) |
                          ( cmd_mirror ) |
                          ( ~cmd_fix & ( ( next_word & size_mask ) == {C_S_AXI_BYTES_LOG{1'b0}} ) ) | 
                          ( ~cmd_fix & last_word );
  
  // Pop word from SI-side.
  assign S_AXI_WREADY_I = cmd_valid & word_completed & M_AXI_WREADY_I;
  assign S_AXI_WREADY   = S_AXI_WREADY_I;
  
  // Indicate when there is data available @ MI-side.
  assign M_AXI_WVALID_I = S_AXI_WVALID & cmd_valid;
  
  // Get MI-side data.
  assign pop_mi_data    = M_AXI_WVALID_I & M_AXI_WREADY_I;
  
  // Signal that the command is done (so that it can be poped from command queue).
  assign cmd_ready_i    = cmd_valid & pop_mi_data & last_word;
  assign cmd_ready      = cmd_ready_i;
  
  // Detect when MI-side is stalling.
  assign mi_stalling    = M_AXI_WVALID_I & ~M_AXI_WREADY_I;
                          
  
  /////////////////////////////////////////////////////////////////////////////
  // Keep track of data extraction:
  // 
  // Current address is taken form the command buffer for the first data beat
  // to handle unaligned Read transactions. After this is the extraction 
  // address usually calculated from this point.
  // FIX transactions uses the same word address for all data beats. 
  // 
  // Next word address is generated as current word plus the current step 
  // size, with masking to facilitate sub-sized wraping. The Mask is all ones
  // for normal wraping, and less when sub-sized wraping is used.
  // 
  // The calculated word addresses (current and next) is offseted by the 
  // current Offset. For sub-sized transaction the Offset points to the least 
  // significant address of the included data beats. (The least significant 
  // word is not necessarily the first data to be extracted, consider WRAP).
  // Offset is only used for sub-sized WRAP transcation that are Complete.
  // 
  // First word is active during the first MI-side data beat.
  // 
  // First MI is set during the first MI-side data beat.
  //
  // The transaction length is taken from the command buffer combinatorialy
  // during the First MI cycle. For each generated MI word it is decreased 
  // until Last Beat is reached.
  // 
  // Last word is determined depending as the last MI-side word generated for 
  // the command (generated from the AW translation).
  // If burst aren't supported all MI-side words are concidered to be the last.
  //
  /////////////////////////////////////////////////////////////////////////////
  
  // Select if the offset comes from command queue directly or 
  // from a counter while when extracting multiple MI words per SI word
  always @ *
  begin
    if ( first_word | cmd_fix )
      current_word = cmd_first_word;
    else
      current_word = current_word_1;
  end
  
  // Calculate next word.
  assign next_word              = ( current_word + cmd_step ) & cmd_mask;
  
  // Calculate the word address with offset.
  assign current_word_adjusted  = current_word + cmd_offset;
  
  // Get the ratio bits (MI-side words vs SI-side words).
  assign current_index          = current_word_adjusted[C_S_AXI_BYTES_LOG-C_RATIO_LOG +: C_RATIO_LOG];
  
  // Prepare next word address.
  always @ (posedge ACLK) begin
    if (ARESET) begin
      first_word      <= 1'b1;
      current_word_1  <= 'b0;
    end else begin
      if ( pop_mi_data ) begin
        if ( M_AXI_WLAST_I ) begin
          // Prepare for next access.
          first_word      <=  1'b1;
        end else begin
          first_word      <=  1'b0;
        end
      
        current_word_1  <= next_word;
      end
    end
  end
  
  // Select command length or counted length.
  always @ *
  begin
    if ( first_mi_word )
      length_counter = cmd_length;
    else
      length_counter = length_counter_1;
  end
  
  // Calculate next length counter value.
  assign next_length_counter = length_counter - 1'b1;
  
  // Keep track of burst length.
  always @ (posedge ACLK) begin
    if (ARESET) begin
      first_mi_word    <= 1'b1;
      length_counter_1 <= 8'b0;
    end else begin
      if ( pop_mi_data ) begin
        if ( M_AXI_WLAST_I ) begin
          first_mi_word    <= 1'b1;
        end else begin
          first_mi_word    <= 1'b0;
        end
      
        length_counter_1 <= next_length_counter;
      end
    end
  end
  
  // Detect last beat in a burst.
  assign last_beat = ( length_counter == 8'b0 );
  
  // Determine if this last word that shall be extracted from this SI-side word.
  assign last_word = ( last_beat );
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Select the SI-side word to write.
  // Data must be multiplexed.
  //
  // Last need special handling since it is the last MI-side word generated 
  // from the SI-side word that shall be marked.
  // Split transactions needs to insert new LAST transactions. So to simplify
  // is the LAST signal always generated.
  //
  /////////////////////////////////////////////////////////////////////////////
   
  // Data has to be multiplexed.
  assign M_AXI_WDATA_I  = S_AXI_WDATA[current_index * C_M_AXI_DATA_WIDTH   +: C_M_AXI_DATA_WIDTH];
  assign M_AXI_WSTRB_I  = S_AXI_WSTRB[current_index * C_M_AXI_DATA_WIDTH/8 +: C_M_AXI_DATA_WIDTH/8];
  
  // Handle last flag, i.e. set for MI-side last word.
  assign M_AXI_WLAST_I  = last_word;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // MI-side output handling
  /////////////////////////////////////////////////////////////////////////////
// TODO: registered?  
  assign M_AXI_WDATA    = M_AXI_WDATA_I;
  assign M_AXI_WSTRB    = M_AXI_WSTRB_I;
  assign M_AXI_WLAST    = M_AXI_WLAST_I;
  assign M_AXI_WVALID   = M_AXI_WVALID_I;
  assign M_AXI_WREADY_I = M_AXI_WREADY;
  
endmodule


// -- (c) Copyright 2010 - 2011 Xilinx, Inc. All rights reserved.
// --
// -- This file contains confidential and proprietary information
// -- of Xilinx, Inc. and is protected under U.S. and 
// -- international copyright and other intellectual property
// -- laws.
// --
// -- DISCLAIMER
// -- This disclaimer is not a license and does not grant any
// -- rights to the materials distributed herewith. Except as
// -- otherwise provided in a valid license issued to you by
// -- Xilinx, and to the maximum extent permitted by applicable
// -- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// -- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// -- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// -- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// -- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// -- (2) Xilinx shall not be liable (whether in contract or tort,
// -- including negligence, or under any other theory of
// -- liability) for any loss or damage of any kind or nature
// -- related to, arising under or in connection with these
// -- materials, including for any direct, or any indirect,
// -- special, incidental, or consequential loss or damage
// -- (including loss of data, profits, goodwill, or any type of
// -- loss or damage suffered as a result of any action brought
// -- by a third party) even if such damage or loss was
// -- reasonably foreseeable or Xilinx had been advised of the
// -- possibility of the same.
// --
// -- CRITICAL APPLICATIONS
// -- Xilinx products are not designed or intended to be fail-
// -- safe, or for use in any application requiring fail-safe
// -- performance, such as life-support or safety devices or
// -- systems, Class III medical devices, nuclear facilities,
// -- applications related to the deployment of airbags, or any
// -- other applications that could lead to death, personal
// -- injury, or severe property or environmental damage
// -- (individually and collectively, "Critical
// -- Applications"). Customer assumes the sole risk and
// -- liability of any use of Xilinx products in Critical
// -- Applications, subject only to applicable laws and
// -- regulations governing limitations on product liability.
// --
// -- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// -- PART OF THIS FILE AT ALL TIMES.
//-----------------------------------------------------------------------------
//
// Description: Down-Sizer
// Down-Sizer for generic SI- and MI-side data widths. This module instantiates
// Address, Write Data, Write Response and Read Data Down-Sizer modules, each one taking care
// of the channel specific tasks.
// The Address Down-Sizer can handle both AR and AW channels.
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   downsizer
//     a_downsizer
//       axic_fifo
//         fifo_gen
//           fifo_coregen
//     w_downsizer
//     b_downsizer
//     r_downsizer
//
//--------------------------------------------------------------------------
`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_dwidth_converter_v2_1_12_axi_downsizer #
  (
   parameter         C_FAMILY                         = "none", 
                       // FPGA Family.
   parameter integer C_AXI_PROTOCOL = 0, 
                       // Protocol of SI and MI (0=AXI4, 1=AXI3).
   parameter integer C_S_AXI_ID_WIDTH                   = 1, 
                       // Width of all ID signals on SI side of converter.
                       // Range: 1 - 32.
   parameter integer C_SUPPORTS_ID                    = 0, 
                       // Indicates whether SI-side ID needs to be stored and compared.
                       // 0 = No, SI is single-threaded, propagate all transactions.
                       // 1 = Yes, stall any transaction with ID different than outstanding transactions.
   parameter integer C_AXI_ADDR_WIDTH                 = 32, 
                       // Width of all ADDR signals on SI and MI.
                       // Range (AXI4, AXI3): 12 - 64.
   parameter integer C_S_AXI_DATA_WIDTH               = 64,
                       // Width of s_axi_wdata and s_axi_rdata.
                       // Range: 64, 128, 256, 512, 1024.
   parameter integer C_M_AXI_DATA_WIDTH               = 32,
                       // Width of m_axi_wdata and m_axi_rdata. 
                       // Assume always smaller than C_S_AXI_DATA_WIDTH.
                       // Range: 32, 64, 128, 256, 512.
                       // S_DATA_WIDTH = M_DATA_WIDTH not allowed.
   parameter integer C_AXI_SUPPORTS_WRITE             = 1,
   parameter integer C_AXI_SUPPORTS_READ              = 1,
   parameter integer C_MAX_SPLIT_BEATS              = 256
                       // Max burst length after transaction splitting.
                       // Range: 0 (no splitting), 1 (convert to singles), 16, 256.
   )
  (
   // Global Signals
   input  wire                              aresetn,
   input  wire                              aclk,

   // Slave Interface Write Address Ports
   input  wire [C_S_AXI_ID_WIDTH-1:0]       s_axi_awid,
   input  wire [C_AXI_ADDR_WIDTH-1:0]       s_axi_awaddr,
   input  wire [8-1:0]                      s_axi_awlen,
   input  wire [3-1:0]                      s_axi_awsize,
   input  wire [2-1:0]                      s_axi_awburst,
   input  wire [2-1:0]                      s_axi_awlock,
   input  wire [4-1:0]                      s_axi_awcache,
   input  wire [3-1:0]                      s_axi_awprot,
   input  wire [4-1:0]                      s_axi_awregion,
   input  wire [4-1:0]                      s_axi_awqos,
   input  wire                              s_axi_awvalid,
   output wire                              s_axi_awready,
   // Slave Interface Write Data Ports
   input  wire [C_S_AXI_DATA_WIDTH-1:0]     s_axi_wdata,
   input  wire [C_S_AXI_DATA_WIDTH/8-1:0]   s_axi_wstrb,
   input  wire                              s_axi_wlast,
   input  wire                              s_axi_wvalid,
   output wire                              s_axi_wready,
   // Slave Interface Write Response Ports
   output wire [C_S_AXI_ID_WIDTH-1:0]       s_axi_bid,
   output wire [2-1:0]                      s_axi_bresp,
   output wire                              s_axi_bvalid,
   input  wire                              s_axi_bready,
   // Slave Interface Read Address Ports
   input  wire [C_S_AXI_ID_WIDTH-1:0]       s_axi_arid,
   input  wire [C_AXI_ADDR_WIDTH-1:0]       s_axi_araddr,
   input  wire [8-1:0]                      s_axi_arlen,
   input  wire [3-1:0]                      s_axi_arsize,
   input  wire [2-1:0]                      s_axi_arburst,
   input  wire [2-1:0]                      s_axi_arlock,
   input  wire [4-1:0]                      s_axi_arcache,
   input  wire [3-1:0]                      s_axi_arprot,
   input  wire [4-1:0]                      s_axi_arregion,
   input  wire [4-1:0]                      s_axi_arqos,
   input  wire                              s_axi_arvalid,
   output wire                              s_axi_arready,
   // Slave Interface Read Data Ports
   output wire [C_S_AXI_ID_WIDTH-1:0]       s_axi_rid,
   output wire [C_S_AXI_DATA_WIDTH-1:0]     s_axi_rdata,
   output wire [2-1:0]                      s_axi_rresp,
   output wire                              s_axi_rlast,
   output wire                              s_axi_rvalid,
   input  wire                              s_axi_rready,

   // Master Interface Write Address Port
   output wire [C_AXI_ADDR_WIDTH-1:0]       m_axi_awaddr,
   output wire [8-1:0]                      m_axi_awlen,
   output wire [3-1:0]                      m_axi_awsize,
   output wire [2-1:0]                      m_axi_awburst,
   output wire [2-1:0]                      m_axi_awlock,
   output wire [4-1:0]                      m_axi_awcache,
   output wire [3-1:0]                      m_axi_awprot,
   output wire [4-1:0]                      m_axi_awregion,
   output wire [4-1:0]                      m_axi_awqos,
   output wire                              m_axi_awvalid,
   input  wire                              m_axi_awready,
   // Master Interface Write Data Ports
   output wire [C_M_AXI_DATA_WIDTH-1:0]     m_axi_wdata,
   output wire [C_M_AXI_DATA_WIDTH/8-1:0]   m_axi_wstrb,
   output wire                              m_axi_wlast,
   output wire                              m_axi_wvalid,
   input  wire                              m_axi_wready,
   // Master Interface Write Response Ports
   input  wire [2-1:0]                      m_axi_bresp,
   input  wire                              m_axi_bvalid,
   output wire                              m_axi_bready,
   // Master Interface Read Address Port
   output wire [C_AXI_ADDR_WIDTH-1:0]       m_axi_araddr,
   output wire [8-1:0]                      m_axi_arlen,
   output wire [3-1:0]                      m_axi_arsize,
   output wire [2-1:0]                      m_axi_arburst,
   output wire [2-1:0]                      m_axi_arlock,
   output wire [4-1:0]                      m_axi_arcache,
   output wire [3-1:0]                      m_axi_arprot,
   output wire [4-1:0]                      m_axi_arregion,
   output wire [4-1:0]                      m_axi_arqos,
   output wire                              m_axi_arvalid,
   input  wire                              m_axi_arready,
   // Master Interface Read Data Ports
   input  wire [C_M_AXI_DATA_WIDTH-1:0]     m_axi_rdata,
   input  wire [2-1:0]                      m_axi_rresp,
   input  wire                              m_axi_rlast,
   input  wire                              m_axi_rvalid,
   output wire                              m_axi_rready
   );

  /////////////////////////////////////////////////////////////////////////////
  // Functions
  /////////////////////////////////////////////////////////////////////////////
  
  // Log2.
  function integer log2
    (
     input integer x
     );
    integer acc;
    begin
      acc=0;
      while ((2**acc) < x)
        acc = acc + 1;
      log2 = acc;
    end
  endfunction
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Local params
  /////////////////////////////////////////////////////////////////////////////
  
  // Log2 of number of 32bit word on SI-side.
  localparam integer C_S_AXI_BYTES_LOG                = log2(C_S_AXI_DATA_WIDTH/8);
  
  // Log2 of number of 32bit word on MI-side.
  localparam integer C_M_AXI_BYTES_LOG                = log2(C_M_AXI_DATA_WIDTH/8);
  
  // Log2 of Up-Sizing ratio for data.
  localparam integer C_RATIO                          = C_S_AXI_DATA_WIDTH / C_M_AXI_DATA_WIDTH;
  localparam integer C_RATIO_LOG                      = log2(C_RATIO);
  localparam integer P_AXI_ADDR_WIDTH                 = (C_AXI_ADDR_WIDTH < 13) ? 13 : C_AXI_ADDR_WIDTH;
  
  wire [P_AXI_ADDR_WIDTH-1:0] s_axi_awaddr_i;
  wire [P_AXI_ADDR_WIDTH-1:0] s_axi_araddr_i;
  wire [P_AXI_ADDR_WIDTH-1:0] m_axi_awaddr_i;
  wire [P_AXI_ADDR_WIDTH-1:0] m_axi_araddr_i;
  assign s_axi_awaddr_i = s_axi_awaddr;
  assign s_axi_araddr_i = s_axi_araddr;
  assign m_axi_awaddr = m_axi_awaddr_i[0 +: C_AXI_ADDR_WIDTH] ;
  assign m_axi_araddr = m_axi_araddr_i[0 +: C_AXI_ADDR_WIDTH];
  
  localparam integer P_AXI4 = 0;
  localparam integer P_AXI3 = 1;
  localparam integer P_AXILITE = 2;
  
  localparam integer P_MAX_SPLIT_BEATS = (C_MAX_SPLIT_BEATS >= 16) ? C_MAX_SPLIT_BEATS :
    (C_AXI_PROTOCOL == P_AXI4) ? 256 : 16;
  localparam integer P_MAX_SPLIT_BEATS_LOG = log2(P_MAX_SPLIT_BEATS);
  
  /////////////////////////////////////////////////////////////////////////////
  // Handle Write Channels (AW/W/B)
  /////////////////////////////////////////////////////////////////////////////
  generate
    if (C_AXI_SUPPORTS_WRITE == 1) begin : USE_WRITE
    
      // Write Channel Signals for Commands Queue Interface.
      wire                              wr_cmd_valid;
      wire                              wr_cmd_split;
      wire                              wr_cmd_mirror;
      wire                              wr_cmd_fix;
      wire [C_S_AXI_BYTES_LOG-1:0]      wr_cmd_first_word;
      wire [C_S_AXI_BYTES_LOG-1:0]      wr_cmd_offset;
      wire [C_S_AXI_BYTES_LOG-1:0]      wr_cmd_mask;
      wire [C_M_AXI_BYTES_LOG:0]        wr_cmd_step;
      wire [3-1:0]                      wr_cmd_size;
      wire [8-1:0]                      wr_cmd_length;
      wire                              wr_cmd_ready;
      
      wire                              wr_cmd_b_valid;
      wire                              wr_cmd_b_split;
      wire [8-1:0]                      wr_cmd_b_repeat ;
      wire                              wr_cmd_b_ready;
      wire [C_S_AXI_ID_WIDTH-1:0]       wr_cmd_b_id;
      
      wire [8-1:0]                  s_axi_awlen_i;
      wire [2-1:0]                  s_axi_awlock_i;
      
      assign s_axi_awlen_i = (C_AXI_PROTOCOL == P_AXI3) ? {4'b0000, s_axi_awlen[3:0]}: s_axi_awlen;
      assign s_axi_awlock_i = (C_AXI_PROTOCOL == P_AXI3) ? s_axi_awlock : {1'b0, s_axi_awlock[0]};
      
      // Write Address Channel.
      axi_dwidth_converter_v2_1_12_a_downsizer #
      (
       .C_FAMILY                    (C_FAMILY),
       .C_AXI_PROTOCOL              (C_AXI_PROTOCOL),
       .C_AXI_ID_WIDTH              (C_S_AXI_ID_WIDTH),
       .C_SUPPORTS_ID               (C_SUPPORTS_ID),
       .C_AXI_ADDR_WIDTH            (P_AXI_ADDR_WIDTH),
       .C_S_AXI_DATA_WIDTH          (C_S_AXI_DATA_WIDTH),
       .C_M_AXI_DATA_WIDTH          (C_M_AXI_DATA_WIDTH),
       .C_AXI_CHANNEL               (0),
       .C_MAX_SPLIT_BEATS           (P_MAX_SPLIT_BEATS),
       .C_MAX_SPLIT_BEATS_LOG       (P_MAX_SPLIT_BEATS_LOG),
       .C_S_AXI_BYTES_LOG           (C_S_AXI_BYTES_LOG),
       .C_M_AXI_BYTES_LOG           (C_M_AXI_BYTES_LOG),
       .C_RATIO_LOG                 (C_RATIO_LOG)
        ) write_addr_inst
       (
        // Global Signals
        .ARESET                     (!aresetn),
        .ACLK                       (aclk),
    
        // Command Interface (W)
        .cmd_valid                  (wr_cmd_valid),
        .cmd_split                  (wr_cmd_split),
        .cmd_mirror                 (wr_cmd_mirror),
        .cmd_fix                    (wr_cmd_fix),
        .cmd_first_word             (wr_cmd_first_word),
        .cmd_offset                 (wr_cmd_offset),
        .cmd_mask                   (wr_cmd_mask),
        .cmd_step                   (wr_cmd_step),
        .cmd_size                   (wr_cmd_size),
        .cmd_length                 (wr_cmd_length),
        .cmd_ready                  (wr_cmd_ready),
       
        // Command Interface (B)
        .cmd_b_valid                (wr_cmd_b_valid),
        .cmd_b_split                (wr_cmd_b_split),
        .cmd_b_repeat               (wr_cmd_b_repeat),
        .cmd_b_ready                (wr_cmd_b_ready),
        .cmd_id                     (wr_cmd_b_id),
       
        // Slave Interface Write Address Ports
        .S_AXI_AID                  (s_axi_awid),
        .S_AXI_AADDR                (s_axi_awaddr_i),
        .S_AXI_ALEN                 (s_axi_awlen_i),
        .S_AXI_ASIZE                (s_axi_awsize),
        .S_AXI_ABURST               (s_axi_awburst),
        .S_AXI_ALOCK                (s_axi_awlock_i),
        .S_AXI_ACACHE               (s_axi_awcache),
        .S_AXI_APROT                (s_axi_awprot),
        .S_AXI_AREGION              (s_axi_awregion),
        .S_AXI_AQOS                 (s_axi_awqos),
        .S_AXI_AVALID               (s_axi_awvalid),
        .S_AXI_AREADY               (s_axi_awready),
        
        // Master Interface Write Address Port
        .M_AXI_AADDR                (m_axi_awaddr_i),
        .M_AXI_ALEN                 (m_axi_awlen),
        .M_AXI_ASIZE                (m_axi_awsize),
        .M_AXI_ABURST               (m_axi_awburst),
        .M_AXI_ALOCK                (m_axi_awlock),
        .M_AXI_ACACHE               (m_axi_awcache),
        .M_AXI_APROT                (m_axi_awprot),
        .M_AXI_AREGION              (m_axi_awregion),
        .M_AXI_AQOS                 (m_axi_awqos),
        .M_AXI_AVALID               (m_axi_awvalid),
        .M_AXI_AREADY               (m_axi_awready)
       );
       
      // Write Data channel.
      axi_dwidth_converter_v2_1_12_w_downsizer #
      (
       .C_FAMILY                    (C_FAMILY),
       .C_S_AXI_DATA_WIDTH          (C_S_AXI_DATA_WIDTH),
       .C_M_AXI_DATA_WIDTH          (C_M_AXI_DATA_WIDTH),
       .C_S_AXI_BYTES_LOG           (C_S_AXI_BYTES_LOG),
       .C_M_AXI_BYTES_LOG           (C_M_AXI_BYTES_LOG),
       .C_RATIO_LOG                 (C_RATIO_LOG)
        ) write_data_inst
       (
        // Global Signals
        .ARESET                     (!aresetn),
        .ACLK                       (aclk),
    
        // Command Interface
        .cmd_valid                  (wr_cmd_valid),
        .cmd_mirror                 (wr_cmd_mirror),
        .cmd_fix                    (wr_cmd_fix),
        .cmd_first_word             (wr_cmd_first_word),
        .cmd_offset                 (wr_cmd_offset),
        .cmd_mask                   (wr_cmd_mask),
        .cmd_step                   (wr_cmd_step),
        .cmd_size                   (wr_cmd_size),
        .cmd_length                 (wr_cmd_length),
        .cmd_ready                  (wr_cmd_ready),
       
        // Slave Interface Write Data Ports
        .S_AXI_WDATA                (s_axi_wdata),
        .S_AXI_WSTRB                (s_axi_wstrb),
        .S_AXI_WLAST                (s_axi_wlast),
        .S_AXI_WVALID               (s_axi_wvalid),
        .S_AXI_WREADY               (s_axi_wready),
        
        // Master Interface Write Data Ports
        .M_AXI_WDATA                (m_axi_wdata),
        .M_AXI_WSTRB                (m_axi_wstrb),
        .M_AXI_WLAST                (m_axi_wlast),
        .M_AXI_WVALID               (m_axi_wvalid),
        .M_AXI_WREADY               (m_axi_wready)
       );
      
      // Write Response channel.
      if ( P_MAX_SPLIT_BEATS > 0 ) begin : USE_SPLIT
        axi_dwidth_converter_v2_1_12_b_downsizer #
        (
         .C_FAMILY                    (C_FAMILY),
         .C_AXI_ID_WIDTH              (C_S_AXI_ID_WIDTH)
          ) write_resp_inst
         (
          // Global Signals
          .ARESET                     (!aresetn),
          .ACLK                       (aclk),
      
          // Command Interface
          .cmd_valid                  (wr_cmd_b_valid),
          .cmd_split                  (wr_cmd_b_split),
          .cmd_repeat                 (wr_cmd_b_repeat),
          .cmd_ready                  (wr_cmd_b_ready),
          .cmd_id                     (wr_cmd_b_id),
          
          // Slave Interface Write Response Ports
          .S_AXI_BID                  (s_axi_bid),
          .S_AXI_BRESP                (s_axi_bresp),
          .S_AXI_BVALID               (s_axi_bvalid),
          .S_AXI_BREADY               (s_axi_bready),
          
          // Master Interface Write Response Ports
          .M_AXI_BRESP                (m_axi_bresp),
          .M_AXI_BVALID               (m_axi_bvalid),
          .M_AXI_BREADY               (m_axi_bready)
         );
        
      end else begin : NO_SPLIT
        assign s_axi_bid     = wr_cmd_b_id;
        assign s_axi_bresp   = m_axi_bresp;
        assign s_axi_bvalid  = m_axi_bvalid;
        assign m_axi_bready  = s_axi_bready;
        
      end
    end else begin : NO_WRITE
      // Slave Interface Write Address Ports
      assign s_axi_awready = 1'b0;
      // Slave Interface Write Data Ports
      assign s_axi_wready  = 1'b0;
      // Slave Interface Write Response Ports
      assign s_axi_bid     = {C_S_AXI_ID_WIDTH{1'b0}};
      assign s_axi_bresp   = 2'b0;
      assign s_axi_bvalid  = 1'b0;
      
      // Master Interface Write Address Port
      assign m_axi_awaddr_i  = {P_AXI_ADDR_WIDTH{1'b0}};
      assign m_axi_awlen   = 8'b0;
      assign m_axi_awsize  = 3'b0;
      assign m_axi_awburst = 2'b0;
      assign m_axi_awlock  = 2'b0;
      assign m_axi_awcache = 4'b0;
      assign m_axi_awprot  = 3'b0;
      assign m_axi_awregion = 4'b0;
      assign m_axi_awqos   = 4'b0;
      assign m_axi_awvalid = 1'b0;
      // Master Interface Write Data Ports
      assign m_axi_wdata   = {C_M_AXI_DATA_WIDTH{1'b0}};
      assign m_axi_wstrb   = {C_M_AXI_DATA_WIDTH/8{1'b0}};
      assign m_axi_wlast   = 1'b0;
//      assign m_axi_wuser   = {C_AXI_WUSER_WIDTH{1'b0}};
      assign m_axi_wvalid  = 1'b0;
      // Master Interface Write Response Ports
      assign m_axi_bready  = 1'b0;
      
    end
  endgenerate
  
  /////////////////////////////////////////////////////////////////////////////
  // Handle Read Channels (AR/R)
  /////////////////////////////////////////////////////////////////////////////
  generate
    if (C_AXI_SUPPORTS_READ == 1) begin : USE_READ
    
      // Read Channel Signals for Commands Queue Interface.
      wire                              rd_cmd_valid;
      wire                              rd_cmd_split;
      wire                              rd_cmd_mirror;
      wire                              rd_cmd_fix;
      wire [C_S_AXI_BYTES_LOG-1:0]      rd_cmd_first_word;
      wire [C_S_AXI_BYTES_LOG-1:0]      rd_cmd_offset;
      wire [C_S_AXI_BYTES_LOG-1:0]      rd_cmd_mask;
      wire [C_M_AXI_BYTES_LOG:0]        rd_cmd_step;
      wire [3-1:0]                      rd_cmd_size;
      wire [8-1:0]                      rd_cmd_length;
      wire                              rd_cmd_ready;
      wire [C_S_AXI_ID_WIDTH-1:0]       rd_cmd_id;
      
      wire [8-1:0]                  s_axi_arlen_i;
      wire [2-1:0]                  s_axi_arlock_i;
      
      assign s_axi_arlen_i = (C_AXI_PROTOCOL == P_AXI3) ? {4'b0000, s_axi_arlen[3:0]}: s_axi_arlen;
      assign s_axi_arlock_i = (C_AXI_PROTOCOL == P_AXI3) ? s_axi_arlock : {1'b0, s_axi_arlock[0]};
      
      // Write Address Channel.
      axi_dwidth_converter_v2_1_12_a_downsizer #
      (
       .C_FAMILY                    (C_FAMILY),
       .C_AXI_PROTOCOL              (C_AXI_PROTOCOL),
       .C_AXI_ID_WIDTH              (C_S_AXI_ID_WIDTH),
       .C_SUPPORTS_ID               (C_SUPPORTS_ID),
       .C_AXI_ADDR_WIDTH            (P_AXI_ADDR_WIDTH),
       .C_S_AXI_DATA_WIDTH          (C_S_AXI_DATA_WIDTH),
       .C_M_AXI_DATA_WIDTH          (C_M_AXI_DATA_WIDTH),
       .C_AXI_CHANNEL               (1),
       .C_MAX_SPLIT_BEATS           (P_MAX_SPLIT_BEATS),
       .C_MAX_SPLIT_BEATS_LOG       (P_MAX_SPLIT_BEATS_LOG),
       .C_S_AXI_BYTES_LOG           (C_S_AXI_BYTES_LOG),
       .C_M_AXI_BYTES_LOG           (C_M_AXI_BYTES_LOG),
       .C_RATIO_LOG                 (C_RATIO_LOG)
        ) read_addr_inst
       (
        // Global Signals
        .ARESET                     (!aresetn),
        .ACLK                       (aclk),
    
        // Command Interface (R)
        .cmd_valid                  (rd_cmd_valid),
        .cmd_split                  (rd_cmd_split),
        .cmd_mirror                 (rd_cmd_mirror),
        .cmd_fix                    (rd_cmd_fix),
        .cmd_first_word             (rd_cmd_first_word),
        .cmd_offset                 (rd_cmd_offset),
        .cmd_mask                   (rd_cmd_mask),
        .cmd_step                   (rd_cmd_step),
        .cmd_size                   (rd_cmd_size),
        .cmd_length                 (rd_cmd_length),
        .cmd_ready                  (rd_cmd_ready),
        .cmd_id                     (rd_cmd_id),
       
        // Command Interface (B)
        .cmd_b_valid                (),
        .cmd_b_split                (),
        .cmd_b_repeat               (),
        .cmd_b_ready                (1'b0),
       
        // Slave Interface Write Address Ports
        .S_AXI_AID                  (s_axi_arid),
        .S_AXI_AADDR                (s_axi_araddr_i),
        .S_AXI_ALEN                 (s_axi_arlen_i),
        .S_AXI_ASIZE                (s_axi_arsize),
        .S_AXI_ABURST               (s_axi_arburst),
        .S_AXI_ALOCK                (s_axi_arlock_i),
        .S_AXI_ACACHE               (s_axi_arcache),
        .S_AXI_APROT                (s_axi_arprot),
        .S_AXI_AREGION              (s_axi_arregion),
        .S_AXI_AQOS                 (s_axi_arqos),
        .S_AXI_AVALID               (s_axi_arvalid),
        .S_AXI_AREADY               (s_axi_arready),
        
        // Master Interface Write Address Port
        .M_AXI_AADDR                (m_axi_araddr_i),
        .M_AXI_ALEN                 (m_axi_arlen),
        .M_AXI_ASIZE                (m_axi_arsize),
        .M_AXI_ABURST               (m_axi_arburst),
        .M_AXI_ALOCK                (m_axi_arlock),
        .M_AXI_ACACHE               (m_axi_arcache),
        .M_AXI_APROT                (m_axi_arprot),
        .M_AXI_AREGION              (m_axi_arregion),
        .M_AXI_AQOS                 (m_axi_arqos),
        .M_AXI_AVALID               (m_axi_arvalid),
        .M_AXI_AREADY               (m_axi_arready)
       );
       
      // Read Data channel.
      axi_dwidth_converter_v2_1_12_r_downsizer #
      (
       .C_FAMILY                    (C_FAMILY),
       .C_AXI_ID_WIDTH              (C_S_AXI_ID_WIDTH),
       .C_S_AXI_DATA_WIDTH          (C_S_AXI_DATA_WIDTH),
       .C_M_AXI_DATA_WIDTH          (C_M_AXI_DATA_WIDTH),
       .C_S_AXI_BYTES_LOG           (C_S_AXI_BYTES_LOG),
       .C_M_AXI_BYTES_LOG           (C_M_AXI_BYTES_LOG),
       .C_RATIO_LOG                 (C_RATIO_LOG)
        ) read_data_inst
       (
        // Global Signals
        .ARESET                     (!aresetn),
        .ACLK                       (aclk),
    
        // Command Interface
        .cmd_valid                  (rd_cmd_valid),
        .cmd_split                  (rd_cmd_split),
        .cmd_mirror                 (rd_cmd_mirror),
        .cmd_fix                    (rd_cmd_fix),
        .cmd_first_word             (rd_cmd_first_word),
        .cmd_offset                 (rd_cmd_offset),
        .cmd_mask                   (rd_cmd_mask),
        .cmd_step                   (rd_cmd_step),
        .cmd_size                   (rd_cmd_size),
        .cmd_length                 (rd_cmd_length),
        .cmd_ready                  (rd_cmd_ready),
        .cmd_id                     (rd_cmd_id),
       
        // Slave Interface Read Data Ports
        .S_AXI_RID                  (s_axi_rid),
        .S_AXI_RDATA                (s_axi_rdata),
        .S_AXI_RRESP                (s_axi_rresp),
        .S_AXI_RLAST                (s_axi_rlast),
        .S_AXI_RVALID               (s_axi_rvalid),
        .S_AXI_RREADY               (s_axi_rready),
        
        // Master Interface Read Data Ports
        .M_AXI_RDATA                (m_axi_rdata),
        .M_AXI_RRESP                (m_axi_rresp),
        .M_AXI_RLAST                (m_axi_rlast),
        .M_AXI_RVALID               (m_axi_rvalid),
        .M_AXI_RREADY               (m_axi_rready)
       );
       
    end else begin : NO_READ
      // Slave Interface Read Address Ports
      assign s_axi_arready = 1'b0;
      // Slave Interface Read Data Ports
      assign s_axi_rid     = {C_S_AXI_ID_WIDTH{1'b0}};
      assign s_axi_rdata   = {C_S_AXI_DATA_WIDTH{1'b0}};
      assign s_axi_rresp   = 2'b0;
      assign s_axi_rlast   = 1'b0;
//      assign s_axi_ruser   = {C_AXI_RUSER_WIDTH{1'b0}};
      assign s_axi_rvalid  = 1'b0;
      
      // Master Interface Read Address Port
      assign m_axi_araddr_i  = {P_AXI_ADDR_WIDTH{1'b0}};
      assign m_axi_arlen   = 8'b0;
      assign m_axi_arsize  = 3'b0;
      assign m_axi_arburst = 2'b0;
      assign m_axi_arlock  = 2'b0;
      assign m_axi_arcache = 4'b0;
      assign m_axi_arprot  = 3'b0;
      assign m_axi_arregion = 4'b0;
      assign m_axi_arqos   = 4'b0;
      assign m_axi_arvalid = 1'b0;
      // Master Interface Read Data Ports
      assign m_axi_rready  = 1'b0;
      
    end
  endgenerate
  
endmodule


// -- (c) Copyright 2010 - 2011 Xilinx, Inc. All rights reserved.
// --
// -- This file contains confidential and proprietary information
// -- of Xilinx, Inc. and is protected under U.S. and 
// -- international copyright and other intellectual property
// -- laws.
// --
// -- DISCLAIMER
// -- This disclaimer is not a license and does not grant any
// -- rights to the materials distributed herewith. Except as
// -- otherwise provided in a valid license issued to you by
// -- Xilinx, and to the maximum extent permitted by applicable
// -- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// -- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// -- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// -- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// -- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// -- (2) Xilinx shall not be liable (whether in contract or tort,
// -- including negligence, or under any other theory of
// -- liability) for any loss or damage of any kind or nature
// -- related to, arising under or in connection with these
// -- materials, including for any direct, or any indirect,
// -- special, incidental, or consequential loss or damage
// -- (including loss of data, profits, goodwill, or any type of
// -- loss or damage suffered as a result of any action brought
// -- by a third party) even if such damage or loss was
// -- reasonably foreseeable or Xilinx had been advised of the
// -- possibility of the same.
// --
// -- CRITICAL APPLICATIONS
// -- Xilinx products are not designed or intended to be fail-
// -- safe, or for use in any application requiring fail-safe
// -- performance, such as life-support or safety devices or
// -- systems, Class III medical devices, nuclear facilities,
// -- applications related to the deployment of airbags, or any
// -- other applications that could lead to death, personal
// -- injury, or severe property or environmental damage
// -- (individually and collectively, "Critical
// -- Applications"). Customer assumes the sole risk and
// -- liability of any use of Xilinx products in Critical
// -- Applications, subject only to applicable laws and
// -- regulations governing limitations on product liability.
// --
// -- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// -- PART OF THIS FILE AT ALL TIMES.
//-----------------------------------------------------------------------------
//
// Description: Down-Sizer
// Down-Sizer for generic SI- and MI-side data widths. This module instantiates
// Address, Write Data, Write Response and Read Data Down-Sizer modules, each one taking care
// of the channel specific tasks.
// The Address Down-Sizer can handle both AR and AW channels.
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   axi4lite_downsizer
//
//--------------------------------------------------------------------------
`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_dwidth_converter_v2_1_12_axi4lite_downsizer #
  (
   parameter         C_FAMILY                         = "none", 
                       // FPGA Family.
   parameter integer C_AXI_ADDR_WIDTH                 = 32, 
                       // Width of all ADDR signals on SI and MI.
                       // Range (AXI4, AXI3): 12 - 64.
   parameter integer C_AXI_SUPPORTS_WRITE             = 1,
   parameter integer C_AXI_SUPPORTS_READ              = 1
   )
  (
   // Global Signals
   input  wire                              aresetn,
   input  wire                              aclk,

   // Slave Interface Write Address Ports
   input  wire [C_AXI_ADDR_WIDTH-1:0]       s_axi_awaddr,
   input  wire [3-1:0]                      s_axi_awprot,
   input  wire                              s_axi_awvalid,
   output wire                              s_axi_awready,
   // Slave Interface Write Data Ports
   input  wire [64-1:0]                     s_axi_wdata,
   input  wire [64/8-1:0]                   s_axi_wstrb,
   input  wire                              s_axi_wvalid,
   output wire                              s_axi_wready,
   // Slave Interface Write Response Ports
   output wire [2-1:0]                      s_axi_bresp,
   output wire                              s_axi_bvalid,
   input  wire                              s_axi_bready,
   // Slave Interface Read Address Ports
   input  wire [C_AXI_ADDR_WIDTH-1:0]       s_axi_araddr,
   input  wire [3-1:0]                      s_axi_arprot,
   input  wire                              s_axi_arvalid,
   output wire                              s_axi_arready,
   // Slave Interface Read Data Ports
   output wire [64-1:0]                     s_axi_rdata,
   output wire [2-1:0]                      s_axi_rresp,
   output wire                              s_axi_rvalid,
   input  wire                              s_axi_rready,

   // Master Interface Write Address Port
   output wire [C_AXI_ADDR_WIDTH-1:0]       m_axi_awaddr,
   output wire [3-1:0]                      m_axi_awprot,
   output wire                              m_axi_awvalid,
   input  wire                              m_axi_awready,
   // Master Interface Write Data Ports
   output wire [32-1:0]                     m_axi_wdata,
   output wire [32/8-1:0]                   m_axi_wstrb,
   output wire                              m_axi_wvalid,
   input  wire                              m_axi_wready,
   // Master Interface Write Response Ports
   input  wire [2-1:0]                      m_axi_bresp,
   input  wire                              m_axi_bvalid,
   output wire                              m_axi_bready,
   // Master Interface Read Address Port
   output wire [C_AXI_ADDR_WIDTH-1:0]       m_axi_araddr,
   output wire [3-1:0]                      m_axi_arprot,
   output wire                              m_axi_arvalid,
   input  wire                              m_axi_arready,
   // Master Interface Read Data Ports
   input  wire [32-1:0]                     m_axi_rdata,
   input  wire [2-1:0]                      m_axi_rresp,
   input  wire                              m_axi_rvalid,
   output wire                              m_axi_rready
   );

  reg                                       s_axi_arready_i = 1'b0 ;
  reg                                       s_axi_rvalid_i = 1'b0  ;
  reg                                       m_axi_arvalid_i = 1'b0 ;
  reg                                       m_axi_rready_i = 1'b0  ;
  reg                                       split_ar        ;
  reg                                       split_r         ;
  reg                                       ar_start        ;
  reg                                       aw_start        ;
  reg                                       ar_done         ;
  reg  [31:0]                               rdata_low       ;
  reg  [1:0]                                rresp_low       ;
  reg                                       s_axi_awready_i = 1'b0;
  reg                                       s_axi_bvalid_i = 1'b0  ;
  reg                                       m_axi_awvalid_i = 1'b0 ;
  reg                                       m_axi_wvalid_i = 1'b0  ;
  reg                                       m_axi_bready_i = 1'b0  ;
  reg                                       split_aw        ;
  reg                                       split_w         ;
  reg                                       high_aw         ;
  reg                                       aw_done         ;
  reg                                       w_done          ;
  reg  [1:0]                                bresp_low       ;
  wire [C_AXI_ADDR_WIDTH-1:0]               s_axaddr        ;
  wire [C_AXI_ADDR_WIDTH-1:0]               m_axaddr        ;
  
  generate
  if (C_AXI_SUPPORTS_READ != 0) begin : gen_read
    always @(posedge aclk) begin
      if (~aresetn) begin
        s_axi_arready_i <= 1'b0 ;
        s_axi_rvalid_i  <= 1'b0 ;
        m_axi_arvalid_i <= 1'b0 ;
        m_axi_rready_i  <= 1'b0 ;
        split_ar        <= 1'b0 ;
        split_r         <= 1'b0 ;
        ar_start        <= 1'b0 ;
        ar_done         <= 1'b0 ;
        rdata_low       <= 32'b0 ;
        rresp_low       <= 2'b0 ;
      end else begin
        m_axi_rready_i <= 1'b0; // end single-cycle pulse
        if (s_axi_rvalid_i) begin
          if (s_axi_rready) begin
            s_axi_rvalid_i <= 1'b0;
            m_axi_rready_i <= 1'b1; // begin single-cycle pulse
            split_ar <= 1'b0;
            split_r <= 1'b0;
            ar_start <= 1'b0;
          end
        end else if (s_axi_arready_i) begin
          s_axi_arready_i <= 1'b0; // end single-cycle pulse
          s_axi_rvalid_i <= 1'b1;
        end else if (ar_done) begin
          if (m_axi_rvalid) begin
            ar_done <= 1'b0;
            if (split_ar & ~split_r) begin
              split_r <= 1'b1;
              rdata_low <= m_axi_rdata;
              rresp_low <= m_axi_rresp;
              m_axi_rready_i <= 1'b1; // begin single-cycle pulse
              m_axi_arvalid_i <= 1'b1;
            end else begin
              s_axi_arready_i <= 1'b1; // begin single-cycle pulse
            end
          end
        end else if (m_axi_arvalid_i) begin
          if (m_axi_arready) begin
            m_axi_arvalid_i <= 1'b0;
            ar_done <= 1'b1;
          end
        end else if (s_axi_arvalid & ((C_AXI_SUPPORTS_WRITE==0) | (~aw_start))) begin
          m_axi_arvalid_i <= 1'b1;
          split_ar <= ~s_axi_araddr[2];
          ar_start <= 1'b1;
        end
      end
    end
    assign s_axi_arready = s_axi_arready_i ;
    assign s_axi_rvalid  = s_axi_rvalid_i  ;
    assign m_axi_arvalid = m_axi_arvalid_i ;
    assign m_axi_rready  = m_axi_rready_i  ;
    assign m_axi_araddr = m_axaddr;
    assign s_axi_rresp    = split_r ? ({m_axi_rresp[1], &m_axi_rresp} | {rresp_low[1], &rresp_low}) : m_axi_rresp;
    assign s_axi_rdata    = split_r ? {m_axi_rdata,rdata_low} : {m_axi_rdata,m_axi_rdata};
    assign m_axi_arprot   = s_axi_arprot;
  end else begin : gen_noread
    assign s_axi_arready = 1'b0 ;
    assign s_axi_rvalid  = 1'b0 ;
    assign m_axi_arvalid = 1'b0 ;
    assign m_axi_rready  = 1'b0 ;
    assign m_axi_araddr  = {C_AXI_ADDR_WIDTH{1'b0}} ;
    assign s_axi_rresp   = 2'b0 ;
    assign s_axi_rdata   = 64'b0 ;
    assign m_axi_arprot  = 3'b0 ;
    always @ * begin
      ar_start = 1'b0;
      split_r = 1'b0;
    end
  end
  
  if (C_AXI_SUPPORTS_WRITE != 0) begin : gen_write
    always @(posedge aclk) begin
      if (~aresetn) begin
        s_axi_awready_i <= 1'b0 ;
        s_axi_bvalid_i  <= 1'b0 ;
        m_axi_awvalid_i <= 1'b0 ;
        m_axi_wvalid_i  <= 1'b0 ;
        m_axi_bready_i  <= 1'b0 ;
        split_aw        <= 1'b0 ;
        split_w         <= 1'b0 ;
        high_aw         <= 1'b0 ;
        aw_start        <= 1'b0 ;
        aw_done         <= 1'b0 ;
        w_done          <= 1'b0 ;
        bresp_low       <= 2'b0 ;
      end else begin
        m_axi_bready_i <= 1'b0; // end single-cycle pulse
        if (s_axi_bvalid_i) begin
          if (s_axi_bready) begin
            s_axi_bvalid_i <= 1'b0;
            m_axi_bready_i <= 1'b1; // begin single-cycle pulse
            split_aw <= 1'b0;
            split_w <= 1'b0;
            high_aw <= 1'b0;
            aw_start <= 1'b0 ;
          end
        end else if (s_axi_awready_i) begin
          s_axi_awready_i <= 1'b0; // end single-cycle pulse
          s_axi_bvalid_i <= 1'b1;
        end else if (aw_done & w_done) begin
          if (m_axi_bvalid) begin
            aw_done <= 1'b0;
            w_done <= 1'b0;
            if (split_aw & ~split_w) begin
              split_w <= 1'b1;
              bresp_low <= m_axi_bresp;
              m_axi_bready_i <= 1'b1; // begin single-cycle pulse
              m_axi_awvalid_i <= 1'b1;
              m_axi_wvalid_i <= 1'b1;
            end else begin
              s_axi_awready_i <= 1'b1; // begin single-cycle pulse
            end
          end
        end else begin
          if (m_axi_awvalid_i | m_axi_wvalid_i) begin
            if (m_axi_awvalid_i & m_axi_awready) begin
              m_axi_awvalid_i <= 1'b0;
              aw_done <= 1'b1;
            end
            if (m_axi_wvalid_i & m_axi_wready) begin
              m_axi_wvalid_i <= 1'b0;
              w_done <= 1'b1;
            end
          end else if (s_axi_awvalid & s_axi_wvalid & ~aw_done & ~w_done & ((C_AXI_SUPPORTS_READ==0) | (~ar_start & ~s_axi_arvalid))) begin
            m_axi_awvalid_i <= 1'b1;
            m_axi_wvalid_i <= 1'b1;
            aw_start        <= 1'b1 ;
            split_aw <= ~s_axi_awaddr[2] & (|s_axi_wstrb[7:4]) & (|s_axi_wstrb[3:0]);
            high_aw <= ~s_axi_awaddr[2] & (|s_axi_wstrb[7:4]) & ~(|s_axi_wstrb[3:0]);
          end
        end
      end
    end
    assign s_axi_awready = s_axi_awready_i ;
    assign s_axi_wready  = s_axi_awready_i ;
    assign s_axi_bvalid  = s_axi_bvalid_i  ;
    assign m_axi_awvalid = m_axi_awvalid_i ;
    assign m_axi_wvalid  = m_axi_wvalid_i  ;
    assign m_axi_bready  = m_axi_bready_i  ;
    assign m_axi_awaddr = m_axaddr;
    assign s_axi_bresp    = split_w ? ({m_axi_bresp[1], &m_axi_bresp} | {bresp_low[1], &bresp_low}) : m_axi_bresp;
    assign m_axi_wdata    = (split_w | s_axi_awaddr[2] | (|s_axi_wstrb[7:4]) & ~(|s_axi_wstrb[3:0])) ? s_axi_wdata[63:32] : s_axi_wdata[31:0];
    assign m_axi_wstrb    = (split_w | s_axi_awaddr[2] | (|s_axi_wstrb[7:4]) & ~(|s_axi_wstrb[3:0])) ? s_axi_wstrb[7:4] : s_axi_wstrb[3:0];
    assign m_axi_awprot   = s_axi_awprot;
  end else begin : gen_nowrite
    assign s_axi_awready = 1'b0 ;
    assign s_axi_wready  = 1'b0 ;
    assign s_axi_bvalid  = 1'b0 ;
    assign m_axi_awvalid = 1'b0 ;
    assign m_axi_wvalid  = 1'b0 ;
    assign m_axi_bready  = 1'b0 ;
    assign m_axi_awaddr  = {C_AXI_ADDR_WIDTH{1'b0}} ;
    assign s_axi_bresp   = 2'b0 ;
    assign m_axi_wdata   = 32'b0 ;
    assign m_axi_wstrb   = 4'b0 ;
    assign m_axi_awprot  = 3'b0 ;
    always @ * begin
      aw_start = 1'b0;
      split_w = 1'b0;
    end
  end

  if (C_AXI_SUPPORTS_WRITE == 0) begin : gen_ro_addr
    assign m_axaddr = split_r ? ({s_axi_araddr[C_AXI_ADDR_WIDTH-1:2], 2'b00}  | 3'b100) : s_axi_araddr;
  end else if (C_AXI_SUPPORTS_READ == 0) begin : gen_wo_addr
    assign m_axaddr = (split_w | high_aw) ? ({s_axi_awaddr[C_AXI_ADDR_WIDTH-1:2], 2'b00}  | 3'b100) : s_axi_awaddr;
  end else begin : gen_rw_addr
    assign s_axaddr = ar_start ? s_axi_araddr : s_axi_awaddr;
    assign m_axaddr = (split_w | split_r | high_aw) ? ({s_axaddr[C_AXI_ADDR_WIDTH-1:2], 2'b00}  | 3'b100) : s_axaddr;
  end
  
  endgenerate
endmodule


// -- (c) Copyright 2010 - 2011 Xilinx, Inc. All rights reserved.
// --
// -- This file contains confidential and proprietary information
// -- of Xilinx, Inc. and is protected under U.S. and 
// -- international copyright and other intellectual property
// -- laws.
// --
// -- DISCLAIMER
// -- This disclaimer is not a license and does not grant any
// -- rights to the materials distributed herewith. Except as
// -- otherwise provided in a valid license issued to you by
// -- Xilinx, and to the maximum extent permitted by applicable
// -- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// -- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// -- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// -- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// -- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// -- (2) Xilinx shall not be liable (whether in contract or tort,
// -- including negligence, or under any other theory of
// -- liability) for any loss or damage of any kind or nature
// -- related to, arising under or in connection with these
// -- materials, including for any direct, or any indirect,
// -- special, incidental, or consequential loss or damage
// -- (including loss of data, profits, goodwill, or any type of
// -- loss or damage suffered as a result of any action brought
// -- by a third party) even if such damage or loss was
// -- reasonably foreseeable or Xilinx had been advised of the
// -- possibility of the same.
// --
// -- CRITICAL APPLICATIONS
// -- Xilinx products are not designed or intended to be fail-
// -- safe, or for use in any application requiring fail-safe
// -- performance, such as life-support or safety devices or
// -- systems, Class III medical devices, nuclear facilities,
// -- applications related to the deployment of airbags, or any
// -- other applications that could lead to death, personal
// -- injury, or severe property or environmental damage
// -- (individually and collectively, "Critical
// -- Applications"). Customer assumes the sole risk and
// -- liability of any use of Xilinx products in Critical
// -- Applications, subject only to applicable laws and
// -- regulations governing limitations on product liability.
// --
// -- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// -- PART OF THIS FILE AT ALL TIMES.
//-----------------------------------------------------------------------------
//
// Description: AXI4Lite Upizer
// Converts 32-bit AXI4Lite on Slave Interface to 64-bit AXI4Lite on Master Interface.
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   axi4lite_upsizer
//
//--------------------------------------------------------------------------
`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_dwidth_converter_v2_1_12_axi4lite_upsizer #
  (
   parameter         C_FAMILY                         = "none", 
                       // FPGA Family.
   parameter integer C_AXI_ADDR_WIDTH                 = 32, 
                       // Width of all ADDR signals on SI and MI.
                       // Range 3 - 64.
   parameter integer C_AXI_SUPPORTS_WRITE             = 1,
   parameter integer C_AXI_SUPPORTS_READ              = 1
   )
  (
   // Global Signals
   input  wire                              aresetn,
   input  wire                              aclk,

   // Slave Interface Write Address Ports
   input  wire [C_AXI_ADDR_WIDTH-1:0]       s_axi_awaddr,
   input  wire [3-1:0]                      s_axi_awprot,
   input  wire                              s_axi_awvalid,
   output wire                              s_axi_awready,
   // Slave Interface Write Data Ports
   input  wire [32-1:0]                     s_axi_wdata,
   input  wire [32/8-1:0]                   s_axi_wstrb,
   input  wire                              s_axi_wvalid,
   output wire                              s_axi_wready,
   // Slave Interface Write Response Ports
   output wire [2-1:0]                      s_axi_bresp,
   output wire                              s_axi_bvalid,
   input  wire                              s_axi_bready,
   // Slave Interface Read Address Ports
   input  wire [C_AXI_ADDR_WIDTH-1:0]       s_axi_araddr,
   input  wire [3-1:0]                      s_axi_arprot,
   input  wire                              s_axi_arvalid,
   output wire                              s_axi_arready,
   // Slave Interface Read Data Ports
   output wire [32-1:0]                     s_axi_rdata,
   output wire [2-1:0]                      s_axi_rresp,
   output wire                              s_axi_rvalid,
   input  wire                              s_axi_rready,

   // Master Interface Write Address Port
   output wire [C_AXI_ADDR_WIDTH-1:0]       m_axi_awaddr,
   output wire [3-1:0]                      m_axi_awprot,
   output wire                              m_axi_awvalid,
   input  wire                              m_axi_awready,
   // Master Interface Write Data Ports
   output wire [64-1:0]                     m_axi_wdata,
   output wire [64/8-1:0]                   m_axi_wstrb,
   output wire                              m_axi_wvalid,
   input  wire                              m_axi_wready,
   // Master Interface Write Response Ports
   input  wire [2-1:0]                      m_axi_bresp,
   input  wire                              m_axi_bvalid,
   output wire                              m_axi_bready,
   // Master Interface Read Address Port
   output wire [C_AXI_ADDR_WIDTH-1:0]       m_axi_araddr,
   output wire [3-1:0]                      m_axi_arprot,
   output wire                              m_axi_arvalid,
   input  wire                              m_axi_arready,
   // Master Interface Read Data Ports
   input  wire [64-1:0]                     m_axi_rdata,
   input  wire [2-1:0]                      m_axi_rresp,
   input  wire                              m_axi_rvalid,
   output wire                              m_axi_rready
   );

  reg                                       s_axi_arready_i = 1'b0 ;
  reg                                       m_axi_arvalid_i = 1'b0 ;
  reg                                       m_axi_rready_i = 1'b0 ;
  reg                                       s_axi_rvalid_i = 1'b0 ;
  reg                                       ar_done         ;
  reg                                       araddr2         ;
  reg                                       s_axi_awready_i = 1'b0 ;
  reg                                       s_axi_bvalid_i = 1'b0  ;
  reg                                       m_axi_awvalid_i = 1'b0 ;
  reg                                       m_axi_wvalid_i = 1'b0  ;
  reg                                       m_axi_bready_i = 1'b0  ;
  reg                                       aw_done         ;
  reg                                       w_done          ;
  
  generate
  if (C_AXI_SUPPORTS_READ != 0) begin : gen_read
    always @(posedge aclk) begin
      if (~aresetn) begin
        s_axi_arready_i <= 1'b0 ;
        m_axi_arvalid_i <= 1'b0 ;
        s_axi_rvalid_i <= 1'b0;
        m_axi_rready_i <= 1'b1;
        ar_done         <= 1'b0 ;
        araddr2         <= 1'b0 ;
      end else begin
        s_axi_arready_i <= 1'b0 ; // end single-cycle pulse
        m_axi_rready_i <= 1'b0; // end single-cycle pulse
        if (s_axi_rvalid_i) begin
          if (s_axi_rready) begin
            s_axi_rvalid_i <= 1'b0;
            m_axi_rready_i <= 1'b1; // begin single-cycle pulse
            ar_done <= 1'b0;
          end
        end else if (m_axi_rvalid & ar_done) begin
          s_axi_rvalid_i <= 1'b1;
        end else if (m_axi_arvalid_i) begin
          if (m_axi_arready) begin
            m_axi_arvalid_i <= 1'b0;
            s_axi_arready_i <= 1'b1 ; // begin single-cycle pulse
            araddr2 <= s_axi_araddr[2];
            ar_done <= 1'b1;
          end
        end else if (s_axi_arvalid & ~ar_done) begin
          m_axi_arvalid_i <= 1'b1;
        end
      end
    end
    assign m_axi_arvalid = m_axi_arvalid_i ;
    assign s_axi_arready = s_axi_arready_i ;
    assign m_axi_araddr = s_axi_araddr;
    assign m_axi_arprot   = s_axi_arprot;
    assign s_axi_rvalid  = s_axi_rvalid_i  ;
    assign m_axi_rready  = m_axi_rready_i  ;
    assign s_axi_rdata    = araddr2 ? m_axi_rdata[63:32] : m_axi_rdata[31:0];
    assign s_axi_rresp    = m_axi_rresp;
  end else begin : gen_noread
    assign m_axi_arvalid = 1'b0 ;
    assign s_axi_arready = 1'b0 ;
    assign m_axi_araddr  = {C_AXI_ADDR_WIDTH{1'b0}} ;
    assign m_axi_arprot  = 3'b0 ;
    assign s_axi_rvalid  = 1'b0 ;
    assign m_axi_rready  = 1'b0 ;
    assign s_axi_rresp   = 2'b0 ;
    assign s_axi_rdata   = 32'b0 ;
  end
  
  if (C_AXI_SUPPORTS_WRITE != 0) begin : gen_write
    always @(posedge aclk) begin
      if (~aresetn) begin
        m_axi_awvalid_i <= 1'b0 ;
        s_axi_awready_i <= 1'b0 ;
        m_axi_wvalid_i  <= 1'b0 ;
        s_axi_bvalid_i  <= 1'b0 ;
        m_axi_bready_i  <= 1'b0 ;
        aw_done         <= 1'b0 ;
        w_done          <= 1'b0 ;
      end else begin
        m_axi_bready_i <= 1'b0; // end single-cycle pulse
        if (s_axi_bvalid_i) begin
          if (s_axi_bready) begin
            s_axi_bvalid_i <= 1'b0;
            m_axi_bready_i <= 1'b1; // begin single-cycle pulse
            aw_done <= 1'b0;
            w_done <= 1'b0;
          end
        end else if (s_axi_awready_i) begin
          s_axi_awready_i <= 1'b0; // end single-cycle pulse
          s_axi_bvalid_i <= 1'b1;
        end else if (aw_done & w_done) begin
          if (m_axi_bvalid) begin
            s_axi_awready_i <= 1'b1; // begin single-cycle pulse
          end
        end else begin
          if (m_axi_awvalid_i) begin
            if (m_axi_awready) begin
              m_axi_awvalid_i <= 1'b0;
              aw_done <= 1'b1;
            end
          end else if (s_axi_awvalid & ~aw_done) begin
            m_axi_awvalid_i <= 1'b1;
          end
          if (m_axi_wvalid_i) begin
            if (m_axi_wready) begin
              m_axi_wvalid_i <= 1'b0;
              w_done <= 1'b1;
            end
          end else if (s_axi_wvalid & (m_axi_awvalid_i | aw_done) & ~w_done) begin
            m_axi_wvalid_i <= 1'b1;
          end
        end
      end
    end
    assign m_axi_awvalid = m_axi_awvalid_i ;
    assign s_axi_awready = s_axi_awready_i ;
    assign m_axi_awaddr = s_axi_awaddr;
    assign m_axi_awprot   = s_axi_awprot;
    assign m_axi_wvalid  = m_axi_wvalid_i  ;
    assign s_axi_wready  = s_axi_awready_i ;
    assign m_axi_wdata    = {s_axi_wdata,s_axi_wdata};
    assign m_axi_wstrb    = s_axi_awaddr[2] ? {s_axi_wstrb, 4'b0} : {4'b0, s_axi_wstrb};
    assign s_axi_bvalid  = s_axi_bvalid_i  ;
    assign m_axi_bready  = m_axi_bready_i  ;
    assign s_axi_bresp    = m_axi_bresp;
  end else begin : gen_nowrite
    assign m_axi_awvalid = 1'b0 ;
    assign s_axi_awready = 1'b0 ;
    assign m_axi_awaddr  = {C_AXI_ADDR_WIDTH{1'b0}} ;
    assign m_axi_awprot  = 3'b0 ;
    assign m_axi_wvalid  = 1'b0 ;
    assign s_axi_wready  = 1'b0 ;
    assign m_axi_wdata   = 64'b0 ;
    assign m_axi_wstrb   = 8'b0 ;
    assign s_axi_bvalid  = 1'b0 ;
    assign m_axi_bready  = 1'b0 ;
    assign s_axi_bresp   = 2'b0 ;
  end

  endgenerate
endmodule


// -- (c) Copyright 2010 - 2012 Xilinx, Inc. All rights reserved.
// --
// -- This file contains confidential and proprietary information
// -- of Xilinx, Inc. and is protected under U.S. and 
// -- international copyright and other intellectual property
// -- laws.
// --
// -- DISCLAIMER
// -- This disclaimer is not a license and does not grant any
// -- rights to the materials distributed herewith. Except as
// -- otherwise provided in a valid license issued to you by
// -- Xilinx, and to the maximum extent permitted by applicable
// -- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// -- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// -- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// -- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// -- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// -- (2) Xilinx shall not be liable (whether in contract or tort,
// -- including negligence, or under any other theory of
// -- liability) for any loss or damage of any kind or nature
// -- related to, arising under or in connection with these
// -- materials, including for any direct, or any indirect,
// -- special, incidental, or consequential loss or damage
// -- (including loss of data, profits, goodwill, or any type of
// -- loss or damage suffered as a result of any action brought
// -- by a third party) even if such damage or loss was
// -- reasonably foreseeable or Xilinx had been advised of the
// -- possibility of the same.
// --
// -- CRITICAL APPLICATIONS
// -- Xilinx products are not designed or intended to be fail-
// -- safe, or for use in any application requiring fail-safe
// -- performance, such as life-support or safety devices or
// -- systems, Class III medical devices, nuclear facilities,
// -- applications related to the deployment of airbags, or any
// -- other applications that could lead to death, personal
// -- injury, or severe property or environmental damage
// -- (individually and collectively, "Critical
// -- Applications"). Customer assumes the sole risk and
// -- liability of any use of Xilinx products in Critical
// -- Applications, subject only to applicable laws and
// -- regulations governing limitations on product liability.
// --
// -- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// -- PART OF THIS FILE AT ALL TIMES.
//-----------------------------------------------------------------------------
//
// Description: Address Up-Sizer
//
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   a_upsizer
//     generic_baseblocks/*
//
//--------------------------------------------------------------------------
`timescale 1ps/1ps


(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_dwidth_converter_v2_1_12_a_upsizer #
  (
   parameter         C_FAMILY                         = "rtl", 
                       // FPGA Family. Current version: virtex6 or spartan6.
   parameter integer C_AXI_PROTOCOL = 0, 
                       // Protocol of SI and MI (0=AXI4, 1=AXI3).
   parameter integer C_AXI_ID_WIDTH                   = 1, 
                       // Width of all ID signals on SI side of converter.
                       // Range: 1 - 32.
   parameter integer C_SUPPORTS_ID                    = 0, 
                       // Indicates whether SI-side ID needs to be stored and compared.
                       // 0 = No, SI is single-threaded, propagate all transactions.
                       // 1 = Yes, stall any transaction with ID different than outstanding transactions.
   parameter integer C_AXI_ADDR_WIDTH                 = 32, 
                       // Width of all ADDR signals on SI and MI side of converter.
                       // Range: 32.
   parameter integer C_S_AXI_DATA_WIDTH               = 64,
                       // Width of s_axi_wdata and s_axi_rdata.
                       // Range: 32, 64, 128, 256, 512, 1024.
   parameter integer C_M_AXI_DATA_WIDTH               = 32,
                       // Width of m_axi_wdata and m_axi_rdata. 
                       // Assume always >= than C_S_AXI_DATA_WIDTH.
                       // Range: 32, 64, 128, 256, 512, 1024.
   parameter integer C_M_AXI_REGISTER                 = 0,
                       // Clock output data.
                       // Range: 0, 1
   parameter integer C_AXI_CHANNEL                      = 0,
                       // 0 = AXI AW Channel.
                       // 1 = AXI AR Channel.
   parameter integer C_PACKING_LEVEL                    = 1,
                       // 0 = Never pack (expander only); packing logic is omitted.
                       // 1 = Pack only when CACHE[1] (Modifiable) is high.
                       // 2 = Always pack, regardless of sub-size transaction or Modifiable bit.
                       //     (Required when used as helper-core by mem-con.)
   parameter integer C_FIFO_MODE                        = 0,
                       // 0=None, 1=Packet_FIFO, 2=Clock_conversion_Packet_FIFO, 3=Simple_FIFO (FUTURE), 4=Clock_conversion_Simple_FIFO (FUTURE)
   parameter integer C_ID_QUEUE                         = 0,
   parameter integer C_S_AXI_BYTES_LOG                = 3,
                       // Log2 of number of 32bit word on SI-side.
   parameter integer C_M_AXI_BYTES_LOG                = 3
                       // Log2 of number of 32bit word on MI-side.
   )
  (
   // Global Signals
   input  wire                                                    ARESET,
   input  wire                                                    ACLK,

   // Command Interface
   output wire                              cmd_valid,
   output wire                              cmd_fix,
   output wire                              cmd_modified,
   output wire                              cmd_complete_wrap,
   output wire                              cmd_packed_wrap,
   output wire [C_M_AXI_BYTES_LOG-1:0]      cmd_first_word, 
   output wire [C_M_AXI_BYTES_LOG-1:0]      cmd_next_word, 
   output wire [C_M_AXI_BYTES_LOG-1:0]      cmd_last_word,
   output wire [C_M_AXI_BYTES_LOG-1:0]      cmd_offset,
   output wire [C_M_AXI_BYTES_LOG-1:0]      cmd_mask,
   output wire [C_S_AXI_BYTES_LOG:0]        cmd_step,
   output wire [8-1:0]                      cmd_length,
   output wire [C_AXI_ID_WIDTH-1:0]         cmd_id,
   input  wire                              cmd_ready,
   input  wire                              cmd_id_ready,
   output  wire [C_AXI_ADDR_WIDTH-1:0]       cmd_si_addr,
   output wire [C_AXI_ID_WIDTH-1:0]          cmd_si_id,
   output  wire [8-1:0]                      cmd_si_len,
   output  wire [3-1:0]                      cmd_si_size,
   output  wire [2-1:0]                      cmd_si_burst,
   
   // Slave Interface Write Address Ports
   input  wire [C_AXI_ID_WIDTH-1:0]            S_AXI_AID,
   input  wire [C_AXI_ADDR_WIDTH-1:0]          S_AXI_AADDR,
   input  wire [8-1:0]                         S_AXI_ALEN,
   input  wire [3-1:0]                         S_AXI_ASIZE,
   input  wire [2-1:0]                         S_AXI_ABURST,
   input  wire [2-1:0]                         S_AXI_ALOCK,
   input  wire [4-1:0]                         S_AXI_ACACHE,
   input  wire [3-1:0]                         S_AXI_APROT,
   input  wire [4-1:0]                         S_AXI_AREGION,
   input  wire [4-1:0]                         S_AXI_AQOS,
   input  wire                                                   S_AXI_AVALID,
   output wire                                                   S_AXI_AREADY,

   // Master Interface Write Address Port
   output wire [C_AXI_ADDR_WIDTH-1:0]          M_AXI_AADDR,
   output wire [8-1:0]                         M_AXI_ALEN,
   output wire [3-1:0]                         M_AXI_ASIZE,
   output wire [2-1:0]                         M_AXI_ABURST,
   output wire [2-1:0]                         M_AXI_ALOCK,
   output wire [4-1:0]                         M_AXI_ACACHE,
   output wire [3-1:0]                         M_AXI_APROT,
   output wire [4-1:0]                         M_AXI_AREGION,
   output wire [4-1:0]                         M_AXI_AQOS,
   output wire                                                   M_AXI_AVALID,
   input  wire                                                   M_AXI_AREADY
   );
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Local params
  /////////////////////////////////////////////////////////////////////////////
  
  // Decode the native transaction size on the SI-side interface.
  localparam [3-1:0] C_S_AXI_NATIVE_SIZE = (C_S_AXI_DATA_WIDTH == 1024) ? 3'b111 :
                                           (C_S_AXI_DATA_WIDTH ==  512) ? 3'b110 :
                                           (C_S_AXI_DATA_WIDTH ==  256) ? 3'b101 :
                                           (C_S_AXI_DATA_WIDTH ==  128) ? 3'b100 :
                                           (C_S_AXI_DATA_WIDTH ==   64) ? 3'b011 :
                                           (C_S_AXI_DATA_WIDTH ==   32) ? 3'b010 :
                                           (C_S_AXI_DATA_WIDTH ==   16) ? 3'b001 :
                                           3'b000;
  
  // Decode the native transaction size on the MI-side interface.
  localparam [3-1:0] C_M_AXI_NATIVE_SIZE = (C_M_AXI_DATA_WIDTH == 1024) ? 3'b111 :
                                           (C_M_AXI_DATA_WIDTH ==  512) ? 3'b110 :
                                           (C_M_AXI_DATA_WIDTH ==  256) ? 3'b101 :
                                           (C_M_AXI_DATA_WIDTH ==  128) ? 3'b100 :
                                           (C_M_AXI_DATA_WIDTH ==   64) ? 3'b011 :
                                           (C_M_AXI_DATA_WIDTH ==   32) ? 3'b010 :
                                           (C_M_AXI_DATA_WIDTH ==   16) ? 3'b001 :
                                           3'b000;
  
  // Constants used to generate maximum length on SI-side for complete wrap.
  localparam [24-1:0] C_DOUBLE_LEN       = 24'b0000_0000_0000_0000_1111_1111;
  
  // Constants for burst types.
  localparam [2-1:0] C_FIX_BURST         = 2'b00;
  localparam [2-1:0] C_INCR_BURST        = 2'b01;
  localparam [2-1:0] C_WRAP_BURST        = 2'b10;
  
  // Constants for packing levels.
  localparam integer C_NEVER_PACK        = 0;
  localparam integer C_DEFAULT_PACK      = 1;
  localparam integer C_ALWAYS_PACK       = 2;
  
  // Depth for command FIFO.
  localparam integer C_FIFO_DEPTH_LOG    = 5;
  
  // Maximum address bit coverage by WRAP.
  localparam integer C_BURST_BYTES_LOG   = 4 + C_S_AXI_BYTES_LOG;
  
  // Calculate unused address bits.
  localparam integer C_SI_UNUSED_LOG     = C_AXI_ADDR_WIDTH-C_S_AXI_BYTES_LOG;
  localparam integer C_MI_UNUSED_LOG     = C_AXI_ADDR_WIDTH-C_M_AXI_BYTES_LOG;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Variables for generating parameter controlled instances.
  /////////////////////////////////////////////////////////////////////////////
  
  genvar bit_cnt;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Functions
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Internal signals
  /////////////////////////////////////////////////////////////////////////////
  
  // Access decoding related signals.
  wire                                access_is_fix;
  wire                                access_is_incr;
  wire                                access_is_wrap;
  wire                                access_is_modifiable;
  wire                                access_is_unaligned;
  reg  [8-1:0]                        si_maximum_length;
  wire [16-1:0]                       mi_word_intra_len_complete;
  wire [20-1:0]                       mask_help_vector;
  reg  [C_M_AXI_BYTES_LOG-1:0]        mi_word_intra_len;
  reg  [8-1:0]                        upsized_length;
  wire                                sub_sized_wrap;
  reg  [C_M_AXI_BYTES_LOG-1:0]        size_mask;
  reg  [C_BURST_BYTES_LOG-1:0]        burst_mask;
  
  // Translation related signals.
  wire                                access_need_extra_word;
  wire [8-1:0]                        adjusted_length;
  wire [C_BURST_BYTES_LOG-1:0]        wrap_addr_aligned;
  
  // Command buffer help signals.
  wire                                cmd_empty;
  wire                                s_ready;
  wire                                cmd_full;
  wire                                allow_new_cmd;
  wire                                cmd_push;
  reg                                 cmd_push_block = 1'b0;
  wire                                s_id_ready;
  
  // Internal Command Interface signals.
  wire                                cmd_valid_i;
  wire                                cmd_fix_i;
  wire                                cmd_modified_i;
  wire                                cmd_complete_wrap_i;
  wire                                cmd_packed_wrap_i;
  wire [C_M_AXI_BYTES_LOG-1:0]        cmd_first_word_ii;
  wire [C_M_AXI_BYTES_LOG-1:0]        cmd_first_word_i;
  wire [C_M_AXI_BYTES_LOG-1:0]        cmd_next_word_ii;
  wire [C_M_AXI_BYTES_LOG-1:0]        cmd_next_word_i;
  wire [C_M_AXI_BYTES_LOG:0]          cmd_last_word_ii;
  wire [C_M_AXI_BYTES_LOG-1:0]        cmd_last_word_i;
  wire [C_M_AXI_BYTES_LOG-1:0]        cmd_offset_i;
  reg  [C_M_AXI_BYTES_LOG-1:0]        cmd_mask_i;
  wire [3-1:0]                        cmd_size_i;
  wire [3-1:0]                        cmd_size;
  reg  [8-1:0]                        cmd_step_ii;
  wire [C_S_AXI_BYTES_LOG:0]          cmd_step_i;
  reg  [8-1:0]                        cmd_length_i;
  
  // Internal SI-side signals.
  wire                                S_AXI_AREADY_I;
   
  // Internal MI-side signals.
  reg  [C_AXI_ADDR_WIDTH-1:0]         M_AXI_AADDR_I;
  reg  [8-1:0]                        M_AXI_ALEN_I;
  reg  [3-1:0]                        M_AXI_ASIZE_I;
  reg  [2-1:0]                        M_AXI_ABURST_I;
  wire [2-1:0]                        M_AXI_ALOCK_I;
  wire [4-1:0]                        M_AXI_ACACHE_I;
  wire [3-1:0]                        M_AXI_APROT_I;
  wire [4-1:0]                        M_AXI_AREGION_I;
  wire [4-1:0]                        M_AXI_AQOS_I;
  wire                                M_AXI_AVALID_I;
  wire                                M_AXI_AREADY_I;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Decode the incoming transaction:
  //
  // Determine the burst type sucha as FIX, INCR and WRAP. Only WRAP and INCR 
  // transactions can be upsized to the MI-side data width.
  // Detect if the transaction is modifiable and if it is of native size. Only
  // native sized transaction are upsized when allowed, unless forced by 
  // parameter. FIX can never be upsized (packed) regardless if force is 
  // turned on. However the FIX data will be steered to the correct 
  // byte lane(s) and the transaction will be native on MI-side when 
  // applicable.
  //
  // Calculate the MI-side length for the SI-side transaction.
  // 
  // Decode the affected address bits in the MI-side. Used to determine last 
  // word for a burst and if necassarily adjust the length of the upsized 
  // transaction. Length adjustment only occurs when the trasaction is longer 
  // than can fit in MI-side and there is an unalignment for the first word
  // (and the last word crosses MI-word boundary and wraps).
  // 
  // The maximum allowed SI-side length is calculated to be able to determine 
  // if a WRAP transaction can fit inside a single MI-side data word.
  // 
  // Determine address bits mask for the SI-side transaction size, i.e. address
  // bits that shall be removed for unalignment when managing data in W and 
  // R channels. For example: the two least significant bits are not used 
  // for data packing in a 32-bit SI-side transaction (address 1-3 will appear
  // as 0 for the W and R channels, but the untouched address is still forwarded 
  // to the MI-side).
  // 
  // Determine the Mask bits for the address bits that are affected by a
  // sub-sized WRAP transaction (up to and including complete WRAP). The Mask 
  // is used to generate the correct data mapping for a sub-sized and
  // complete WRAP, i.e. having a local wrap in a partial MI-side word.
  // 
  // Detect any SI-side address unalignment when used on the MI-side.
  // 
  /////////////////////////////////////////////////////////////////////////////
  
  assign cmd_si_addr  = S_AXI_AADDR;
  assign cmd_si_id    = C_SUPPORTS_ID ? S_AXI_AID : 1'b0;
  assign cmd_si_len   = S_AXI_ALEN;
  assign cmd_si_size  = S_AXI_ASIZE;
  assign cmd_si_burst = S_AXI_ABURST;
  
  // Transaction burst type.
  assign access_is_fix          = ( S_AXI_ABURST == C_FIX_BURST );
  assign access_is_incr         = ( S_AXI_ABURST == C_INCR_BURST );
  assign access_is_wrap         = ( S_AXI_ABURST == C_WRAP_BURST );
  assign cmd_fix_i              = access_is_fix;
  
  // Get if it is allowed to modify transaction.
  assign access_is_modifiable   = S_AXI_ACACHE[1];
  
  // Get SI-side maximum length to fit MI-side.
  always @ *
  begin
    case (S_AXI_ASIZE)
      3'b000: si_maximum_length = C_S_AXI_NATIVE_SIZE >= 3'b000 ? C_DOUBLE_LEN[ 8-C_M_AXI_BYTES_LOG +: 8] : 8'b0;
      3'b001: si_maximum_length = C_S_AXI_NATIVE_SIZE >= 3'b001 ? C_DOUBLE_LEN[ 9-C_M_AXI_BYTES_LOG +: 8] : 8'b0;
      3'b010: si_maximum_length = C_S_AXI_NATIVE_SIZE >= 3'b010 ? C_DOUBLE_LEN[10-C_M_AXI_BYTES_LOG +: 8] : 8'b0;
      3'b011: si_maximum_length = C_S_AXI_NATIVE_SIZE >= 3'b011 ? C_DOUBLE_LEN[11-C_M_AXI_BYTES_LOG +: 8] : 8'b0;
      3'b100: si_maximum_length = C_S_AXI_NATIVE_SIZE >= 3'b100 ? C_DOUBLE_LEN[12-C_M_AXI_BYTES_LOG +: 8] : 8'b0;
      3'b101: si_maximum_length = C_S_AXI_NATIVE_SIZE >= 3'b101 ? C_DOUBLE_LEN[13-C_M_AXI_BYTES_LOG +: 8] : 8'b0;
      3'b110: si_maximum_length = C_S_AXI_NATIVE_SIZE >= 3'b110 ? C_DOUBLE_LEN[14-C_M_AXI_BYTES_LOG +: 8] : 8'b0;
      3'b111: si_maximum_length = C_S_AXI_NATIVE_SIZE >= 3'b111 ? C_DOUBLE_LEN[15-C_M_AXI_BYTES_LOG +: 8] : 8'b0;
    endcase
  end
  
  // Help vector to determine the length of thransaction in the MI-side domain.
  assign mi_word_intra_len_complete = {S_AXI_ALEN, 8'b0};
  
  // Get intra MI-side word length bits (in bytes).
  always @ *
  begin
      if ( ~cmd_fix_i ) begin
        case (S_AXI_ASIZE)
          3'b000: mi_word_intra_len = C_S_AXI_NATIVE_SIZE >= 3'b000 ? 
                                      mi_word_intra_len_complete[8-0 +: C_M_AXI_BYTES_LOG] : {C_M_AXI_BYTES_LOG{1'b0}};
          3'b001: mi_word_intra_len = C_S_AXI_NATIVE_SIZE >= 3'b001 ? 
                                      mi_word_intra_len_complete[8-1 +: C_M_AXI_BYTES_LOG] : {C_M_AXI_BYTES_LOG{1'b0}};
          3'b010: mi_word_intra_len = C_S_AXI_NATIVE_SIZE >= 3'b010 ? 
                                      mi_word_intra_len_complete[8-2 +: C_M_AXI_BYTES_LOG] : {C_M_AXI_BYTES_LOG{1'b0}};
          3'b011: mi_word_intra_len = C_S_AXI_NATIVE_SIZE >= 3'b011 ? 
                                      mi_word_intra_len_complete[8-3 +: C_M_AXI_BYTES_LOG] : {C_M_AXI_BYTES_LOG{1'b0}};
          3'b100: mi_word_intra_len = C_S_AXI_NATIVE_SIZE >= 3'b100 ? 
                                      mi_word_intra_len_complete[8-4 +: C_M_AXI_BYTES_LOG] : {C_M_AXI_BYTES_LOG{1'b0}};
          3'b101: mi_word_intra_len = C_S_AXI_NATIVE_SIZE >= 3'b101 ? 
                                      mi_word_intra_len_complete[8-5 +: C_M_AXI_BYTES_LOG] : {C_M_AXI_BYTES_LOG{1'b0}};
          3'b110: mi_word_intra_len = C_S_AXI_NATIVE_SIZE >= 3'b110 ? 
                                      mi_word_intra_len_complete[8-6 +: C_M_AXI_BYTES_LOG] : {C_M_AXI_BYTES_LOG{1'b0}};
          3'b111: mi_word_intra_len = C_S_AXI_NATIVE_SIZE >= 3'b111 ? 
                                      mi_word_intra_len_complete[8-7 +: C_M_AXI_BYTES_LOG] : {C_M_AXI_BYTES_LOG{1'b0}};  // Illegal setting.
        endcase
      end else begin
        mi_word_intra_len = {C_M_AXI_BYTES_LOG{1'b0}};
      end
  end
  
  // Get MI-side length after upsizing.
  always @ *
  begin
      if ( cmd_fix_i | ~cmd_modified_i ) begin
        // Fix has to maintain length even if forced packing.
        upsized_length = S_AXI_ALEN;
      end else begin
        case (S_AXI_ASIZE)
          3'b000: upsized_length = C_S_AXI_NATIVE_SIZE >= 3'b000 ? 
                                   (S_AXI_ALEN >> C_M_AXI_BYTES_LOG-0) : 8'b0;
          3'b001: upsized_length = C_S_AXI_NATIVE_SIZE >= 3'b001 ? 
                                   (S_AXI_ALEN >> C_M_AXI_BYTES_LOG-1) : 8'b0;
          3'b010: upsized_length = C_S_AXI_NATIVE_SIZE >= 3'b010 ? 
                                   (S_AXI_ALEN >> C_M_AXI_BYTES_LOG-2) : 8'b0;
          3'b011: upsized_length = C_S_AXI_NATIVE_SIZE >= 3'b011 ? 
                                   (S_AXI_ALEN >> C_M_AXI_BYTES_LOG-3) : 8'b0;
          3'b100: upsized_length = C_S_AXI_NATIVE_SIZE >= 3'b100 ? 
                                   (S_AXI_ALEN >> C_M_AXI_BYTES_LOG-4) : 8'b0;
          3'b101: upsized_length = C_S_AXI_NATIVE_SIZE >= 3'b101 ? 
                                   (S_AXI_ALEN >> C_M_AXI_BYTES_LOG-5) : 8'b0;
          3'b110: upsized_length = C_S_AXI_NATIVE_SIZE >= 3'b110 ? 
                                   (S_AXI_ALEN >> C_M_AXI_BYTES_LOG-6) : 8'b0;
          3'b111: upsized_length = C_S_AXI_NATIVE_SIZE >= 3'b111 ? 
                                   (S_AXI_ALEN                       ) : 8'b0;  // Illegal setting.
        endcase
      end
  end
  
  // Generate address bits used for SI-side transaction size.
  always @ *
  begin
    case (S_AXI_ASIZE)
      3'b000: size_mask = ~C_DOUBLE_LEN[8 +: C_S_AXI_BYTES_LOG];
      3'b001: size_mask = ~C_DOUBLE_LEN[7 +: C_S_AXI_BYTES_LOG];
      3'b010: size_mask = ~C_DOUBLE_LEN[6 +: C_S_AXI_BYTES_LOG];
      3'b011: size_mask = ~C_DOUBLE_LEN[5 +: C_S_AXI_BYTES_LOG];
      3'b100: size_mask = ~C_DOUBLE_LEN[4 +: C_S_AXI_BYTES_LOG];
      3'b101: size_mask = ~C_DOUBLE_LEN[3 +: C_S_AXI_BYTES_LOG];
      3'b110: size_mask = ~C_DOUBLE_LEN[2 +: C_S_AXI_BYTES_LOG];
      3'b111: size_mask = ~C_DOUBLE_LEN[1 +: C_S_AXI_BYTES_LOG];  // Illegal setting.
    endcase
  end
  
  // Help vector to determine the length of thransaction in the MI-side domain.
  assign mask_help_vector = {4'b0, S_AXI_ALEN, 8'b1};
  
  // Calculate the address bits that are affected when a complete wrap is detected.
  always @ *
  begin
    if ( sub_sized_wrap ) begin
      case (S_AXI_ASIZE)
        3'b000: cmd_mask_i = C_S_AXI_NATIVE_SIZE >= 3'b000 ? 
                             mask_help_vector[8-0 +: C_M_AXI_BYTES_LOG] : {C_M_AXI_BYTES_LOG{1'b0}};
        3'b001: cmd_mask_i = C_S_AXI_NATIVE_SIZE >= 3'b000 ? 
                             mask_help_vector[8-1 +: C_M_AXI_BYTES_LOG] : {C_M_AXI_BYTES_LOG{1'b0}};
        3'b010: cmd_mask_i = C_S_AXI_NATIVE_SIZE >= 3'b000 ? 
                             mask_help_vector[8-2 +: C_M_AXI_BYTES_LOG] : {C_M_AXI_BYTES_LOG{1'b0}};
        3'b011: cmd_mask_i = C_S_AXI_NATIVE_SIZE >= 3'b000 ? 
                             mask_help_vector[8-3 +: C_M_AXI_BYTES_LOG] : {C_M_AXI_BYTES_LOG{1'b0}};
        3'b100: cmd_mask_i = C_S_AXI_NATIVE_SIZE >= 3'b000 ? 
                             mask_help_vector[8-4 +: C_M_AXI_BYTES_LOG] : {C_M_AXI_BYTES_LOG{1'b0}};
        3'b101: cmd_mask_i = C_S_AXI_NATIVE_SIZE >= 3'b000 ? 
                             mask_help_vector[8-5 +: C_M_AXI_BYTES_LOG] : {C_M_AXI_BYTES_LOG{1'b0}};
        3'b110: cmd_mask_i = C_S_AXI_NATIVE_SIZE >= 3'b000 ? 
                             mask_help_vector[8-6 +: C_M_AXI_BYTES_LOG] : {C_M_AXI_BYTES_LOG{1'b0}};
        3'b111: cmd_mask_i = C_S_AXI_NATIVE_SIZE >= 3'b000 ? 
                             mask_help_vector[8-7 +: C_M_AXI_BYTES_LOG] : {C_M_AXI_BYTES_LOG{1'b0}};  // Illegal setting.
      endcase
    end else begin
      cmd_mask_i = {C_M_AXI_BYTES_LOG{1'b1}};
    end
  end

  // Calculate the address bits that are affected when a complete wrap is detected.
  always @ *
  begin
    case (S_AXI_ASIZE)
      3'b000: burst_mask = C_S_AXI_NATIVE_SIZE >= 3'b000 ? 
                           mask_help_vector[8-0 +: C_BURST_BYTES_LOG] : {C_BURST_BYTES_LOG{1'b0}};
      3'b001: burst_mask = C_S_AXI_NATIVE_SIZE >= 3'b000 ? 
                           mask_help_vector[8-1 +: C_BURST_BYTES_LOG] : {C_BURST_BYTES_LOG{1'b0}};
      3'b010: burst_mask = C_S_AXI_NATIVE_SIZE >= 3'b000 ? 
                           mask_help_vector[8-2 +: C_BURST_BYTES_LOG] : {C_BURST_BYTES_LOG{1'b0}};
      3'b011: burst_mask = C_S_AXI_NATIVE_SIZE >= 3'b000 ? 
                           mask_help_vector[8-3 +: C_BURST_BYTES_LOG] : {C_BURST_BYTES_LOG{1'b0}};
      3'b100: burst_mask = C_S_AXI_NATIVE_SIZE >= 3'b000 ? 
                           mask_help_vector[8-4 +: C_BURST_BYTES_LOG] : {C_BURST_BYTES_LOG{1'b0}};
      3'b101: burst_mask = C_S_AXI_NATIVE_SIZE >= 3'b000 ? 
                           mask_help_vector[8-5 +: C_BURST_BYTES_LOG] : {C_BURST_BYTES_LOG{1'b0}};
      3'b110: burst_mask = C_S_AXI_NATIVE_SIZE >= 3'b000 ? 
                           mask_help_vector[8-6 +: C_BURST_BYTES_LOG] : {C_BURST_BYTES_LOG{1'b0}};
      3'b111: burst_mask = C_S_AXI_NATIVE_SIZE >= 3'b000 ? 
                           mask_help_vector[8-7 +: C_BURST_BYTES_LOG] : {C_BURST_BYTES_LOG{1'b0}};  // Illegal setting.
    endcase
  end

  // Propagate the SI-side size of the transaction.
  assign cmd_size_i = S_AXI_ASIZE;
  
  // Detect if there is any unalignment in regards to the MI-side.
  assign access_is_unaligned = ( S_AXI_AADDR[0 +: C_M_AXI_BYTES_LOG] != {C_M_AXI_BYTES_LOG{1'b0}} );
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Evaluate if transaction is to be translated:
  // * Forcefully translate when C_PACKING_LEVEL is set to C_ALWAYS_PACK. 
  // * When SI-side transaction size is native, it is allowed and default 
  //   packing is set. (Expander mode never packs).
  //
  /////////////////////////////////////////////////////////////////////////////
  
  // Modify transaction forcefully or when transaction allows it
  assign cmd_modified_i = ~access_is_fix &
                          ( ( C_PACKING_LEVEL == C_ALWAYS_PACK  ) | 
                            ( access_is_modifiable & ( S_AXI_ALEN != 8'b0 ) & ( C_PACKING_LEVEL == C_DEFAULT_PACK ) ) );
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Translate SI-side access to MI-side:
  //
  // Detemine if this is a complete WRAP. Conditions are that it must fit 
  // inside a single MI-side data word, it must be a WRAP access and that
  // bursts are allowed. Without burst there can never be a WRAP access.
  //
  // Determine if this ia a packed WRAP, i.e. a WRAP that is to large to 
  // be a complete wrap and it is unaligned SI-side address relative to 
  // the native MI-side data width.
  //
  // The address for the First SI-side data word is adjusted to when there 
  // is a complete WRAP, otherwise it only the least significant bits of the 
  // SI-side address.
  // For complete WRAP access the Offset is generated as the most significant 
  // bits that are left by the Mask.
  // Last address is calculated with the adjusted First word address.
  //
  // The Adjusted MI-side burst length is calculated as the Upsized length
  // plus one when the SI-side data must wrap on the MI-side (unless it is
  // a complete or packed WRAP).
  // 
  // Depending on the conditions some of the forwarded MI-side tranaction 
  // and Command Queue parameters has to be adjusted:
  // * For unmodified transaction the parameter are left un affected.
  //   (M_AXI_AADDR, M_AXI_ASIZE, M_AXI_ABURST, M_AXI_ALEN and cmd_length 
  //    are untouched)
  // * For complete WRAP transactions the burst type is changed to INCR
  //   and the address is adjusted to the sub-size affected by the transaction
  //   (the sub-size can be 2 bytes up to a full MI-side data word).
  //   The size is set to the native MI-side transaction size. And the length
  //   is set to the calculated upsized length.
  // * For all other modified transations the address and burst type remains 
  //   the same. The length is adjusted to the previosly described length
  //   and size is set to native MI-side transaction size.
  //
  /////////////////////////////////////////////////////////////////////////////
  
  // Detemine if this is a sub-sized transaction.
  assign sub_sized_wrap         = access_is_wrap & ( S_AXI_ALEN <= si_maximum_length );
  
  // See if entite burst can fit inside one MI-side word.
  assign cmd_complete_wrap_i    = cmd_modified_i & sub_sized_wrap;
  
  // Detect if this is a packed WRAP (multiple MI-side words).
  assign cmd_packed_wrap_i      = cmd_modified_i & access_is_wrap & ( S_AXI_ALEN > si_maximum_length ) & 
                                  access_is_unaligned;
  
  // Get unalignment address bits (including aligning it inside covered area).
  assign cmd_first_word_ii      = S_AXI_AADDR[C_M_AXI_BYTES_LOG-1:0];
  assign cmd_first_word_i       = cmd_first_word_ii & cmd_mask_i & size_mask;
  
  // Generate next word address.
  assign cmd_next_word_ii       = cmd_first_word_ii + cmd_step_ii[C_M_AXI_BYTES_LOG-1:0];
  assign cmd_next_word_i        = cmd_next_word_ii & cmd_mask_i & size_mask;
  
  // Offset is the bits that is outside of the Mask.
  assign cmd_offset_i           = cmd_first_word_ii & ~cmd_mask_i;
  
  // Select RTL or Optimized implementation.
  generate
    if ( C_FAMILY == "rtl" ) begin : USE_RTL_ADJUSTED_LEN
      // Calculate Last word on MI-side.
      assign cmd_last_word_ii       = cmd_first_word_i + mi_word_intra_len;
      assign cmd_last_word_i        = cmd_last_word_ii[C_M_AXI_BYTES_LOG-1:0] & cmd_mask_i & size_mask;
      
      // Detect if extra word on MI-side is needed.
      assign access_need_extra_word = cmd_last_word_ii[C_M_AXI_BYTES_LOG] & 
                                      access_is_incr & cmd_modified_i;
      
      // Calculate true length of modified transaction.
      assign adjusted_length        = upsized_length + access_need_extra_word;
          
    end else begin : USE_FPGA_ADJUSTED_LEN
      
      wire [C_M_AXI_BYTES_LOG:0]          last_word_local_carry;
      wire [C_M_AXI_BYTES_LOG-1:0]        last_word_sel;
      wire [C_M_AXI_BYTES_LOG:0]          last_word_for_mask_local_carry;
      wire [C_M_AXI_BYTES_LOG-1:0]        last_word_for_mask_dummy_carry1;
      wire [C_M_AXI_BYTES_LOG-1:0]        last_word_for_mask_dummy_carry2;
      wire [C_M_AXI_BYTES_LOG-1:0]        last_word_for_mask_dummy_carry3;
      wire [C_M_AXI_BYTES_LOG-1:0]        last_word_for_mask_sel;
      wire [C_M_AXI_BYTES_LOG-1:0]        last_word_for_mask;
      wire [C_M_AXI_BYTES_LOG-1:0]        last_word_mask;
      wire                                sel_access_need_extra_word;
      wire [8:0]                          adjusted_length_local_carry;
      wire [8-1:0]                        adjusted_length_sel;
    
      
      assign last_word_local_carry[0] = 1'b0;
      assign last_word_for_mask_local_carry[0] = 1'b0;
      
      for (bit_cnt = 0; bit_cnt < C_M_AXI_BYTES_LOG ; bit_cnt = bit_cnt + 1) begin : LUT_LAST_MASK
        
        assign last_word_for_mask_sel[bit_cnt]  = cmd_first_word_ii[bit_cnt] ^ mi_word_intra_len[bit_cnt];
        assign last_word_mask[bit_cnt]          = cmd_mask_i[bit_cnt] & size_mask[bit_cnt];
        
        MUXCY and_inst1 
        (
         .O (last_word_for_mask_dummy_carry1[bit_cnt]), 
         .CI (last_word_for_mask_local_carry[bit_cnt]), 
         .DI (mi_word_intra_len[bit_cnt]), 
         .S (last_word_for_mask_sel[bit_cnt])
        ); 
        
        MUXCY and_inst2 
        (
         .O (last_word_for_mask_dummy_carry2[bit_cnt]), 
         .CI (last_word_for_mask_dummy_carry1[bit_cnt]), 
         .DI (1'b0), 
         .S (1'b1)
        ); 
        
        MUXCY and_inst3 
        (
         .O (last_word_for_mask_dummy_carry3[bit_cnt]), 
         .CI (last_word_for_mask_dummy_carry2[bit_cnt]), 
         .DI (1'b0), 
         .S (1'b1)
        ); 
        
        MUXCY and_inst4 
        (
         .O (last_word_for_mask_local_carry[bit_cnt+1]), 
         .CI (last_word_for_mask_dummy_carry3[bit_cnt]), 
         .DI (1'b0), 
         .S (1'b1)
        ); 
        
        XORCY xorcy_inst 
        (
         .O(last_word_for_mask[bit_cnt]),
         .CI(last_word_for_mask_local_carry[bit_cnt]),
         .LI(last_word_for_mask_sel[bit_cnt])
        );
        
        generic_baseblocks_v2_1_0_carry_latch_and #
          (
           .C_FAMILY(C_FAMILY)
           ) last_mask_inst
          (
           .CIN(last_word_for_mask[bit_cnt]),
           .I(last_word_mask[bit_cnt]),
           .O(cmd_last_word_i[bit_cnt])
           );
           
      end // end for bit_cnt
      
      for (bit_cnt = 0; bit_cnt < C_M_AXI_BYTES_LOG ; bit_cnt = bit_cnt + 1) begin : LUT_LAST
        
        assign last_word_sel[bit_cnt] = cmd_first_word_ii[bit_cnt] ^ mi_word_intra_len[bit_cnt];
        
        MUXCY and_inst 
        (
         .O (last_word_local_carry[bit_cnt+1]), 
         .CI (last_word_local_carry[bit_cnt]), 
         .DI (mi_word_intra_len[bit_cnt]), 
         .S (last_word_sel[bit_cnt])
        ); 
        
        XORCY xorcy_inst 
        (
         .O(cmd_last_word_ii[bit_cnt]),
         .CI(last_word_local_carry[bit_cnt]),
         .LI(last_word_sel[bit_cnt])
        );
        
      end // end for bit_cnt
      
      assign sel_access_need_extra_word = access_is_incr & cmd_modified_i;
      
      generic_baseblocks_v2_1_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) access_need_extra_word_inst
        (
         .CIN(last_word_local_carry[C_M_AXI_BYTES_LOG]),
         .S(sel_access_need_extra_word),
         .COUT(adjusted_length_local_carry[0])
         );
         
      for (bit_cnt = 0; bit_cnt < 8 ; bit_cnt = bit_cnt + 1) begin : LUT_ADJUST
        
        assign adjusted_length_sel[bit_cnt] = ( upsized_length[bit_cnt] &  cmd_modified_i) |
                                              ( S_AXI_ALEN[bit_cnt]     & ~cmd_modified_i);
        
        MUXCY and_inst 
        (
         .O (adjusted_length_local_carry[bit_cnt+1]), 
         .CI (adjusted_length_local_carry[bit_cnt]), 
         .DI (1'b0), 
         .S (adjusted_length_sel[bit_cnt])
        ); 
        
        XORCY xorcy_inst 
        (
         .O(adjusted_length[bit_cnt]),
         .CI(adjusted_length_local_carry[bit_cnt]),
         .LI(adjusted_length_sel[bit_cnt])
        );
        
      end // end for bit_cnt
      
    end
  endgenerate
  
  // Generate adjusted wrap address.
  assign wrap_addr_aligned      = ( C_AXI_CHANNEL != 0 ) ? 
                                  ( S_AXI_AADDR[0 +: C_BURST_BYTES_LOG] ) :
                                  ( S_AXI_AADDR[0 +: C_BURST_BYTES_LOG] + ( 2 ** C_M_AXI_BYTES_LOG ) );
  
  // Select directly forwarded or modified transaction.
  always @ *
  begin
    if ( cmd_modified_i ) begin
      // SI to MI-side transaction translation.
      if ( cmd_complete_wrap_i ) begin
        // Complete wrap is turned into incr
        M_AXI_AADDR_I  = S_AXI_AADDR & {{C_MI_UNUSED_LOG{1'b1}}, ~cmd_mask_i};
        M_AXI_ABURST_I = C_INCR_BURST;
        
      end else begin
        // Retain the currenent 
        if ( cmd_packed_wrap_i ) begin
            M_AXI_AADDR_I  = {S_AXI_AADDR[C_BURST_BYTES_LOG +: C_AXI_ADDR_WIDTH-C_BURST_BYTES_LOG], 
                              (S_AXI_AADDR[0 +: C_BURST_BYTES_LOG] & ~burst_mask) | (wrap_addr_aligned & burst_mask) } & 
                             {{C_MI_UNUSED_LOG{1'b1}}, ~cmd_mask_i};
        end else begin
          M_AXI_AADDR_I  = S_AXI_AADDR;
        end
        M_AXI_ABURST_I = S_AXI_ABURST;
        
      end
      
      M_AXI_ASIZE_I  = C_M_AXI_NATIVE_SIZE;
    end else begin
      // SI to MI-side transaction forwarding.
      M_AXI_AADDR_I  = S_AXI_AADDR;
      M_AXI_ASIZE_I  = S_AXI_ASIZE;
      M_AXI_ABURST_I = S_AXI_ABURST;
    end
    
    M_AXI_ALEN_I   = adjusted_length;
    cmd_length_i   = adjusted_length;
  end
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Forward the command to the MI-side interface.
  //
  // It is determined that this is an allowed command/access when there is 
  // room in the command queue (and it passes any ID checks as required).
  //
  /////////////////////////////////////////////////////////////////////////////
  
  // Select RTL or Optimized implementation.
  generate
    if ( C_FAMILY == "rtl" || ( C_SUPPORTS_ID == 0 ) ) begin : USE_RTL_AVALID
      // Only allowed to forward translated command when command queue is ok with it.
      assign M_AXI_AVALID_I = allow_new_cmd & S_AXI_AVALID;
      
    end else begin : USE_FPGA_AVALID
      
      wire sel_s_axi_avalid;
      
      assign sel_s_axi_avalid = S_AXI_AVALID & ~ARESET;
      
      generic_baseblocks_v2_1_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) avalid_inst
        (
         .CIN(allow_new_cmd),
         .S(sel_s_axi_avalid),
         .COUT(M_AXI_AVALID_I)
         );
      
    end
  endgenerate
                          
  
  /////////////////////////////////////////////////////////////////////////////
  // Simple transfer of paramters that doesn't need to be adjusted.
  //
  // ID     - Transaction still recognized with the same ID.
  // LOCK   - No need to change exclusive or barrier transactions.
  // CACHE  - No need to change the chache features. Even if the modyfiable
  //          bit is overridden (forcefully) there is no need to let downstream
  //          component beleive it is ok to modify it further.
  // PROT   - Security level of access is not changed when upsizing.
  // REGION - Address region stays the same.
  // QOS    - Quality of Service remains the same.
  // USER   - User bits remains the same.
  // 
  /////////////////////////////////////////////////////////////////////////////
  
  assign M_AXI_ALOCK_I    = S_AXI_ALOCK;
  assign M_AXI_ACACHE_I   = S_AXI_ACACHE;
  assign M_AXI_APROT_I    = S_AXI_APROT;
  assign M_AXI_AREGION_I  = S_AXI_AREGION;
  assign M_AXI_AQOS_I     = S_AXI_AQOS;
  
  /////////////////////////////////////////////////////////////////////////////
  // Command queue to W/R channel.
  // 
  // Commands can be pushed into the Cmd FIFO even if MI-side is stalling.
  // A flag is set if MI-side is stalling when Command is pushed to the 
  // Cmd FIFO. This will prevent multiple push of the same Command as well as
  // keeping the MI-side Valid signal if the Allow Cmd requirement has been 
  // updated to disable furter Commands (I.e. it is made sure that the SI-side 
  // Command has been forwarded to both Cmd FIFO and MI-side).
  // 
  // It is allowed to continue pushing new commands as long as
  // * There is room in the queue
  // * The ID is the same as previously queued. Since data is not reordered
  //   for the same ID it is ok to let them proceed.
  //
  /////////////////////////////////////////////////////////////////////////////
  
  generate
    if ( C_ID_QUEUE != 0 ) begin : gen_id_queue
      generic_baseblocks_v2_1_0_command_fifo #
      (
       .C_FAMILY                    ("rtl"),
       .C_ENABLE_S_VALID_CARRY      (0),
       .C_ENABLE_REGISTERED_OUTPUT  (1),
       .C_FIFO_DEPTH_LOG            (C_FIFO_DEPTH_LOG),
       .C_FIFO_WIDTH                (C_AXI_ID_WIDTH)
       ) 
       id_queue
      (
       .ACLK    (ACLK),
       .ARESET  (ARESET),
       .EMPTY   (),
       .S_MESG  (S_AXI_AID),
       .S_VALID (cmd_push),
       .S_READY (s_id_ready),
       .M_MESG  (cmd_id),
       .M_VALID (),
       .M_READY (cmd_id_ready)
       );

    end else begin : gen_no_id_queue
  
      assign cmd_id = 1'b0;
      assign s_id_ready = 1'b1;
      
    end
  endgenerate
      
      // Check if it is allowed to push more commands (ID is allowed and there is room in the queue).
      assign allow_new_cmd  = (~cmd_full & s_id_ready) | cmd_push_block;
      
      // Push new command when allowed and MI-side is able to receive the command.
      assign cmd_push       = M_AXI_AVALID_I & ~cmd_push_block;
      
  // Block further push until command has been forwarded to MI-side.
  always @ (posedge ACLK) begin
    if (ARESET) begin
      cmd_push_block <= 1'b0;
    end else begin
      cmd_push_block <= M_AXI_AVALID_I & ~M_AXI_AREADY_I;
    end
  end
  
  // Acknowledge command when we can push it into queue (and forward it).
  assign S_AXI_AREADY_I = M_AXI_AREADY_I & allow_new_cmd & ~ARESET;
  assign S_AXI_AREADY   = S_AXI_AREADY_I;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Command Queue:
  // 
  // Instantiate a FIFO as the queue and adjust the control signals.
  //
  // Decode size to step before passing it along.
  //
  // When there is no need for bursts the command FIFO can be greatly reduced 
  // becase the following is always true:
  // * first = last
  // * length = 0
  // * nothing can be packed (i.e. no WRAP at all)
  //   * never any sub-size wraping => static offset (0) and mask (1)
  // 
  /////////////////////////////////////////////////////////////////////////////
  
  // Translate SI-side size to step for upsizer function.
  always @ *
  begin
    case (cmd_size_i)
      3'b000: cmd_step_ii = 8'b00000001;
      3'b001: cmd_step_ii = 8'b00000010;
      3'b010: cmd_step_ii = 8'b00000100;
      3'b011: cmd_step_ii = 8'b00001000;
      3'b100: cmd_step_ii = 8'b00010000;
      3'b101: cmd_step_ii = 8'b00100000;
      3'b110: cmd_step_ii = 8'b01000000;
      3'b111: cmd_step_ii = 8'b10000000; // Illegal setting.
    endcase
  end
  
  // Get only the applicable bits in step.
  assign cmd_step_i = cmd_step_ii[C_S_AXI_BYTES_LOG:0];
  
  generate
  if (C_FIFO_MODE == 0) begin : GEN_CMD_QUEUE
  // Instantiated queue.
      generic_baseblocks_v2_1_0_command_fifo #
      (
       .C_FAMILY                    ("rtl"),
       .C_ENABLE_S_VALID_CARRY      (1),
       .C_ENABLE_REGISTERED_OUTPUT  (1),
       .C_FIFO_DEPTH_LOG            (C_FIFO_DEPTH_LOG),
       .C_FIFO_WIDTH                (1+1+1+1+C_M_AXI_BYTES_LOG+C_M_AXI_BYTES_LOG+
                                     C_M_AXI_BYTES_LOG+C_M_AXI_BYTES_LOG+C_M_AXI_BYTES_LOG+C_S_AXI_BYTES_LOG+1+8)
       ) 
       cmd_queue
      (
       .ACLK    (ACLK),
       .ARESET  (ARESET),
       .EMPTY   (cmd_empty),
       .S_MESG  ({cmd_fix_i, cmd_modified_i, cmd_complete_wrap_i, cmd_packed_wrap_i, cmd_first_word_i, cmd_next_word_i, 
                  cmd_last_word_i, cmd_offset_i, cmd_mask_i, cmd_step_i, cmd_length_i}),
       .S_VALID (cmd_push),
       .S_READY (s_ready),
       .M_MESG  ({cmd_fix, cmd_modified, cmd_complete_wrap, cmd_packed_wrap, cmd_first_word, cmd_next_word, 
                  cmd_last_word, cmd_offset, cmd_mask, cmd_step, cmd_length}),
       .M_VALID (cmd_valid_i),
       .M_READY (cmd_ready)
       );

    // Queue is concidered full when not ready.
    assign cmd_full = ~s_ready;
    
    // Assign external signal.
    assign cmd_valid = cmd_valid_i;
    
  end else begin : NO_CMD_QUEUE
    reg [C_FIFO_DEPTH_LOG-1:0] cmd_cnt = {C_FIFO_DEPTH_LOG{1'b0}};
    
    always @ (posedge ACLK) begin
      if (ARESET) begin
        cmd_cnt <= 0;
      end else begin
        if (cmd_push & ~cmd_ready) begin
          cmd_cnt <= cmd_cnt + 1;
        end else if (~cmd_push & cmd_ready & |cmd_cnt) begin
          cmd_cnt <= cmd_cnt - 1;
        end
      end
    end

    assign cmd_full = &cmd_cnt;
    assign cmd_empty = cmd_cnt == 0;
    assign cmd_fix           = 1'b0 ;
    assign cmd_modified      = 1'b0 ;
    assign cmd_complete_wrap = 1'b0 ;
    assign cmd_packed_wrap   = 1'b0 ;
    assign cmd_first_word    = 0 ;
    assign cmd_next_word     = 0 ;
    assign cmd_last_word     = 0 ;
    assign cmd_offset        = 0 ;
    assign cmd_mask          = 0 ;
    assign cmd_step          = 0 ;
    assign cmd_length        = 0 ;
    assign cmd_valid = 1'b0;
    
  end
  endgenerate
  
  
  
  /////////////////////////////////////////////////////////////////////////////
  // MI-side output handling
  /////////////////////////////////////////////////////////////////////////////
  
  generate
    if ( C_M_AXI_REGISTER ) begin : USE_REGISTER
    
      reg  [C_AXI_ADDR_WIDTH-1:0]         M_AXI_AADDR_q;
      reg  [8-1:0]                        M_AXI_ALEN_q;
      reg  [3-1:0]                        M_AXI_ASIZE_q;
      reg  [2-1:0]                        M_AXI_ABURST_q;
      reg  [2-1:0]                        M_AXI_ALOCK_q;
      reg  [4-1:0]                        M_AXI_ACACHE_q;
      reg  [3-1:0]                        M_AXI_APROT_q;
      reg  [4-1:0]                        M_AXI_AREGION_q;
      reg  [4-1:0]                        M_AXI_AQOS_q;
      reg                                 M_AXI_AVALID_q = 1'b0;
    
      // Register MI-side Data.
      always @ (posedge ACLK) begin
        if (ARESET) begin
          M_AXI_AVALID_q    <= 1'b0;
        end else if ( M_AXI_AREADY_I ) begin
          M_AXI_AVALID_q    <= M_AXI_AVALID_I;
        end

        if ( M_AXI_AREADY_I ) begin
          M_AXI_AADDR_q     <= M_AXI_AADDR_I;
          M_AXI_ALEN_q      <= M_AXI_ALEN_I;
          M_AXI_ASIZE_q     <= M_AXI_ASIZE_I;
          M_AXI_ABURST_q    <= M_AXI_ABURST_I;
          M_AXI_ALOCK_q     <= M_AXI_ALOCK_I;
          M_AXI_ACACHE_q    <= M_AXI_ACACHE_I;
          M_AXI_APROT_q     <= M_AXI_APROT_I;
          M_AXI_AREGION_q   <= M_AXI_AREGION_I;
          M_AXI_AQOS_q      <= M_AXI_AQOS_I;
        end
      end
      
      assign M_AXI_AADDR      = M_AXI_AADDR_q;
      assign M_AXI_ALEN       = M_AXI_ALEN_q;
      assign M_AXI_ASIZE      = M_AXI_ASIZE_q;
      assign M_AXI_ABURST     = M_AXI_ABURST_q;
      assign M_AXI_ALOCK      = M_AXI_ALOCK_q;
      assign M_AXI_ACACHE     = M_AXI_ACACHE_q;
      assign M_AXI_APROT      = M_AXI_APROT_q;
      assign M_AXI_AREGION    = M_AXI_AREGION_q;
      assign M_AXI_AQOS       = M_AXI_AQOS_q;
      assign M_AXI_AVALID     = M_AXI_AVALID_q;
      assign M_AXI_AREADY_I = ( M_AXI_AVALID_q & M_AXI_AREADY) | ~M_AXI_AVALID_q;
      
    end else begin : NO_REGISTER
    
      // Combinatorial MI-side Data.
      assign M_AXI_AADDR    = M_AXI_AADDR_I;
      assign M_AXI_ALEN     = M_AXI_ALEN_I;
      assign M_AXI_ASIZE    = M_AXI_ASIZE_I;
      assign M_AXI_ABURST   = M_AXI_ABURST_I;
      assign M_AXI_ALOCK    = M_AXI_ALOCK_I;
      assign M_AXI_ACACHE   = M_AXI_ACACHE_I;
      assign M_AXI_APROT    = M_AXI_APROT_I;
      assign M_AXI_AREGION  = M_AXI_AREGION_I;
      assign M_AXI_AQOS     = M_AXI_AQOS_I;
      assign M_AXI_AVALID   = M_AXI_AVALID_I;
      assign M_AXI_AREADY_I = M_AXI_AREADY;
                          
    end
  endgenerate
  
endmodule



// -- (c) Copyright 2010 - 2012 Xilinx, Inc. All rights reserved.
// --
// -- This file contains confidential and proprietary information
// -- of Xilinx, Inc. and is protected under U.S. and 
// -- international copyright and other intellectual property
// -- laws.
// --
// -- DISCLAIMER
// -- This disclaimer is not a license and does not grant any
// -- rights to the materials distributed herewith. Except as
// -- otherwise provided in a valid license issued to you by
// -- Xilinx, and to the maximum extent permitted by applicable
// -- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// -- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// -- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// -- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// -- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// -- (2) Xilinx shall not be liable (whether in contract or tort,
// -- including negligence, or under any other theory of
// -- liability) for any loss or damage of any kind or nature
// -- related to, arising under or in connection with these
// -- materials, including for any direct, or any indirect,
// -- special, incidental, or consequential loss or damage
// -- (including loss of data, profits, goodwill, or any type of
// -- loss or damage suffered as a result of any action brought
// -- by a third party) even if such damage or loss was
// -- reasonably foreseeable or Xilinx had been advised of the
// -- possibility of the same.
// --
// -- CRITICAL APPLICATIONS
// -- Xilinx products are not designed or intended to be fail-
// -- safe, or for use in any application requiring fail-safe
// -- performance, such as life-support or safety devices or
// -- systems, Class III medical devices, nuclear facilities,
// -- applications related to the deployment of airbags, or any
// -- other applications that could lead to death, personal
// -- injury, or severe property or environmental damage
// -- (individually and collectively, "Critical
// -- Applications"). Customer assumes the sole risk and
// -- liability of any use of Xilinx products in Critical
// -- Applications, subject only to applicable laws and
// -- regulations governing limitations on product liability.
// --
// -- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// -- PART OF THIS FILE AT ALL TIMES.
//-----------------------------------------------------------------------------
//
// Description: Read Data Response Up-Sizer
// Extract SI-side Data from packed and unpacked MI-side data.
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   r_upsizer
//
//--------------------------------------------------------------------------
`timescale 1ps/1ps


(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_dwidth_converter_v2_1_12_r_upsizer #
  (
   parameter         C_FAMILY                         = "rtl", 
                       // FPGA Family. Current version: virtex6 or spartan6.
   parameter integer C_AXI_ID_WIDTH                   = 4, 
                       // Width of all ID signals on SI and MI side of converter.
                       // Range: >= 1.
   parameter integer C_S_AXI_DATA_WIDTH               = 64,
                       // Width of s_axi_wdata and s_axi_rdata.
                       // Range: 32, 64, 128, 256, 512, 1024.
   parameter integer C_M_AXI_DATA_WIDTH               = 32,
                       // Width of m_axi_wdata and m_axi_rdata. 
                       // Assume always >= than C_S_AXI_DATA_WIDTH.
                       // Range: 32, 64, 128, 256, 512, 1024.
   parameter integer C_S_AXI_REGISTER                 = 0,
                       // Clock output data.
                       // Range: 0, 1
   parameter integer C_PACKING_LEVEL                    = 1,
                       // 0 = Never pack (expander only); packing logic is omitted.
                       // 1 = Pack only when CACHE[1] (Modifiable) is high.
                       // 2 = Always pack, regardless of sub-size transaction or Modifiable bit.
                       //     (Required when used as helper-core by mem-con.)
   parameter integer C_S_AXI_BYTES_LOG                = 3,
                       // Log2 of number of 32bit word on SI-side.
   parameter integer C_M_AXI_BYTES_LOG                = 3,
                       // Log2 of number of 32bit word on MI-side.
   parameter integer C_RATIO                          = 2,
                       // Up-Sizing ratio for data.
   parameter integer C_RATIO_LOG                      = 1
                       // Log2 of Up-Sizing ratio for data.
   )
  (
   // Global Signals
   input  wire                                                    ARESET,
   input  wire                                                    ACLK,

   // Command Interface
   input  wire                              cmd_valid,
   input  wire                              cmd_fix,
   input  wire                              cmd_modified,
   input  wire                              cmd_complete_wrap,
   input  wire                              cmd_packed_wrap,
   input  wire [C_M_AXI_BYTES_LOG-1:0]      cmd_first_word, 
   input  wire [C_M_AXI_BYTES_LOG-1:0]      cmd_next_word,
   input  wire [C_M_AXI_BYTES_LOG-1:0]      cmd_last_word,
   input  wire [C_M_AXI_BYTES_LOG-1:0]      cmd_offset,
   input  wire [C_M_AXI_BYTES_LOG-1:0]      cmd_mask,
   input  wire [C_S_AXI_BYTES_LOG:0]        cmd_step,
   input  wire [8-1:0]                      cmd_length,
   input  wire [C_AXI_ID_WIDTH-1:0]         cmd_id,
   output wire                              cmd_ready,
   
   // Slave Interface Read Data Ports
   output wire [C_AXI_ID_WIDTH-1:0]           S_AXI_RID,
   output wire [C_S_AXI_DATA_WIDTH-1:0]    S_AXI_RDATA,
   output wire [2-1:0]                          S_AXI_RRESP,
   output wire                                                    S_AXI_RLAST,
   output wire                                                    S_AXI_RVALID,
   input  wire                                                    S_AXI_RREADY,

   // Master Interface Read Data Ports
   input  wire [C_M_AXI_DATA_WIDTH-1:0]    M_AXI_RDATA,
   input  wire [2-1:0]                         M_AXI_RRESP,
   input  wire                                                   M_AXI_RLAST,
   input  wire                                                   M_AXI_RVALID,
   output wire                                                   M_AXI_RREADY
   );
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Variables for generating parameter controlled instances.
  /////////////////////////////////////////////////////////////////////////////
  
  genvar bit_cnt;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Local params
  /////////////////////////////////////////////////////////////////////////////
  
  // Constants for packing levels.
  localparam integer C_NEVER_PACK        = 0;
  localparam integer C_DEFAULT_PACK      = 1;
  localparam integer C_ALWAYS_PACK       = 2;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Functions
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Internal signals
  /////////////////////////////////////////////////////////////////////////////
  
  // Sub-word handling.
  wire                            sel_first_word;
  reg                             first_word;
  reg  [C_M_AXI_BYTES_LOG-1:0]    current_word_1;
  reg  [C_M_AXI_BYTES_LOG-1:0]    current_word_cmb;
  wire [C_M_AXI_BYTES_LOG-1:0]    current_word;
  wire [C_M_AXI_BYTES_LOG-1:0]    current_word_adjusted;
  wire                            last_beat;
  wire                            last_word;
  wire [C_M_AXI_BYTES_LOG-1:0]    cmd_step_i;
  
  // Sub-word handling for the next cycle.
  wire [C_M_AXI_BYTES_LOG-1:0]    pre_next_word_i;
  wire [C_M_AXI_BYTES_LOG-1:0]    pre_next_word;
  reg  [C_M_AXI_BYTES_LOG-1:0]    pre_next_word_1;
  wire [C_M_AXI_BYTES_LOG-1:0]    next_word_i;
  wire [C_M_AXI_BYTES_LOG-1:0]    next_word;
  
  // Burst length handling.
  wire                            first_mi_word;
  wire [8-1:0]                    length_counter_1;
  reg  [8-1:0]                    length_counter;
  wire [8-1:0]                    next_length_counter;
  
  // Handle wrap buffering.
  wire                            store_in_wrap_buffer;
  reg                             use_wrap_buffer;
  reg                             wrap_buffer_available;
  reg [2-1:0]                     rresp_wrap_buffer;
  
  // Throttling help signals.
  wire                            next_word_wrap;
  wire                            word_complete_next_wrap;
  wire                            word_complete_next_wrap_ready;
  wire                            word_complete_next_wrap_pop;
  wire                            word_complete_last_word;
  wire                            word_complete_rest;
  wire                            word_complete_rest_ready;
  wire                            word_complete_rest_pop;
  wire                            word_completed;
  wire                            cmd_ready_i;
  wire                            pop_si_data;
  wire                            pop_mi_data;
  wire                            si_stalling;
  
  // Internal signals for MI-side.
  reg  [C_M_AXI_DATA_WIDTH-1:0]   M_AXI_RDATA_I;
  wire                            M_AXI_RLAST_I;
  wire                            M_AXI_RVALID_I;
  wire                            M_AXI_RREADY_I;
  
  // Internal signals for SI-side.
  wire [C_AXI_ID_WIDTH-1:0]       S_AXI_RID_I;
  wire [C_S_AXI_DATA_WIDTH-1:0]   S_AXI_RDATA_I;
  wire [2-1:0]                    S_AXI_RRESP_I;
  wire                            S_AXI_RLAST_I;
  wire                            S_AXI_RVALID_I;
  wire                            S_AXI_RREADY_I;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Handle interface handshaking:
  //
  // Determine if a MI side word has been completely used. For FIX transactions
  // the MI-side word is used to extract a single data word. This is also true
  // for for an upsizer in Expander mode (Never Pack). Unmodified burst also 
  // only use the MI word to extract a single SI-side word (although with 
  // different offsets).
  // Otherwise is the MI-side word considered to be used when last SI-side beat
  // has been extracted or when the last (most significant) SI-side word has 
  // been extracted from ti MI word.
  //
  // Data on the SI-side is available when data is being taken from MI-side or
  // from wrap buffer.
  //
  // The command is popped from the command queue once the last beat on the 
  // SI-side has been ackowledged.
  //
  /////////////////////////////////////////////////////////////////////////////
  
  generate
    if ( C_RATIO_LOG > 1 ) begin : USE_LARGE_UPSIZING
      assign cmd_step_i = {{C_RATIO_LOG-1{1'b0}}, cmd_step};
    end else begin : NO_LARGE_UPSIZING
      assign cmd_step_i = cmd_step;
    end
  endgenerate
  
  generate
    if ( C_FAMILY == "rtl" || 
       ( C_PACKING_LEVEL == C_NEVER_PACK ) ) begin : USE_RTL_WORD_COMPLETED
      // Detect when MI-side word is completely used.
      assign word_completed = cmd_valid & 
                              ( ( cmd_fix ) |
                                ( ~cmd_fix & ~cmd_complete_wrap & next_word == {C_M_AXI_BYTES_LOG{1'b0}} ) | 
                                ( ~cmd_fix & last_word & ~use_wrap_buffer ) | 
                                ( ~cmd_modified & ( C_PACKING_LEVEL == C_DEFAULT_PACK ) ) |
                                ( C_PACKING_LEVEL == C_NEVER_PACK ) );
      
      // RTL equivalent of optimized partial extressions (address wrap for next word).
      assign word_complete_next_wrap       = ( ~cmd_fix & ~cmd_complete_wrap & next_word == {C_M_AXI_BYTES_LOG{1'b0}} ) | 
                                            ( C_PACKING_LEVEL == C_NEVER_PACK );
      assign word_complete_next_wrap_ready = word_complete_next_wrap & M_AXI_RVALID_I & ~si_stalling;
      assign word_complete_next_wrap_pop   = word_complete_next_wrap_ready & M_AXI_RVALID_I;
      
      // RTL equivalent of optimized partial extressions (last word and the remaining).
      assign word_complete_last_word  = last_word & (~cmd_fix & ~use_wrap_buffer);
      assign word_complete_rest       = word_complete_last_word | cmd_fix | 
                                        ( ~cmd_modified & ( C_PACKING_LEVEL == C_DEFAULT_PACK ) );
      assign word_complete_rest_ready = word_complete_rest & M_AXI_RVALID_I & ~si_stalling;
      assign word_complete_rest_pop   = word_complete_rest_ready & M_AXI_RVALID_I;
      
    end else begin : USE_FPGA_WORD_COMPLETED
    
      wire sel_word_complete_next_wrap;
      wire sel_word_completed;
      wire sel_m_axi_rready;
      wire sel_word_complete_last_word;
      wire sel_word_complete_rest;
      
      // Optimize next word address wrap branch of expression.
      //
      generic_baseblocks_v2_1_0_comparator_sel_static #
        (
         .C_FAMILY(C_FAMILY),
         .C_VALUE({C_M_AXI_BYTES_LOG{1'b0}}),
         .C_DATA_WIDTH(C_M_AXI_BYTES_LOG)
         ) next_word_wrap_inst
        (
         .CIN(1'b1),
         .S(sel_first_word),
         .A(pre_next_word_1),
         .B(cmd_next_word),
         .COUT(next_word_wrap)
         );
         
      assign sel_word_complete_next_wrap = ~cmd_fix & ~cmd_complete_wrap;
      
      generic_baseblocks_v2_1_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_next_wrap_inst
        (
         .CIN(next_word_wrap),
         .S(sel_word_complete_next_wrap),
         .COUT(word_complete_next_wrap)
         );
         
      assign sel_m_axi_rready = cmd_valid & S_AXI_RREADY_I;
      
      generic_baseblocks_v2_1_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_next_wrap_ready_inst
        (
         .CIN(word_complete_next_wrap),
         .S(sel_m_axi_rready),
         .COUT(word_complete_next_wrap_ready)
         );
      
      generic_baseblocks_v2_1_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_next_wrap_pop_inst
        (
         .CIN(word_complete_next_wrap_ready),
         .S(M_AXI_RVALID_I),
         .COUT(word_complete_next_wrap_pop)
         );
      
      // Optimize last word and "rest" branch of expression.
      //
      assign sel_word_complete_last_word = ~cmd_fix & ~use_wrap_buffer;
      
      generic_baseblocks_v2_1_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_last_word_inst
        (
         .CIN(last_word),
         .S(sel_word_complete_last_word),
         .COUT(word_complete_last_word)
         );
      
      assign sel_word_complete_rest = cmd_fix | ( ~cmd_modified & ( C_PACKING_LEVEL == C_DEFAULT_PACK ) );
      
      generic_baseblocks_v2_1_0_carry_or #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_rest_inst
        (
         .CIN(word_complete_last_word),
         .S(sel_word_complete_rest),
         .COUT(word_complete_rest)
         );
         
      generic_baseblocks_v2_1_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_rest_ready_inst
        (
         .CIN(word_complete_rest),
         .S(sel_m_axi_rready),
         .COUT(word_complete_rest_ready)
         );
      
      generic_baseblocks_v2_1_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_rest_pop_inst
        (
         .CIN(word_complete_rest_ready),
         .S(M_AXI_RVALID_I),
         .COUT(word_complete_rest_pop)
         );
      
      // Combine the two branches to generate the full signal.
      assign word_completed = word_complete_next_wrap | word_complete_rest;
      
    end
  endgenerate
  
  // Only propagate Valid when there is command information available.
  assign M_AXI_RVALID_I = M_AXI_RVALID & cmd_valid;
  
  generate
    if ( C_FAMILY == "rtl" ) begin : USE_RTL_CTRL
      // Pop word from MI-side.
      assign M_AXI_RREADY_I = word_completed & S_AXI_RREADY_I;
      
      // Get MI-side data.
      assign pop_mi_data    = M_AXI_RVALID_I & M_AXI_RREADY_I;
      
      // Signal that the command is done (so that it can be poped from command queue).
      assign cmd_ready_i    = cmd_valid & S_AXI_RLAST_I & pop_si_data;
      
    end else begin : USE_FPGA_CTRL
      wire sel_cmd_ready;
      
      assign M_AXI_RREADY_I = word_complete_next_wrap_ready | word_complete_rest_ready;
      
      assign pop_mi_data    = word_complete_next_wrap_pop | word_complete_rest_pop;
      
      assign sel_cmd_ready  = cmd_valid & pop_si_data;
    
      generic_baseblocks_v2_1_0_carry_latch_and #
        (
         .C_FAMILY(C_FAMILY)
         ) cmd_ready_inst
        (
         .CIN(S_AXI_RLAST_I),
         .I(sel_cmd_ready),
         .O(cmd_ready_i)
         );
      
    end
  endgenerate
  
  // Indicate when there is data available @ SI-side.
  assign S_AXI_RVALID_I = ( M_AXI_RVALID_I | use_wrap_buffer );
  
  // Get SI-side data.
  assign pop_si_data    = S_AXI_RVALID_I & S_AXI_RREADY_I;
  
  // Assign external signals.
  assign M_AXI_RREADY   = M_AXI_RREADY_I;
  assign cmd_ready      = cmd_ready_i;
  
  // Detect when SI-side is stalling.
  assign si_stalling    = S_AXI_RVALID_I & ~S_AXI_RREADY_I;
                          
  
  /////////////////////////////////////////////////////////////////////////////
  // Keep track of data extraction:
  // 
  // Current address is taken form the command buffer for the first data beat
  // to handle unaligned Read transactions. After this is the extraction 
  // address usually calculated from this point.
  // FIX transactions uses the same word address for all data beats. 
  // 
  // Next word address is generated as current word plus the current step 
  // size, with masking to facilitate sub-sized wraping. The Mask is all ones
  // for normal wraping, and less when sub-sized wraping is used.
  // 
  // The calculated word addresses (current and next) is offseted by the 
  // current Offset. For sub-sized transaction the Offset points to the least 
  // significant address of the included data beats. (The least significant 
  // word is not necessarily the first data to be extracted, consider WRAP).
  // Offset is only used for sub-sized WRAP transcation that are Complete.
  // 
  // First word is active during the first SI-side data beat.
  // 
  // First MI is set while the entire first MI-side word is processed.
  //
  // The transaction length is taken from the command buffer combinatorialy
  // during the First MI cycle. For each used MI word it is decreased until 
  // Last beat is reached.
  // 
  // Last word is determined depending on the current command, i.e. modified 
  // burst has to scale since multiple words could be packed into one MI-side
  // word.
  // Last word is 1:1 for:
  // FIX, when burst support is disabled or unmodified for Normal Pack.
  // Last word is scaled for all other transactions.
  //
  /////////////////////////////////////////////////////////////////////////////
  
  // Select if the offset comes from command queue directly or 
  // from a counter while when extracting multiple SI words per MI word
  assign sel_first_word = first_word | cmd_fix;
  assign current_word   = sel_first_word ? cmd_first_word : 
                                           current_word_1;
  
  generate
    if ( C_FAMILY == "rtl" ) begin : USE_RTL_NEXT_WORD
      
      // Calculate next word.
      assign pre_next_word_i  = ( next_word_i + cmd_step_i );
      
      // Calculate next word.
      assign next_word_i      = sel_first_word ? cmd_next_word : 
                                                 pre_next_word_1;
      
    end else begin : USE_FPGA_NEXT_WORD
      wire [C_M_AXI_BYTES_LOG-1:0]  next_sel;
      wire [C_M_AXI_BYTES_LOG:0]    next_carry_local;

      // Assign input to local vectors.
      assign next_carry_local[0]      = 1'b0;
    
      // Instantiate one carry and per level.
      for (bit_cnt = 0; bit_cnt < C_M_AXI_BYTES_LOG ; bit_cnt = bit_cnt + 1) begin : LUT_LEVEL
        
        LUT6_2 # (
         .INIT(64'h5A5A_5A66_F0F0_F0CC) 
        ) LUT6_2_inst (
        .O6(next_sel[bit_cnt]),         // 6/5-LUT output (1-bit)
        .O5(next_word_i[bit_cnt]),      // 5-LUT output (1-bit)
        .I0(cmd_step_i[bit_cnt]),       // LUT input (1-bit)
        .I1(pre_next_word_1[bit_cnt]),  // LUT input (1-bit)
        .I2(cmd_next_word[bit_cnt]),    // LUT input (1-bit)
        .I3(first_word),                // LUT input (1-bit)
        .I4(cmd_fix),                   // LUT input (1-bit)
        .I5(1'b1)                       // LUT input (1-bit)
        );
        
        MUXCY next_carry_inst 
        (
         .O (next_carry_local[bit_cnt+1]), 
         .CI (next_carry_local[bit_cnt]), 
         .DI (cmd_step_i[bit_cnt]), 
         .S (next_sel[bit_cnt])
        ); 
        
        XORCY next_xorcy_inst 
        (
         .O(pre_next_word_i[bit_cnt]),
         .CI(next_carry_local[bit_cnt]),
         .LI(next_sel[bit_cnt])
        );
        
      end // end for bit_cnt
      
    end
  endgenerate
  
  // Calculate next word.
  assign next_word              = next_word_i     & cmd_mask;
  assign pre_next_word          = pre_next_word_i & cmd_mask;
  
  // Calculate the word address with offset.
  assign current_word_adjusted  = current_word | cmd_offset;
  
  // Prepare next word address.
  always @ (posedge ACLK) begin
    if (ARESET) begin
      first_word      <= 1'b1;
      current_word_1  <= 'b0;
      pre_next_word_1 <= {C_M_AXI_BYTES_LOG{1'b0}};
    end else begin
      if ( pop_si_data ) begin
        if ( last_word ) begin
          // Prepare for next access.
          first_word      <=  1'b1;
        end else begin
          first_word      <=  1'b0;
        end
      
        current_word_1  <= next_word;
        pre_next_word_1 <= pre_next_word;
      end
    end
  end
  
  // Select command length or counted length.
  always @ *
  begin
    if ( first_mi_word )
      length_counter = cmd_length;
    else
      length_counter = length_counter_1;
  end
  
  // Calculate next length counter value.
  assign next_length_counter = length_counter - 1'b1;
  
  generate
    if ( C_FAMILY == "rtl" ) begin : USE_RTL_LENGTH
      reg  [8-1:0]                    length_counter_q;
      reg                             first_mi_word_q;
    
      always @ (posedge ACLK) begin
        if (ARESET) begin
          first_mi_word_q  <= 1'b1;
          length_counter_q <= 8'b0;
        end else begin
          if ( pop_mi_data ) begin
            if ( M_AXI_RLAST ) begin
              first_mi_word_q  <= 1'b1;
            end else begin
              first_mi_word_q  <= 1'b0;
            end
          
            length_counter_q <= next_length_counter;
          end
        end
      end
      
      assign first_mi_word    = first_mi_word_q;
      assign length_counter_1 = length_counter_q;
      
    end else begin : USE_FPGA_LENGTH
      wire [8-1:0]  length_counter_i;
      wire [8-1:0]  length_sel;
      wire [8-1:0]  length_di;
      wire [8:0]    length_local_carry;
      
      // Assign input to local vectors.
      assign length_local_carry[0] = 1'b0;
    
      for (bit_cnt = 0; bit_cnt < 8 ; bit_cnt = bit_cnt + 1) begin : BIT_LANE

        LUT6_2 # (
         .INIT(64'h333C_555A_FFF0_FFF0) 
        ) LUT6_2_inst (
        .O6(length_sel[bit_cnt]),           // 6/5-LUT output (1-bit)
        .O5(length_di[bit_cnt]),            // 5-LUT output (1-bit)
        .I0(length_counter_1[bit_cnt]),     // LUT input (1-bit)
        .I1(cmd_length[bit_cnt]),           // LUT input (1-bit)
        .I2(word_complete_next_wrap_pop),  // LUT input (1-bit)
        .I3(word_complete_rest_pop),        // LUT input (1-bit)
        .I4(first_mi_word),                 // LUT input (1-bit)
        .I5(1'b1)                           // LUT input (1-bit)
        );
        
        MUXCY and_inst 
        (
         .O (length_local_carry[bit_cnt+1]), 
         .CI (length_local_carry[bit_cnt]), 
         .DI (length_di[bit_cnt]), 
         .S (length_sel[bit_cnt])
        ); 
        
        XORCY xorcy_inst 
        (
         .O(length_counter_i[bit_cnt]),
         .CI(length_local_carry[bit_cnt]),
         .LI(length_sel[bit_cnt])
        );
        
        FDRE #(
         .INIT(1'b0)                    // Initial value of register (1'b0 or 1'b1)
         ) FDRE_inst (
         .Q(length_counter_1[bit_cnt]), // Data output
         .C(ACLK),                      // Clock input
         .CE(1'b1),                     // Clock enable input
         .R(ARESET),                    // Synchronous reset input
         .D(length_counter_i[bit_cnt])  // Data input
         );
      end // end for bit_cnt
      
      wire first_mi_word_i;
      
      LUT6 # (
       .INIT(64'hAAAC_AAAC_AAAC_AAAC) 
      ) LUT6_cnt_inst (
      .O(first_mi_word_i),                // 6-LUT output (1-bit)
      .I0(M_AXI_RLAST),                   // LUT input (1-bit)
      .I1(first_mi_word),                 // LUT input (1-bit)
      .I2(word_complete_next_wrap_pop),  // LUT input (1-bit)
      .I3(word_complete_rest_pop),        // LUT input (1-bit)
      .I4(1'b1),                          // LUT input (1-bit)
      .I5(1'b1)                           // LUT input (1-bit)
      );
          
      FDSE #(
       .INIT(1'b1)                    // Initial value of register (1'b0 or 1'b1)
       ) FDRE_inst (
       .Q(first_mi_word),             // Data output
       .C(ACLK),                      // Clock input
       .CE(1'b1),                     // Clock enable input
       .S(ARESET),                    // Synchronous reset input
       .D(first_mi_word_i)            // Data input
       );
      
    end
  endgenerate
  
  generate
    if ( C_FAMILY == "rtl" ) begin : USE_RTL_LAST_WORD
      // Detect last beat in a burst.
      assign last_beat = ( length_counter == 8'b0 );
      
      // Determine if this last word that shall be extracted from this MI-side word.
      assign last_word = ( last_beat & ( current_word == cmd_last_word ) & ~wrap_buffer_available & ( current_word == cmd_last_word ) ) |
                         ( use_wrap_buffer & ( current_word == cmd_last_word ) ) |
                         ( last_beat & ( current_word == cmd_last_word ) & ( C_PACKING_LEVEL == C_NEVER_PACK ) );
  
    end else begin : USE_FPGA_LAST_WORD
    
      wire sel_last_word;
      wire last_beat_ii;
      
      
      comparator_sel_static #
        (
         .C_FAMILY(C_FAMILY),
         .C_VALUE(8'b0),
         .C_DATA_WIDTH(8)
         ) last_beat_inst
        (
         .CIN(1'b1),
         .S(first_mi_word),
         .A(length_counter_1),
         .B(cmd_length),
         .COUT(last_beat)
         );
      
      if ( C_PACKING_LEVEL != C_NEVER_PACK  ) begin : USE_FPGA_PACK
        // 
        //
        wire sel_last_beat;
        wire last_beat_i;
        
        assign sel_last_beat = ~wrap_buffer_available;
        
        carry_and #
          (
           .C_FAMILY(C_FAMILY)
           ) last_beat_inst_1
          (
           .CIN(last_beat),
           .S(sel_last_beat),
           .COUT(last_beat_i)
           );
  
        carry_or #
          (
           .C_FAMILY(C_FAMILY)
           ) last_beat_wrap_inst
          (
           .CIN(last_beat_i),
           .S(use_wrap_buffer),
           .COUT(last_beat_ii)
           );
  
      end else begin : NO_PACK
        assign last_beat_ii = last_beat;
           
      end
        
      comparator_sel #
        (
         .C_FAMILY(C_FAMILY),
         .C_DATA_WIDTH(C_M_AXI_BYTES_LOG)
         ) last_beat_curr_word_inst
        (
         .CIN(last_beat_ii),
         .S(sel_first_word),
         .A(current_word_1),
         .B(cmd_first_word),
         .V(cmd_last_word),
         .COUT(last_word)
         );
      
    end
  endgenerate
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Handle wrap buffer:
  // 
  // The wrap buffer is used to move data around in an unaligned WRAP 
  // transaction. The requested read address has been rounded down, meaning 
  // that parts of the first MI-side data beat has to be delayed for later use.
  // The extraction starts at the origian unaligned address, the remaining data
  // is stored in the wrap buffer to be extracted after the last MI-side data 
  // beat has been fully processed.
  // For example: an 32bit to 64bit read upsizing @ 0x4 will request a MI-side
  // read WRAP transaction 0x0. The 0x4 data word is used at once and the 0x0 
  // word is delayed to be used after all data in the last MI-side beat has 
  // arrived.
  // 
  /////////////////////////////////////////////////////////////////////////////
  
  // Save data to be able to perform buffer wraping.
  assign store_in_wrap_buffer = M_AXI_RVALID_I & cmd_packed_wrap & first_mi_word & ~use_wrap_buffer;
  
  // Mark that there are data available for wrap buffering.
  always @ (posedge ACLK) begin
    if (ARESET) begin
      wrap_buffer_available <= 1'b0;
    end else begin
      if ( store_in_wrap_buffer & word_completed & pop_si_data  ) begin
        wrap_buffer_available <= 1'b1;
      end else if ( last_beat & word_completed & pop_si_data  ) begin
        wrap_buffer_available <= 1'b0;
      end
    end
  end
  
  // Start using the wrap buffer.
  always @ (posedge ACLK) begin
    if (ARESET) begin
      use_wrap_buffer <= 1'b0;
    end else begin
      if ( wrap_buffer_available & last_beat & word_completed & pop_si_data ) begin
        use_wrap_buffer <= 1'b1;
      end else if ( cmd_ready_i ) begin
        use_wrap_buffer <= 1'b0;
      end
    end
  end
  
  // Store data in wrap buffer.
  always @ (posedge ACLK) begin
    if (ARESET) begin
      M_AXI_RDATA_I     <= {C_M_AXI_DATA_WIDTH{1'b0}};
      rresp_wrap_buffer <= 2'b0;
    end else begin
      if ( store_in_wrap_buffer ) begin
        M_AXI_RDATA_I     <= M_AXI_RDATA;
        rresp_wrap_buffer <= M_AXI_RRESP;
      end
    end
  end
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Select the SI-side word to read.
  //
  // Everything must be multiplexed since the next transfer can be arriving 
  // with a different set of signals while the wrap buffer is still being 
  // processed for the current transaction.
  // 
  // Non modifiable word has a 1:1 ratio, i.e. only one SI-side word is 
  // generated per MI-side word.
  // Data is taken either directly from the incomming MI-side data or the 
  // wrap buffer (for packed WRAP).
  //
  // Last need special handling since it is the last SI-side word generated 
  // from the MI-side word.
  //
  /////////////////////////////////////////////////////////////////////////////
  
  // ID, RESP and USER has to be multiplexed.
  assign S_AXI_RID_I    = cmd_id;
  assign S_AXI_RRESP_I  = ( use_wrap_buffer ) ? 
                          rresp_wrap_buffer :
                          M_AXI_RRESP;
                          
  // Data has to be multiplexed.
  generate
    if ( C_RATIO == 1 ) begin : SINGLE_WORD
      assign S_AXI_RDATA_I  = ( use_wrap_buffer ) ? 
                              M_AXI_RDATA_I :
                              M_AXI_RDATA;
    end else begin : MULTIPLE_WORD
      // Get the ratio bits (MI-side words vs SI-side words).
      wire [C_RATIO_LOG-1:0]          current_index;
      assign current_index  = current_word_adjusted[C_M_AXI_BYTES_LOG-C_RATIO_LOG +: C_RATIO_LOG];
      
      assign S_AXI_RDATA_I  = ( use_wrap_buffer ) ? 
                              M_AXI_RDATA_I[current_index * C_S_AXI_DATA_WIDTH +: C_S_AXI_DATA_WIDTH] :
                              M_AXI_RDATA[current_index * C_S_AXI_DATA_WIDTH +: C_S_AXI_DATA_WIDTH];
    end
  endgenerate
  
  // Generate the true last flag including "keep" while using wrap buffer.
  assign M_AXI_RLAST_I  = ( M_AXI_RLAST | use_wrap_buffer );
  
  // Handle last flag, i.e. set for SI-side last word.
  assign S_AXI_RLAST_I  = last_word;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // SI-side output handling
  /////////////////////////////////////////////////////////////////////////////
  
  generate
    if ( C_S_AXI_REGISTER ) begin : USE_REGISTER
      reg  [C_AXI_ID_WIDTH-1:0]       S_AXI_RID_q;
      reg  [C_S_AXI_DATA_WIDTH-1:0]   S_AXI_RDATA_q;
      reg  [2-1:0]                    S_AXI_RRESP_q;
      reg                             S_AXI_RLAST_q;
      reg                             S_AXI_RVALID_q = 1'b0;
      reg                             S_AXI_RREADY_q = 1'b0;
    
      // Register SI-side Data.
      always @ (posedge ACLK) begin
        if (ARESET) begin
          S_AXI_RID_q       <= {C_AXI_ID_WIDTH{1'b0}};
          S_AXI_RDATA_q     <= {C_S_AXI_DATA_WIDTH{1'b0}};
          S_AXI_RRESP_q     <= 2'b0;
          S_AXI_RLAST_q     <= 1'b0;
          S_AXI_RVALID_q    <= 1'b0;
        end else begin
          if ( S_AXI_RREADY_I ) begin
            S_AXI_RID_q       <= S_AXI_RID_I;
            S_AXI_RDATA_q     <= S_AXI_RDATA_I;
            S_AXI_RRESP_q     <= S_AXI_RRESP_I;
            S_AXI_RLAST_q     <= S_AXI_RLAST_I;
            S_AXI_RVALID_q    <= S_AXI_RVALID_I;
          end
          
        end
      end
      
      assign S_AXI_RID      = S_AXI_RID_q;
      assign S_AXI_RDATA    = S_AXI_RDATA_q;
      assign S_AXI_RRESP    = S_AXI_RRESP_q;
      assign S_AXI_RLAST    = S_AXI_RLAST_q;
      assign S_AXI_RVALID   = S_AXI_RVALID_q;
      assign S_AXI_RREADY_I = ( S_AXI_RVALID_q & S_AXI_RREADY) | ~S_AXI_RVALID_q;
      
    end else begin : NO_REGISTER
    
      // Combinatorial SI-side Data.
      assign S_AXI_RREADY_I = S_AXI_RREADY;
      assign S_AXI_RVALID   = S_AXI_RVALID_I;
      assign S_AXI_RID      = S_AXI_RID_I;
      assign S_AXI_RDATA    = S_AXI_RDATA_I;
      assign S_AXI_RRESP    = S_AXI_RRESP_I;
      assign S_AXI_RLAST    = S_AXI_RLAST_I;
  
    end
  endgenerate
  
  
endmodule


// -- (c) Copyright 2010 - 2011 Xilinx, Inc. All rights reserved.
// --
// -- This file contains confidential and proprietary information
// -- of Xilinx, Inc. and is protected under U.S. and 
// -- international copyright and other intellectual property
// -- laws.
// --
// -- DISCLAIMER
// -- This disclaimer is not a license and does not grant any
// -- rights to the materials distributed herewith. Except as
// -- otherwise provided in a valid license issued to you by
// -- Xilinx, and to the maximum extent permitted by applicable
// -- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// -- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// -- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// -- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// -- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// -- (2) Xilinx shall not be liable (whether in contract or tort,
// -- including negligence, or under any other theory of
// -- liability) for any loss or damage of any kind or nature
// -- related to, arising under or in connection with these
// -- materials, including for any direct, or any indirect,
// -- special, incidental, or consequential loss or damage
// -- (including loss of data, profits, goodwill, or any type of
// -- loss or damage suffered as a result of any action brought
// -- by a third party) even if such damage or loss was
// -- reasonably foreseeable or Xilinx had been advised of the
// -- possibility of the same.
// --
// -- CRITICAL APPLICATIONS
// -- Xilinx products are not designed or intended to be fail-
// -- safe, or for use in any application requiring fail-safe
// -- performance, such as life-support or safety devices or
// -- systems, Class III medical devices, nuclear facilities,
// -- applications related to the deployment of airbags, or any
// -- other applications that could lead to death, personal
// -- injury, or severe property or environmental damage
// -- (individually and collectively, "Critical
// -- Applications"). Customer assumes the sole risk and
// -- liability of any use of Xilinx products in Critical
// -- Applications, subject only to applicable laws and
// -- regulations governing limitations on product liability.
// --
// -- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// -- PART OF THIS FILE AT ALL TIMES.
//-----------------------------------------------------------------------------
//
// Description: Write Data Up-Sizer
// Mirror data for simple accesses.
// Merge data for burst.
//
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   w_upsizer
//
//--------------------------------------------------------------------------
`timescale 1ps/1ps


(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_dwidth_converter_v2_1_12_w_upsizer #
  (
   parameter         C_FAMILY                         = "rtl", 
                       // FPGA Family. Current version: virtex6 or spartan6.
   parameter integer C_S_AXI_DATA_WIDTH               = 64,
                       // Width of s_axi_wdata and s_axi_rdata.
                       // Range: 32, 64, 128, 256, 512, 1024.
   parameter integer C_M_AXI_DATA_WIDTH               = 32,
                       // Width of m_axi_wdata and m_axi_rdata. 
                       // Assume always >= than C_S_AXI_DATA_WIDTH.
                       // Range: 32, 64, 128, 256, 512, 1024.
   parameter integer C_M_AXI_REGISTER                 = 0,
                       // Clock output data.
                       // Range: 0, 1
   parameter integer C_PACKING_LEVEL                    = 1,
                       // 0 = Never pack (expander only); packing logic is omitted.
                       // 1 = Pack only when CACHE[1] (Modifiable) is high.
                       // 2 = Always pack, regardless of sub-size transaction or Modifiable bit.
                       //     (Required when used as helper-core by mem-con.)
   parameter integer C_S_AXI_BYTES_LOG                = 3,
                       // Log2 of number of 32bit word on SI-side.
   parameter integer C_M_AXI_BYTES_LOG                = 3,
                       // Log2 of number of 32bit word on MI-side.
   parameter integer C_RATIO                          = 2,
                       // Up-Sizing ratio for data.
   parameter integer C_RATIO_LOG                      = 1
                       // Log2 of Up-Sizing ratio for data.
   )
  (
   // Global Signals
   input  wire                                                    ARESET,
   input  wire                                                    ACLK,

   // Command Interface
   input  wire                              cmd_valid,
   input  wire                              cmd_fix,
   input  wire                              cmd_modified,
   input  wire                              cmd_complete_wrap,
   input  wire                              cmd_packed_wrap,
   input  wire [C_M_AXI_BYTES_LOG-1:0]      cmd_first_word, 
   input  wire [C_M_AXI_BYTES_LOG-1:0]      cmd_next_word,
   input  wire [C_M_AXI_BYTES_LOG-1:0]      cmd_last_word,
   input  wire [C_M_AXI_BYTES_LOG-1:0]      cmd_offset,
   input  wire [C_M_AXI_BYTES_LOG-1:0]      cmd_mask,
   input  wire [C_S_AXI_BYTES_LOG:0]        cmd_step,
   input  wire [8-1:0]                      cmd_length,
   output wire                              cmd_ready,
   
   // Slave Interface Write Data Ports
   input  wire [C_S_AXI_DATA_WIDTH-1:0]     S_AXI_WDATA,
   input  wire [C_S_AXI_DATA_WIDTH/8-1:0]   S_AXI_WSTRB,
   input  wire                                                    S_AXI_WLAST,
   input  wire                                                    S_AXI_WVALID,
   output wire                                                    S_AXI_WREADY,

   // Master Interface Write Data Ports
   output wire [C_M_AXI_DATA_WIDTH-1:0]    M_AXI_WDATA,
   output wire [C_M_AXI_DATA_WIDTH/8-1:0]  M_AXI_WSTRB,
   output wire                                                   M_AXI_WLAST,
   output wire                                                   M_AXI_WVALID,
   input  wire                                                   M_AXI_WREADY
   );
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Variables for generating parameter controlled instances.
  /////////////////////////////////////////////////////////////////////////////
  
  // Generate variable for SI-side word lanes on MI-side.
  genvar word_cnt;
  
  // Generate variable for intra SI-word byte control (on MI-side) for always pack.
  genvar byte_cnt;
  genvar bit_cnt;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Local params
  /////////////////////////////////////////////////////////////////////////////
  
  // Constants for packing levels.
  localparam integer C_NEVER_PACK        = 0;
  localparam integer C_DEFAULT_PACK      = 1;
  localparam integer C_ALWAYS_PACK       = 2;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Functions
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Internal signals
  /////////////////////////////////////////////////////////////////////////////

  // Sub-word handling.
  wire                            sel_first_word;
  wire                            first_word;
  wire [C_M_AXI_BYTES_LOG-1:0]    current_word_1;
  wire [C_M_AXI_BYTES_LOG-1:0]    current_word;
  wire [C_M_AXI_BYTES_LOG-1:0]    current_word_adjusted;
  wire [C_RATIO-1:0]              current_word_idx;
  wire                            last_beat;
  wire                            last_word;
  wire                            last_word_extra_carry;
  wire [C_M_AXI_BYTES_LOG-1:0]    cmd_step_i;
  
  // Sub-word handling for the next cycle.
  wire [C_M_AXI_BYTES_LOG-1:0]    pre_next_word_i;
  wire [C_M_AXI_BYTES_LOG-1:0]    pre_next_word;
  wire [C_M_AXI_BYTES_LOG-1:0]    pre_next_word_1;
  wire [C_M_AXI_BYTES_LOG-1:0]    next_word_i;
  wire [C_M_AXI_BYTES_LOG-1:0]    next_word;
  
  // Burst length handling.
  wire                            first_mi_word;
  wire [8-1:0]                    length_counter_1;
  reg  [8-1:0]                    length_counter;
  wire [8-1:0]                    next_length_counter;
  
  // Handle wrap buffering.
  wire                            store_in_wrap_buffer_enabled;
  wire                            store_in_wrap_buffer;
  wire                            ARESET_or_store_in_wrap_buffer;
  wire                            use_wrap_buffer;
  reg                             wrap_buffer_available;
  
  // Detect start of MI word.
  wire                            first_si_in_mi;
  
  // Throttling help signals.
  wire                            word_complete_next_wrap;
  wire                            word_complete_next_wrap_qual;
  wire                            word_complete_next_wrap_valid;
  wire                            word_complete_next_wrap_pop;
  wire                            word_complete_next_wrap_last;
  wire                            word_complete_next_wrap_stall;
  wire                            word_complete_last_word;
  wire                            word_complete_rest;
  wire                            word_complete_rest_qual;
  wire                            word_complete_rest_valid;
  wire                            word_complete_rest_pop;
  wire                            word_complete_rest_last;
  wire                            word_complete_rest_stall;
  wire                            word_completed;
  wire                            word_completed_qualified;
  wire                            cmd_ready_i;
  wire                            pop_si_data;
  wire                            pop_mi_data_i;
  wire                            pop_mi_data;
  wire                            mi_stalling;
  
  // Internal SI side control signals.
  wire                            S_AXI_WREADY_I;
   
  // Internal packed write data.
  wire                            use_expander_data;
  wire [C_M_AXI_DATA_WIDTH/8-1:0] wdata_qualifier;          // For FPGA only
  wire [C_M_AXI_DATA_WIDTH/8-1:0] wstrb_qualifier;          // For FPGA only
  wire [C_M_AXI_DATA_WIDTH/8-1:0] wrap_qualifier;           // For FPGA only
  wire [C_M_AXI_DATA_WIDTH-1:0]   wdata_buffer_i;           // For FPGA only
  wire [C_M_AXI_DATA_WIDTH/8-1:0] wstrb_buffer_i;           // For FPGA only
  reg  [C_M_AXI_DATA_WIDTH-1:0]   wdata_buffer_q;           // For RTL only
  reg  [C_M_AXI_DATA_WIDTH/8-1:0] wstrb_buffer_q;           // For RTL only
  wire [C_M_AXI_DATA_WIDTH-1:0]   wdata_buffer;
  wire [C_M_AXI_DATA_WIDTH/8-1:0] wstrb_buffer;
  reg  [C_M_AXI_DATA_WIDTH-1:0]   wdata_last_word_mux;
  reg  [C_M_AXI_DATA_WIDTH/8-1:0] wstrb_last_word_mux;
  reg  [C_M_AXI_DATA_WIDTH-1:0]   wdata_wrap_buffer_cmb;    // For FPGA only
  reg  [C_M_AXI_DATA_WIDTH/8-1:0] wstrb_wrap_buffer_cmb;    // For FPGA only
  reg  [C_M_AXI_DATA_WIDTH-1:0]   wdata_wrap_buffer_q;      // For RTL only
  reg  [C_M_AXI_DATA_WIDTH/8-1:0] wstrb_wrap_buffer_q;      // For RTL only
  wire [C_M_AXI_DATA_WIDTH-1:0]   wdata_wrap_buffer;
  wire [C_M_AXI_DATA_WIDTH/8-1:0] wstrb_wrap_buffer;
  
  // Internal signals for MI-side.
  wire [C_M_AXI_DATA_WIDTH-1:0]   M_AXI_WDATA_cmb;          // For FPGA only
  wire [C_M_AXI_DATA_WIDTH-1:0]   M_AXI_WDATA_q;            // For FPGA only
  reg  [C_M_AXI_DATA_WIDTH-1:0]   M_AXI_WDATA_I;
  wire [C_M_AXI_DATA_WIDTH/8-1:0] M_AXI_WSTRB_cmb;          // For FPGA only
  wire [C_M_AXI_DATA_WIDTH/8-1:0] M_AXI_WSTRB_q;            // For FPGA only
  reg  [C_M_AXI_DATA_WIDTH/8-1:0] M_AXI_WSTRB_I;
  wire                            M_AXI_WLAST_I;
  wire                            M_AXI_WVALID_I;
  wire                            M_AXI_WREADY_I;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Handle interface handshaking:
  //
  // Data on the MI-side is available when data a complete word has been 
  // assembled from the data on SI-side (and potentially from any remainder in
  // the wrap buffer).
  // No data is produced on the MI-side when a unaligned packed wrap is 
  // encountered, instead it stored in the wrap buffer to be used when the 
  // last SI-side data beat is received.
  //
  // The command is popped from the command queue once the last beat on the 
  // SI-side has been ackowledged.
  // 
  // The packing process is stalled when a new MI-side is completed but not 
  // yet acknowledged (by ready).
  //
  /////////////////////////////////////////////////////////////////////////////
  
  generate
    if ( C_RATIO_LOG > 1 ) begin : USE_LARGE_UPSIZING
      assign cmd_step_i = {{C_RATIO_LOG-1{1'b0}}, cmd_step};
    end else begin : NO_LARGE_UPSIZING
      assign cmd_step_i = cmd_step;
    end
  endgenerate
  
  generate
    if ( C_FAMILY == "rtl" ||
       ( C_PACKING_LEVEL == C_NEVER_PACK ) ) begin : USE_RTL_WORD_COMPLETED
      
      // Detect when MI-side word is completely assembled.
      assign word_completed = ( cmd_fix ) |
                              ( ~cmd_fix & ~cmd_complete_wrap & next_word == {C_M_AXI_BYTES_LOG{1'b0}} ) | 
                              ( ~cmd_fix & last_word ) | 
                              ( ~cmd_modified ) |
                              ( C_PACKING_LEVEL == C_NEVER_PACK );
      
      assign word_completed_qualified   = word_completed & cmd_valid & ~store_in_wrap_buffer_enabled;
      
      // RTL equivalent of optimized partial extressions (address wrap for next word).
      assign word_complete_next_wrap        = ( ~cmd_fix & ~cmd_complete_wrap & 
                                                next_word == {C_M_AXI_BYTES_LOG{1'b0}} ) | 
                                              ( C_PACKING_LEVEL == C_NEVER_PACK );
      assign word_complete_next_wrap_qual   = word_complete_next_wrap & cmd_valid & ~store_in_wrap_buffer_enabled;
      assign word_complete_next_wrap_valid  = word_complete_next_wrap_qual & S_AXI_WVALID;
      assign word_complete_next_wrap_pop    = word_complete_next_wrap_valid & M_AXI_WREADY_I;
      assign word_complete_next_wrap_last   = word_complete_next_wrap_pop & M_AXI_WLAST_I;
      assign word_complete_next_wrap_stall  = word_complete_next_wrap_valid & ~M_AXI_WREADY_I;
      
      // RTL equivalent of optimized partial extressions (last word and the remaining).
      assign word_complete_last_word   = last_word & ~cmd_fix;
      assign word_complete_rest        = word_complete_last_word | cmd_fix | ~cmd_modified;
      assign word_complete_rest_qual   = word_complete_rest & cmd_valid & ~store_in_wrap_buffer_enabled;
      assign word_complete_rest_valid  = word_complete_rest_qual & S_AXI_WVALID;
      assign word_complete_rest_pop    = word_complete_rest_valid & M_AXI_WREADY_I;
      assign word_complete_rest_last   = word_complete_rest_pop & M_AXI_WLAST_I;
      assign word_complete_rest_stall  = word_complete_rest_valid & ~M_AXI_WREADY_I;
      
    end else begin : USE_FPGA_WORD_COMPLETED
    
      wire next_word_wrap;
      wire sel_word_complete_next_wrap;
      wire sel_word_complete_next_wrap_qual;
      wire sel_word_complete_next_wrap_stall;
      
      wire sel_last_word;
      wire sel_word_complete_rest;
      wire sel_word_complete_rest_qual;
      wire sel_word_complete_rest_stall;
      
      
      // Optimize next word address wrap branch of expression.
      //
      generic_baseblocks_v2_1_0_comparator_sel_static #
        (
         .C_FAMILY(C_FAMILY),
         .C_VALUE({C_M_AXI_BYTES_LOG{1'b0}}),
         .C_DATA_WIDTH(C_M_AXI_BYTES_LOG)
         ) next_word_wrap_inst
        (
         .CIN(1'b1),
         .S(sel_first_word),
         .A(pre_next_word_1),
         .B(cmd_next_word),
         .COUT(next_word_wrap)
         );
         
      assign sel_word_complete_next_wrap = ~cmd_fix & ~cmd_complete_wrap;
      
      generic_baseblocks_v2_1_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_next_wrap_inst
        (
         .CIN(next_word_wrap),
         .S(sel_word_complete_next_wrap),
         .COUT(word_complete_next_wrap)
         );
         
      assign sel_word_complete_next_wrap_qual = cmd_valid & ~store_in_wrap_buffer_enabled;
      
      generic_baseblocks_v2_1_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_next_wrap_valid_inst
        (
         .CIN(word_complete_next_wrap),
         .S(sel_word_complete_next_wrap_qual),
         .COUT(word_complete_next_wrap_qual)
         );
         
      generic_baseblocks_v2_1_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_next_wrap_qual_inst
        (
         .CIN(word_complete_next_wrap_qual),
         .S(S_AXI_WVALID),
         .COUT(word_complete_next_wrap_valid)
         );
         
      generic_baseblocks_v2_1_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_next_wrap_pop_inst
        (
         .CIN(word_complete_next_wrap_valid),
         .S(M_AXI_WREADY_I),
         .COUT(word_complete_next_wrap_pop)
         );
         
      assign sel_word_complete_next_wrap_stall = ~M_AXI_WREADY_I;
      
      generic_baseblocks_v2_1_0_carry_latch_and #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_next_wrap_stall_inst
        (
         .CIN(word_complete_next_wrap_valid),
         .I(sel_word_complete_next_wrap_stall),
         .O(word_complete_next_wrap_stall)
         );
         
      generic_baseblocks_v2_1_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_next_wrap_last_inst
        (
         .CIN(word_complete_next_wrap_pop),
         .S(M_AXI_WLAST_I),
         .COUT(word_complete_next_wrap_last)
         );
         
      // Optimize last word and "rest" branch of expression.
      //
      assign sel_last_word = ~cmd_fix;
      
      generic_baseblocks_v2_1_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) last_word_inst_2
        (
         .CIN(last_word_extra_carry),
         .S(sel_last_word),
         .COUT(word_complete_last_word)
         );
      
      assign sel_word_complete_rest = cmd_fix | ~cmd_modified;
      
      generic_baseblocks_v2_1_0_carry_or #
        (
         .C_FAMILY(C_FAMILY)
         ) pop_si_data_inst
        (
         .CIN(word_complete_last_word),
         .S(sel_word_complete_rest),
         .COUT(word_complete_rest)
         );
      
      assign sel_word_complete_rest_qual = cmd_valid & ~store_in_wrap_buffer_enabled;
      
      generic_baseblocks_v2_1_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_rest_valid_inst
        (
         .CIN(word_complete_rest),
         .S(sel_word_complete_rest_qual),
         .COUT(word_complete_rest_qual)
         );
         
      generic_baseblocks_v2_1_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_rest_qual_inst
        (
         .CIN(word_complete_rest_qual),
         .S(S_AXI_WVALID),
         .COUT(word_complete_rest_valid)
         );
         
      generic_baseblocks_v2_1_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_rest_pop_inst
        (
         .CIN(word_complete_rest_valid),
         .S(M_AXI_WREADY_I),
         .COUT(word_complete_rest_pop)
         );
         
      assign sel_word_complete_rest_stall = ~M_AXI_WREADY_I;
      
      generic_baseblocks_v2_1_0_carry_latch_and #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_rest_stall_inst
        (
         .CIN(word_complete_rest_valid),
         .I(sel_word_complete_rest_stall),
         .O(word_complete_rest_stall)
         );
         
      generic_baseblocks_v2_1_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_rest_last_inst
        (
         .CIN(word_complete_rest_pop),
         .S(M_AXI_WLAST_I),
         .COUT(word_complete_rest_last)
         );
      
      // Combine the two branches to generate the full signal.
      assign word_completed = word_complete_next_wrap | word_complete_rest;
      
      assign word_completed_qualified   = word_complete_next_wrap_qual | word_complete_rest_qual;
      
    end
  endgenerate
      
  // Pop word from SI-side.
  assign S_AXI_WREADY_I = ~mi_stalling & cmd_valid;
  assign S_AXI_WREADY   = S_AXI_WREADY_I;
  
  // Indicate when there is data available @ MI-side.
  generate
    if ( C_FAMILY == "rtl" ) begin : USE_RTL_M_WVALID
      assign M_AXI_WVALID_I = S_AXI_WVALID & word_completed_qualified;
      
    end else begin : USE_FPGA_M_WVALID
      
      assign M_AXI_WVALID_I = ( word_complete_next_wrap_valid | word_complete_rest_valid);
      
    end
  endgenerate
  
  // Get SI-side data.
  generate
    if ( C_M_AXI_REGISTER ) begin : USE_REGISTER_SI_POP
      assign pop_si_data    = S_AXI_WVALID & ~mi_stalling & cmd_valid;
    end else begin : NO_REGISTER_SI_POP
      if ( C_FAMILY == "rtl" ) begin : USE_RTL_POP_SI
        assign pop_si_data    = S_AXI_WVALID & S_AXI_WREADY_I;
      end else begin : USE_FPGA_POP_SI
        assign pop_si_data = ~( word_complete_next_wrap_stall | word_complete_rest_stall ) &
                             cmd_valid & S_AXI_WVALID;
      end
    end
  endgenerate
      
  // Signal that the command is done (so that it can be poped from command queue).
  generate
    if ( C_FAMILY == "rtl" ) begin : USE_RTL_CMD_READY
      assign cmd_ready_i    = cmd_valid & M_AXI_WLAST_I & pop_mi_data_i;
      
    end else begin : USE_FPGA_CMD_READY
      assign cmd_ready_i = ( word_complete_next_wrap_last | word_complete_rest_last);
      
    end
  endgenerate
  assign cmd_ready      = cmd_ready_i;
  
  // Set last upsized word.
  assign M_AXI_WLAST_I  = S_AXI_WLAST;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Keep track of data extraction:
  // 
  // Current address is taken form the command buffer for the first data beat
  // to handle unaligned Write transactions. After this is the extraction 
  // address usually calculated from this point.
  // FIX transactions uses the same word address for all data beats. 
  // 
  // Next word address is generated as current word plus the current step 
  // size, with masking to facilitate sub-sized wraping. The Mask is all ones
  // for normal wraping, and less when sub-sized wraping is used.
  // 
  // The calculated word addresses (current and next) is offseted by the 
  // current Offset. For sub-sized transaction the Offest points to the least 
  // significant address of the included data beats. (The least significant 
  // word is not necessarily the first data to be packed, consider WRAP).
  // Offset is only used for sub-sized WRAP transcation that are Complete.
  // 
  // First word is active during the first SI-side data beat.
  // 
  // First MI is set while the entire first MI-side word is processed.
  //
  // The transaction length is taken from the command buffer combinatorialy
  // during the First MI cycle. For each generated MI word it is decreased 
  // until Last beat is reached.
  // 
  /////////////////////////////////////////////////////////////////////////////
  
  // Select if the offset comes from command queue directly or 
  // from a counter while when extracting multiple SI words per MI word
  assign sel_first_word = first_word | cmd_fix;
  assign current_word   = sel_first_word ? cmd_first_word : 
                                           current_word_1;
  
  generate
    if ( C_FAMILY == "rtl" ) begin : USE_RTL_NEXT_WORD
      
      // Calculate next word.
      assign pre_next_word_i  = ( next_word_i + cmd_step_i );
      
      // Calculate next word.
      assign next_word_i      = sel_first_word ? cmd_next_word : 
                                                 pre_next_word_1;
      
    end else begin : USE_FPGA_NEXT_WORD
      wire [C_M_AXI_BYTES_LOG-1:0]  next_sel;
      wire [C_M_AXI_BYTES_LOG:0]    next_carry_local;
      
      // Assign input to local vectors.
      assign next_carry_local[0]      = 1'b0;
    
      // Instantiate one carry and per level.
      for (bit_cnt = 0; bit_cnt < C_M_AXI_BYTES_LOG ; bit_cnt = bit_cnt + 1) begin : LUT_LEVEL
        
        LUT6_2 # (
         .INIT(64'h5A5A_5A66_F0F0_F0CC) 
        ) LUT6_2_inst (
        .O6(next_sel[bit_cnt]),         // 6/5-LUT output (1-bit)
        .O5(next_word_i[bit_cnt]),      // 5-LUT output (1-bit)
        .I0(cmd_step_i[bit_cnt]),       // LUT input (1-bit)
        .I1(pre_next_word_1[bit_cnt]),  // LUT input (1-bit)
        .I2(cmd_next_word[bit_cnt]),    // LUT input (1-bit)
        .I3(first_word),                // LUT input (1-bit)
        .I4(cmd_fix),                   // LUT input (1-bit)
        .I5(1'b1)                       // LUT input (1-bit)
        );
        
        MUXCY next_carry_inst 
        (
         .O (next_carry_local[bit_cnt+1]), 
         .CI (next_carry_local[bit_cnt]), 
         .DI (cmd_step_i[bit_cnt]), 
         .S (next_sel[bit_cnt])
        ); 
        
        XORCY next_xorcy_inst 
        (
         .O(pre_next_word_i[bit_cnt]),
         .CI(next_carry_local[bit_cnt]),
         .LI(next_sel[bit_cnt])
        );
        
      end // end for bit_cnt
      
    end
  endgenerate
  
  // Calculate next word.
  assign next_word              = next_word_i & cmd_mask;
  assign pre_next_word          = pre_next_word_i & cmd_mask;
      
  // Calculate the word address with offset.
  assign current_word_adjusted  = sel_first_word ? ( cmd_first_word | cmd_offset ) : 
                                                   ( current_word_1 | cmd_offset );

  // Prepare next word address.
  generate
    if ( C_FAMILY == "rtl" || C_M_AXI_REGISTER ) begin : USE_RTL_CURR_WORD
      reg  [C_M_AXI_BYTES_LOG-1:0]    current_word_q;
      reg                             first_word_q;
      reg  [C_M_AXI_BYTES_LOG-1:0]    pre_next_word_q;
    
      always @ (posedge ACLK) begin
        if (ARESET) begin
          first_word_q    <= 1'b1;
          current_word_q  <= {C_M_AXI_BYTES_LOG{1'b0}};
          pre_next_word_q <= {C_M_AXI_BYTES_LOG{1'b0}};
        end else begin
          if ( pop_si_data ) begin
            if ( S_AXI_WLAST ) begin
              // Prepare for next access.
              first_word_q    <= 1'b1;
            end else begin
              first_word_q    <= 1'b0;
            end
            
            current_word_q  <= next_word;
            pre_next_word_q <= pre_next_word;
          end
        end
      end
      
      assign first_word       = first_word_q;
      assign current_word_1   = current_word_q;
      assign pre_next_word_1  = pre_next_word_q;
      
    end else begin : USE_FPGA_CURR_WORD
      reg                             first_word_cmb;
      wire                            first_word_i;
      wire [C_M_AXI_BYTES_LOG-1:0]    current_word_i;
      wire [C_M_AXI_BYTES_LOG-1:0]    local_pre_next_word_i;
      
      
      always @ *
      begin
          if ( S_AXI_WLAST ) begin
            // Prepare for next access.
            first_word_cmb    = 1'b1;
          end else begin
            first_word_cmb    = 1'b0;
          end
      end
      
      for (bit_cnt = 0; bit_cnt < C_M_AXI_BYTES_LOG ; bit_cnt = bit_cnt + 1) begin : BIT_LANE
        LUT6 # (
         .INIT(64'hCCCA_CCCC_CCCC_CCCC) 
        ) LUT6_current_inst (
        .O(current_word_i[bit_cnt]),          // 6-LUT output (1-bit)
        .I0(next_word[bit_cnt]),              // LUT input (1-bit)
        .I1(current_word_1[bit_cnt]),         // LUT input (1-bit)
        .I2(word_complete_rest_stall),        // LUT input (1-bit)
        .I3(word_complete_next_wrap_stall),   // LUT input (1-bit)
        .I4(cmd_valid),                       // LUT input (1-bit)
        .I5(S_AXI_WVALID)                     // LUT input (1-bit)
        );
            
        FDRE #(
         .INIT(1'b0)                          // Initial value of register (1'b0 or 1'b1)
         ) FDRE_current_inst (
         .Q(current_word_1[bit_cnt]),         // Data output
         .C(ACLK),                            // Clock input
         .CE(1'b1),                           // Clock enable input
         .R(ARESET),                          // Synchronous reset input
         .D(current_word_i[bit_cnt])          // Data input
         );
         
        LUT6 # (
         .INIT(64'hCCCA_CCCC_CCCC_CCCC) 
        ) LUT6_next_inst (
        .O(local_pre_next_word_i[bit_cnt]),   // 6-LUT output (1-bit)
        .I0(pre_next_word[bit_cnt]),          // LUT input (1-bit)
        .I1(pre_next_word_1[bit_cnt]),        // LUT input (1-bit)
        .I2(word_complete_rest_stall),        // LUT input (1-bit)
        .I3(word_complete_next_wrap_stall),   // LUT input (1-bit)
        .I4(cmd_valid),                       // LUT input (1-bit)
        .I5(S_AXI_WVALID)                     // LUT input (1-bit)
        );
            
        FDRE #(
         .INIT(1'b0)                          // Initial value of register (1'b0 or 1'b1)
         ) FDRE_next_inst (
         .Q(pre_next_word_1[bit_cnt]),        // Data output
         .C(ACLK),                            // Clock input
         .CE(1'b1),                           // Clock enable input
         .R(ARESET),                          // Synchronous reset input
         .D(local_pre_next_word_i[bit_cnt])   // Data input
         );
      end // end for bit_cnt
      
      LUT6 # (
       .INIT(64'hCCCA_CCCC_CCCC_CCCC) 
      ) LUT6_first_inst (
      .O(first_word_i),                     // 6-LUT output (1-bit)
      .I0(first_word_cmb),                  // LUT input (1-bit)
      .I1(first_word),                      // LUT input (1-bit)
      .I2(word_complete_rest_stall),        // LUT input (1-bit)
      .I3(word_complete_next_wrap_stall),   // LUT input (1-bit)
      .I4(cmd_valid),                       // LUT input (1-bit)
      .I5(S_AXI_WVALID)                     // LUT input (1-bit)
      );
          
      FDSE #(
       .INIT(1'b1)                    // Initial value of register (1'b0 or 1'b1)
       ) FDSE_first_inst (
       .Q(first_word),                // Data output
       .C(ACLK),                      // Clock input
       .CE(1'b1),                     // Clock enable input
       .S(ARESET),                    // Synchronous reset input
       .D(first_word_i)               // Data input
       );
    end
  endgenerate
  
  // Select command length or counted length.
  always @ *
  begin
    if ( first_mi_word )
      length_counter = cmd_length;
    else
      length_counter = length_counter_1;
  end
  
  generate
    if ( C_FAMILY == "rtl" ) begin : USE_RTL_LENGTH
      reg  [8-1:0]                    length_counter_q;
      reg                             first_mi_word_q;
    
      // Calculate next length counter value.
      assign next_length_counter = length_counter - 1'b1;
      
      // Keep track of burst length.
      always @ (posedge ACLK) begin
        if (ARESET) begin
          first_mi_word_q  <= 1'b1;
          length_counter_q <= 8'b0;
        end else begin
          if ( pop_mi_data_i ) begin
            if ( M_AXI_WLAST_I ) begin
              first_mi_word_q  <= 1'b1;
            end else begin
              first_mi_word_q  <= 1'b0;
            end
          
            length_counter_q <= next_length_counter;
          end
        end
      end
      
      assign first_mi_word    = first_mi_word_q;
      assign length_counter_1 = length_counter_q;
      
    end else begin : USE_FPGA_LENGTH
      wire [8-1:0]  length_counter_i;
      wire [8-1:0]  length_counter_ii;
      wire [8-1:0]  length_sel;
      wire [8-1:0]  length_di;
      wire [8:0]    length_local_carry;
      
      // Assign input to local vectors.
      assign length_local_carry[0] = 1'b0;
    
      for (bit_cnt = 0; bit_cnt < 8 ; bit_cnt = bit_cnt + 1) begin : BIT_LANE

        LUT6_2 # (
         .INIT(64'h333C_555A_FFF0_FFF0) 
        ) LUT6_length_inst (
        .O6(length_sel[bit_cnt]),           // 6/5-LUT output (1-bit)
        .O5(length_di[bit_cnt]),            // 5-LUT output (1-bit)
        .I0(length_counter_1[bit_cnt]),     // LUT input (1-bit)
        .I1(cmd_length[bit_cnt]),           // LUT input (1-bit)
        .I2(1'b1),                          // LUT input (1-bit)
        .I3(1'b1),                          // LUT input (1-bit)
        .I4(first_mi_word),                 // LUT input (1-bit)
        .I5(1'b1)                           // LUT input (1-bit)
        );
        
        MUXCY carry_inst 
        (
         .O (length_local_carry[bit_cnt+1]), 
         .CI (length_local_carry[bit_cnt]), 
         .DI (length_di[bit_cnt]), 
         .S (length_sel[bit_cnt])
        ); 
        
        XORCY xorcy_inst 
        (
         .O(length_counter_ii[bit_cnt]),
         .CI(length_local_carry[bit_cnt]),
         .LI(length_sel[bit_cnt])
        );
        
        LUT4 # (
         .INIT(16'hCCCA) 
        ) LUT4_inst (
        .O(length_counter_i[bit_cnt]),    // 5-LUT output (1-bit)
        .I0(length_counter_1[bit_cnt]),     // LUT input (1-bit)
        .I1(length_counter_ii[bit_cnt]),  // LUT input (1-bit)
        .I2(word_complete_rest_pop),      // LUT input (1-bit)
        .I3(word_complete_next_wrap_pop)  // LUT input (1-bit)
        );
        
        FDRE #(
         .INIT(1'b0)                    // Initial value of register (1'b0 or 1'b1)
         ) FDRE_length_inst (
         .Q(length_counter_1[bit_cnt]), // Data output
         .C(ACLK),                      // Clock input
         .CE(1'b1),                     // Clock enable input
         .R(ARESET),                    // Synchronous reset input
         .D(length_counter_i[bit_cnt])  // Data input
         );
         
      end // end for bit_cnt
      
      wire first_mi_word_i;
      
      LUT6 # (
       .INIT(64'hAAAC_AAAC_AAAC_AAAC) 
      ) LUT6_first_mi_inst (
      .O(first_mi_word_i),                // 6-LUT output (1-bit)
      .I0(M_AXI_WLAST_I),                 // LUT input (1-bit)
      .I1(first_mi_word),                 // LUT input (1-bit)
      .I2(word_complete_rest_pop),        // LUT input (1-bit)
      .I3(word_complete_next_wrap_pop),   // LUT input (1-bit)
      .I4(1'b1),                          // LUT input (1-bit)
      .I5(1'b1)                           // LUT input (1-bit)
      );
          
      FDSE #(
       .INIT(1'b1)                    // Initial value of register (1'b0 or 1'b1)
       ) FDSE_inst (
       .Q(first_mi_word),             // Data output
       .C(ACLK),                      // Clock input
       .CE(1'b1),                     // Clock enable input
       .S(ARESET),                    // Synchronous reset input
       .D(first_mi_word_i)            // Data input
       );
      
    end
  endgenerate
  
  generate
    if ( C_FAMILY == "rtl" ) begin : USE_RTL_LAST_WORD
      // Detect last beat in a burst.
      assign last_beat = ( length_counter == 8'b0 );
      
      // Determine if this last word that shall be assembled into this MI-side word.
      assign last_word = ( cmd_modified & last_beat & ( current_word == cmd_last_word ) );
      
    end else begin : USE_FPGA_LAST_WORD
      wire last_beat_curr_word;
      
      generic_baseblocks_v2_1_0_comparator_sel_static #
        (
         .C_FAMILY(C_FAMILY),
         .C_VALUE(8'b0),
         .C_DATA_WIDTH(8)
         ) last_beat_inst
        (
         .CIN(1'b1),
         .S(first_mi_word),
         .A(length_counter_1),
         .B(cmd_length),
         .COUT(last_beat)
         );
      
      generic_baseblocks_v2_1_0_comparator_sel #
        (
         .C_FAMILY(C_FAMILY),
         .C_DATA_WIDTH(C_M_AXI_BYTES_LOG)
         ) last_beat_curr_word_inst
        (
         .CIN(last_beat),
         .S(sel_first_word),
         .A(current_word_1),
         .B(cmd_first_word),
         .V(cmd_last_word),
         .COUT(last_beat_curr_word)
         );
      
      generic_baseblocks_v2_1_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) last_word_inst
        (
         .CIN(last_beat_curr_word),
         .S(cmd_modified),
         .COUT(last_word)
         );

    end
  endgenerate
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Handle wrap buffer:
  //
  // The wrap buffer is used to move data around in an unaligned WRAP 
  // transaction. SI-side data word(s) for an unaligned accesses are delay 
  // to be packed with with the tail of the transaction to make it a WRAP
  // transaction that is aligned to native MI-side data with.
  // For example: an 32bit to 64bit write upsizing @ 0x4 will delay the first 
  // word until the 0x0 data arrives in the last data beat. This will make the 
  // Upsized transaction be WRAP at 0x8 on the MI-side 
  // (was WRAP @ 0x4 on SI-side).
  // 
  /////////////////////////////////////////////////////////////////////////////
  
  // The unaligned SI-side words are pushed into the wrap buffer.
  assign store_in_wrap_buffer_enabled   = cmd_packed_wrap & ~wrap_buffer_available & cmd_valid;
  assign store_in_wrap_buffer           = store_in_wrap_buffer_enabled & S_AXI_WVALID;
  assign ARESET_or_store_in_wrap_buffer = store_in_wrap_buffer | ARESET;
  // The wrap buffer is used to complete last word.
  generate
    if ( C_FAMILY == "rtl" ) begin : USE_RTL_USE_WRAP
      assign use_wrap_buffer      = wrap_buffer_available & last_word;
      
    end else begin : USE_FPGA_USE_WRAP
      wire last_word_carry;  
    
      carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) last_word_inst2
        (
         .CIN(last_word),
         .S(1'b1),
         .COUT(last_word_carry)
         );

      carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) last_word_inst3
        (
         .CIN(last_word_carry),
         .S(1'b1),
         .COUT(last_word_extra_carry)
         );

      carry_latch_and #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_next_wrap_stall_inst
        (
         .CIN(last_word_carry),
         .I(wrap_buffer_available),
         .O(use_wrap_buffer)
         );
    end
  endgenerate
  
  // Wrap buffer becomes available when the unaligned wrap words has been taken care of.
  always @ (posedge ACLK) begin
    if (ARESET) begin
      wrap_buffer_available <= 1'b0;
    end else begin
      if ( store_in_wrap_buffer & word_completed ) begin
        wrap_buffer_available <= 1'b1;
      end else if ( cmd_ready_i ) begin
        wrap_buffer_available <= 1'b0;
      end
    end
  end
  
    /////////////////////////////////////////////////////////////////////////////
  // Pack multiple data SI-side words into fewer MI-side data word.
  // Data is only packed when modify is set. Granularity is SI-side word for 
  // the combinatorial data mux.
  //
  // Expander:
  // WDATA is expanded to all SI-word lane on the MI-side.
  // WSTRB is activted to the correct SI-word lane on the MI-side.
  //
  // Packer:
  // The WDATA and WSTRB registers are always cleared before a new word is 
  // assembled.
  // WDATA is (SI-side word granularity)
  //  * Combinatorial WDATA is used for current word line or when expanding.
  //  * All other is taken from registers.
  // WSTRB is
  //  * Combinatorial for single data to matching word lane
  //  * Zero for single data to mismatched word lane
  //  * Register data when multiple data
  // 
  // To support sub-sized packing during Always Pack is the combinatorial 
  // information packed with "or" instead of multiplexing.
  //
  /////////////////////////////////////////////////////////////////////////////
  
  // Determine if expander data should be used.
  assign use_expander_data = ~cmd_modified & cmd_valid;
  
  // Registers and combinatorial data word mux.
  generate
    for (word_cnt = 0; word_cnt < C_RATIO ; word_cnt = word_cnt + 1) begin : WORD_LANE
      
      // Generate select signal per SI-side word.
      if ( C_RATIO == 1 ) begin : SINGLE_WORD
        assign current_word_idx[word_cnt] = 1'b1;
      end else begin : MULTIPLE_WORD
        assign current_word_idx[word_cnt] = current_word_adjusted[C_M_AXI_BYTES_LOG-C_RATIO_LOG +: C_RATIO_LOG] == word_cnt;
      end
      
      if ( ( C_PACKING_LEVEL == C_NEVER_PACK ) ) begin : USE_EXPANDER
        // Expander only functionality.
      
        if ( C_M_AXI_REGISTER ) begin : USE_REGISTER
            
          always @ (posedge ACLK) begin
            if (ARESET) begin
              M_AXI_WDATA_I[word_cnt*C_S_AXI_DATA_WIDTH   +: C_S_AXI_DATA_WIDTH]    = {C_S_AXI_DATA_WIDTH{1'b0}};
              M_AXI_WSTRB_I[word_cnt*C_S_AXI_DATA_WIDTH/8 +: C_S_AXI_DATA_WIDTH/8]  = {C_S_AXI_DATA_WIDTH/8{1'b0}};
            end else begin
              if ( pop_si_data ) begin
                M_AXI_WDATA_I[word_cnt*C_S_AXI_DATA_WIDTH   +: C_S_AXI_DATA_WIDTH] = S_AXI_WDATA;
            
                // Multiplex write strobe.
                if ( current_word_idx[word_cnt] ) begin
                  // Combinatorial for last word to MI-side (only word for single).
                  M_AXI_WSTRB_I[word_cnt*C_S_AXI_DATA_WIDTH/8 +: C_S_AXI_DATA_WIDTH/8] = S_AXI_WSTRB;
                end else begin
                  // Use registered strobes. Registers are zero until valid data is written.
                  // I.e. zero when used for mismatched lanes while expanding.
                  M_AXI_WSTRB_I[word_cnt*C_S_AXI_DATA_WIDTH/8 +: C_S_AXI_DATA_WIDTH/8] = {C_S_AXI_DATA_WIDTH/8{1'b0}};
                end
              end
            end
          end
          
        end else begin : NO_REGISTER
          always @ *
          begin
            M_AXI_WDATA_I[word_cnt*C_S_AXI_DATA_WIDTH   +: C_S_AXI_DATA_WIDTH] = S_AXI_WDATA;
          
            // Multiplex write strobe.
            if ( current_word_idx[word_cnt] ) begin
              // Combinatorial for last word to MI-side (only word for single).
              M_AXI_WSTRB_I[word_cnt*C_S_AXI_DATA_WIDTH/8 +: C_S_AXI_DATA_WIDTH/8] = S_AXI_WSTRB;
            end else begin
              // Use registered strobes. Registers are zero until valid data is written.
              // I.e. zero when used for mismatched lanes while expanding.
              M_AXI_WSTRB_I[word_cnt*C_S_AXI_DATA_WIDTH/8 +: C_S_AXI_DATA_WIDTH/8] = {C_S_AXI_DATA_WIDTH/8{1'b0}};
            end
          end
          
        end // end if C_M_AXI_REGISTER
        
      end else begin : USE_ALWAYS_PACKER
        // Packer functionality
      
        for (byte_cnt = 0; byte_cnt < C_S_AXI_DATA_WIDTH / 8 ; byte_cnt = byte_cnt + 1) begin : BYTE_LANE
        
          if ( C_FAMILY == "rtl" ) begin : USE_RTL_DATA
            // Generate extended write data and strobe in wrap buffer.
            always @ (posedge ACLK) begin
              if (ARESET) begin
                wdata_wrap_buffer_q[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8] <= 8'b0;
                wstrb_wrap_buffer_q[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1] <= 1'b0;
              end else begin
                if ( cmd_ready_i ) begin
                  wdata_wrap_buffer_q[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8] <= 8'b0;
                  wstrb_wrap_buffer_q[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1] <= 1'b0;
                end else if ( current_word_idx[word_cnt] & store_in_wrap_buffer & S_AXI_WSTRB[byte_cnt] ) begin
                  wdata_wrap_buffer_q[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8] <= S_AXI_WDATA[byte_cnt*8 +: 8];
                  wstrb_wrap_buffer_q[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1] <= S_AXI_WSTRB[byte_cnt];
                end
              end
            end
            
            assign wdata_wrap_buffer[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8] = 
                                    wdata_wrap_buffer_q[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8];
            assign wstrb_wrap_buffer[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1] = 
                                    wstrb_wrap_buffer_q[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1];
            
            if ( C_M_AXI_REGISTER ) begin : USE_REGISTER
              
              always @ (posedge ACLK) begin
                if (ARESET) begin
                  M_AXI_WDATA_I[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8] <= 8'b0;
                  M_AXI_WSTRB_I[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1] <= 1'b0;
                end else begin
                  if ( ( current_word_idx[word_cnt] & S_AXI_WSTRB[byte_cnt] | use_expander_data ) & pop_si_data & ~store_in_wrap_buffer ) begin
                    M_AXI_WDATA_I[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8] <= S_AXI_WDATA[byte_cnt*8 +: 8];
                  end else if ( use_wrap_buffer & pop_si_data &
                                wstrb_wrap_buffer[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1] ) begin
                    M_AXI_WDATA_I[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8] <= wdata_wrap_buffer[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8];
                  end else if ( pop_mi_data ) begin
                    M_AXI_WDATA_I[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8] <= 8'b0;
                  end
                  
                  if ( current_word_idx[word_cnt] & S_AXI_WSTRB[byte_cnt] & pop_si_data & ~store_in_wrap_buffer ) begin
                    M_AXI_WSTRB_I[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1] <= S_AXI_WSTRB[byte_cnt];
                  end else if ( use_wrap_buffer & pop_si_data &
                                wstrb_wrap_buffer[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1] ) begin
                    M_AXI_WSTRB_I[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1] <= 1'b1;
                  end else if ( pop_mi_data ) begin
                    M_AXI_WSTRB_I[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1] <= 1'b0;
                  end
                end
              end
              
            end else begin : NO_REGISTER
              
              // Generate extended write data and strobe.
              always @ (posedge ACLK) begin
                if (ARESET) begin
                  wdata_buffer_q[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8] <= 8'b0;
                  wstrb_buffer_q[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1] <= 1'b0;
                end else begin
                  if ( pop_mi_data | store_in_wrap_buffer_enabled ) begin
                    wdata_buffer_q[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8] <= 8'b0;
                    wstrb_buffer_q[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1] <= 1'b0;
                  end else if ( current_word_idx[word_cnt] & pop_si_data & S_AXI_WSTRB[byte_cnt] ) begin
                    wdata_buffer_q[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8] <= S_AXI_WDATA[byte_cnt*8 +: 8];
                    wstrb_buffer_q[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1] <= S_AXI_WSTRB[byte_cnt];
                  end
                end
              end
              
              assign wdata_buffer[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8] = 
                                 wdata_buffer_q[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8];
              assign wstrb_buffer[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1] = 
                                 wstrb_buffer_q[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1];
              
              // Select packed or extended data.
              always @ *
              begin
                // Multiplex data.
                if ( ( current_word_idx[word_cnt] & S_AXI_WSTRB[byte_cnt] ) | use_expander_data ) begin
                  wdata_last_word_mux[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8] = S_AXI_WDATA[byte_cnt*8 +: 8];
                end else begin
                  wdata_last_word_mux[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8] = 8'b0;
                end
              
                // Multiplex write strobe.
                if ( current_word_idx[word_cnt] ) begin
                  // Combinatorial for last word to MI-side (only word for single).
                  wstrb_last_word_mux[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1] = S_AXI_WSTRB[byte_cnt];
                end else begin
                  // Use registered strobes. Registers are zero until valid data is written.
                  // I.e. zero when used for mismatched lanes while expanding.
                  wstrb_last_word_mux[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1] = 1'b0;
                end
              end
              
              // Merge previous with current data.
              always @ *
              begin
                M_AXI_WSTRB_I[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1] = 
                                (        wstrb_buffer[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1] ) | 
                                ( wstrb_last_word_mux[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1] ) | 
                                (   wstrb_wrap_buffer[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1] & use_wrap_buffer );
                                
                M_AXI_WDATA_I[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8] = 
                                (        wdata_buffer[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8] ) | 
                                ( wdata_last_word_mux[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8] ) |
                                (   wdata_wrap_buffer[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8] & {8{use_wrap_buffer}} );
              end
              
            end // end if C_M_AXI_REGISTER
          end else begin : USE_FPGA_DATA
          
            always @ *
            begin
              if ( cmd_ready_i ) begin
                wdata_wrap_buffer_cmb[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8] = 8'b0;
                wstrb_wrap_buffer_cmb[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1] = 1'b0;
              end else if ( current_word_idx[word_cnt] & store_in_wrap_buffer & S_AXI_WSTRB[byte_cnt] ) begin
                wdata_wrap_buffer_cmb[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8] = S_AXI_WDATA[byte_cnt*8 +: 8];
                wstrb_wrap_buffer_cmb[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1] = S_AXI_WSTRB[byte_cnt];
              end else begin
                wdata_wrap_buffer_cmb[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8] = 
                                      wdata_wrap_buffer[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8];
                wstrb_wrap_buffer_cmb[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1] = 
                                      wstrb_wrap_buffer[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1];
              end
            end
            
            for (bit_cnt = 0; bit_cnt < 8 ; bit_cnt = bit_cnt + 1) begin : BIT_LANE
              FDRE #(
               .INIT(1'b0)             // Initial value of register (1'b0 or 1'b1)
               ) FDRE_wdata_inst (
               .Q(wdata_wrap_buffer[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8+bit_cnt]),    // Data output
               .C(ACLK),                                                                 // Clock input
               .CE(1'b1),                                                                // Clock enable input
               .R(ARESET),                                                               // Synchronous reset input
               .D(wdata_wrap_buffer_cmb[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8+bit_cnt]) // Data input
               );
              
            end // end for bit_cnt
            
            FDRE #(
             .INIT(1'b0)             // Initial value of register (1'b0 or 1'b1)
             ) FDRE_wstrb_inst (
             .Q(wstrb_wrap_buffer[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt]),      // Data output
             .C(ACLK),                                                           // Clock input
             .CE(1'b1),                                                          // Clock enable input
             .R(ARESET),                                                         // Synchronous reset input
             .D(wstrb_wrap_buffer_cmb[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt])   // Data input
             );
             
            if ( C_M_AXI_REGISTER ) begin : USE_REGISTER
            
              assign wdata_qualifier[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt] = ( current_word_idx[word_cnt] & S_AXI_WSTRB[byte_cnt] | use_expander_data ) & pop_si_data & ~store_in_wrap_buffer_enabled;
              assign wstrb_qualifier[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt] = current_word_idx[word_cnt] & S_AXI_WSTRB[byte_cnt] & pop_si_data & ~store_in_wrap_buffer_enabled;
            
              assign wrap_qualifier[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt]  = use_wrap_buffer & pop_si_data &
                                                                               wstrb_wrap_buffer[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1];
            
              for (bit_cnt = 0; bit_cnt < 8 ; bit_cnt = bit_cnt + 1) begin : BIT_LANE
                    
                LUT6 # (
                 .INIT(64'hF0F0_F0F0_CCCC_00AA) 
                ) LUT6_data_inst (
                .O(M_AXI_WDATA_cmb[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8+bit_cnt]),    // 6-LUT output (1-bit)
                .I0(M_AXI_WDATA_q[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8+bit_cnt]),     // LUT input (1-bit)
                .I1(wdata_wrap_buffer[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8+bit_cnt]), // LUT input (1-bit)
                .I2(S_AXI_WDATA[byte_cnt*8+bit_cnt]),                                   // LUT input (1-bit)
                .I3(pop_mi_data),                                                       // LUT input (1-bit)
                .I4(wrap_qualifier[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt]),            // LUT input (1-bit)
                .I5(wdata_qualifier[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt])            // LUT input (1-bit)
                );
                    
                FDRE #(
                 .INIT(1'b0)             // Initial value of register (1'b0 or 1'b1)
                 ) FDRE_wdata_inst (
                 .Q(M_AXI_WDATA_q[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8+bit_cnt]),     // Data output
                 .C(ACLK),                                                              // Clock input
                 .CE(1'b1),                                                             // Clock enable input
                 .R(ARESET),                                                            // Synchronous reset input
                 .D(M_AXI_WDATA_cmb[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8+bit_cnt])    // Data input
                 );
                
              end // end for bit_cnt
              
              LUT6 # (
               .INIT(64'hF0F0_F0F0_CCCC_00AA) 
              ) LUT6_strb_inst (
              .O(M_AXI_WSTRB_cmb[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt]),            // 6-LUT output (1-bit)
              .I0(M_AXI_WSTRB_q[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt]),             // LUT input (1-bit)
              .I1(wrap_qualifier[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt]),            // LUT input (1-bit)
              .I2(S_AXI_WSTRB[byte_cnt]),                                             // LUT input (1-bit)
              .I3(pop_mi_data),                                                       // LUT input (1-bit)
              .I4(wrap_qualifier[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt]),            // LUT input (1-bit)
              .I5(wstrb_qualifier[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt])            // LUT input (1-bit)
              );
            
              FDRE #(
               .INIT(1'b0)             // Initial value of register (1'b0 or 1'b1)
               ) FDRE_wstrb_inst (
               .Q(M_AXI_WSTRB_q[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt]),     // Data output
               .C(ACLK),                                                      // Clock input
               .CE(1'b1),                                                     // Clock enable input
               .R(ARESET),                                                    // Synchronous reset input
               .D(M_AXI_WSTRB_cmb[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt])    // Data input
               );
               
              always @ * 
              begin
                M_AXI_WDATA_I[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8] = M_AXI_WDATA_q[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8];
                M_AXI_WSTRB_I[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1] = M_AXI_WSTRB_q[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1];
              end
              
            end else begin : NO_REGISTER
            
              assign wdata_qualifier[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt]  = current_word_idx[word_cnt] & cmd_valid & S_AXI_WSTRB[byte_cnt];
            
              assign wstrb_qualifier[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt]  = current_word_idx[word_cnt] & 
                                                                                S_AXI_WSTRB[byte_cnt] & 
                                                                                cmd_valid & S_AXI_WVALID;
              
              for (bit_cnt = 0; bit_cnt < 8 ; bit_cnt = bit_cnt + 1) begin : BIT_LANE
                LUT6 # (
                 .INIT(64'hCCCA_CCCC_CCCC_CCCC) 
                ) LUT6_data_inst (
                .O(wdata_buffer_i[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8+bit_cnt]),   // 6-LUT output (1-bit)
                .I0(S_AXI_WDATA[byte_cnt*8+bit_cnt]),                                 // LUT input (1-bit)
                .I1(wdata_buffer[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8+bit_cnt]),    // LUT input (1-bit)
                .I2(word_complete_rest_stall),                                        // LUT input (1-bit)
                .I3(word_complete_next_wrap_stall),                                   // LUT input (1-bit)
                .I4(wdata_qualifier[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt]),         // LUT input (1-bit)
                .I5(S_AXI_WVALID)                                                     // LUT input (1-bit)
                );
                    
                FDRE #(
                 .INIT(1'b0)             // Initial value of register (1'b0 or 1'b1)
                 ) FDRE_wdata_inst (
                 .Q(wdata_buffer[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8+bit_cnt]),    // Data output
                 .C(ACLK),                                                            // Clock input
                 .CE(1'b1),                                                           // Clock enable input
                 .R(ARESET),                                                          // Synchronous reset input
                 .D(wdata_buffer_i[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8+bit_cnt])   // Data input
                 );
                
              end // end for bit_cnt
              
              LUT6 # (
               .INIT(64'h0000_0000_0000_AAAE) 
              ) LUT6_strb_inst (
              .O(wstrb_buffer_i[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt]),     // 6-LUT output (1-bit)
              .I0(wstrb_buffer[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt]),      // LUT input (1-bit)
              .I1(wstrb_qualifier[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt]),   // LUT input (1-bit)
              .I2(word_complete_rest_stall),                                  // LUT input (1-bit)
              .I3(word_complete_next_wrap_stall),                             // LUT input (1-bit)
              .I4(word_complete_rest_pop),                                    // LUT input (1-bit)
              .I5(word_complete_next_wrap_pop)                                // LUT input (1-bit)
              );
              
              FDRE #(
               .INIT(1'b0)             // Initial value of register (1'b0 or 1'b1)
               ) FDRE_wstrb_inst (
               .Q(wstrb_buffer[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt]),      // Data output
               .C(ACLK),                                                      // Clock input
               .CE(1'b1),                                                     // Clock enable input
               .R(ARESET_or_store_in_wrap_buffer),                            // Synchronous reset input
               .D(wstrb_buffer_i[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt])     // Data input
               );
              
              // Select packed or extended data.
              always @ *
              begin
                // Multiplex data.
                if ( ( current_word_idx[word_cnt] & S_AXI_WSTRB[byte_cnt] ) | use_expander_data ) begin
                  wdata_last_word_mux[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8] = S_AXI_WDATA[byte_cnt*8 +: 8];
                end else begin
                  wdata_last_word_mux[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8] = 
                                (        wdata_buffer[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8] & {8{wstrb_buffer[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt]}} ) | 
                                (   wdata_wrap_buffer[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8] & {8{use_wrap_buffer}} );
                end
              
                // Multiplex write strobe.
                if ( current_word_idx[word_cnt] ) begin
                  // Combinatorial for last word to MI-side (only word for single).
                  wstrb_last_word_mux[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1] = S_AXI_WSTRB[byte_cnt] |
                                (        wstrb_buffer[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt] ) | 
                                (   wstrb_wrap_buffer[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1] & use_wrap_buffer );
                end else begin
                  // Use registered strobes. Registers are zero until valid data is written.
                  // I.e. zero when used for mismatched lanes while expanding.
                  wstrb_last_word_mux[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1] = 
                                (        wstrb_buffer[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt] ) | 
                                (   wstrb_wrap_buffer[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1] & use_wrap_buffer );
                end
              end
              
              // Merge previous with current data.
              always @ *
              begin
                M_AXI_WSTRB_I[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1] = 
                                ( wstrb_last_word_mux[word_cnt*C_S_AXI_DATA_WIDTH/8+byte_cnt +: 1] );
                                
                M_AXI_WDATA_I[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8] = 
                                ( wdata_last_word_mux[word_cnt*C_S_AXI_DATA_WIDTH+byte_cnt*8 +: 8] );
              end
              
            end // end if C_M_AXI_REGISTER
          end // end if C_FAMILY
        end // end for byte_cnt
      end // end if USE_ALWAYS_PACKER
    end // end for word_cnt
  endgenerate
      
  
  /////////////////////////////////////////////////////////////////////////////
  // MI-side output handling
  /////////////////////////////////////////////////////////////////////////////
  
  generate
    if ( C_M_AXI_REGISTER ) begin : USE_REGISTER
      reg                             M_AXI_WLAST_q;
      reg                             M_AXI_WVALID_q = 1'b0;
    
      // Register MI-side Data.
      always @ (posedge ACLK) begin
        if (ARESET) begin
          M_AXI_WLAST_q     <= 1'b0;
          M_AXI_WVALID_q    <= 1'b0;
          
        end else begin
          if ( M_AXI_WREADY_I ) begin
            M_AXI_WLAST_q     <= M_AXI_WLAST_I;
            M_AXI_WVALID_q    <= M_AXI_WVALID_I;
          end
          
        end
      end
      
      assign M_AXI_WDATA    = M_AXI_WDATA_I;
      assign M_AXI_WSTRB    = M_AXI_WSTRB_I;
      assign M_AXI_WLAST    = M_AXI_WLAST_q;
      assign M_AXI_WVALID   = M_AXI_WVALID_q;
      assign M_AXI_WREADY_I = ( M_AXI_WVALID_q & M_AXI_WREADY) | ~M_AXI_WVALID_q;
      
      // Get MI-side data.
      assign pop_mi_data_i  = M_AXI_WVALID_I & M_AXI_WREADY_I;
      assign pop_mi_data    = M_AXI_WVALID_q & M_AXI_WREADY_I;
      
      // Detect when MI-side is stalling.
      assign mi_stalling    = ( M_AXI_WVALID_q & ~M_AXI_WREADY_I ) & ~store_in_wrap_buffer_enabled;
                          
    end else begin : NO_REGISTER
    
      // Combinatorial MI-side Data.
      assign M_AXI_WDATA    = M_AXI_WDATA_I;
      assign M_AXI_WSTRB    = M_AXI_WSTRB_I;
      assign M_AXI_WLAST    = M_AXI_WLAST_I;
      assign M_AXI_WVALID   = M_AXI_WVALID_I;
      assign M_AXI_WREADY_I = M_AXI_WREADY;
      
      // Get MI-side data.
      if ( C_FAMILY == "rtl" ) begin : USE_RTL_POP_MI
        assign pop_mi_data_i  = M_AXI_WVALID_I & M_AXI_WREADY_I;
        
      end else begin : USE_FPGA_POP_MI
        
        assign pop_mi_data_i  = ( word_complete_next_wrap_pop | word_complete_rest_pop);
                             
      end
      assign pop_mi_data    = pop_mi_data_i;
      
      // Detect when MI-side is stalling.
      assign mi_stalling    = word_completed_qualified & ~M_AXI_WREADY_I;
                          
    end
  endgenerate
  
  
endmodule


// -- (c) Copyright 2012 Xilinx, Inc. All rights reserved.
// --
// -- This file contains confidential and proprietary information
// -- of Xilinx, Inc. and is protected under U.S. and 
// -- international copyright and other intellectual property
// -- laws.
// --
// -- DISCLAIMER
// -- This disclaimer is not a license and does not grant any
// -- rights to the materials distributed herewith. Except as
// -- otherwise provided in a valid license issued to you by
// -- Xilinx, and to the maximum extent permitted by applicable
// -- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// -- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// -- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// -- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// -- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// -- (2) Xilinx shall not be liable (whether in contract or tort,
// -- including negligence, or under any other theory of
// -- liability) for any loss or damage of any kind or nature
// -- related to, arising under or in connection with these
// -- materials, including for any direct, or any indirect,
// -- special, incidental, or consequential loss or damage
// -- (including loss of data, profits, goodwill, or any type of
// -- loss or damage suffered as a result of any action brought
// -- by a third party) even if such damage or loss was
// -- reasonably foreseeable or Xilinx had been advised of the
// -- possibility of the same.
// --
// -- CRITICAL APPLICATIONS
// -- Xilinx products are not designed or intended to be fail-
// -- safe, or for use in any application requiring fail-safe
// -- performance, such as life-support or safety devices or
// -- systems, Class III medical devices, nuclear facilities,
// -- applications related to the deployment of airbags, or any
// -- other applications that could lead to death, personal
// -- injury, or severe property or environmental damage
// -- (individually and collectively, "Critical
// -- Applications"). Customer assumes the sole risk and
// -- liability of any use of Xilinx products in Critical
// -- Applications, subject only to applicable laws and
// -- regulations governing limitations on product liability.
// --
// -- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// -- PART OF THIS FILE AT ALL TIMES.
//-----------------------------------------------------------------------------
//
// Description: Write Data Up-Sizer with Packet FIFO
//
//--------------------------------------------------------------------------
`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_dwidth_converter_v2_1_12_w_upsizer_pktfifo #
  (
   parameter         C_FAMILY                         = "virtex7", 
                       // FPGA Family. Current version: virtex6 or spartan6.
   parameter integer C_S_AXI_DATA_WIDTH               = 64,
                       // Width of s_axi_wdata and s_axi_rdata.
                       // Range: 32, 64, 128, 256, 512, 1024.
   parameter integer C_M_AXI_DATA_WIDTH               = 32,
                       // Width of m_axi_wdata and m_axi_rdata. 
                       // Assume always >= than C_S_AXI_DATA_WIDTH.
                       // Range: 32, 64, 128, 256, 512, 1024.
   parameter integer C_AXI_ADDR_WIDTH                 = 32, 
   parameter         C_CLK_CONV         = 1'b0,
   parameter integer C_S_AXI_ACLK_RATIO = 1,     // Clock frequency ratio of SI w.r.t. MI.
                                                 // Range = [1..16].
   parameter integer C_M_AXI_ACLK_RATIO = 2,     // Clock frequency ratio of MI w.r.t. SI.
                                                 // Range = [2..16] if C_S_AXI_ACLK_RATIO = 1; else must be 1.
   parameter integer C_AXI_IS_ACLK_ASYNC = 0,    // Indicates whether S and M clocks are asynchronous.
                                                 // FUTURE FEATURE
                                                 // Range = [0, 1].
   parameter integer C_S_AXI_BYTES_LOG                = 3,
                       // Log2 of number of 32bit word on SI-side.
   parameter integer C_M_AXI_BYTES_LOG                = 3,
                       // Log2 of number of 32bit word on MI-side.
   parameter integer C_RATIO                          = 2,
                       // Up-Sizing ratio for data.
   parameter integer C_RATIO_LOG                      = 1,
                       // Log2 of Up-Sizing ratio for data.
   parameter integer C_SYNCHRONIZER_STAGE             = 3
   )
  (
   // Global Signals
   input  wire                              S_AXI_ACLK,
   input  wire                              M_AXI_ACLK,
   input  wire                              S_AXI_ARESETN,
   input  wire                              M_AXI_ARESETN,

   // Command Interface
   input  wire [C_AXI_ADDR_WIDTH-1:0]       cmd_si_addr,
   input  wire [8-1:0]                      cmd_si_len,
   input  wire [3-1:0]                      cmd_si_size,
   input  wire [2-1:0]                      cmd_si_burst,
   output wire                              cmd_ready,
   
   // Slave Interface Write Address Port
   input  wire [C_AXI_ADDR_WIDTH-1:0]          S_AXI_AWADDR,
   input  wire [8-1:0]                         S_AXI_AWLEN,
   input  wire [3-1:0]                         S_AXI_AWSIZE,
   input  wire [2-1:0]                         S_AXI_AWBURST,
   input  wire [2-1:0]                         S_AXI_AWLOCK,
   input  wire [4-1:0]                         S_AXI_AWCACHE,
   input  wire [3-1:0]                         S_AXI_AWPROT,
   input  wire [4-1:0]                         S_AXI_AWREGION,
   input  wire [4-1:0]                         S_AXI_AWQOS,
   input  wire                                 S_AXI_AWVALID,
   output wire                                 S_AXI_AWREADY,

   // Master Interface Write Address Port
   output wire [C_AXI_ADDR_WIDTH-1:0]          M_AXI_AWADDR,
   output wire [8-1:0]                         M_AXI_AWLEN,
   output wire [3-1:0]                         M_AXI_AWSIZE,
   output wire [2-1:0]                         M_AXI_AWBURST,
   output wire [2-1:0]                         M_AXI_AWLOCK,
   output wire [4-1:0]                         M_AXI_AWCACHE,
   output wire [3-1:0]                         M_AXI_AWPROT,
   output wire [4-1:0]                         M_AXI_AWREGION,
   output wire [4-1:0]                         M_AXI_AWQOS,
   output wire                                 M_AXI_AWVALID,
   input  wire                                 M_AXI_AWREADY,

   // Slave Interface Write Data Ports
   input  wire [C_S_AXI_DATA_WIDTH-1:0]     S_AXI_WDATA,
   input  wire [C_S_AXI_DATA_WIDTH/8-1:0]   S_AXI_WSTRB,
   input  wire                              S_AXI_WLAST,
   input  wire                              S_AXI_WVALID,
   output wire                              S_AXI_WREADY,

   // Master Interface Write Data Ports
   output wire [C_M_AXI_DATA_WIDTH-1:0]     M_AXI_WDATA,
   output wire [C_M_AXI_DATA_WIDTH/8-1:0]   M_AXI_WSTRB,
   output wire                              M_AXI_WLAST,
   output wire                              M_AXI_WVALID,
   input  wire                              M_AXI_WREADY,
   
   input wire                               SAMPLE_CYCLE_EARLY,
   input wire                               SAMPLE_CYCLE

   );

  localparam integer P_SI_BYTES = C_S_AXI_DATA_WIDTH / 8;
  localparam integer P_MI_BYTES = C_M_AXI_DATA_WIDTH / 8;
  localparam integer P_MAX_BYTES = 1024 / 8;
  localparam integer P_SI_SIZE = f_ceil_log2(P_SI_BYTES);
  localparam integer P_MI_SIZE = f_ceil_log2(P_MI_BYTES);
  localparam integer P_RATIO = C_M_AXI_DATA_WIDTH / C_S_AXI_DATA_WIDTH;
  localparam integer P_RATIO_LOG = f_ceil_log2(P_RATIO);
  localparam integer P_NUM_BUF = (P_RATIO > 16) ? 32 : (P_RATIO * 2);
  localparam integer P_NUM_BUF_LOG = f_ceil_log2(P_NUM_BUF);
  localparam integer P_AWFIFO_TRESHOLD = P_NUM_BUF - 2;
  localparam integer P_M_WBUFFER_WIDTH = P_MI_BYTES * 9;
  localparam integer P_M_WBUFFER_DEPTH = 512;
  localparam integer P_M_WBUFFER_DEPTH_LOG = 9;
  localparam integer P_M_WBUFFER_WORDS = P_M_WBUFFER_DEPTH / P_NUM_BUF;
  localparam integer P_M_WBUFFER_WORDS_LOG = f_ceil_log2(P_M_WBUFFER_WORDS);
  localparam integer P_MAX_RBUFFER_BYTES_LOG = f_ceil_log2((P_M_WBUFFER_DEPTH / 4) * P_MAX_BYTES);
  localparam [1:0] P_INCR = 2'b01, P_WRAP = 2'b10, P_FIXED = 2'b00;
  localparam [1:0] S_IDLE = 2'b00, S_WRITING = 2'b01, S_AWFULL = 2'b11;
  localparam [2:0] M_IDLE = 3'b000, M_ISSUE1 = 3'b001, M_WRITING1 = 3'b011, M_AW_STALL = 3'b010, M_AW_DONE1 = 3'b110, M_ISSUE2 = 3'b111, M_WRITING2 = 3'b101, M_AW_DONE2 = 3'b100;
  localparam  P_SI_LT_MI = (C_S_AXI_ACLK_RATIO < C_M_AXI_ACLK_RATIO);
  localparam integer P_ACLK_RATIO = P_SI_LT_MI ? (C_M_AXI_ACLK_RATIO / C_S_AXI_ACLK_RATIO) : (C_S_AXI_ACLK_RATIO / C_M_AXI_ACLK_RATIO);
  localparam integer P_AWFIFO_WIDTH = 29 + C_AXI_ADDR_WIDTH + P_MI_SIZE;
  localparam integer P_COMMON_CLOCK = (C_CLK_CONV & C_AXI_IS_ACLK_ASYNC) ? 0 : 1;
  
  reg  S_AXI_WREADY_i = 1'b0;
  reg  M_AXI_AWVALID_i = 1'b0;
  wire [C_AXI_ADDR_WIDTH-1:0] M_AXI_AWADDR_i;
  wire [7:0] M_AXI_AWLEN_i;
  wire [2:0] M_AXI_AWSIZE_i;
  wire [1:0] M_AXI_AWBURST_i;
  wire M_AXI_AWLOCK_i;
  reg  M_AXI_WVALID_i = 1'b0;
  reg  M_AXI_WLAST_i;
  wire S_AXI_AWLOCK_i;
  reg  aw_push;
  wire push_ready;
  wire aw_ready;
  reg  load_si_ptr;
  reg  [1:0] si_state = S_IDLE;
  reg  [1:0] si_state_ns;
  reg  S_AXI_WREADY_ns;
  reg  aw_pop;
  reg  aw_pop_extend;
  wire aw_pop_event;
  wire aw_pop_resync;
  reg  cmd_ready_i;
  wire si_buf_en;
  reg  [P_NUM_BUF_LOG-1:0] si_buf;
  reg  [P_NUM_BUF_LOG-1:0] buf_cnt;
  reg  [P_M_WBUFFER_WORDS_LOG-1:0] si_ptr;
  reg  [1:0] si_burst;
  reg  [2:0] si_size;
  reg  [P_SI_BYTES-1:0] si_be;
  wire [P_MI_BYTES-1:0] si_we;
  reg  [P_SI_BYTES-1:0] si_wrap_be_next;
  reg  [P_MI_SIZE-P_SI_SIZE-1:0] si_word;
  reg  [P_MI_SIZE-P_SI_SIZE-1:0] si_wrap_word_next;
  reg  [3:0] si_wrap_cnt;
  reg  [2:0] mi_state = M_IDLE;
  reg  [2:0] mi_state_ns;
  reg  M_AXI_AWVALID_ns;
  reg  M_AXI_WVALID_ns;
  reg  load_mi_ptr;
  reg  load_mi_next;
  reg  load_mi_d1;
  reg  load_mi_d2;
  reg  first_load_mi_d1;
  wire mi_w_done;
  reg  mi_last;
  reg  mi_last_d1;
  reg  next_valid;
  reg  [P_NUM_BUF_LOG-1:0] mi_buf;
  reg  [P_M_WBUFFER_WORDS_LOG-1:0] mi_ptr;
  reg  [7:0] mi_wcnt;
  wire mi_buf_en;
  wire mi_awvalid;
  reg  [1:0] mi_burst;
  reg  [2:0] mi_size;
  reg  [P_MI_BYTES-1:0] mi_be;
  reg  [P_MI_BYTES-1:0] mi_be_d1;
  reg  [P_MI_BYTES-1:0] mi_wstrb_mask_d2;
  reg  [P_MI_BYTES-1:0] mi_wrap_be_next;
  reg  [P_MI_SIZE-1:0] mi_addr;
  reg  [P_MI_SIZE-1:0] mi_addr_d1;
  wire [P_MI_SIZE-1:0] si_last_index;
  wire [P_MI_SIZE-1:0] si_last_index_reg;
  wire [P_MI_SIZE-1:0] mi_last_index_reg;
  reg  [P_MI_SIZE-1:0] mi_last_index_reg_d0;
  reg  [P_MI_SIZE-1:0] mi_last_index_reg_d1;
  reg  [P_MI_SIZE-1:0] next_mi_last_index_reg;
  reg  mi_first;
  reg  mi_first_d1;
  reg  [3:0] mi_wrap_cnt;
  reg  [7:0] next_mi_len;
  reg  [1:0] next_mi_burst;
  reg  [2:0] next_mi_size;
  reg  [P_MI_SIZE+4-1:0] next_mi_addr;
  wire [P_M_WBUFFER_WIDTH-1:0] si_wpayload;
  wire [P_M_WBUFFER_WIDTH-1:0] mi_wpayload;
  wire [P_M_WBUFFER_DEPTH_LOG-1:0] si_buf_addr;
  wire [P_M_WBUFFER_DEPTH_LOG-1:0] mi_buf_addr;
  wire s_awvalid_reg;
  wire s_awready_reg;
  wire [C_AXI_ADDR_WIDTH-1:0] s_awaddr_reg;
  wire [7:0] s_awlen_reg;
  wire [2:0] s_awsize_reg;
  wire [1:0] s_awburst_reg;
  wire s_awlock_reg;
  wire [3:0] s_awcache_reg;
  wire [2:0] s_awprot_reg;
  wire [3:0] s_awqos_reg;
  wire [3:0] s_awregion_reg;
  
  wire m_aclk;
  wire m_aresetn;
  wire s_aresetn;
  wire aw_fifo_s_aclk;
  wire aw_fifo_m_aclk;
  wire aw_fifo_aresetn;
  wire awpop_reset;
  wire s_sample_cycle;
  wire s_sample_cycle_early;
  wire m_sample_cycle;
  wire m_sample_cycle_early;
  wire fast_aclk;
  reg  fast_aresetn_r = 1'b0;
  
  function integer f_ceil_log2
    (
     input integer x
     );
    integer acc;
    begin
      acc=0;
      while ((2**acc) < x)
        acc = acc + 1;
      f_ceil_log2 = acc;
    end
  endfunction

  // Byte-enable pattern, for a full SI data-width transfer, at the given starting address.
  function [P_SI_BYTES-1:0] f_si_be_init
    (
      input [P_SI_SIZE-1:0] addr,
      input [2:0] size
    );
    integer i;
    reg [P_MAX_RBUFFER_BYTES_LOG-1:0] addr_i;
    begin
      addr_i = addr;
      for (i=0; i<P_SI_BYTES; i=i+1) begin
        case (P_SI_SIZE)
          2: case (size[1:0])
            2'h0: f_si_be_init[i] = addr_i[ 1 :  0] == i[ 1 :  0];
            2'h1: f_si_be_init[i] = addr_i[ 1 :  1] == i[ 1 :  1];
            default: f_si_be_init[i] = 1'b1;
          endcase
          3: case (size[1:0])
            2'h0: f_si_be_init[i] = addr_i[ 2 :  0] == i[ 2 :  0];
            2'h1: f_si_be_init[i] = addr_i[ 2 :  1] == i[ 2 :  1];
            2'h2: f_si_be_init[i] = addr_i[ 2 :  2] == i[ 2 :  2];
            default: f_si_be_init[i] = 1'b1;
          endcase
          4: case (size)
            3'h0: f_si_be_init[i] = addr_i[ 3 :  0] == i[ 3 :  0];
            3'h1: f_si_be_init[i] = addr_i[ 3 :  1] == i[ 3 :  1];
            3'h2: f_si_be_init[i] = addr_i[ 3 :  2] == i[ 3 :  2];
            3'h3: f_si_be_init[i] = addr_i[ 3 :  3] == i[ 3 :  3];
            default: f_si_be_init[i] = 1'b1;
          endcase
          5: case (size)
            3'h0: f_si_be_init[i] = addr_i[ 4 :  0] == i[ 4 :  0];
            3'h1: f_si_be_init[i] = addr_i[ 4 :  1] == i[ 4 :  1];
            3'h2: f_si_be_init[i] = addr_i[ 4 :  2] == i[ 4 :  2];
            3'h3: f_si_be_init[i] = addr_i[ 4 :  3] == i[ 4 :  3];
            3'h4: f_si_be_init[i] = addr_i[ 4 :  4] == i[ 4 :  4];
            default: f_si_be_init[i] = 1'b1;
          endcase
          6: case (size)
            3'h0: f_si_be_init[i] = addr_i[ 5 :  0] == i[ 5 :  0];
            3'h1: f_si_be_init[i] = addr_i[ 5 :  1] == i[ 5 :  1];
            3'h2: f_si_be_init[i] = addr_i[ 5 :  2] == i[ 5 :  2];
            3'h3: f_si_be_init[i] = addr_i[ 5 :  3] == i[ 5 :  3];
            3'h4: f_si_be_init[i] = addr_i[ 5 :  4] == i[ 5 :  4];
            3'h5: f_si_be_init[i] = addr_i[ 5 :  5] == i[ 5 :  5];
            default: f_si_be_init[i] = 1'b1;
          endcase
        endcase
      end
    end
  endfunction
 
  // Byte-enable pattern, for a full MI data-width transfer, at the given starting address.
  function [P_MI_BYTES-1:0] f_mi_be_init
    (
      input [P_MI_SIZE-1:0] addr,
      input [2:0] size
    );
    integer i;
    reg [P_MAX_RBUFFER_BYTES_LOG-1:0] addr_i;
    begin
      addr_i = addr;
      for (i=0; i<P_MI_BYTES; i=i+1) begin
        case (P_MI_SIZE)
          3: case (size)
            3'h0: f_mi_be_init[i] = addr_i[ 2 :  0] == i[ 2 :  0];
            3'h1: f_mi_be_init[i] = addr_i[ 2 :  1] == i[ 2 :  1];
            3'h2: f_mi_be_init[i] = addr_i[ 2 :  2] == i[ 2 :  2];
            default: f_mi_be_init[i] = 1'b1;  // Fully-packed
          endcase
          4: case (size)
            3'h0: f_mi_be_init[i] = addr_i[ 3 :  0] == i[ 3 :  0];
            3'h1: f_mi_be_init[i] = addr_i[ 3 :  1] == i[ 3 :  1];
            3'h2: f_mi_be_init[i] = addr_i[ 3 :  2] == i[ 3 :  2];
            3'h3: f_mi_be_init[i] = addr_i[ 3 :  3] == i[ 3 :  3];
            default: f_mi_be_init[i] = 1'b1;
          endcase
          5: case (size)
            3'h0: f_mi_be_init[i] = addr_i[ 4 :  0] == i[ 4 :  0];
            3'h1: f_mi_be_init[i] = addr_i[ 4 :  1] == i[ 4 :  1];
            3'h2: f_mi_be_init[i] = addr_i[ 4 :  2] == i[ 4 :  2];
            3'h3: f_mi_be_init[i] = addr_i[ 4 :  3] == i[ 4 :  3];
            3'h4: f_mi_be_init[i] = addr_i[ 4 :  4] == i[ 4 :  4];
            default: f_mi_be_init[i] = 1'b1;
          endcase
          6: case (size)
            3'h0: f_mi_be_init[i] = addr_i[ 5 :  0] == i[ 5 :  0];
            3'h1: f_mi_be_init[i] = addr_i[ 5 :  1] == i[ 5 :  1];
            3'h2: f_mi_be_init[i] = addr_i[ 5 :  2] == i[ 5 :  2];
            3'h3: f_mi_be_init[i] = addr_i[ 5 :  3] == i[ 5 :  3];
            3'h4: f_mi_be_init[i] = addr_i[ 5 :  4] == i[ 5 :  4];
            3'h5: f_mi_be_init[i] = addr_i[ 5 :  5] == i[ 5 :  5];
            default: f_mi_be_init[i] = 1'b1;
          endcase
          7: case (size)
            3'h0: f_mi_be_init[i] = addr_i[ 6 :  0] == i[ 6 :  0];
            3'h1: f_mi_be_init[i] = addr_i[ 6 :  1] == i[ 6 :  1];
            3'h2: f_mi_be_init[i] = addr_i[ 6 :  2] == i[ 6 :  2];
            3'h3: f_mi_be_init[i] = addr_i[ 6 :  3] == i[ 6 :  3];
            3'h4: f_mi_be_init[i] = addr_i[ 6 :  4] == i[ 6 :  4];
            3'h5: f_mi_be_init[i] = addr_i[ 6 :  5] == i[ 6 :  5];
            3'h6: f_mi_be_init[i] = addr_i[ 6 :  6] == i[ 6 :  6];
            default: f_mi_be_init[i] = 1'b1;
          endcase
        endcase
      end
    end
  endfunction
 
  // Byte-enable mask for the first fully-packed MI transfer (mask off ragged-head burst).
  function [P_MI_BYTES-1:0] f_mi_be_first_mask
    (
      input [P_MI_SIZE-1:0] addr
    );
    integer i;
    begin
      for (i=0; i<P_MI_BYTES; i=i+1) begin
        f_mi_be_first_mask[i] = (i >= {1'b0, addr});
      end
    end
  endfunction
 
  // Index of last byte written in last MI transfer.
  function [P_MI_SIZE-1:0] f_mi_be_last_index
    (
      input [P_MI_SIZE-1:0] addr,
      input [2:0] size,
      input [7:0] len,
      input [1:0] burst
    );
    reg [P_MI_SIZE-1:0] bytes;
    reg [P_MI_SIZE-1:0] mask;
    begin
      case (P_SI_SIZE)
        2: case (size)
          3'h0:    begin bytes =  len       ; mask =    1'b0  ; end
          3'h1:    begin bytes = {len, 1'b0}; mask = {1{1'b1}}; end
          3'h2:    begin bytes = {len, 2'b0}; mask = {2{1'b1}}; end
        endcase
        3: case (size)
          3'h0:    begin bytes =  len       ; mask =    1'b0  ; end
          3'h1:    begin bytes = {len, 1'b0}; mask = {1{1'b1}}; end
          3'h2:    begin bytes = {len, 2'b0}; mask = {2{1'b1}}; end
          3'h3:    begin bytes = {len, 3'b0}; mask = {3{1'b1}}; end
        endcase
        4: case (size)
          3'h0:    begin bytes =  len       ; mask =    1'b0  ; end
          3'h1:    begin bytes = {len, 1'b0}; mask = {1{1'b1}}; end
          3'h2:    begin bytes = {len, 2'b0}; mask = {2{1'b1}}; end
          3'h3:    begin bytes = {len, 3'b0}; mask = {3{1'b1}}; end
          3'h4:    begin bytes = {len, 4'b0}; mask = {4{1'b1}}; end
        endcase
        5: case (size)
          3'h0:    begin bytes =  len       ; mask =    1'b0  ; end
          3'h1:    begin bytes = {len, 1'b0}; mask = {1{1'b1}}; end
          3'h2:    begin bytes = {len, 2'b0}; mask = {2{1'b1}}; end
          3'h3:    begin bytes = {len, 3'b0}; mask = {3{1'b1}}; end
          3'h4:    begin bytes = {len, 4'b0}; mask = {4{1'b1}}; end
          3'h5:    begin bytes = {len, 5'b0}; mask = {5{1'b1}}; end
        endcase
        6: case (size)
          3'h0:    begin bytes =  len       ; mask =    1'b0  ; end
          3'h1:    begin bytes = {len, 1'b0}; mask = {1{1'b1}}; end
          3'h2:    begin bytes = {len, 2'b0}; mask = {2{1'b1}}; end
          3'h3:    begin bytes = {len, 3'b0}; mask = {3{1'b1}}; end
          3'h4:    begin bytes = {len, 4'b0}; mask = {4{1'b1}}; end
          3'h5:    begin bytes = {len, 5'b0}; mask = {5{1'b1}}; end
          3'h6:    begin bytes = {len, 6'b0}; mask = {6{1'b1}}; end
        endcase
      endcase

      case (burst)
        P_INCR:
          f_mi_be_last_index = (addr + bytes) | mask;
        P_WRAP:
          f_mi_be_last_index = addr | bytes | mask;
        P_FIXED:
          f_mi_be_last_index = {P_MI_SIZE{1'b1}};
      endcase
    end
  endfunction
 
  // Byte-enable mask for the last fully-packed MI transfer (mask off ragged-tail burst).
  function [P_MI_BYTES-1:0] f_mi_be_last_mask
    (
      input [P_MI_SIZE-1:0] index
    );
    integer i;
    begin
      for (i=0; i<P_MI_BYTES; i=i+1) begin
        f_mi_be_last_mask[i] = (i <= {1'b0, index});
      end
    end
  endfunction
 
  // Byte-enable pattern, within the SI data-width, of the transfer at the wrap boundary.
  function [P_SI_BYTES-1:0] f_si_wrap_be
    (
      input [P_SI_SIZE-1:0] addr,
      input [2:0] size,
      input [7:0] len
    );
    integer i;
    reg [P_MAX_RBUFFER_BYTES_LOG-1:0] addr_i;
    begin
      addr_i = addr;
      for (i=0; i<P_SI_BYTES; i=i+1) begin
        case (P_SI_SIZE)
          2: case (size[1:0])
            2'h0:    f_si_wrap_be[i] =                                                                                   len[1] ? (            2'b0  == i[1:0]) : ({addr_i[1:1], 1'b0} == i[1:0]);
            2'h1:    f_si_wrap_be[i] =                                                                                                                            (            1'b0  == i[1:1]);
            default: f_si_wrap_be[i] = 1'b1;
          endcase
          3: case (size[1:0])
            2'h0:    f_si_wrap_be[i] =                                          len[2] ? (            3'b0  == i[2:0]) : len[1] ? ({addr_i[2:2], 2'b0} == i[2:0]) : ({addr_i[2:1], 1'b0} == i[2:0]);
            2'h1:    f_si_wrap_be[i] =                                                                                   len[1] ? (            2'b0  == i[2:1]) : ({addr_i[2:2], 1'b0} == i[2:1]);
            2'h2:    f_si_wrap_be[i] =                                                                                                                            (            1'b0  == i[2:2]);
            default: f_si_wrap_be[i] = 1'b1;
          endcase
          4: case (size)
            3'h0:    f_si_wrap_be[i] = len[3] ? (            4'b0  == i[3:0]) : len[2] ? ({addr_i[3:3], 3'b0} == i[3:0]) : len[1] ? ({addr_i[3:2], 2'b0} == i[3:0]) : ({addr_i[3:1], 1'b0} == i[3:0]);
            3'h1:    f_si_wrap_be[i] =                                          len[2] ? (            3'b0  == i[3:1]) : len[1] ? ({addr_i[3:3], 2'b0} == i[3:1]) : ({addr_i[3:2], 1'b0} == i[3:1]);
            3'h2:    f_si_wrap_be[i] =                                                                                   len[1] ? (            2'b0  == i[3:2]) : ({addr_i[3:3], 1'b0} == i[3:2]);
            3'h3:    f_si_wrap_be[i] =                                                                                                                            (            1'b0  == i[3:3]);
            default: f_si_wrap_be[i] = 1'b1;
          endcase
          5: case (size)
            3'h0:    f_si_wrap_be[i] = len[3] ? ({addr_i[4:4], 4'b0} == i[4:0]) : len[2] ? ({addr_i[4:3], 3'b0} == i[4:0]) : len[1] ? ({addr_i[4:2], 2'b0} == i[4:0]) : ({addr_i[4:1], 1'b0} == i[4:0]);
            3'h1:    f_si_wrap_be[i] = len[3] ? (            4'b0  == i[4:1]) : len[2] ? ({addr_i[4:4], 3'b0} == i[4:1]) : len[1] ? ({addr_i[4:3], 2'b0} == i[4:1]) : ({addr_i[4:2], 1'b0} == i[4:1]);
            3'h2:    f_si_wrap_be[i] =                                          len[2] ? (            3'b0  == i[4:2]) : len[1] ? ({addr_i[4:4], 2'b0} == i[4:2]) : ({addr_i[4:3], 1'b0} == i[4:2]);
            3'h3:    f_si_wrap_be[i] =                                                                                   len[1] ? (            2'b0  == i[4:3]) : ({addr_i[4:4], 1'b0} == i[4:3]);
            3'h4:    f_si_wrap_be[i] =                                                                                                                            (            1'b0  == i[4:4]);
            default: f_si_wrap_be[i] = 1'b1;
          endcase
          6: case (size)
            3'h0:    f_si_wrap_be[i] = len[3] ? ({addr_i[5:4], 4'b0} == i[5:0]) : len[2] ? ({addr_i[5:3], 3'b0} == i[5:0]) : len[1] ? ({addr_i[5:2], 2'b0} == i[5:0]) : ({addr_i[5:1], 1'b0} == i[5:0]);
            3'h1:    f_si_wrap_be[i] = len[3] ? ({addr_i[5:5], 4'b0} == i[5:1]) : len[2] ? ({addr_i[5:4], 3'b0} == i[5:1]) : len[1] ? ({addr_i[5:3], 2'b0} == i[5:1]) : ({addr_i[5:2], 1'b0} == i[5:1]);
            3'h2:    f_si_wrap_be[i] = len[3] ? (            4'b0  == i[5:2]) : len[2] ? ({addr_i[5:5], 3'b0} == i[5:2]) : len[1] ? ({addr_i[5:4], 2'b0} == i[5:2]) : ({addr_i[5:3], 1'b0} == i[5:2]);
            3'h3:    f_si_wrap_be[i] =                                          len[2] ? (            3'b0  == i[5:3]) : len[1] ? ({addr_i[5:5], 2'b0} == i[5:3]) : ({addr_i[5:4], 1'b0} == i[5:3]);
            3'h4:    f_si_wrap_be[i] =                                                                                   len[1] ? (            2'b0  == i[5:4]) : ({addr_i[5:5], 1'b0} == i[5:4]);
            3'h5:    f_si_wrap_be[i] =                                                                                                                            (            1'b0  == i[5:5]);
            default: f_si_wrap_be[i] = 1'b1;
          endcase
        endcase
      end
    end
  endfunction
 
  // Byte-enable pattern, within the MI data-width, of the transfer at the wrap boundary.
  function [P_MI_BYTES-1:0] f_mi_wrap_be
    (
      input [P_MI_SIZE-1:0] addr,
      input [2:0] size,
      input [7:0] len
    );
    integer i;
    reg [P_MAX_RBUFFER_BYTES_LOG-1:0] addr_i;
    begin
      addr_i = addr;
      for (i=0; i<P_MI_BYTES; i=i+1) begin
        case (P_MI_SIZE)
          3: case (size)
            3'h0:    f_mi_wrap_be[i] =                                          len[2] ? (            3'b0  == i[2:0]) : len[1] ? ({addr_i[2:2], 2'b0} == i[2:0]) : ({addr_i[2:1], 1'b0} == i[2:0]);
            3'h1:    f_mi_wrap_be[i] =                                                                                   len[1] ? (            2'b0  == i[2:1]) : ({addr_i[2:2], 1'b0} == i[2:1]);
            3'h2:    f_mi_wrap_be[i] =                                                                                                                            (            1'b0  == i[2:2]);
            default: f_mi_wrap_be[i] = 1'b1;
          endcase
          4: case (size)
            3'h0:    f_mi_wrap_be[i] = len[3] ? (            4'b0  == i[3:0]) : len[2] ? ({addr_i[3:3], 3'b0} == i[3:0]) : len[1] ? ({addr_i[3:2], 2'b0} == i[3:0]) : ({addr_i[3:1], 1'b0} == i[3:0]);
            3'h1:    f_mi_wrap_be[i] =                                          len[2] ? (            3'b0  == i[3:1]) : len[1] ? ({addr_i[3:3], 2'b0} == i[3:1]) : ({addr_i[3:2], 1'b0} == i[3:1]);
            3'h2:    f_mi_wrap_be[i] =                                                                                   len[1] ? (            2'b0  == i[3:2]) : ({addr_i[3:3], 1'b0} == i[3:2]);
            3'h3:    f_mi_wrap_be[i] =                                                                                                                            (            1'b0  == i[3:3]);
            default: f_mi_wrap_be[i] = 1'b1;
          endcase
          5: case (size)
            3'h0:    f_mi_wrap_be[i] = len[3] ? ({addr_i[4:4], 4'b0} == i[4:0]) : len[2] ? ({addr_i[4:3], 3'b0} == i[4:0]) : len[1] ? ({addr_i[4:2], 2'b0} == i[4:0]) : ({addr_i[4:1], 1'b0} == i[4:0]);
            3'h1:    f_mi_wrap_be[i] = len[3] ? (            4'b0  == i[4:1]) : len[2] ? ({addr_i[4:4], 3'b0} == i[4:1]) : len[1] ? ({addr_i[4:3], 2'b0} == i[4:1]) : ({addr_i[4:2], 1'b0} == i[4:1]);
            3'h2:    f_mi_wrap_be[i] =                                          len[2] ? (            3'b0  == i[4:2]) : len[1] ? ({addr_i[4:4], 2'b0} == i[4:2]) : ({addr_i[4:3], 1'b0} == i[4:2]);
            3'h3:    f_mi_wrap_be[i] =                                                                                   len[1] ? (            2'b0  == i[4:3]) : ({addr_i[4:4], 1'b0} == i[4:3]);
            3'h4:    f_mi_wrap_be[i] =                                                                                                                            (            1'b0  == i[4:4]);
            default: f_mi_wrap_be[i] = 1'b1;
          endcase
          6: case (size)
            3'h0:    f_mi_wrap_be[i] = len[3] ? ({addr_i[5:4], 4'b0} == i[5:0]) : len[2] ? ({addr_i[5:3], 3'b0} == i[5:0]) : len[1] ? ({addr_i[5:2], 2'b0} == i[5:0]) : ({addr_i[5:1], 1'b0} == i[5:0]);
            3'h1:    f_mi_wrap_be[i] = len[3] ? ({addr_i[5:5], 4'b0} == i[5:1]) : len[2] ? ({addr_i[5:4], 3'b0} == i[5:1]) : len[1] ? ({addr_i[5:3], 2'b0} == i[5:1]) : ({addr_i[5:2], 1'b0} == i[5:1]);
            3'h2:    f_mi_wrap_be[i] = len[3] ? (            4'b0  == i[5:2]) : len[2] ? ({addr_i[5:5], 3'b0} == i[5:2]) : len[1] ? ({addr_i[5:4], 2'b0} == i[5:2]) : ({addr_i[5:3], 1'b0} == i[5:2]);
            3'h3:    f_mi_wrap_be[i] =                                          len[2] ? (            3'b0  == i[5:3]) : len[1] ? ({addr_i[5:5], 2'b0} == i[5:3]) : ({addr_i[5:4], 1'b0} == i[5:3]);
            3'h4:    f_mi_wrap_be[i] =                                                                                   len[1] ? (            2'b0  == i[5:4]) : ({addr_i[5:5], 1'b0} == i[5:4]);
            3'h5:    f_mi_wrap_be[i] =                                                                                                                            (            1'b0  == i[5:5]);
            default: f_mi_wrap_be[i] = 1'b1;
          endcase
          7: case (size)
            3'h0:    f_mi_wrap_be[i] = len[3] ? ({addr_i[6:4], 4'b0} == i[6:0]) : len[2] ? ({addr_i[6:3], 3'b0} == i[6:0]) : len[1] ? ({addr_i[6:2], 2'b0} == i[6:0]) : ({addr_i[6:1], 1'b0} == i[6:0]);
            3'h1:    f_mi_wrap_be[i] = len[3] ? ({addr_i[6:5], 4'b0} == i[6:1]) : len[2] ? ({addr_i[6:4], 3'b0} == i[6:1]) : len[1] ? ({addr_i[6:3], 2'b0} == i[6:1]) : ({addr_i[6:2], 1'b0} == i[6:1]);
            3'h2:    f_mi_wrap_be[i] = len[3] ? ({addr_i[6:6], 4'b0} == i[6:2]) : len[2] ? ({addr_i[6:5], 3'b0} == i[6:2]) : len[1] ? ({addr_i[6:4], 2'b0} == i[6:2]) : ({addr_i[6:3], 1'b0} == i[6:2]);
            3'h3:    f_mi_wrap_be[i] = len[3] ? (            4'b0  == i[6:3]) : len[2] ? ({addr_i[6:6], 3'b0} == i[6:3]) : len[1] ? ({addr_i[6:5], 2'b0} == i[6:3]) : ({addr_i[6:4], 1'b0} == i[6:3]);
            3'h4:    f_mi_wrap_be[i] =                                          len[2] ? (            3'b0  == i[6:4]) : len[1] ? ({addr_i[6:6], 2'b0} == i[6:4]) : ({addr_i[6:5], 1'b0} == i[6:4]);
            3'h5:    f_mi_wrap_be[i] =                                                                                   len[1] ? (            2'b0  == i[6:5]) : ({addr_i[6:6], 1'b0} == i[6:5]);
            3'h6:    f_mi_wrap_be[i] =                                                                                                                            (            1'b0  == i[6:6]);
            default: f_mi_wrap_be[i] = 1'b1;
          endcase
        endcase
      end
    end
  endfunction
 
  // Number of SI transfers until wrapping (0 = wrap after first transfer; 4'hF = no wrapping)
  function [3:0] f_si_wrap_cnt
    (
      input [(P_MI_SIZE+4-1):0] addr,
      input [2:0] size,
      input [7:0] len
    );
    reg [3:0] start;
    reg [P_MAX_RBUFFER_BYTES_LOG-1:0] addr_i;
    begin
      addr_i = addr;
      case (P_SI_SIZE)
        2: case (size[1:0])
          2'h0:    start = addr_i[ 0 +: 4];
          2'h1:    start = addr_i[ 1 +: 4];
          default: start = addr_i[ 2 +: 4];
        endcase
        3: case (size[1:0])
          2'h0:    start = addr_i[ 0 +: 4];
          2'h1:    start = addr_i[ 1 +: 4];
          2'h2:    start = addr_i[ 2 +: 4];
          default: start = addr_i[ 3 +: 4];
        endcase
        4: case (size)
          3'h0:    start = addr_i[ 0 +: 4];
          3'h1:    start = addr_i[ 1 +: 4];
          3'h2:    start = addr_i[ 2 +: 4];
          3'h3:    start = addr_i[ 3 +: 4];
          default: start = addr_i[ 4 +: 4];
        endcase
        5: case (size)
          3'h0:    start = addr_i[ 0 +: 4];
          3'h1:    start = addr_i[ 1 +: 4];
          3'h2:    start = addr_i[ 2 +: 4];
          3'h3:    start = addr_i[ 3 +: 4];
          3'h4:    start = addr_i[ 4 +: 4];
          default: start = addr_i[ 5 +: 4];
        endcase
        6: case (size)
          3'h0:    start = addr_i[ 0 +: 4];
          3'h1:    start = addr_i[ 1 +: 4];
          3'h2:    start = addr_i[ 2 +: 4];
          3'h3:    start = addr_i[ 3 +: 4];
          3'h4:    start = addr_i[ 4 +: 4];
          3'h5:    start = addr_i[ 5 +: 4];
          default: start = addr_i[ 6 +: 4];
        endcase
      endcase
      f_si_wrap_cnt = {len[3:1], 1'b1} & ~start;
    end
  endfunction
 
  // Number of MI transfers until wrapping (0 = wrap after first transfer; 4'hF = no wrapping)
  function [3:0] f_mi_wrap_cnt
    (
      input [(P_MI_SIZE+4-1):0] addr,
      input [2:0] size,
      input [7:0] len
    );
    reg [3:0] start;
    reg [P_MAX_RBUFFER_BYTES_LOG-1:0] addr_i;
    begin
      addr_i = addr;
      case (P_MI_SIZE)
        3: case (size)
          3'h0:    start = addr_i[ 0 +: 4];
          3'h1:    start = addr_i[ 1 +: 4];
          3'h2:    start = addr_i[ 2 +: 4];
          default: start = addr_i[ 3 +: 4];
        endcase
        4: case (size)
          3'h0:    start = addr_i[ 0 +: 4];
          3'h1:    start = addr_i[ 1 +: 4];
          3'h2:    start = addr_i[ 2 +: 4];
          3'h3:    start = addr_i[ 3 +: 4];
          default: start = addr_i[ 4 +: 4];
        endcase
        5: case (size)
          3'h0:    start = addr_i[ 0 +: 4];
          3'h1:    start = addr_i[ 1 +: 4];
          3'h2:    start = addr_i[ 2 +: 4];
          3'h3:    start = addr_i[ 3 +: 4];
          3'h4:    start = addr_i[ 4 +: 4];
          default: start = addr_i[ 5 +: 4];
        endcase
        6: case (size)
          3'h0:    start = addr_i[ 0 +: 4];
          3'h1:    start = addr_i[ 1 +: 4];
          3'h2:    start = addr_i[ 2 +: 4];
          3'h3:    start = addr_i[ 3 +: 4];
          3'h4:    start = addr_i[ 4 +: 4];
          3'h5:    start = addr_i[ 5 +: 4];
          default: start = addr_i[ 6 +: 4];
        endcase
        7: case (size)
          3'h0:    start = addr_i[ 0 +: 4];
          3'h1:    start = addr_i[ 1 +: 4];
          3'h2:    start = addr_i[ 2 +: 4];
          3'h3:    start = addr_i[ 3 +: 4];
          3'h4:    start = addr_i[ 4 +: 4];
          3'h5:    start = addr_i[ 5 +: 4];
          3'h6:    start = addr_i[ 6 +: 4];
          default: start = addr_i[ 7 +: 4];
        endcase
      endcase
      f_mi_wrap_cnt = {len[3:1], 1'b1} & ~start;
    end
  endfunction
 
  // Mask of address bits used to point to buffer line (MI data-width) of first SI wrap transfer.
  function [2:0] f_si_wrap_mask
    (
      input [2:0] size,
      input [7:0] len
    );
    begin
      case (P_RATIO_LOG)
        1: case (P_SI_SIZE)
          6: case (size)
            3'h6:    f_si_wrap_mask = len[3:1];
            3'h5:    f_si_wrap_mask = len[3:2];
            3'h4:    f_si_wrap_mask = len[3:3];
            default: f_si_wrap_mask = 0    ;
          endcase
          5: case (size)
            3'h5:    f_si_wrap_mask = len[3:1];
            3'h4:    f_si_wrap_mask = len[3:2];
            3'h3:    f_si_wrap_mask = len[3:3];
            default: f_si_wrap_mask = 0    ;
          endcase
          4: case (size)
            3'h4:    f_si_wrap_mask = len[3:1];
            3'h3:    f_si_wrap_mask = len[3:2];
            3'h2:    f_si_wrap_mask = len[3:3];
            default: f_si_wrap_mask = 0    ;
          endcase
          3: case (size[1:0])
            2'h3:    f_si_wrap_mask = len[3:1];
            2'h2:    f_si_wrap_mask = len[3:2];
            2'h1:    f_si_wrap_mask = len[3:3];
            default: f_si_wrap_mask = 0    ;
          endcase
          2: case (size[1:0])
            2'h2:    f_si_wrap_mask = len[3:1];
            2'h1:    f_si_wrap_mask = len[3:2];
            default: f_si_wrap_mask = len[3:3];
          endcase
        endcase
        2: case (P_SI_SIZE)
          5: case (size)
            3'h5:    f_si_wrap_mask = len[3:2];
            3'h4:    f_si_wrap_mask = len[3:3];
            default: f_si_wrap_mask = 0    ;
          endcase
          4: case (size)
            3'h4:    f_si_wrap_mask = len[3:2];
            3'h3:    f_si_wrap_mask = len[3:3];
            default: f_si_wrap_mask = 0    ;
          endcase
          3: case (size[1:0])
            2'h3:    f_si_wrap_mask = len[3:2];
            2'h2:    f_si_wrap_mask = len[3:3];
            default: f_si_wrap_mask = 0    ;
          endcase
          2: case (size[1:0])
            2'h2:    f_si_wrap_mask = len[3:2];
            2'h1:    f_si_wrap_mask = len[3:3];
            default: f_si_wrap_mask = 0    ;
          endcase
        endcase
        3: case (P_SI_SIZE)
          4: case (size)
            3'h4:    f_si_wrap_mask = len[3:3];
            default: f_si_wrap_mask = 0    ;
          endcase
          3: case (size[1:0])
            2'h3:    f_si_wrap_mask = len[3:3];
            default: f_si_wrap_mask = 0    ;
          endcase
          2: case (size[1:0])
            2'h2:    f_si_wrap_mask = len[3:3];
            default: f_si_wrap_mask = 0    ;
          endcase
        endcase
        default: f_si_wrap_mask = 0    ;
      endcase
    end
  endfunction
 
  // Mask of address bits used to point to buffer line of first MI wrap transfer.
  function [2:0] f_mi_wrap_mask
    (
      input [2:0] size,
      input [7:0] len
    );
    begin
      case (P_RATIO_LOG)
        1: case (P_MI_SIZE)
          7: case (size)
            3'h7:    f_mi_wrap_mask = {len[2:1], 1'b1};
            3'h6:    f_mi_wrap_mask = len[3:1];
            3'h5:    f_mi_wrap_mask = len[3:2];
            3'h4:    f_mi_wrap_mask = len[3:3];
            default: f_mi_wrap_mask = 0    ;
          endcase
          6: case (size)
            3'h6:    f_mi_wrap_mask = {len[2:1], 1'b1};
            3'h5:    f_mi_wrap_mask = len[3:1];
            3'h4:    f_mi_wrap_mask = len[3:2];
            3'h3:    f_mi_wrap_mask = len[3:3];
            default: f_mi_wrap_mask = 0    ;
          endcase
          5: case (size)
            3'h5:    f_mi_wrap_mask = {len[2:1], 1'b1};
            3'h4:    f_mi_wrap_mask = len[3:1];
            3'h3:    f_mi_wrap_mask = len[3:2];
            3'h2:    f_mi_wrap_mask = len[3:3];
            default: f_mi_wrap_mask = 0    ;
          endcase
          4: case (size)
            3'h4:    f_mi_wrap_mask = {len[2:1], 1'b1};
            3'h3:    f_mi_wrap_mask = len[3:1];
            3'h2:    f_mi_wrap_mask = len[3:2];
            3'h1:    f_mi_wrap_mask = len[3:3];
            default: f_mi_wrap_mask = 0    ;
          endcase
          3: case (size[1:0])
            2'h3:    f_mi_wrap_mask = {len[2:1], 1'b1};
            2'h2:    f_mi_wrap_mask = len[3:1];
            2'h1:    f_mi_wrap_mask = len[3:2];
            default: f_mi_wrap_mask = len[3:3];
          endcase
        endcase
        2: case (P_MI_SIZE)
          7: case (size)
            3'h7:    f_mi_wrap_mask = {len[1:1], 1'b1};
            3'h5:    f_mi_wrap_mask = len[3:2];
            3'h4:    f_mi_wrap_mask = len[3:3];
            default: f_mi_wrap_mask = 0    ;
          endcase
          6: case (size)
            3'h6:    f_mi_wrap_mask = {len[1:1], 1'b1};
            3'h4:    f_mi_wrap_mask = len[3:2];
            3'h3:    f_mi_wrap_mask = len[3:3];
            default: f_mi_wrap_mask = 0    ;
          endcase
          5: case (size)
            3'h5:    f_mi_wrap_mask = {len[1:1], 1'b1};
            3'h3:    f_mi_wrap_mask = len[3:2];
            3'h2:    f_mi_wrap_mask = len[3:3];
            default: f_mi_wrap_mask = 0    ;
          endcase
          4: case (size)
            3'h4:    f_mi_wrap_mask = {len[1:1], 1'b1};
            3'h2:    f_mi_wrap_mask = len[3:2];
            3'h1:    f_mi_wrap_mask = len[3:3];
            default: f_mi_wrap_mask = 0    ;
          endcase
        endcase
        3: case (P_MI_SIZE)
          7: case (size)
            3'h7:    f_mi_wrap_mask = 1'b1;
            3'h4:    f_mi_wrap_mask = len[3:3];
            default: f_mi_wrap_mask = 0    ;
          endcase
          6: case (size)
            3'h6:    f_mi_wrap_mask = 1'b1;
            3'h3:    f_mi_wrap_mask = len[3:3];
            default: f_mi_wrap_mask = 0    ;
          endcase
          5: case (size)
            3'h5:    f_mi_wrap_mask = 1'b1;
            3'h2:    f_mi_wrap_mask = len[3:3];
            default: f_mi_wrap_mask = 0    ;
          endcase
        endcase
        default: f_mi_wrap_mask = 0    ;
      endcase
    end
  endfunction
 
  // Index of SI transfer within buffer line following wrap
  function [P_MI_SIZE-P_SI_SIZE-1:0] f_si_wrap_word
    (
      input [(P_MI_SIZE+4-1):0] addr,
      input [2:0] size,
      input [7:0] len
    );
    reg [P_MI_SIZE-P_SI_SIZE-1:0] mask;
    begin
      case (P_SI_SIZE)
        2: case (size[1:0])
          3'h2:    mask =  {len[3:1], {1{1'b1}}};
          3'h1:    mask =  len[3:1];
          default: mask =  len[3:2];
        endcase            
        3: case (size)     
          3'h3:    mask =  {len[3:1], {1{1'b1}}};
          3'h2:    mask =  len[3:1];
          3'h1:    mask =  len[3:2];
          default: mask =  len[3:3];
        endcase            
        4: case (size)     
          3'h4:    mask =  {len[3:1], {1{1'b1}}};
          3'h3:    mask =  len[3:1];
          3'h2:    mask =  len[3:2];
          3'h1:    mask =  len[3:3];
          default: mask =  0;
        endcase            
        5: case (size)     
          3'h5:    mask =  {len[3:1], {1{1'b1}}};
          3'h4:    mask =  len[3:1];
          3'h3:    mask =  len[3:2];
          3'h2:    mask =  len[3:3];
          default: mask =  0;
        endcase            
        6: case (size)     
          3'h6:    mask =  {len[3:1], {1{1'b1}}};
          3'h5:    mask =  len[3:1];
          3'h4:    mask =  len[3:2];
          3'h3:    mask =  len[3:3];
          default: mask =  0;
        endcase
      endcase
      f_si_wrap_word = addr[P_MI_SIZE-1 : P_SI_SIZE] & ~mask;
    end
  endfunction
 
  // Complete byte-enable pattern for writing SI data word to buffer (MI data-width).
  function [P_MI_BYTES-1:0] f_si_we
    (
      input [P_RATIO_LOG-1:0] word,  // Index of SI transfer within buffer line
      input [P_SI_BYTES-1:0] be     // Byte-enable pattern within SI transfer (SI data-width)
    );
    integer i;
    begin
      for (i=0; i<P_RATIO; i=i+1) begin
        f_si_we[i*P_SI_BYTES +: P_SI_BYTES] = (i == word) ? be : 0;
      end
    end
  endfunction
 
  // Rotate byte-enable mask around SI-width boundary.
  function [P_SI_BYTES-1:0] f_si_be_rot
    (
      input [P_SI_BYTES-1:0] be,     // Byte-enable pattern within SI transfer (SI data-width)
      input [2:0] size
    );
    reg [63:0] be_i;
    begin
      be_i = be;
      case (P_SI_SIZE)
        2: case (size[1:0])
          2'h0:    f_si_be_rot = {be_i[0 +: ( 4 -  1)], be_i[ 3 -:  1]};
          2'h1:    f_si_be_rot = {be_i[0 +: ( 4 -  2)], be_i[ 3 -:  2]};
          default: f_si_be_rot =  {4{1'b1}};
        endcase
        3: case (size[1:0])
          2'h0:    f_si_be_rot = {be_i[0 +: ( 8 -  1)], be_i[ 7 -:  1]};
          2'h1:    f_si_be_rot = {be_i[0 +: ( 8 -  2)], be_i[ 7 -:  2]};
          2'h2:    f_si_be_rot = {be_i[0 +: ( 8 -  4)], be_i[ 7 -:  4]};
          default: f_si_be_rot =  {8{1'b1}};
        endcase
        4: case (size)
          3'h0:    f_si_be_rot = {be_i[0 +: (16 -  1)], be_i[15 -:  1]};
          3'h1:    f_si_be_rot = {be_i[0 +: (16 -  2)], be_i[15 -:  2]};
          3'h2:    f_si_be_rot = {be_i[0 +: (16 -  4)], be_i[15 -:  4]};
          3'h3:    f_si_be_rot = {be_i[0 +: (16 -  8)], be_i[15 -:  8]};
          default: f_si_be_rot =  {16{1'b1}};
        endcase
        5: case (size)
          3'h0:    f_si_be_rot = {be_i[0 +: (32 -  1)], be_i[31 -:  1]};
          3'h1:    f_si_be_rot = {be_i[0 +: (32 -  2)], be_i[31 -:  2]};
          3'h2:    f_si_be_rot = {be_i[0 +: (32 -  4)], be_i[31 -:  4]};
          3'h3:    f_si_be_rot = {be_i[0 +: (32 -  8)], be_i[31 -:  8]};
          3'h4:    f_si_be_rot = {be_i[0 +: (32 - 16)], be_i[31 -: 16]};
          default: f_si_be_rot =  {32{1'b1}};
        endcase
        6: case (size)
          3'h0:    f_si_be_rot = {be_i[0 +: (64 -  1)], be_i[63 -:  1]};
          3'h1:    f_si_be_rot = {be_i[0 +: (64 -  2)], be_i[63 -:  2]};
          3'h2:    f_si_be_rot = {be_i[0 +: (64 -  4)], be_i[63 -:  4]};
          3'h3:    f_si_be_rot = {be_i[0 +: (64 -  8)], be_i[63 -:  8]};
          3'h4:    f_si_be_rot = {be_i[0 +: (64 - 16)], be_i[63 -: 16]};
          3'h5:    f_si_be_rot = {be_i[0 +: (64 - 32)], be_i[63 -: 32]};
          default: f_si_be_rot =  {64{1'b1}};
        endcase
      endcase
    end
  endfunction
 
  // Rotate byte-enable mask around MI-width boundary.
  function [P_MI_BYTES-1:0] f_mi_be_rot
    (
      input [P_MI_BYTES-1:0] be,     // Byte-enable pattern within MI transfer
      input [2:0] size
    );
    reg [127:0] be_i;
    begin
      be_i = be;
      case (P_MI_SIZE)
        3: case (size)
          3'h0:    f_mi_be_rot = {be_i[0 +: (  8 -  1)], be_i[  7 -:  1]};
          3'h1:    f_mi_be_rot = {be_i[0 +: (  8 -  2)], be_i[  7 -:  2]};
          3'h2:    f_mi_be_rot = {be_i[0 +: (  8 -  4)], be_i[  7 -:  4]};
          default: f_mi_be_rot =  {8{1'b1}};
        endcase
        4: case (size)
          3'h0:    f_mi_be_rot = {be_i[0 +: ( 16 -  1)], be_i[ 15 -:  1]};
          3'h1:    f_mi_be_rot = {be_i[0 +: ( 16 -  2)], be_i[ 15 -:  2]};
          3'h2:    f_mi_be_rot = {be_i[0 +: ( 16 -  4)], be_i[ 15 -:  4]};
          3'h3:    f_mi_be_rot = {be_i[0 +: ( 16 -  8)], be_i[ 15 -:  8]};
          default: f_mi_be_rot =  {16{1'b1}};
        endcase
        5: case (size)
          3'h0:    f_mi_be_rot = {be_i[0 +: ( 32 -  1)], be_i[ 31 -:  1]};
          3'h1:    f_mi_be_rot = {be_i[0 +: ( 32 -  2)], be_i[ 31 -:  2]};
          3'h2:    f_mi_be_rot = {be_i[0 +: ( 32 -  4)], be_i[ 31 -:  4]};
          3'h3:    f_mi_be_rot = {be_i[0 +: ( 32 -  8)], be_i[ 31 -:  8]};
          3'h4:    f_mi_be_rot = {be_i[0 +: ( 32 - 16)], be_i[ 31 -: 16]};
          default: f_mi_be_rot =  {32{1'b1}};
        endcase
        6: case (size)
          3'h0:    f_mi_be_rot = {be_i[0 +: ( 64 -  1)], be_i[ 63 -:  1]};
          3'h1:    f_mi_be_rot = {be_i[0 +: ( 64 -  2)], be_i[ 63 -:  2]};
          3'h2:    f_mi_be_rot = {be_i[0 +: ( 64 -  4)], be_i[ 63 -:  4]};
          3'h3:    f_mi_be_rot = {be_i[0 +: ( 64 -  8)], be_i[ 63 -:  8]};
          3'h4:    f_mi_be_rot = {be_i[0 +: ( 64 - 16)], be_i[ 63 -: 16]};
          3'h5:    f_mi_be_rot = {be_i[0 +: ( 64 - 32)], be_i[ 63 -: 32]};
          default: f_mi_be_rot =  {64{1'b1}};
        endcase
        7: case (size)
          3'h0:    f_mi_be_rot = {be_i[0 +: (128 -  1)], be_i[127 -:  1]};
          3'h1:    f_mi_be_rot = {be_i[0 +: (128 -  2)], be_i[127 -:  2]};
          3'h2:    f_mi_be_rot = {be_i[0 +: (128 -  4)], be_i[127 -:  4]};
          3'h3:    f_mi_be_rot = {be_i[0 +: (128 -  8)], be_i[127 -:  8]};
          3'h4:    f_mi_be_rot = {be_i[0 +: (128 - 16)], be_i[127 -: 16]};
          3'h5:    f_mi_be_rot = {be_i[0 +: (128 - 32)], be_i[127 -: 32]};
          3'h6:    f_mi_be_rot = {be_i[0 +: (128 - 64)], be_i[127 -: 64]};
          default: f_mi_be_rot =  {128{1'b1}};
        endcase
      endcase
    end
  endfunction
 
  function [P_SI_BYTES*9-1:0] f_wpayload
    (
      input [C_S_AXI_DATA_WIDTH-1:0] wdata,
      input [C_S_AXI_DATA_WIDTH/8-1:0] wstrb
    );
    integer i;
    begin
      for (i=0; i<P_SI_BYTES; i=i+1) begin
        f_wpayload[i*9 +: 9] = {wstrb[i], wdata[i*8 +: 8]};
      end
    end
  endfunction
 
  function [C_M_AXI_DATA_WIDTH-1:0] f_wdata
    (
      input [P_MI_BYTES*9-1:0] wpayload
    );
    integer i;
    begin
      for (i=0; i<P_MI_BYTES; i=i+1) begin
        f_wdata[i*8 +: 8] = wpayload[i*9 +: 8];
      end
    end
  endfunction
 
  function [C_M_AXI_DATA_WIDTH/8-1:0] f_wstrb
    (
      input [P_MI_BYTES*9-1:0] wpayload
    );
    integer i;
    begin
      for (i=0; i<P_MI_BYTES; i=i+1) begin
        f_wstrb[i] = wpayload[i*9+8];
      end
    end
  endfunction
  
  generate
  
  if (C_CLK_CONV) begin : gen_clock_conv
    if (C_AXI_IS_ACLK_ASYNC) begin : gen_async_conv
      
      assign m_aclk = M_AXI_ACLK;
      assign m_aresetn = M_AXI_ARESETN;
      assign s_aresetn = S_AXI_ARESETN;
      assign aw_fifo_s_aclk = S_AXI_ACLK;
      assign aw_fifo_m_aclk = M_AXI_ACLK;
      assign aw_fifo_aresetn = S_AXI_ARESETN & M_AXI_ARESETN;
      assign awpop_reset = ~S_AXI_ARESETN | ~M_AXI_ARESETN;
      assign s_sample_cycle_early = 1'b1;
      assign s_sample_cycle       = 1'b1;
      assign m_sample_cycle_early = 1'b1;
      assign m_sample_cycle       = 1'b1;
      
    end else begin : gen_sync_conv
    
      if (P_SI_LT_MI) begin : gen_fastclk_mi
        assign fast_aclk = M_AXI_ACLK;
      end else begin : gen_fastclk_si
        assign fast_aclk = S_AXI_ACLK;
      end
    
      assign m_aclk = M_AXI_ACLK;
      assign m_aresetn = fast_aresetn_r;
      assign s_aresetn = fast_aresetn_r;
      assign aw_fifo_s_aclk = fast_aclk;
      assign aw_fifo_m_aclk = 1'b0;
      assign aw_fifo_aresetn = fast_aresetn_r;
      assign s_sample_cycle_early = P_SI_LT_MI ? 1'b1 : SAMPLE_CYCLE_EARLY;
      assign s_sample_cycle       = P_SI_LT_MI ? 1'b1 : SAMPLE_CYCLE;
      assign m_sample_cycle_early = P_SI_LT_MI ? SAMPLE_CYCLE_EARLY : 1'b1;
      assign m_sample_cycle       = P_SI_LT_MI ? SAMPLE_CYCLE : 1'b1;
  
      always @(posedge fast_aclk) begin
        if (~S_AXI_ARESETN | ~M_AXI_ARESETN) begin
          fast_aresetn_r <= 1'b0;
        end else if (S_AXI_ARESETN & M_AXI_ARESETN & SAMPLE_CYCLE_EARLY) begin
          fast_aresetn_r <= 1'b1;
        end
      end
    end
  
  end else begin : gen_no_clk_conv
    
    assign m_aclk = S_AXI_ACLK;
    assign m_aresetn = S_AXI_ARESETN;
    assign s_aresetn = S_AXI_ARESETN;
    assign aw_fifo_s_aclk = S_AXI_ACLK;
    assign aw_fifo_m_aclk = 1'b0;
    assign aw_fifo_aresetn = S_AXI_ARESETN;
    assign fast_aclk = S_AXI_ACLK;
    assign s_sample_cycle_early = 1'b1;
    assign s_sample_cycle       = 1'b1;
    assign m_sample_cycle_early = 1'b1;
    assign m_sample_cycle       = 1'b1;
    
  end

    assign S_AXI_WREADY = S_AXI_WREADY_i;
    assign S_AXI_AWLOCK_i = S_AXI_AWLOCK[0];
    assign si_buf_en = S_AXI_WVALID & S_AXI_WREADY_i;
    assign cmd_ready = cmd_ready_i;
    assign s_awready_reg = aw_push;
    assign si_last_index = f_mi_be_last_index(cmd_si_addr[0 +: P_MI_SIZE], cmd_si_size, cmd_si_len, cmd_si_burst);
    assign push_ready = s_awvalid_reg & aw_ready & (buf_cnt != P_AWFIFO_TRESHOLD);

        
    always @ * begin
      aw_push = 1'b0;
      load_si_ptr = 1'b0;
      si_state_ns = si_state;
      S_AXI_WREADY_ns = S_AXI_WREADY_i;
      case (si_state)
        S_IDLE: begin
          if (S_AXI_AWVALID) begin
            load_si_ptr = 1'b1;
            S_AXI_WREADY_ns = 1'b1;
            si_state_ns = S_WRITING;
          end
        end
        S_WRITING: begin
          if (S_AXI_WVALID & S_AXI_WREADY_i & S_AXI_WLAST) begin
            if (push_ready) begin
              aw_push = m_sample_cycle;  // Sample strobe when AW FIFO is on faster M_AXI_ACLK.
              if (S_AXI_AWVALID) begin
                load_si_ptr = 1'b1;
              end else begin
                S_AXI_WREADY_ns = 1'b0;  //stall W-channel waiting for new AW command
                si_state_ns = S_IDLE;
              end
            end else begin
              S_AXI_WREADY_ns = 1'b0;  //stall W-channel waiting for AW FIFO push
              si_state_ns = S_AWFULL;
            end
          end
        end
        S_AWFULL: begin
          if (push_ready) begin
            aw_push = m_sample_cycle;  // Sample strobe when AW FIFO is on faster M_AXI_ACLK.
            if (S_AXI_AWVALID) begin
              load_si_ptr = 1'b1;
              S_AXI_WREADY_ns = 1'b1;
              si_state_ns = S_WRITING;
            end else begin
              S_AXI_WREADY_ns = 1'b0;  //stall W-channel waiting for new AW command
              si_state_ns = S_IDLE;
            end
          end
        end
        default: si_state_ns = S_IDLE;
      endcase
    end
    
    always @ (posedge S_AXI_ACLK) begin
      if (~s_aresetn) begin
        si_state <= S_IDLE;
        S_AXI_WREADY_i <= 1'b0;
        si_buf <= 0;
        buf_cnt <= 0;
        cmd_ready_i <= 1'b0;
      end else begin
        si_state <= si_state_ns;
        S_AXI_WREADY_i <= S_AXI_WREADY_ns;
        cmd_ready_i <= aw_pop_resync;

        if (aw_push) begin
          si_buf <= si_buf + 1;
        end
        
        if (aw_push & ~aw_pop_resync) begin
          buf_cnt <= buf_cnt + 1;
        end else if (~aw_push & aw_pop_resync & |buf_cnt) begin
          buf_cnt <= buf_cnt - 1;
        end
      end
    end
    
    always @ (posedge S_AXI_ACLK) begin
      if (load_si_ptr) begin
        if (cmd_si_burst == P_WRAP) begin
          si_ptr <= cmd_si_addr[P_MI_SIZE +: 3] & f_si_wrap_mask(cmd_si_size, cmd_si_len);
        end else begin
          si_ptr <= 0;
        end
        si_burst <= cmd_si_burst;
        si_size <= cmd_si_size;
        si_be <= f_si_be_init(cmd_si_addr[0 +: P_SI_SIZE], cmd_si_size);
        si_word <= cmd_si_addr[P_MI_SIZE-1 : P_SI_SIZE];
        si_wrap_cnt <= f_si_wrap_cnt(cmd_si_addr[0 +: (P_MI_SIZE + 4)], cmd_si_size, cmd_si_len);
        si_wrap_be_next <= f_si_wrap_be(cmd_si_addr[0 +: P_SI_SIZE], cmd_si_size, cmd_si_len);
        si_wrap_word_next <= f_si_wrap_word(cmd_si_addr[0 +: (P_MI_SIZE + 4)], cmd_si_size, cmd_si_len);
      end else if (si_buf_en) begin
        if (si_burst == P_FIXED) begin
          si_ptr <= si_ptr + 1;
        end else if ((si_burst == P_WRAP) && (si_wrap_cnt == 0)) begin
          si_ptr <= 0;
          si_be <= si_wrap_be_next;
          si_word <= si_wrap_word_next;
        end else begin
          if (si_be[P_SI_BYTES-1]) begin
            if (&si_word) begin
              si_ptr <= si_ptr + 1;  // Wrap long INCR bursts around end of buffer
            end
            si_word <= si_word + 1;
          end
          si_be <= f_si_be_rot(si_be, si_size);
        end
        si_wrap_cnt <= si_wrap_cnt - 1;
      end
    end
    
    always @ * begin
      mi_state_ns = mi_state;
      M_AXI_AWVALID_ns = M_AXI_AWVALID_i;
      M_AXI_WVALID_ns = M_AXI_WVALID_i;
      aw_pop = 1'b0;
      load_mi_ptr = 1'b0;
      load_mi_next = 1'b0;
      case (mi_state)
        M_IDLE: begin  // mi_state = 0
          M_AXI_AWVALID_ns = 1'b0;
          M_AXI_WVALID_ns = 1'b0;
          if (mi_awvalid) begin
            load_mi_ptr = 1'b1;
            mi_state_ns = M_ISSUE1;
          end
        end
        M_ISSUE1: begin  // mi_state = 1
          M_AXI_AWVALID_ns = 1'b1;
          mi_state_ns = M_WRITING1;
        end
        M_WRITING1: begin  // mi_state = 3
          M_AXI_WVALID_ns = 1'b1;
          if (M_AXI_AWREADY) begin
            aw_pop = s_sample_cycle;  // Sample strobe when AW FIFO is on faster S_AXI_ACLK.
            M_AXI_AWVALID_ns = 1'b0;
            if (mi_w_done) begin
              M_AXI_WVALID_ns = 1'b0;
              mi_state_ns = M_IDLE;
            end else begin
              mi_state_ns = M_AW_DONE1;
            end
          end else if (mi_w_done) begin
            M_AXI_WVALID_ns = 1'b0;
            mi_state_ns = M_AW_STALL;
          end
        end
        M_AW_STALL: begin  // mi_state = 2
          if (M_AXI_AWREADY) begin
            aw_pop = s_sample_cycle;  // Sample strobe when AW FIFO is on faster S_AXI_ACLK.
            M_AXI_AWVALID_ns = 1'b0;
            mi_state_ns = M_IDLE;
          end
        end
        M_AW_DONE1: begin  // mi_state = 6
          if (mi_awvalid) begin
            if (mi_w_done) begin
              M_AXI_WVALID_ns = 1'b0;
              load_mi_ptr = 1'b1;
              mi_state_ns = M_ISSUE1;
            end else if (~mi_last & ~mi_last_d1 & ~M_AXI_WLAST_i) begin
              load_mi_next = 1'b1;
              mi_state_ns = M_ISSUE2;
            end
          end else if (mi_w_done) begin
            M_AXI_WVALID_ns = 1'b0;
            mi_state_ns = M_IDLE;
          end
        end
        M_ISSUE2: begin  // mi_state = 7
          M_AXI_AWVALID_ns = 1'b1;
          if (mi_w_done) begin
            M_AXI_WVALID_ns = 1'b0;
            load_mi_ptr = 1'b1;
            mi_state_ns = M_ISSUE1;
          end else begin
            mi_state_ns = M_WRITING2;
          end
        end
        M_WRITING2: begin  // mi_state = 5
          if (M_AXI_AWREADY) begin
            M_AXI_AWVALID_ns = 1'b0;
            if (mi_w_done) begin
            aw_pop = s_sample_cycle;  // Sample strobe when AW FIFO is on faster S_AXI_ACLK.
              mi_state_ns = M_AW_DONE1;
            end else begin
              mi_state_ns = M_AW_DONE2;
            end
          end else if (mi_w_done) begin
            mi_state_ns = M_WRITING1;
          end
        end
        M_AW_DONE2: begin  // mi_state = 4
          if (mi_w_done) begin
            aw_pop = s_sample_cycle;  // Sample strobe when AW FIFO is on faster S_AXI_ACLK.
            mi_state_ns = M_AW_DONE1;
          end
        end
        default: mi_state_ns = M_IDLE;
      endcase
    end
    
    always @ (posedge m_aclk) begin
      if (~m_aresetn) begin
        mi_state <= M_IDLE;
        mi_buf <= 0;
        M_AXI_AWVALID_i <= 1'b0;
        M_AXI_WVALID_i <= 1'b0;
        mi_last <= 1'b0;
        mi_last_d1 <= 1'b0;
        M_AXI_WLAST_i <= 1'b0;
        mi_wstrb_mask_d2 <= {P_MI_BYTES{1'b1}}; 
        first_load_mi_d1 <= 1'b0; 
        next_valid <= 1'b0;
      end else begin
        mi_state <= mi_state_ns;
        M_AXI_AWVALID_i <= M_AXI_AWVALID_ns;
        M_AXI_WVALID_i <= M_AXI_WVALID_ns;
        
        if (mi_buf_en & mi_last) begin
          mi_buf <= mi_buf + 1;
        end
        
        if (load_mi_ptr) begin
          mi_last <= (M_AXI_AWLEN_i == 0);
          M_AXI_WLAST_i <= 1'b0;
        end else if (mi_buf_en) begin
          M_AXI_WLAST_i <= mi_last_d1;
          mi_last_d1 <= mi_last;
          if (first_load_mi_d1) begin
            mi_wstrb_mask_d2 <= mi_be_d1 & 
              (mi_first_d1 ? f_mi_be_first_mask(mi_addr_d1) : {P_MI_BYTES{1'b1}}) & 
              (mi_last_d1 ? f_mi_be_last_mask(mi_last_index_reg_d1) : {P_MI_BYTES{1'b1}});
          end
          if (mi_last) begin
            mi_last <= next_valid & (next_mi_len == 0);
          end else begin
            mi_last <= (mi_wcnt == 1);
          end
        end
      
        if (load_mi_d1) begin
          first_load_mi_d1 <= 1'b1;  // forever
        end
        
        if (mi_last & mi_buf_en) begin
          next_valid <= 1'b0;
        end else if (load_mi_next) begin
          next_valid <= 1'b1;
        end
        
        if (m_sample_cycle) begin
          aw_pop_extend <= 1'b0;
        end else if (aw_pop) begin
          aw_pop_extend <= 1'b1;
        end
      end
    end
    
    assign mi_buf_en = (M_AXI_WVALID_i & M_AXI_WREADY) | load_mi_d1 | load_mi_d2;
    assign mi_w_done = M_AXI_WVALID_i & M_AXI_WREADY & M_AXI_WLAST_i;
    
    always @ (posedge m_aclk) begin
      load_mi_d2 <= load_mi_d1;
      load_mi_d1 <= load_mi_ptr;
      if (load_mi_ptr) begin
        if (M_AXI_AWBURST_i == P_WRAP) begin
          mi_ptr <= M_AXI_AWADDR_i[P_MI_SIZE +: 3] & f_mi_wrap_mask(M_AXI_AWSIZE_i, M_AXI_AWLEN_i);
        end else begin
          mi_ptr <= 0;
        end
        mi_wcnt <= M_AXI_AWLEN_i;
        mi_burst <= M_AXI_AWBURST_i;
        mi_size <= M_AXI_AWSIZE_i;
        mi_be <= f_mi_be_init(M_AXI_AWADDR_i[0 +: P_MI_SIZE], M_AXI_AWSIZE_i);
        mi_wrap_cnt <= f_mi_wrap_cnt(M_AXI_AWADDR_i[0 +: (P_MI_SIZE + 4)], M_AXI_AWSIZE_i, M_AXI_AWLEN_i);
        mi_wrap_be_next <= f_mi_wrap_be(M_AXI_AWADDR_i[0 +: P_MI_SIZE], M_AXI_AWSIZE_i, M_AXI_AWLEN_i);
        mi_first <= 1'b1;
        mi_addr <= M_AXI_AWADDR_i[0 +: P_MI_SIZE];
        mi_last_index_reg_d0 <= mi_last_index_reg;
      end else if (mi_buf_en) begin
        mi_be_d1 <= mi_be;
        mi_first_d1 <= mi_first;
        mi_last_index_reg_d1 <= mi_last_index_reg_d0;
        mi_addr_d1 <= mi_addr;
        if (mi_last) begin
          if (next_mi_burst == P_WRAP) begin
            mi_ptr <= next_mi_addr[P_MI_SIZE +: 3] & f_mi_wrap_mask(next_mi_size, next_mi_len);
          end else begin
            mi_ptr <= 0;
          end
          if (next_valid) begin
            mi_wcnt <= next_mi_len;
            mi_addr <= next_mi_addr[0 +: P_MI_SIZE];
            mi_last_index_reg_d0 <= next_mi_last_index_reg;
          end
          mi_burst <= next_mi_burst;
          mi_size <= next_mi_size;
          mi_be <= f_mi_be_init(next_mi_addr[0 +: P_MI_SIZE], next_mi_size);
          mi_wrap_cnt <= f_mi_wrap_cnt(next_mi_addr, next_mi_size, next_mi_len);
          mi_wrap_be_next <= f_mi_wrap_be(next_mi_addr[0 +: P_MI_SIZE], next_mi_size, next_mi_len);
          mi_first <= 1'b1;
        end else begin
          mi_first <= 1'b0;
          if (mi_burst == P_FIXED) begin
            mi_ptr <= mi_ptr + 1;
          end else if ((mi_burst == P_WRAP) && (mi_wrap_cnt == 0)) begin
            mi_ptr <= 0;
            mi_be <= mi_wrap_be_next;
          end else begin
            if (mi_be[P_MI_BYTES-1]) begin
              mi_ptr <= (mi_ptr + 1);  // Wrap long INCR bursts around end of buffer
            end
            mi_be <= f_mi_be_rot(mi_be, mi_size);
          end
          mi_wcnt <= mi_wcnt - 1;
          mi_wrap_cnt <= mi_wrap_cnt - 1;
        end
      end
      
      if (load_mi_next) begin
        next_mi_len <= M_AXI_AWLEN_i;
        next_mi_burst <= M_AXI_AWBURST_i;
        next_mi_size <= M_AXI_AWSIZE_i;
        next_mi_addr <= M_AXI_AWADDR_i[0 +: (P_MI_SIZE + 4)];
        next_mi_last_index_reg <= mi_last_index_reg;
      end
    end
    
    assign si_wpayload = {P_RATIO{f_wpayload(S_AXI_WDATA,S_AXI_WSTRB)}};
    assign M_AXI_WDATA = f_wdata(mi_wpayload);
    assign M_AXI_WSTRB = f_wstrb(mi_wpayload) & mi_wstrb_mask_d2 & {P_MI_BYTES{M_AXI_WVALID_i}};
    assign M_AXI_WVALID = M_AXI_WVALID_i;
    assign M_AXI_WLAST = M_AXI_WLAST_i;
    assign M_AXI_AWVALID = M_AXI_AWVALID_i;
    assign M_AXI_AWADDR = M_AXI_AWADDR_i;
    assign M_AXI_AWLEN = M_AXI_AWLEN_i;
    assign M_AXI_AWSIZE = M_AXI_AWSIZE_i;
    assign M_AXI_AWBURST = M_AXI_AWBURST_i;
    assign M_AXI_AWLOCK = {1'b0,M_AXI_AWLOCK_i};
    assign si_buf_addr = {si_buf, si_ptr};
    assign mi_buf_addr = {mi_buf, mi_ptr};
    assign si_we = f_si_we(si_word, si_be);
    
  blk_mem_gen_v8_3_6 #(
    .C_FAMILY(C_FAMILY),
    .C_XDEVICEFAMILY(C_FAMILY),
    .C_INTERFACE_TYPE(0),
    .C_AXI_TYPE(1),
    .C_AXI_SLAVE_TYPE(0),
    .C_HAS_AXI_ID(0),
    .C_AXI_ID_WIDTH(4),
    .C_MEM_TYPE(1),
    .C_BYTE_SIZE(9),
    .C_ALGORITHM(1),
    .C_PRIM_TYPE(1),
    .C_LOAD_INIT_FILE(0),
    .C_INIT_FILE_NAME("BlankString"),
    .C_INIT_FILE("BlankString"),
    .C_USE_DEFAULT_DATA(0),
    .C_DEFAULT_DATA("0"),
    .C_HAS_RSTA(0),
    .C_RST_PRIORITY_A("CE"),
    .C_RSTRAM_A(0),
    .C_INITA_VAL("0"),
    .C_HAS_ENA(1),
    .C_HAS_REGCEA(0),
    .C_USE_BYTE_WEA(1),
    .C_WEA_WIDTH(P_MI_BYTES),
    .C_WRITE_MODE_A("WRITE_FIRST"),
    .C_WRITE_WIDTH_A(P_M_WBUFFER_WIDTH),
    .C_READ_WIDTH_A(P_M_WBUFFER_WIDTH),
    .C_WRITE_DEPTH_A(P_M_WBUFFER_DEPTH),
    .C_READ_DEPTH_A(P_M_WBUFFER_DEPTH),
    .C_ADDRA_WIDTH(P_M_WBUFFER_DEPTH_LOG),
    .C_HAS_RSTB(0),
    .C_RST_PRIORITY_B("CE"),
    .C_RSTRAM_B(0),
    .C_INITB_VAL("0"),
    .C_HAS_ENB(1),
    .C_HAS_REGCEB(0),
    .C_USE_BYTE_WEB(1),
    .C_WEB_WIDTH(P_MI_BYTES),
    .C_WRITE_MODE_B("WRITE_FIRST"),
    .C_WRITE_WIDTH_B(P_M_WBUFFER_WIDTH),
    .C_READ_WIDTH_B(P_M_WBUFFER_WIDTH),
    .C_WRITE_DEPTH_B(P_M_WBUFFER_DEPTH),
    .C_READ_DEPTH_B(P_M_WBUFFER_DEPTH),
    .C_ADDRB_WIDTH(P_M_WBUFFER_DEPTH_LOG),
    .C_HAS_MEM_OUTPUT_REGS_A(0),
    .C_HAS_MEM_OUTPUT_REGS_B(1),
    .C_HAS_MUX_OUTPUT_REGS_A(0),
    .C_HAS_MUX_OUTPUT_REGS_B(0),
    .C_MUX_PIPELINE_STAGES(0),
    .C_HAS_SOFTECC_INPUT_REGS_A(0),
    .C_HAS_SOFTECC_OUTPUT_REGS_B(0),
    .C_USE_SOFTECC(0),
    .C_USE_ECC(0),
    .C_HAS_INJECTERR(0),
    .C_SIM_COLLISION_CHECK("GENERATE_X_ONLY"),
    .C_COMMON_CLK(0),
    .C_ENABLE_32BIT_ADDRESS(0),
    .C_DISABLE_WARN_BHV_COLL(1),
    .C_DISABLE_WARN_BHV_RANGE(0),
    .C_USE_BRAM_BLOCK(0)
  ) w_buffer (
    .clka(S_AXI_ACLK),
    .rsta(1'b0),
    .ena(si_buf_en),
    .regcea(1'b1),
    .wea(si_we),
    .addra(si_buf_addr),
    .dina(si_wpayload),
    .douta(),
    .clkb(m_aclk),
    .rstb(1'b0),
    .enb(mi_buf_en),
    .regceb(1'b1),
    .web({P_MI_BYTES{1'b0}}),
    .addrb(mi_buf_addr),
    .dinb({P_M_WBUFFER_WIDTH{1'b0}}),
    .doutb(mi_wpayload),
    .injectsbiterr(1'b0),
    .injectdbiterr(1'b0),
    .sbiterr(),
    .dbiterr(),
    .rdaddrecc(),
    .s_aclk(1'b0),
    .s_aresetn(1'b0),
    .s_axi_awid(4'b0),
    .s_axi_awaddr(32'b0),
    .s_axi_awlen(8'b0),
    .s_axi_awsize(3'b0),
    .s_axi_awburst(2'b0),
    .s_axi_awvalid(1'b0),
    .s_axi_awready(),
    .s_axi_wdata({P_M_WBUFFER_WIDTH{1'b0}}),
    .s_axi_wstrb({P_MI_BYTES{1'b0}}),
    .s_axi_wlast(1'b0),
    .s_axi_wvalid(1'b0),
    .s_axi_wready(),
    .s_axi_bid(),
    .s_axi_bresp(),
    .s_axi_bvalid(),
    .s_axi_bready(1'b0),
    .s_axi_arid(4'b0),
    .s_axi_araddr(32'b0),
    .s_axi_arlen(8'b0),
    .s_axi_arsize(3'b0),
    .s_axi_arburst(2'b0),
    .s_axi_arvalid(1'b0),
    .s_axi_arready(),
    .s_axi_rid(),
    .s_axi_rdata(),
    .s_axi_rresp(),
    .s_axi_rlast(),
    .s_axi_rvalid(),
    .s_axi_rready(1'b0),
    .s_axi_injectsbiterr(1'b0),
    .s_axi_injectdbiterr(1'b0),
    .s_axi_sbiterr(),
    .s_axi_dbiterr(),
    .s_axi_rdaddrecc(),
    .sleep(1'b0),
    .eccpipece(1'b0)
  );
    
  fifo_generator_v13_1_4 #(
    .C_FAMILY(C_FAMILY),
    .C_COMMON_CLOCK(P_COMMON_CLOCK),
    .C_MEMORY_TYPE(1),
    .C_SYNCHRONIZER_STAGE(C_SYNCHRONIZER_STAGE),
    .C_INTERFACE_TYPE(2),
    .C_AXI_TYPE(1),
    .C_AXIS_TYPE(0),
    .C_HAS_AXI_ID(0),
    .C_AXI_LEN_WIDTH(8),
    .C_AXI_LOCK_WIDTH(1),
    .C_DIN_WIDTH_WACH(P_AWFIFO_WIDTH),
    .C_DIN_WIDTH_WDCH(37),
    .C_DIN_WIDTH_WRCH(2),
    .C_DIN_WIDTH_RACH(P_AWFIFO_WIDTH),
    .C_DIN_WIDTH_RDCH(35),
    .C_HAS_AXI_WR_CHANNEL(1),
    .C_HAS_AXI_RD_CHANNEL(0),
    .C_AXI_ID_WIDTH(1),
    .C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
    .C_AXI_DATA_WIDTH(32),
    .C_HAS_AXI_AWUSER(1),
    .C_HAS_AXI_WUSER(0),
    .C_HAS_AXI_BUSER(0),
    .C_HAS_AXI_ARUSER(1),
    .C_HAS_AXI_RUSER(0),
    .C_AXI_ARUSER_WIDTH(P_MI_SIZE),
    .C_AXI_AWUSER_WIDTH(P_MI_SIZE),
    .C_AXI_WUSER_WIDTH(1),
    .C_AXI_BUSER_WIDTH(1),
    .C_AXI_RUSER_WIDTH(1),
    .C_WACH_TYPE(0),
    .C_WDCH_TYPE(2),
    .C_WRCH_TYPE(2),
    .C_RACH_TYPE(0),
    .C_RDCH_TYPE(0),
    .C_IMPLEMENTATION_TYPE_WACH(P_COMMON_CLOCK ? 2 : 12),
    .C_IMPLEMENTATION_TYPE_WDCH(P_COMMON_CLOCK ? 1 : 11),
    .C_IMPLEMENTATION_TYPE_WRCH(P_COMMON_CLOCK ? 2 : 12),
    .C_IMPLEMENTATION_TYPE_RACH(P_COMMON_CLOCK ? 2 : 12),
    .C_IMPLEMENTATION_TYPE_RDCH(P_COMMON_CLOCK ? 1 : 11),
    .C_IMPLEMENTATION_TYPE_AXIS(1),
    .C_DIN_WIDTH_AXIS(1),
    .C_WR_DEPTH_WACH(32),
    .C_WR_DEPTH_WDCH(1024),
    .C_WR_DEPTH_WRCH(16),
    .C_WR_DEPTH_RACH(32),
    .C_WR_DEPTH_RDCH(1024),
    .C_WR_DEPTH_AXIS(1024),
    .C_WR_PNTR_WIDTH_WACH(5),
    .C_WR_PNTR_WIDTH_WDCH(10),
    .C_WR_PNTR_WIDTH_WRCH(4),
    .C_WR_PNTR_WIDTH_RACH(5),
    .C_WR_PNTR_WIDTH_RDCH(10),
    .C_WR_PNTR_WIDTH_AXIS(10),
    .C_APPLICATION_TYPE_WACH(P_COMMON_CLOCK ? 2 : 0),
    .C_APPLICATION_TYPE_WDCH(0),
    .C_APPLICATION_TYPE_WRCH(0),
    .C_APPLICATION_TYPE_RACH(0),
    .C_APPLICATION_TYPE_RDCH(0),
    .C_APPLICATION_TYPE_AXIS(0),
    .C_USE_ECC_WACH(0),
    .C_USE_ECC_WDCH(0),
    .C_USE_ECC_WRCH(0),
    .C_USE_ECC_RACH(0),
    .C_USE_ECC_RDCH(0),
    .C_USE_ECC_AXIS(0),
    .C_ERROR_INJECTION_TYPE_WACH(0),
    .C_ERROR_INJECTION_TYPE_WDCH(0),
    .C_ERROR_INJECTION_TYPE_WRCH(0),
    .C_ERROR_INJECTION_TYPE_RACH(0),
    .C_ERROR_INJECTION_TYPE_RDCH(0),
    .C_ERROR_INJECTION_TYPE_AXIS(0),
    .C_HAS_DATA_COUNTS_WACH(0),
    .C_HAS_DATA_COUNTS_WDCH(0),
    .C_HAS_DATA_COUNTS_WRCH(0),
    .C_HAS_DATA_COUNTS_RACH(0),
    .C_HAS_DATA_COUNTS_RDCH(0),
    .C_HAS_DATA_COUNTS_AXIS(0),
    .C_HAS_PROG_FLAGS_WACH(0),
    .C_HAS_PROG_FLAGS_WDCH(0),
    .C_HAS_PROG_FLAGS_WRCH(0),
    .C_HAS_PROG_FLAGS_RACH(0),
    .C_HAS_PROG_FLAGS_RDCH(0),
    .C_HAS_PROG_FLAGS_AXIS(0),
    .C_PROG_FULL_TYPE_WACH(0),
    .C_PROG_FULL_TYPE_WDCH(0),
    .C_PROG_FULL_TYPE_WRCH(0),
    .C_PROG_FULL_TYPE_RACH(0),
    .C_PROG_FULL_TYPE_RDCH(0),
    .C_PROG_FULL_TYPE_AXIS(0),
    .C_PROG_FULL_THRESH_ASSERT_VAL_WACH(31),
    .C_PROG_FULL_THRESH_ASSERT_VAL_WDCH(1023),
    .C_PROG_FULL_THRESH_ASSERT_VAL_WRCH(15),
    .C_PROG_FULL_THRESH_ASSERT_VAL_RACH(15),
    .C_PROG_FULL_THRESH_ASSERT_VAL_RDCH(1023),
    .C_PROG_FULL_THRESH_ASSERT_VAL_AXIS(1023),
    .C_PROG_EMPTY_TYPE_WACH(0),
    .C_PROG_EMPTY_TYPE_WDCH(0),
    .C_PROG_EMPTY_TYPE_WRCH(0),
    .C_PROG_EMPTY_TYPE_RACH(0),
    .C_PROG_EMPTY_TYPE_RDCH(0),
    .C_PROG_EMPTY_TYPE_AXIS(0),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_WACH(30),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_WDCH(1022),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_WRCH(14),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_RACH(14),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_RDCH(1022),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_AXIS(1022),
    .C_REG_SLICE_MODE_WACH(0),
    .C_REG_SLICE_MODE_WDCH(0),
    .C_REG_SLICE_MODE_WRCH(0),
    .C_REG_SLICE_MODE_RACH(0),
    .C_REG_SLICE_MODE_RDCH(0),
    .C_REG_SLICE_MODE_AXIS(0),
    .C_HAS_AXIS_TDATA(0),
    .C_HAS_AXIS_TID(0),
    .C_HAS_AXIS_TDEST(0),
    .C_HAS_AXIS_TUSER(0),
    .C_HAS_AXIS_TREADY(1),
    .C_HAS_AXIS_TLAST(0),
    .C_HAS_AXIS_TSTRB(0),
    .C_HAS_AXIS_TKEEP(0),
    .C_AXIS_TDATA_WIDTH(64),
    .C_AXIS_TID_WIDTH(8),
    .C_AXIS_TDEST_WIDTH(4),
    .C_AXIS_TUSER_WIDTH(4),
    .C_AXIS_TSTRB_WIDTH(4),
    .C_AXIS_TKEEP_WIDTH(4),
    .C_HAS_SLAVE_CE(0),
    .C_HAS_MASTER_CE(0),
    .C_ADD_NGC_CONSTRAINT(0),
    .C_USE_COMMON_OVERFLOW(0),
    .C_USE_COMMON_UNDERFLOW(0),
    .C_USE_DEFAULT_SETTINGS(0),
    .C_COUNT_TYPE(0),
    .C_DATA_COUNT_WIDTH(10),
    .C_DEFAULT_VALUE("BlankString"),
    .C_DIN_WIDTH(18),
    .C_DOUT_RST_VAL("0"),
    .C_DOUT_WIDTH(18),
    .C_ENABLE_RLOCS(0),
    .C_FULL_FLAGS_RST_VAL(1),
    .C_HAS_ALMOST_EMPTY(0),
    .C_HAS_ALMOST_FULL(0),
    .C_HAS_BACKUP(0),
    .C_HAS_DATA_COUNT(0),
    .C_HAS_INT_CLK(0),
    .C_HAS_MEMINIT_FILE(0),
    .C_HAS_OVERFLOW(0),
    .C_HAS_RD_DATA_COUNT(0),
    .C_HAS_RD_RST(0),
    .C_HAS_RST(1),
    .C_HAS_SRST(0),
    .C_HAS_UNDERFLOW(0),
    .C_HAS_VALID(0),
    .C_HAS_WR_ACK(0),
    .C_HAS_WR_DATA_COUNT(0),
    .C_HAS_WR_RST(0),
    .C_IMPLEMENTATION_TYPE(0),
    .C_INIT_WR_PNTR_VAL(0),
    .C_MIF_FILE_NAME("BlankString"),
    .C_OPTIMIZATION_MODE(0),
    .C_OVERFLOW_LOW(0),
    .C_PRELOAD_LATENCY(1),
    .C_PRELOAD_REGS(0),
    .C_PRIM_FIFO_TYPE("4kx4"),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL(2),
    .C_PROG_EMPTY_THRESH_NEGATE_VAL(3),
    .C_PROG_EMPTY_TYPE(0),
    .C_PROG_FULL_THRESH_ASSERT_VAL(1022),
    .C_PROG_FULL_THRESH_NEGATE_VAL(1021),
    .C_PROG_FULL_TYPE(0),
    .C_RD_DATA_COUNT_WIDTH(10),
    .C_RD_DEPTH(1024),
    .C_RD_FREQ(1),
    .C_RD_PNTR_WIDTH(10),
    .C_UNDERFLOW_LOW(0),
    .C_USE_DOUT_RST(1),
    .C_USE_ECC(0),
    .C_USE_EMBEDDED_REG(0),
    .C_USE_FIFO16_FLAGS(0),
    .C_USE_FWFT_DATA_COUNT(0),
    .C_VALID_LOW(0),
    .C_WR_ACK_LOW(0),
    .C_WR_DATA_COUNT_WIDTH(10),
    .C_WR_DEPTH(1024),
    .C_WR_FREQ(1),
    .C_WR_PNTR_WIDTH(10),
    .C_WR_RESPONSE_LATENCY(1),
    .C_MSGON_VAL(1),
    .C_ENABLE_RST_SYNC(1),
    .C_ERROR_INJECTION_TYPE(0)
  ) dw_fifogen_aw (
    .s_aclk(aw_fifo_s_aclk),
    .m_aclk(aw_fifo_m_aclk),
    .s_aresetn(aw_fifo_aresetn),
    .s_axi_awid     (1'b0),
    .s_axi_awaddr   (s_awaddr_reg),
    .s_axi_awlen    (s_awlen_reg),
    .s_axi_awsize   (s_awsize_reg),
    .s_axi_awburst  (s_awburst_reg),
    .s_axi_awlock   (s_awlock_reg),
    .s_axi_awcache  (s_awcache_reg),
    .s_axi_awprot   (s_awprot_reg),
    .s_axi_awqos    (s_awqos_reg),
    .s_axi_awregion (s_awregion_reg),
    .s_axi_awuser   (si_last_index_reg),
    .s_axi_awvalid  (aw_push),
    .s_axi_awready  (aw_ready),
    .s_axi_wid(1'b0),
    .s_axi_wdata(32'b0),
    .s_axi_wstrb(4'b0),
    .s_axi_wlast(1'b0),
    .s_axi_wuser(1'b0),
    .s_axi_wvalid(1'b0),
    .s_axi_wready(),
    .s_axi_bid(),
    .s_axi_bresp(),
    .s_axi_buser(),
    .s_axi_bvalid(),
    .s_axi_bready(1'b0),
    .m_axi_awid(),
    .m_axi_awaddr   (M_AXI_AWADDR_i),
    .m_axi_awlen    (M_AXI_AWLEN_i),
    .m_axi_awsize   (M_AXI_AWSIZE_i),
    .m_axi_awburst  (M_AXI_AWBURST_i),
    .m_axi_awlock   (M_AXI_AWLOCK_i),
    .m_axi_awcache  (M_AXI_AWCACHE),
    .m_axi_awprot   (M_AXI_AWPROT),
    .m_axi_awqos    (M_AXI_AWQOS),
    .m_axi_awregion (M_AXI_AWREGION),
    .m_axi_awuser   (mi_last_index_reg),
    .m_axi_awvalid  (mi_awvalid),
    .m_axi_awready  (aw_pop),
    .m_axi_wid(),
    .m_axi_wdata(),
    .m_axi_wstrb(),
    .m_axi_wuser(),
    .m_axi_wlast(),
    .m_axi_wvalid(),
    .m_axi_wready(1'b0),
    .m_axi_bid(1'b0),
    .m_axi_bresp(2'b0),
    .m_axi_buser(1'b0),
    .m_axi_bvalid(1'b0),
    .m_axi_bready(),
    .s_axi_arid(1'b0),
    .s_axi_araddr({C_AXI_ADDR_WIDTH{1'b0}}),
    .s_axi_arlen(8'b0),
    .s_axi_arsize(3'b0),
    .s_axi_arburst(2'b0),
    .s_axi_arlock(1'b0),
    .s_axi_arcache(4'b0),
    .s_axi_arprot(3'b0),
    .s_axi_arqos(4'b0),
    .s_axi_arregion(4'b0),
    .s_axi_aruser({P_MI_SIZE{1'b0}}),
    .s_axi_arvalid(1'b0),
    .s_axi_arready(),
    .s_axi_rid(),
    .s_axi_rdata(),
    .s_axi_rresp(),
    .s_axi_rlast(),
    .s_axi_ruser(),
    .s_axi_rvalid(),
    .s_axi_rready(1'b0),
    .m_axi_arid(),
    .m_axi_araddr(),
    .m_axi_arlen(),
    .m_axi_arsize(),
    .m_axi_arburst(),
    .m_axi_arlock(),
    .m_axi_arcache(),
    .m_axi_arprot(),
    .m_axi_arqos(),
    .m_axi_arregion(),
    .m_axi_aruser(),
    .m_axi_arvalid(),
    .m_axi_arready(1'b0),
    .m_axi_rid(1'b0),
    .m_axi_rdata(32'b0),
    .m_axi_rresp(2'b0),
    .m_axi_rlast(1'b0),
    .m_axi_ruser(1'b0),
    .m_axi_rvalid(1'b0),
    .m_axi_rready(),
    .m_aclk_en(1'b0),
    .s_aclk_en(1'b0),
    .backup(1'b0),
    .backup_marker(1'b0),
    .clk(1'b0),
    .rst(1'b0),
    .srst(1'b0),
    .wr_clk(1'b0),
    .wr_rst(1'b0),
    .rd_clk(1'b0),
    .rd_rst(1'b0),
    .din(18'b0),
    .wr_en(1'b0),
    .rd_en(1'b0),
    .prog_empty_thresh(10'b0),
    .prog_empty_thresh_assert(10'b0),
    .prog_empty_thresh_negate(10'b0),
    .prog_full_thresh(10'b0),
    .prog_full_thresh_assert(10'b0),
    .prog_full_thresh_negate(10'b0),
    .int_clk(1'b0),
    .injectdbiterr(1'b0),
    .injectsbiterr(1'b0),
    .dout(),
    .full(),
    .almost_full(),
    .wr_ack(),
    .overflow(),
    .empty(),
    .almost_empty(),
    .valid(),
    .underflow(),
    .data_count(),
    .rd_data_count(),
    .wr_data_count(),
    .prog_full(),
    .prog_empty(),
    .sbiterr(),
    .dbiterr(),
    .s_axis_tvalid(1'b0),
    .s_axis_tready(),
    .s_axis_tdata(64'b0),
    .s_axis_tstrb(4'b0),
    .s_axis_tkeep(4'b0),
    .s_axis_tlast(1'b0),
    .s_axis_tid(8'b0),
    .s_axis_tdest(4'b0),
    .s_axis_tuser(4'b0),
    .m_axis_tvalid(),
    .m_axis_tready(1'b0),
    .m_axis_tdata(),
    .m_axis_tstrb(),
    .m_axis_tkeep(),
    .m_axis_tlast(),
    .m_axis_tid(),
    .m_axis_tdest(),
    .m_axis_tuser(),
    .axi_aw_injectsbiterr(1'b0),
    .axi_aw_injectdbiterr(1'b0),
    .axi_aw_prog_full_thresh(5'b0),
    .axi_aw_prog_empty_thresh(5'b0),
    .axi_aw_data_count(),
    .axi_aw_wr_data_count(),
    .axi_aw_rd_data_count(),
    .axi_aw_sbiterr(),
    .axi_aw_dbiterr(),
    .axi_aw_overflow(),
    .axi_aw_underflow(),
    .axi_aw_prog_full(),
    .axi_aw_prog_empty(),
    .axi_w_injectsbiterr(1'b0),
    .axi_w_injectdbiterr(1'b0),
    .axi_w_prog_full_thresh(10'b0),
    .axi_w_prog_empty_thresh(10'b0),
    .axi_w_data_count(),
    .axi_w_wr_data_count(),
    .axi_w_rd_data_count(),
    .axi_w_sbiterr(),
    .axi_w_dbiterr(),
    .axi_w_overflow(),
    .axi_w_underflow(),
    .axi_b_injectsbiterr(1'b0),
    .axi_w_prog_full(),
    .axi_w_prog_empty(),
    .axi_b_injectdbiterr(1'b0),
    .axi_b_prog_full_thresh(4'b0),
    .axi_b_prog_empty_thresh(4'b0),
    .axi_b_data_count(),
    .axi_b_wr_data_count(),
    .axi_b_rd_data_count(),
    .axi_b_sbiterr(),
    .axi_b_dbiterr(),
    .axi_b_overflow(),
    .axi_b_underflow(),
    .axi_ar_injectsbiterr(1'b0),
    .axi_b_prog_full(),
    .axi_b_prog_empty(),
    .axi_ar_injectdbiterr(1'b0),
    .axi_ar_prog_full_thresh(5'b0),
    .axi_ar_prog_empty_thresh(5'b0),
    .axi_ar_data_count(),
    .axi_ar_wr_data_count(),
    .axi_ar_rd_data_count(),
    .axi_ar_sbiterr(),
    .axi_ar_dbiterr(),
    .axi_ar_overflow(),
    .axi_ar_underflow(),
    .axi_ar_prog_full(),
    .axi_ar_prog_empty(),
    .axi_r_injectsbiterr(1'b0),
    .axi_r_injectdbiterr(1'b0),
    .axi_r_prog_full_thresh(10'b0),
    .axi_r_prog_empty_thresh(10'b0),
    .axi_r_data_count(),
    .axi_r_wr_data_count(),
    .axi_r_rd_data_count(),
    .axi_r_sbiterr(),
    .axi_r_dbiterr(),
    .axi_r_overflow(),
    .axi_r_underflow(),
    .axis_injectsbiterr(1'b0),
    .axi_r_prog_full(),
    .axi_r_prog_empty(),
    .axis_injectdbiterr(1'b0),
    .axis_prog_full_thresh(10'b0),
    .axis_prog_empty_thresh(10'b0),
    .axis_data_count(),
    .axis_wr_data_count(),
    .axis_rd_data_count(),
    .axis_sbiterr(),
    .axis_dbiterr(),
    .axis_overflow(),
    .axis_underflow(),
    .axis_prog_full(),
    .axis_prog_empty(),
    .wr_rst_busy(),
    .rd_rst_busy(),
    .sleep(1'b0)
  );
  
  axi_register_slice_v2_1_12_axi_register_slice #(
    .C_FAMILY(C_FAMILY),
    .C_AXI_PROTOCOL(0),
    .C_AXI_ID_WIDTH(1),
    .C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
    .C_AXI_DATA_WIDTH(32),
    .C_AXI_SUPPORTS_USER_SIGNALS(1),
    .C_AXI_AWUSER_WIDTH(P_MI_SIZE),
    .C_AXI_ARUSER_WIDTH(1),
    .C_AXI_WUSER_WIDTH(1),
    .C_AXI_RUSER_WIDTH(1),
    .C_AXI_BUSER_WIDTH(1),
    .C_REG_CONFIG_AW(7),
    .C_REG_CONFIG_W(0),
    .C_REG_CONFIG_B(0),
    .C_REG_CONFIG_AR(0),
    .C_REG_CONFIG_R(0)
  ) s_aw_reg (
    .aclk(S_AXI_ACLK),
    .aresetn(s_aresetn),
    .s_axi_awid(1'b0),
    .s_axi_awaddr  (S_AXI_AWADDR),
    .s_axi_awlen   (S_AXI_AWLEN),
    .s_axi_awsize  (S_AXI_AWSIZE),
    .s_axi_awburst (S_AXI_AWBURST),
    .s_axi_awlock  (S_AXI_AWLOCK_i),
    .s_axi_awcache (S_AXI_AWCACHE),
    .s_axi_awprot  (S_AXI_AWPROT),
    .s_axi_awregion(S_AXI_AWREGION),
    .s_axi_awqos   (S_AXI_AWQOS),
    .s_axi_awuser  (si_last_index),
    .s_axi_awvalid (S_AXI_AWVALID),
    .s_axi_awready (S_AXI_AWREADY),
    .s_axi_wid(1'b0),
    .s_axi_wdata(32'b0),
    .s_axi_wstrb(4'b00),
    .s_axi_wlast(1'b0),
    .s_axi_wuser(1'b0),
    .s_axi_wvalid(1'b0),
    .s_axi_wready(),
    .s_axi_bid(),
    .s_axi_buser(),
    .s_axi_bresp(),
    .s_axi_bvalid(),
    .s_axi_bready(1'b0),
    .s_axi_arid(1'b0),
    .s_axi_araddr({C_AXI_ADDR_WIDTH{1'B0}}),
    .s_axi_arlen(8'b0),
    .s_axi_arsize(3'b0),
    .s_axi_arburst(2'b0),
    .s_axi_arlock(1'b0),
    .s_axi_arcache(4'b0),
    .s_axi_arprot(3'b0),
    .s_axi_arregion(4'b0),
    .s_axi_arqos(4'b0),
    .s_axi_aruser(1'b0),
    .s_axi_arvalid(1'b0),
    .s_axi_arready(),
    .s_axi_rid(),
    .s_axi_ruser(),
    .s_axi_rdata(),
    .s_axi_rresp(),
    .s_axi_rlast(),
    .s_axi_rvalid(),
    .s_axi_rready(1'b0),
    .m_axi_awid(),
    .m_axi_awaddr  (s_awaddr_reg),
    .m_axi_awlen   (s_awlen_reg),
    .m_axi_awsize  (s_awsize_reg),
    .m_axi_awburst (s_awburst_reg),
    .m_axi_awlock  (s_awlock_reg),
    .m_axi_awcache (s_awcache_reg),
    .m_axi_awprot  (s_awprot_reg),
    .m_axi_awregion(s_awregion_reg),
    .m_axi_awqos   (s_awqos_reg),
    .m_axi_awuser  (si_last_index_reg),
    .m_axi_awvalid (s_awvalid_reg),
    .m_axi_awready (s_awready_reg),
    .m_axi_wid(),
    .m_axi_wuser(),
    .m_axi_wdata(),
    .m_axi_wstrb(),
    .m_axi_wlast(),
    .m_axi_wvalid(),
    .m_axi_wready(1'b0),
    .m_axi_bid(1'b0),
    .m_axi_bresp(2'b0),
    .m_axi_buser(1'b0),
    .m_axi_bvalid(1'b0),
    .m_axi_bready(),
    .m_axi_arid(),
    .m_axi_aruser(),
    .m_axi_araddr(),
    .m_axi_arlen(),
    .m_axi_arsize(),
    .m_axi_arburst(),
    .m_axi_arlock(),
    .m_axi_arcache(),
    .m_axi_arprot(),
    .m_axi_arregion(),
    .m_axi_arqos(),
    .m_axi_arvalid(),
    .m_axi_arready(1'b0),
    .m_axi_rid(1'b0),
    .m_axi_rdata(32'b0),
    .m_axi_rresp(2'b0),
    .m_axi_rlast(1'b0),
    .m_axi_ruser(1'b0),
    .m_axi_rvalid(1'b0),
    .m_axi_rready()
  );
  
  if (C_CLK_CONV && C_AXI_IS_ACLK_ASYNC) begin : gen_awpop_fifo
    
    fifo_generator_v13_1_4 #(
      .C_DIN_WIDTH(1),
      .C_DOUT_WIDTH(1),
      .C_RD_DEPTH(32),
      .C_RD_PNTR_WIDTH(5),
      .C_RD_DATA_COUNT_WIDTH(5),
      .C_WR_DEPTH(32),
      .C_WR_PNTR_WIDTH(5),
      .C_WR_DATA_COUNT_WIDTH(5),
      .C_DATA_COUNT_WIDTH(5),
      .C_COMMON_CLOCK(0),
      .C_COUNT_TYPE(0),
      .C_DEFAULT_VALUE("BlankString"),
      .C_DOUT_RST_VAL("0"),
      .C_ENABLE_RLOCS(0),
      .C_FAMILY(C_FAMILY),
      .C_FULL_FLAGS_RST_VAL(0),
      .C_HAS_ALMOST_EMPTY(0),
      .C_HAS_ALMOST_FULL(0),
      .C_HAS_BACKUP(0),
      .C_HAS_DATA_COUNT(0),
      .C_HAS_INT_CLK(0),
      .C_HAS_MEMINIT_FILE(0),
      .C_HAS_OVERFLOW(0),
      .C_HAS_RD_DATA_COUNT(0),
      .C_HAS_RD_RST(0),
      .C_HAS_RST(1),
      .C_HAS_SRST(0),
      .C_HAS_UNDERFLOW(0),
      .C_HAS_VALID(0),
      .C_HAS_WR_ACK(0),
      .C_HAS_WR_DATA_COUNT(0),
      .C_HAS_WR_RST(0),
      .C_IMPLEMENTATION_TYPE(2),
      .C_INIT_WR_PNTR_VAL(0),
      .C_MEMORY_TYPE(2),
      .C_MIF_FILE_NAME("BlankString"),
      .C_OPTIMIZATION_MODE(0),
      .C_OVERFLOW_LOW(0),
      .C_PRELOAD_LATENCY(0),
      .C_PRELOAD_REGS(1),
      .C_PRIM_FIFO_TYPE("512x36"),
      .C_PROG_EMPTY_THRESH_ASSERT_VAL(4),
      .C_PROG_EMPTY_THRESH_NEGATE_VAL(5),
      .C_PROG_EMPTY_TYPE(0),
      .C_PROG_FULL_THRESH_ASSERT_VAL(31),
      .C_PROG_FULL_THRESH_NEGATE_VAL(30),
      .C_PROG_FULL_TYPE(0),
      .C_RD_FREQ(1),
      .C_UNDERFLOW_LOW(0),
      .C_USE_DOUT_RST(0),
      .C_USE_ECC(0),
      .C_USE_EMBEDDED_REG(0),
      .C_USE_FIFO16_FLAGS(0),
      .C_USE_FWFT_DATA_COUNT(1),
      .C_VALID_LOW(0),
      .C_WR_ACK_LOW(0),
      .C_WR_FREQ(1),
      .C_WR_RESPONSE_LATENCY(1),
      .C_MSGON_VAL(1),
      .C_ENABLE_RST_SYNC(1),
      .C_ERROR_INJECTION_TYPE(0),
      .C_SYNCHRONIZER_STAGE(C_SYNCHRONIZER_STAGE),
      .C_INTERFACE_TYPE(0),
      .C_AXI_TYPE(0),
      .C_HAS_AXI_WR_CHANNEL(0),
      .C_HAS_AXI_RD_CHANNEL(0),
      .C_HAS_SLAVE_CE(0),
      .C_HAS_MASTER_CE(0),
      .C_ADD_NGC_CONSTRAINT(0),
      .C_USE_COMMON_OVERFLOW(0),
      .C_USE_COMMON_UNDERFLOW(0),
      .C_USE_DEFAULT_SETTINGS(0),
      .C_AXI_ID_WIDTH(4),
      .C_AXI_ADDR_WIDTH(32),
      .C_AXI_DATA_WIDTH(64),
      .C_HAS_AXI_AWUSER(0),
      .C_HAS_AXI_WUSER(0),
      .C_HAS_AXI_BUSER(0),
      .C_HAS_AXI_ARUSER(0),
      .C_HAS_AXI_RUSER(0),
      .C_AXI_ARUSER_WIDTH(1),
      .C_AXI_AWUSER_WIDTH(1),
      .C_AXI_WUSER_WIDTH(1),
      .C_AXI_BUSER_WIDTH(1),
      .C_AXI_RUSER_WIDTH(1),
      .C_HAS_AXIS_TDATA(0),
      .C_HAS_AXIS_TID(0),
      .C_HAS_AXIS_TDEST(0),
      .C_HAS_AXIS_TUSER(0),
      .C_HAS_AXIS_TREADY(1),
      .C_HAS_AXIS_TLAST(0),
      .C_HAS_AXIS_TSTRB(0),
      .C_HAS_AXIS_TKEEP(0),
      .C_AXIS_TDATA_WIDTH(64),
      .C_AXIS_TID_WIDTH(8),
      .C_AXIS_TDEST_WIDTH(4),
      .C_AXIS_TUSER_WIDTH(4),
      .C_AXIS_TSTRB_WIDTH(4),
      .C_AXIS_TKEEP_WIDTH(4),
      .C_WACH_TYPE(0),
      .C_WDCH_TYPE(0),
      .C_WRCH_TYPE(0),
      .C_RACH_TYPE(0),
      .C_RDCH_TYPE(0),
      .C_AXIS_TYPE(0),
      .C_IMPLEMENTATION_TYPE_WACH(1),
      .C_IMPLEMENTATION_TYPE_WDCH(1),
      .C_IMPLEMENTATION_TYPE_WRCH(1),
      .C_IMPLEMENTATION_TYPE_RACH(1),
      .C_IMPLEMENTATION_TYPE_RDCH(1),
      .C_IMPLEMENTATION_TYPE_AXIS(1),
      .C_APPLICATION_TYPE_WACH(0),
      .C_APPLICATION_TYPE_WDCH(0),
      .C_APPLICATION_TYPE_WRCH(0),
      .C_APPLICATION_TYPE_RACH(0),
      .C_APPLICATION_TYPE_RDCH(0),
      .C_APPLICATION_TYPE_AXIS(0),
      .C_USE_ECC_WACH(0),
      .C_USE_ECC_WDCH(0),
      .C_USE_ECC_WRCH(0),
      .C_USE_ECC_RACH(0),
      .C_USE_ECC_RDCH(0),
      .C_USE_ECC_AXIS(0),
      .C_ERROR_INJECTION_TYPE_WACH(0),
      .C_ERROR_INJECTION_TYPE_WDCH(0),
      .C_ERROR_INJECTION_TYPE_WRCH(0),
      .C_ERROR_INJECTION_TYPE_RACH(0),
      .C_ERROR_INJECTION_TYPE_RDCH(0),
      .C_ERROR_INJECTION_TYPE_AXIS(0),
      .C_DIN_WIDTH_WACH(32),
      .C_DIN_WIDTH_WDCH(64),
      .C_DIN_WIDTH_WRCH(2),
      .C_DIN_WIDTH_RACH(32),
      .C_DIN_WIDTH_RDCH(64),
      .C_DIN_WIDTH_AXIS(1),
      .C_WR_DEPTH_WACH(16),
      .C_WR_DEPTH_WDCH(1024),
      .C_WR_DEPTH_WRCH(16),
      .C_WR_DEPTH_RACH(16),
      .C_WR_DEPTH_RDCH(1024),
      .C_WR_DEPTH_AXIS(1024),
      .C_WR_PNTR_WIDTH_WACH(4),
      .C_WR_PNTR_WIDTH_WDCH(10),
      .C_WR_PNTR_WIDTH_WRCH(4),
      .C_WR_PNTR_WIDTH_RACH(4),
      .C_WR_PNTR_WIDTH_RDCH(10),
      .C_WR_PNTR_WIDTH_AXIS(10),
      .C_HAS_DATA_COUNTS_WACH(0),
      .C_HAS_DATA_COUNTS_WDCH(0),
      .C_HAS_DATA_COUNTS_WRCH(0),
      .C_HAS_DATA_COUNTS_RACH(0),
      .C_HAS_DATA_COUNTS_RDCH(0),
      .C_HAS_DATA_COUNTS_AXIS(0),
      .C_HAS_PROG_FLAGS_WACH(0),
      .C_HAS_PROG_FLAGS_WDCH(0),
      .C_HAS_PROG_FLAGS_WRCH(0),
      .C_HAS_PROG_FLAGS_RACH(0),
      .C_HAS_PROG_FLAGS_RDCH(0),
      .C_HAS_PROG_FLAGS_AXIS(0),
      .C_PROG_FULL_TYPE_WACH(0),
      .C_PROG_FULL_TYPE_WDCH(0),
      .C_PROG_FULL_TYPE_WRCH(0),
      .C_PROG_FULL_TYPE_RACH(0),
      .C_PROG_FULL_TYPE_RDCH(0),
      .C_PROG_FULL_TYPE_AXIS(0),
      .C_PROG_FULL_THRESH_ASSERT_VAL_WACH(1023),
      .C_PROG_FULL_THRESH_ASSERT_VAL_WDCH(1023),
      .C_PROG_FULL_THRESH_ASSERT_VAL_WRCH(1023),
      .C_PROG_FULL_THRESH_ASSERT_VAL_RACH(1023),
      .C_PROG_FULL_THRESH_ASSERT_VAL_RDCH(1023),
      .C_PROG_FULL_THRESH_ASSERT_VAL_AXIS(1023),
      .C_PROG_EMPTY_TYPE_WACH(0),
      .C_PROG_EMPTY_TYPE_WDCH(0),
      .C_PROG_EMPTY_TYPE_WRCH(0),
      .C_PROG_EMPTY_TYPE_RACH(0),
      .C_PROG_EMPTY_TYPE_RDCH(0),
      .C_PROG_EMPTY_TYPE_AXIS(0),
      .C_PROG_EMPTY_THRESH_ASSERT_VAL_WACH(1022),
      .C_PROG_EMPTY_THRESH_ASSERT_VAL_WDCH(1022),
      .C_PROG_EMPTY_THRESH_ASSERT_VAL_WRCH(1022),
      .C_PROG_EMPTY_THRESH_ASSERT_VAL_RACH(1022),
      .C_PROG_EMPTY_THRESH_ASSERT_VAL_RDCH(1022),
      .C_PROG_EMPTY_THRESH_ASSERT_VAL_AXIS(1022),
      .C_REG_SLICE_MODE_WACH(0),
      .C_REG_SLICE_MODE_WDCH(0),
      .C_REG_SLICE_MODE_WRCH(0),
      .C_REG_SLICE_MODE_RACH(0),
      .C_REG_SLICE_MODE_RDCH(0),
      .C_REG_SLICE_MODE_AXIS(0),
      .C_AXI_LEN_WIDTH(8),
      .C_AXI_LOCK_WIDTH(2)
    ) dw_fifogen_awpop (
      .clk(1'b0),
      .wr_clk(M_AXI_ACLK),
      .rd_clk(S_AXI_ACLK),
      .rst(awpop_reset),
      .wr_rst(1'b0),
      .rd_rst(1'b0),
      .srst(1'b0),
      .din(1'b0),
      .dout(),
      .full(),
      .empty(aw_pop_event),
      .wr_en(aw_pop),
      .rd_en(aw_pop_resync),
      .backup(1'b0),
      .backup_marker(1'b0),
      .prog_empty_thresh(5'b0),
      .prog_empty_thresh_assert(5'b0),
      .prog_empty_thresh_negate(5'b0),
      .prog_full_thresh(5'b0),
      .prog_full_thresh_assert(5'b0),
      .prog_full_thresh_negate(5'b0),
      .int_clk(1'b0),
      .injectdbiterr(1'b0),
      .injectsbiterr(1'b0),
      .almost_full(),
      .wr_ack(),
      .overflow(),
      .almost_empty(),
      .valid(),
      .underflow(),
      .data_count(),
      .rd_data_count(),
      .wr_data_count(),
      .prog_full(),
      .prog_empty(),
      .sbiterr(),
      .dbiterr(),
      .m_aclk(1'b0),
      .s_aclk(1'b0),
      .s_aresetn(1'b0),
      .m_aclk_en(1'b0),
      .s_aclk_en(1'b0),
      .s_axi_awid(4'b0),
      .s_axi_awaddr(32'b0),
      .s_axi_awlen(8'b0),
      .s_axi_awsize(3'b0),
      .s_axi_awburst(2'b0),
      .s_axi_awlock(2'b0),
      .s_axi_awcache(4'b0),
      .s_axi_awprot(3'b0),
      .s_axi_awqos(4'b0),
      .s_axi_awregion(4'b0),
      .s_axi_awuser(1'b0),
      .s_axi_awvalid(1'b0),
      .s_axi_awready(),
      .s_axi_wid(4'b0),
      .s_axi_wdata(64'b0),
      .s_axi_wstrb(8'b0),
      .s_axi_wlast(1'b0),
      .s_axi_wuser(1'b0),
      .s_axi_wvalid(1'b0),
      .s_axi_wready(),
      .s_axi_bid(),
      .s_axi_bresp(),
      .s_axi_buser(),
      .s_axi_bvalid(),
      .s_axi_bready(1'b0),
      .m_axi_awid(),
      .m_axi_awaddr(),
      .m_axi_awlen(),
      .m_axi_awsize(),
      .m_axi_awburst(),
      .m_axi_awlock(),
      .m_axi_awcache(),
      .m_axi_awprot(),
      .m_axi_awqos(),
      .m_axi_awregion(),
      .m_axi_awuser(),
      .m_axi_awvalid(),
      .m_axi_awready(1'b0),
      .m_axi_wid(),
      .m_axi_wdata(),
      .m_axi_wstrb(),
      .m_axi_wlast(),
      .m_axi_wuser(),
      .m_axi_wvalid(),
      .m_axi_wready(1'b0),
      .m_axi_bid(4'b0),
      .m_axi_bresp(2'b0),
      .m_axi_buser(1'b0),
      .m_axi_bvalid(1'b0),
      .m_axi_bready(),
      .s_axi_arid(4'b0),
      .s_axi_araddr(32'b0),
      .s_axi_arlen(8'b0),
      .s_axi_arsize(3'b0),
      .s_axi_arburst(2'b0),
      .s_axi_arlock(2'b0),
      .s_axi_arcache(4'b0),
      .s_axi_arprot(3'b0),
      .s_axi_arqos(4'b0),
      .s_axi_arregion(4'b0),
      .s_axi_aruser(1'b0),
      .s_axi_arvalid(1'b0),
      .s_axi_arready(),
      .s_axi_rid(),
      .s_axi_rdata(),
      .s_axi_rresp(),
      .s_axi_rlast(),
      .s_axi_ruser(),
      .s_axi_rvalid(),
      .s_axi_rready(1'b0),
      .m_axi_arid(),
      .m_axi_araddr(),
      .m_axi_arlen(),
      .m_axi_arsize(),
      .m_axi_arburst(),
      .m_axi_arlock(),
      .m_axi_arcache(),
      .m_axi_arprot(),
      .m_axi_arqos(),
      .m_axi_arregion(),
      .m_axi_aruser(),
      .m_axi_arvalid(),
      .m_axi_arready(1'b0),
      .m_axi_rid(4'b0),
      .m_axi_rdata(64'b0),
      .m_axi_rresp(2'b0),
      .m_axi_rlast(1'b0),
      .m_axi_ruser(1'b0),
      .m_axi_rvalid(1'b0),
      .m_axi_rready(),
      .s_axis_tvalid(1'b0),
      .s_axis_tready(),
      .s_axis_tdata(64'b0),
      .s_axis_tstrb(4'b0),
      .s_axis_tkeep(4'b0),
      .s_axis_tlast(1'b0),
      .s_axis_tid(8'b0),
      .s_axis_tdest(4'b0),
      .s_axis_tuser(4'b0),
      .m_axis_tvalid(),
      .m_axis_tready(1'b0),
      .m_axis_tdata(),
      .m_axis_tstrb(),
      .m_axis_tkeep(),
      .m_axis_tlast(),
      .m_axis_tid(),
      .m_axis_tdest(),
      .m_axis_tuser(),
      .axi_aw_injectsbiterr(1'b0),
      .axi_aw_injectdbiterr(1'b0),
      .axi_aw_prog_full_thresh(4'b0),
      .axi_aw_prog_empty_thresh(4'b0),
      .axi_aw_data_count(),
      .axi_aw_wr_data_count(),
      .axi_aw_rd_data_count(),
      .axi_aw_sbiterr(),
      .axi_aw_dbiterr(),
      .axi_aw_overflow(),
      .axi_aw_underflow(),
      .axi_aw_prog_full(),
      .axi_aw_prog_empty(),
      .axi_w_injectsbiterr(1'b0),
      .axi_w_injectdbiterr(1'b0),
      .axi_w_prog_full_thresh(10'b0),
      .axi_w_prog_empty_thresh(10'b0),
      .axi_w_data_count(),
      .axi_w_wr_data_count(),
      .axi_w_rd_data_count(),
      .axi_w_sbiterr(),
      .axi_w_dbiterr(),
      .axi_w_overflow(),
      .axi_w_underflow(),
      .axi_b_injectsbiterr(1'b0),
      .axi_w_prog_full(),
      .axi_w_prog_empty(),
      .axi_b_injectdbiterr(1'b0),
      .axi_b_prog_full_thresh(4'b0),
      .axi_b_prog_empty_thresh(4'b0),
      .axi_b_data_count(),
      .axi_b_wr_data_count(),
      .axi_b_rd_data_count(),
      .axi_b_sbiterr(),
      .axi_b_dbiterr(),
      .axi_b_overflow(),
      .axi_b_underflow(),
      .axi_ar_injectsbiterr(1'b0),
      .axi_b_prog_full(),
      .axi_b_prog_empty(),
      .axi_ar_injectdbiterr(1'b0),
      .axi_ar_prog_full_thresh(4'b0),
      .axi_ar_prog_empty_thresh(4'b0),
      .axi_ar_data_count(),
      .axi_ar_wr_data_count(),
      .axi_ar_rd_data_count(),
      .axi_ar_sbiterr(),
      .axi_ar_dbiterr(),
      .axi_ar_overflow(),
      .axi_ar_underflow(),
      .axi_ar_prog_full(),
      .axi_ar_prog_empty(),
      .axi_r_injectsbiterr(1'b0),
      .axi_r_injectdbiterr(1'b0),
      .axi_r_prog_full_thresh(10'b0),
      .axi_r_prog_empty_thresh(10'b0),
      .axi_r_data_count(),
      .axi_r_wr_data_count(),
      .axi_r_rd_data_count(),
      .axi_r_sbiterr(),
      .axi_r_dbiterr(),
      .axi_r_overflow(),
      .axi_r_underflow(),
      .axis_injectsbiterr(1'b0),
      .axi_r_prog_full(),
      .axi_r_prog_empty(),
      .axis_injectdbiterr(1'b0),
      .axis_prog_full_thresh(10'b0),
      .axis_prog_empty_thresh(10'b0),
      .axis_data_count(),
      .axis_wr_data_count(),
      .axis_rd_data_count(),
      .axis_sbiterr(),
      .axis_dbiterr(),
      .axis_overflow(),
      .axis_underflow(),
      .axis_prog_full(),
      .axis_prog_empty(),
      .wr_rst_busy(),
      .rd_rst_busy(),
      .sleep(1'b0)
    );
    
    assign aw_pop_resync = ~aw_pop_event;
  end else begin : gen_no_awpop_fifo
    assign aw_pop_resync = aw_pop | aw_pop_extend;
  end

  endgenerate
endmodule


// -- (c) Copyright 2012 Xilinx, Inc. All rights reserved.
// --
// -- This file contains confidential and proprietary information
// -- of Xilinx, Inc. and is protected under U.S. and 
// -- international copyright and other intellectual property
// -- laws.
// --
// -- DISCLAIMER
// -- This disclaimer is not a license and does not grant any
// -- rights to the materials distributed herewith. Except as
// -- otherwise provided in a valid license issued to you by
// -- Xilinx, and to the maximum extent permitted by applicable
// -- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// -- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// -- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// -- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// -- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// -- (2) Xilinx shall not be liable (whether in contract or tort,
// -- including negligence, or under any other theory of
// -- liability) for any loss or damage of any kind or nature
// -- related to, arising under or in connection with these
// -- materials, including for any direct, or any indirect,
// -- special, incidental, or consequential loss or damage
// -- (including loss of data, profits, goodwill, or any type of
// -- loss or damage suffered as a result of any action brought
// -- by a third party) even if such damage or loss was
// -- reasonably foreseeable or Xilinx had been advised of the
// -- possibility of the same.
// --
// -- CRITICAL APPLICATIONS
// -- Xilinx products are not designed or intended to be fail-
// -- safe, or for use in any application requiring fail-safe
// -- performance, such as life-support or safety devices or
// -- systems, Class III medical devices, nuclear facilities,
// -- applications related to the deployment of airbags, or any
// -- other applications that could lead to death, personal
// -- injury, or severe property or environmental damage
// -- (individually and collectively, "Critical
// -- Applications"). Customer assumes the sole risk and
// -- liability of any use of Xilinx products in Critical
// -- Applications, subject only to applicable laws and
// -- regulations governing limitations on product liability.
// --
// -- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// -- PART OF THIS FILE AT ALL TIMES.
//-----------------------------------------------------------------------------
//
// Description: Write Data Up-Sizer with Packet FIFO
//
//--------------------------------------------------------------------------

`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_dwidth_converter_v2_1_12_r_upsizer_pktfifo #
  (
   parameter         C_FAMILY                         = "virtex7", 
                       // FPGA Family. Current version: virtex6 or spartan6.
   parameter integer C_S_AXI_DATA_WIDTH               = 64,
                       // Width of s_axi_wdata and s_axi_rdata.
                       // Range: 32, 64, 128, 256, 512, 1024.
   parameter integer C_M_AXI_DATA_WIDTH               = 32,
                       // Width of m_axi_wdata and m_axi_rdata. 
                       // Assume always >= than C_S_AXI_DATA_WIDTH.
                       // Range: 32, 64, 128, 256, 512, 1024.
   parameter integer C_AXI_ID_WIDTH                   = 1, 
   parameter integer C_AXI_ADDR_WIDTH                 = 32, 
   parameter         C_CLK_CONV         = 1'b0,
   parameter integer C_S_AXI_ACLK_RATIO = 1,     // Clock frequency ratio of SI w.r.t. MI.
                                                 // Range = [1..16].
   parameter integer C_M_AXI_ACLK_RATIO = 2,     // Clock frequency ratio of MI w.r.t. SI.
                                                 // Range = [2..16] if C_S_AXI_ACLK_RATIO = 1; else must be 1.
   parameter integer C_AXI_IS_ACLK_ASYNC = 0,    // Indicates whether S and M clocks are asynchronous.
                                                 // FUTURE FEATURE
                                                 // Range = [0, 1].
   parameter integer C_S_AXI_BYTES_LOG                = 3,
                       // Log2 of number of 32bit word on SI-side.
   parameter integer C_M_AXI_BYTES_LOG                = 3,
                       // Log2 of number of 32bit word on MI-side.
   parameter integer C_RATIO                          = 2,
                       // Up-Sizing ratio for data.
   parameter integer C_RATIO_LOG                      = 1,
                       // Log2 of Up-Sizing ratio for data.
   parameter integer C_SYNCHRONIZER_STAGE             = 3
   )
  (
   // Global Signals
   input  wire                              S_AXI_ACLK,
   input  wire                              M_AXI_ACLK,
   input  wire                              S_AXI_ARESETN,
   input  wire                              M_AXI_ARESETN,

   // Command Interface
   input  wire [C_AXI_ADDR_WIDTH-1:0]       cmd_si_addr,
   input  wire [C_AXI_ID_WIDTH-1:0]         cmd_si_id,
   input  wire [8-1:0]                      cmd_si_len,
   input  wire [3-1:0]                      cmd_si_size,
   input  wire [2-1:0]                      cmd_si_burst,
   output wire                              cmd_ready,
   
   // Slave Interface Write Address Port
   input  wire [C_AXI_ADDR_WIDTH-1:0]          S_AXI_ARADDR,
   input  wire [8-1:0]                         S_AXI_ARLEN,
   input  wire [3-1:0]                         S_AXI_ARSIZE,
   input  wire [2-1:0]                         S_AXI_ARBURST,
   input  wire [2-1:0]                         S_AXI_ARLOCK,
   input  wire [4-1:0]                         S_AXI_ARCACHE,
   input  wire [3-1:0]                         S_AXI_ARPROT,
   input  wire [4-1:0]                         S_AXI_ARREGION,
   input  wire [4-1:0]                         S_AXI_ARQOS,
   input  wire                                 S_AXI_ARVALID,
   output wire                                 S_AXI_ARREADY,

   // Master Interface Write Address Port
   output wire [C_AXI_ADDR_WIDTH-1:0]          M_AXI_ARADDR,
   output wire [8-1:0]                         M_AXI_ARLEN,
   output wire [3-1:0]                         M_AXI_ARSIZE,
   output wire [2-1:0]                         M_AXI_ARBURST,
   output wire [2-1:0]                         M_AXI_ARLOCK,
   output wire [4-1:0]                         M_AXI_ARCACHE,
   output wire [3-1:0]                         M_AXI_ARPROT,
   output wire [4-1:0]                         M_AXI_ARREGION,
   output wire [4-1:0]                         M_AXI_ARQOS,
   output wire                                 M_AXI_ARVALID,
   input  wire                                 M_AXI_ARREADY,

   // Slave Interface Write Data Ports
   output wire [C_AXI_ID_WIDTH-1:0]         S_AXI_RID,
   output wire [C_S_AXI_DATA_WIDTH-1:0]     S_AXI_RDATA,
   output wire [1:0]                        S_AXI_RRESP,
   output wire                              S_AXI_RLAST,
   output wire                              S_AXI_RVALID,
   input  wire                              S_AXI_RREADY,

   // Master Interface Write Data Ports
   input  wire [C_M_AXI_DATA_WIDTH-1:0]     M_AXI_RDATA,
   input  wire [1:0]                        M_AXI_RRESP,
   input  wire                              M_AXI_RLAST,
   input  wire                              M_AXI_RVALID,
   output wire                              M_AXI_RREADY,
   
   input wire                               SAMPLE_CYCLE_EARLY,
   input wire                               SAMPLE_CYCLE

   );

  assign cmd_ready = 1'b1;

  localparam integer P_SI_BYTES = C_S_AXI_DATA_WIDTH / 8;
  localparam integer P_MI_BYTES = C_M_AXI_DATA_WIDTH / 8;
  localparam integer P_MAX_BYTES = 1024 / 8;
  localparam integer P_SI_SIZE = f_ceil_log2(P_SI_BYTES);
  localparam integer P_MI_SIZE = f_ceil_log2(P_MI_BYTES);
  localparam integer P_RATIO = C_M_AXI_DATA_WIDTH / C_S_AXI_DATA_WIDTH;
  localparam integer P_RATIO_LOG = f_ceil_log2(P_RATIO);
  localparam integer P_NUM_BUF = (P_RATIO == 2) ? 4 : 8;
  localparam integer P_BUF_LIMIT = P_NUM_BUF - 1;
  localparam integer P_NUM_BUF_LOG = f_ceil_log2(P_NUM_BUF);
  localparam integer P_M_RBUFFER_DEPTH = 512;
  localparam integer P_M_RBUFFER_DEPTH_LOG = 9;
  localparam integer P_S_RBUFFER_DEPTH = P_M_RBUFFER_DEPTH * P_RATIO;
  localparam integer P_S_RBUFFER_DEPTH_LOG = f_ceil_log2(P_S_RBUFFER_DEPTH);
  localparam integer P_M_RBUFFER_WORDS = P_M_RBUFFER_DEPTH / P_NUM_BUF;
  localparam integer P_M_RBUFFER_WORDS_LOG = f_ceil_log2(P_M_RBUFFER_WORDS);
  localparam integer P_S_RBUFFER_WORDS = P_M_RBUFFER_WORDS * P_RATIO;
  localparam integer P_S_RBUFFER_WORDS_LOG = f_ceil_log2(P_S_RBUFFER_WORDS);
  localparam integer P_M_RBUFFER_BYTES = P_M_RBUFFER_WORDS * P_MI_BYTES;
  localparam integer P_M_RBUFFER_BYTES_LOG = f_ceil_log2(P_M_RBUFFER_BYTES);
  localparam integer P_MAX_RBUFFER_BYTES_LOG = f_ceil_log2((P_M_RBUFFER_DEPTH / 4) * P_MAX_BYTES);
  localparam [1:0] P_INCR = 2'b01, P_WRAP = 2'b10, P_FIXED = 2'b00;
  localparam  P_SI_LT_MI = (C_S_AXI_ACLK_RATIO < C_M_AXI_ACLK_RATIO);
  localparam integer P_ACLK_RATIO = P_SI_LT_MI ? (C_M_AXI_ACLK_RATIO / C_S_AXI_ACLK_RATIO) : (C_S_AXI_ACLK_RATIO / C_M_AXI_ACLK_RATIO);
  localparam integer P_NUM_RAMB = C_M_AXI_DATA_WIDTH / 32;
  localparam integer P_S_RAMB_WIDTH = C_S_AXI_DATA_WIDTH / P_NUM_RAMB;
  localparam integer P_S_RAMB_PWIDTH = (P_S_RAMB_WIDTH < 8) ? P_S_RAMB_WIDTH : ((P_SI_BYTES * 9) / P_NUM_RAMB);
  localparam integer P_S_CMD_WIDTH = P_MI_SIZE+4 + C_AXI_ID_WIDTH + 4 + 3 + 8 + 3 + 2;
  localparam integer P_M_CMD_WIDTH = P_MI_SIZE+4 + 8 + 3 + 2;
  localparam integer P_ARFIFO_WIDTH = 29 + C_AXI_ADDR_WIDTH;
  localparam integer P_COMMON_CLOCK = (C_CLK_CONV & C_AXI_IS_ACLK_ASYNC) ? 0 : 1;
  
  genvar i;
  genvar j;
  reg  S_AXI_ARREADY_i = 1'b0;
  reg  M_AXI_RREADY_i = 1'b0;
  reg  M_AXI_ARVALID_i = 1'b0;
  wire [C_AXI_ADDR_WIDTH-1:0] M_AXI_ARADDR_i;
  wire [7:0] M_AXI_ARLEN_i;
  wire [2:0] M_AXI_ARSIZE_i;
  wire [1:0] M_AXI_ARBURST_i;
  wire M_AXI_ARLOCK_i;
  wire ar_push;
  wire ar_fifo_ready;
  wire ar_fifo_valid;
  wire ar_pop;
  wire s_rbuf_en;
  wire [P_NUM_RAMB-1:0] m_rbuf_en;
  reg  [P_NUM_BUF_LOG-1:0] s_buf;
  reg  [P_NUM_BUF_LOG-1:0] m_buf;
  reg  [P_NUM_BUF_LOG-1:0] buf_cnt;
  wire buf_limit;
  reg  [7:0] s_rcnt;
  wire [P_NUM_RAMB*16-1 : 0] s_rdata ;
  wire [C_M_AXI_DATA_WIDTH-1 : 0] m_rdata ;
  reg  [1:0] s_rburst;
  reg  [2:0] s_rsize;
  reg  [3:0] s_wrap_cnt;
  reg  s_rvalid;
  reg  s_rvalid_d1;
  reg  s_rvalid_d2;
  reg  first_rvalid_d1;
  reg  s_rlast;
  reg  s_rlast_d1;
  reg  s_rlast_d2;
  wire [1:0] s_rresp;
  wire [3:0] s_rresp_i;
  wire [1:0] m_rresp;
  wire [3:0] m_rresp_i;
  reg  [1:0] s_rresp_reg;
  reg  [1:0] m_rresp_reg;
  reg  [1:0] s_rresp_d1;
  reg  [1:0] s_rresp_d2;
  reg  [1:0] s_rresp_first;
  reg  [1:0] m_rburst;
  reg  [2:0] m_rsize;
  reg  [3:0] m_wrap_cnt;
  wire s_cmd_push;
  wire s_cmd_pop;
  wire s_cmd_empty;
  wire s_cmd_full;
  wire m_cmd_push;
  wire m_cmd_pop;
  wire m_cmd_empty;
  wire m_cmd_full;
  reg  m_cmd_valid;
  wire [P_S_CMD_WIDTH-1 : 0] s_ar_cmd;
  wire [P_S_CMD_WIDTH-1 : 0] s_r_cmd;
  wire [P_M_CMD_WIDTH-1 : 0] m_ar_cmd;
  wire [P_M_CMD_WIDTH-1 : 0] m_r_cmd;
  wire [P_MI_SIZE+4-1:0] s_cmd_addr;
  wire [C_AXI_ID_WIDTH-1:0] s_cmd_id;
  reg  [C_AXI_ID_WIDTH-1:0] s_id_reg;
  reg  [C_AXI_ID_WIDTH-1:0] s_id_d1;
  reg  [C_AXI_ID_WIDTH-1:0] s_id_d2;
  wire [3:0] s_cmd_conv_len;
  reg  [3:0] s_conv_len;
  wire [2:0] s_cmd_conv_size;
  reg  [2:0] s_conv_size;
  wire [7:0] s_cmd_len;
  wire [2:0] s_cmd_size;
  wire [1:0] s_cmd_burst;
  wire [P_MI_SIZE+4-1:0] m_cmd_addr;
  wire [C_AXI_ID_WIDTH-1:0] m_cmd_id;
  wire [7:0] m_cmd_len;
  wire [2:0] m_cmd_size;
  wire [1:0] m_cmd_burst;
  wire m_transfer;
  wire rresp_fifo_push;
  wire rresp_fifo_pop;
  wire rresp_fifo_empty;
  wire rresp_fifo_full;
  reg  rresp_wrap;
  wire rresp_reuse;
  reg  s_rresp_fifo_stall;
  reg  m_rresp_fifo_stall;
  wire s_eol;
  reg  [P_M_RBUFFER_BYTES_LOG-1:0] s_raddr;
  reg  [P_M_RBUFFER_BYTES_LOG-1:0] m_raddr;
  wire [P_M_RBUFFER_BYTES_LOG-1:0] m_raddr_incr;
  reg  [P_M_RBUFFER_BYTES_LOG-1:0] s_wrap_addr;
  reg  [P_M_RBUFFER_BYTES_LOG-1:0] m_wrap_addr;
  wire [13:0] s_rbuf_addr;
  wire [13:0] m_rbuf_addr;
  wire [3:0] m_rbuf_we;  
  reg  large_incr_last;
  reg  [3:0] large_incr_mask;
  
  wire m_aclk;
  wire m_aresetn;
  wire s_aresetn;
  wire ar_fifo_s_aclk;
  wire ar_fifo_m_aclk;
  wire ar_fifo_aresetn;
  wire s_fifo_rst;
  wire m_fifo_rst;
  wire rresp_fifo_clk;
  wire rresp_fifo_wrclk;
  wire rresp_fifo_rdclk;
  wire rresp_fifo_rst;
  wire s_sample_cycle;
  wire s_sample_cycle_early;
  wire m_sample_cycle;
  wire m_sample_cycle_early;
  wire fast_aclk;
  reg  reset_r;
  reg  s_reset_r;
  reg  m_reset_r;
  reg  fast_aresetn_r;
  reg  fast_reset_r;
  
  function integer f_ceil_log2
    (
     input integer x
     );
    integer acc;
    begin
      acc=0;
      while ((2**acc) < x)
        acc = acc + 1;
      f_ceil_log2 = acc;
    end
  endfunction

  // RAMB SI-side port address
  function [13:0] f_s_rbuf_addr
    (
      input [P_M_RBUFFER_BYTES_LOG-1:0] addr,
      input [2:0] size,
      input [1:0] burst,
      input [P_NUM_BUF_LOG-1:0] s_buf
    );
    reg [P_MAX_RBUFFER_BYTES_LOG-1:0] addr_i;
    reg [P_MAX_RBUFFER_BYTES_LOG-1:0] sparse_addr;
    begin
      if (burst == P_FIXED) begin
        sparse_addr = addr;
      end else begin
      addr_i = addr;
        case (P_MI_SIZE)
          3: case (size)
            3'h0:    sparse_addr = {addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : 3], addr_i[0:0], addr_i[2:0]};
            default: sparse_addr =  addr_i;
          endcase
          4: case (size)
            3'h0:    sparse_addr = {addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : 4], addr_i[1:0], addr_i[3:0]};
            3'h1:    sparse_addr = {addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : 4], addr_i[1:1], addr_i[3:0]};
            default: sparse_addr =  addr_i;
          endcase
          5: case (size)
            3'h0:    sparse_addr = {addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : 5], addr_i[2:0], addr_i[4:0]};
            3'h1:    sparse_addr = {addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : 5], addr_i[2:1], addr_i[4:0]};
            3'h2:    sparse_addr = {addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : 5], addr_i[2:2], addr_i[4:0]};
            default: sparse_addr =  addr_i;
          endcase
          6: case (size)
            3'h0:    sparse_addr = {addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : 6], addr_i[3:1], addr_i[5:0]};
            3'h1:    sparse_addr = {addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : 6], addr_i[3:1], addr_i[5:0]};
            3'h2:    sparse_addr = {addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : 6], addr_i[3:2], addr_i[5:0]};
            3'h3:    sparse_addr = {addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : 6], addr_i[3:3], addr_i[5:0]};
            default: sparse_addr =  addr_i;
          endcase
          7: case (size)
            3'h0:    sparse_addr = {addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : 7], addr_i[4:2], addr_i[6:0]};
            3'h1:    sparse_addr = {addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : 7], addr_i[4:2], addr_i[6:0]};
            3'h2:    sparse_addr = {addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : 7], addr_i[4:2], addr_i[6:0]};
            3'h3:    sparse_addr = {addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : 7], addr_i[4:3], addr_i[6:0]};
            3'h4:    sparse_addr = {addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : 7], addr_i[4:4], addr_i[6:0]};
            default: sparse_addr =  addr_i;
          endcase
        endcase
      end
      f_s_rbuf_addr = {s_buf, {14-P_NUM_BUF_LOG{1'b0}}};
      f_s_rbuf_addr[13-P_NUM_BUF_LOG : 5-P_RATIO_LOG] = sparse_addr[P_SI_SIZE +: 9+P_RATIO_LOG-P_NUM_BUF_LOG];
    end
  endfunction
 
  // RAMB MI-side port address
  function [13:0] f_m_rbuf_addr
    (
      input [P_M_RBUFFER_BYTES_LOG-1:0] addr,
      input [2:0] size,
      input [1:0] burst,
      input [P_NUM_BUF_LOG-1:0] m_buf
    );
    reg [P_MAX_RBUFFER_BYTES_LOG-1:0] addr_i;
    reg [P_MAX_RBUFFER_BYTES_LOG-1:0] sparse_addr;
    begin
      addr_i = addr;
      if (burst == P_FIXED) begin
        sparse_addr = addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : P_MI_SIZE];
      end else begin
        case (P_MI_SIZE)
          3: case (size)
            3'h0:    sparse_addr = {addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : P_MI_SIZE], addr_i[0:0]};
            default: sparse_addr =  addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : P_MI_SIZE];
          endcase
          4: case (size)
            3'h0:    sparse_addr = {addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : P_MI_SIZE], addr_i[1:0]};
            3'h1:    sparse_addr = {addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : P_MI_SIZE], addr_i[1:1]};
            default: sparse_addr =  addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : P_MI_SIZE];
          endcase
          5: case (size)
            3'h0:    sparse_addr = {addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : P_MI_SIZE], addr_i[2:0]};
            3'h1:    sparse_addr = {addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : P_MI_SIZE], addr_i[2:1]};
            3'h2:    sparse_addr = {addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : P_MI_SIZE], addr_i[2:2]};
            default: sparse_addr =  addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : P_MI_SIZE];
          endcase
          6: case (size)
            3'h0:    sparse_addr = {addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : P_MI_SIZE], addr_i[3:1]};
            3'h1:    sparse_addr = {addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : P_MI_SIZE], addr_i[3:1]};
            3'h2:    sparse_addr = {addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : P_MI_SIZE], addr_i[3:2]};
            3'h3:    sparse_addr = {addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : P_MI_SIZE], addr_i[3:3]};
            default: sparse_addr =  addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : P_MI_SIZE];
          endcase
          7: case (size)
            3'h0:    sparse_addr = {addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : P_MI_SIZE], addr_i[4:2]};
            3'h1:    sparse_addr = {addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : P_MI_SIZE], addr_i[4:2]};
            3'h2:    sparse_addr = {addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : P_MI_SIZE], addr_i[4:2]};
            3'h3:    sparse_addr = {addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : P_MI_SIZE], addr_i[4:3]};
            3'h4:    sparse_addr = {addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : P_MI_SIZE], addr_i[4:4]};
            default: sparse_addr =  addr_i[P_MAX_RBUFFER_BYTES_LOG-1 : P_MI_SIZE];
          endcase
        endcase
      end
      f_m_rbuf_addr = {m_buf, sparse_addr[0 +: 9-P_NUM_BUF_LOG], 5'b0};
    end
  endfunction
 
  // RAMB MI-side port write-enables
  function [3:0] f_m_rbuf_we
    (
      input [P_M_RBUFFER_BYTES_LOG-1:0] addr,
      input [2:0] size
    );
    reg [P_MAX_RBUFFER_BYTES_LOG-1:0] addr_i;
    begin
      addr_i = addr;
      case (P_MI_SIZE)
        3: case (size)
          3'h2:    f_m_rbuf_we = addr_i[2] ? 4'b1100 : 4'b0011;
          3'h3:    f_m_rbuf_we = 4'b1111;
          default: f_m_rbuf_we = 4'b0001 << addr_i[2:1];
        endcase
        4: case (size)
          3'h3:    f_m_rbuf_we = addr_i[3] ? 4'b1100 : 4'b0011;
          3'h4:    f_m_rbuf_we = 4'b1111;
          default: f_m_rbuf_we = 4'b0001 << addr_i[3:2];
        endcase
        5: case (size)
          3'h4:    f_m_rbuf_we = addr_i[4] ? 4'b1100 : 4'b0011;
          3'h5:    f_m_rbuf_we = 4'b1111;
          default: f_m_rbuf_we = 4'b0001 << addr_i[4:3];
        endcase
        6: case (size)
          3'h5:    f_m_rbuf_we = addr_i[5] ? 4'b1100 : 4'b0011;
          3'h6:    f_m_rbuf_we = 4'b1111;
          default: f_m_rbuf_we = 4'b0001 << addr_i[5:4];
        endcase
        7: case (size)
          3'h6:    f_m_rbuf_we = addr_i[6] ? 4'b1100 : 4'b0011;
          3'h7:    f_m_rbuf_we = 4'b1111;
          default: f_m_rbuf_we = 4'b0001 << addr_i[6:5];
        endcase
      endcase
    end
  endfunction
 
  // RAMB MI-side write-enable mask for last beat of long unaligned INCR burst wrapping to 1st buffer addr.
  //   Only applies to full-size SI bursts when RATIO = 2 or 4.
  function [3:0] f_large_incr_mask
    (
      input [P_M_RBUFFER_BYTES_LOG-1:0] addr
    );
    reg [P_MAX_RBUFFER_BYTES_LOG-1:0] addr_i;
    reg [3:0] result;
    begin
      addr_i = addr;
      result = 4'b1111;
      case (P_MI_SIZE)
        3:         result = 4'b0011;
        4: case (P_SI_SIZE)
          3'h3:    result = 4'b0011;
          3'h2: case (addr_i[3:2])
            2'b01: result = 4'b0001;
            2'b10: result = 4'b0011;
            2'b11: result = 4'b0111;
          endcase
        endcase
        5: case (P_SI_SIZE)
          3'h4:    result = 4'b0011;
          3'h3: case (addr_i[4:3])
            2'b01: result = 4'b0001;
            2'b10: result = 4'b0011;
            2'b11: result = 4'b0111;
          endcase
        endcase
        6: case (P_SI_SIZE)
          3'h5:    result = 4'b0011;
          3'h4: case (addr_i[5:4])
            2'b01: result = 4'b0001;
            2'b10: result = 4'b0011;
            2'b11: result = 4'b0111;
          endcase
        endcase
        7: case (P_SI_SIZE)
          3'h6:    result = 4'b0011;
          3'h5: case (addr_i[6:5])
            2'b01: result = 4'b0001;
            2'b10: result = 4'b0011;
            2'b11: result = 4'b0111;
          endcase
        endcase
      endcase
      f_large_incr_mask = result;
    end
  endfunction
 
  // RAMB MI-side port-enables
  function [P_NUM_RAMB-1:0] f_m_rbuf_en
    (
      input [P_M_RBUFFER_BYTES_LOG-1:0] addr,
      input [2:0] size
    );
    reg [P_MAX_RBUFFER_BYTES_LOG-1:0] addr_i;
    begin
      addr_i = addr;
      case (P_MI_SIZE)
        6: case (size)
          3'h0:    f_m_rbuf_en = addr_i[0] ? 16'hFF00 : 16'h00FF;
          default: f_m_rbuf_en = 16'hFFFF;
        endcase
        7: case (size)
          3'h0: case (addr_i[1:0])
            2'b00: f_m_rbuf_en = 32'h000000FF;
            2'b01: f_m_rbuf_en = 32'h0000FF00;
            2'b10: f_m_rbuf_en = 32'h00FF0000;
            2'b11: f_m_rbuf_en = 32'hFF000000;
          endcase
          3'h1:    f_m_rbuf_en = addr_i[1] ? 32'hFFFF0000 : 32'h0000FFFF;
          default: f_m_rbuf_en = 32'hFFFFFFFF;
        endcase
        default:   f_m_rbuf_en = {P_NUM_RAMB{1'b1}};
      endcase
    end
  endfunction
 
  // SI-side buffer line fault detection
  function f_s_eol
    (
      input [P_MI_SIZE-1:0] addr,
      input [2:0] s_size,
      input [2:0] m_size
    );
    reg [7-1:0] addr_i;
    begin
      addr_i = addr;
      if (m_size == P_MI_SIZE) begin
        case (P_MI_SIZE)
          3: case (s_size)
            3'h0:    f_s_eol = &(addr_i[2:0]);
            3'h1:    f_s_eol = &(addr_i[2:1]);
            3'h2:    f_s_eol = &(addr_i[2:2]);
          endcase
          4: case (s_size)
            3'h0:    f_s_eol = &(addr_i[3:0]);
            3'h1:    f_s_eol = &(addr_i[3:1]);
            3'h2:    f_s_eol = &(addr_i[3:2]);
            3'h3:    f_s_eol = &(addr_i[3:3]);
          endcase
          5: case (s_size)
            3'h0:    f_s_eol = &(addr_i[4:0]);
            3'h1:    f_s_eol = &(addr_i[4:1]);
            3'h2:    f_s_eol = &(addr_i[4:2]);
            3'h3:    f_s_eol = &(addr_i[4:3]);
            3'h4:    f_s_eol = &(addr_i[4:4]);
          endcase
          6: case (s_size)
            3'h0:    f_s_eol = &(addr_i[5:0]);
            3'h1:    f_s_eol = &(addr_i[5:1]);
            3'h2:    f_s_eol = &(addr_i[5:2]);
            3'h3:    f_s_eol = &(addr_i[5:3]);
            3'h4:    f_s_eol = &(addr_i[5:4]);
            3'h5:    f_s_eol = &(addr_i[5:5]);
          endcase
          7: case (s_size)
            3'h0:    f_s_eol = &(addr_i[6:0]);
            3'h1:    f_s_eol = &(addr_i[6:1]);
            3'h2:    f_s_eol = &(addr_i[6:2]);
            3'h3:    f_s_eol = &(addr_i[6:3]);
            3'h4:    f_s_eol = &(addr_i[6:4]);
            3'h5:    f_s_eol = &(addr_i[6:5]);
            3'h6:    f_s_eol = &(addr_i[6:6]);
          endcase
        endcase
      end else begin
        // Assumes that AR transform is either fully-packed (m_size == P_MI_SIZE) or unpacked (m_size == s_size), no intermediate sizes.
        f_s_eol = 1'b1;
      end
    end
  endfunction
 
  // Number of SI transfers until wrapping (0 = wrap after first transfer; 4'hF = no wrapping)
  function [3:0] f_s_wrap_cnt
    (
      input [P_M_RBUFFER_BYTES_LOG-1:0] addr,
      input [2:0] size,
      input [7:0] len
    );
    reg [3:0] start;
    reg [P_MAX_RBUFFER_BYTES_LOG-1:0] addr_i;
    begin
      addr_i = addr;
      case (P_SI_SIZE)
        2: case (size[1:0])
          2'h0:    start = addr_i[ 0 +: 4];
          2'h1:    start = addr_i[ 1 +: 4];
          default: start = addr_i[ 2 +: 4];
        endcase
        3: case (size[1:0])
          2'h0:    start = addr_i[ 0 +: 4];
          2'h1:    start = addr_i[ 1 +: 4];
          2'h2:    start = addr_i[ 2 +: 4];
          default: start = addr_i[ 3 +: 4];
        endcase
        4: case (size)
          3'h0:    start = addr_i[ 0 +: 4];
          3'h1:    start = addr_i[ 1 +: 4];
          3'h2:    start = addr_i[ 2 +: 4];
          3'h3:    start = addr_i[ 3 +: 4];
          default: start = addr_i[ 4 +: 4];
        endcase
        5: case (size)
          3'h0:    start = addr_i[ 0 +: 4];
          3'h1:    start = addr_i[ 1 +: 4];
          3'h2:    start = addr_i[ 2 +: 4];
          3'h3:    start = addr_i[ 3 +: 4];
          3'h4:    start = addr_i[ 4 +: 4];
          default: start = addr_i[ 5 +: 4];
        endcase
        6: case (size)
          3'h0:    start = addr_i[ 0 +: 4];
          3'h1:    start = addr_i[ 1 +: 4];
          3'h2:    start = addr_i[ 2 +: 4];
          3'h3:    start = addr_i[ 3 +: 4];
          3'h4:    start = addr_i[ 4 +: 4];
          3'h5:    start = addr_i[ 5 +: 4];
          default: start = addr_i[ 6 +: 4];
        endcase
      endcase
      f_s_wrap_cnt = {len[3:1], 1'b1} & ~start;
    end
  endfunction
 
  // Number of MI transfers until wrapping (0 = wrap after first transfer; 4'hF = no wrapping)
  function [3:0] f_m_wrap_cnt
    (
      input [P_M_RBUFFER_BYTES_LOG-1:0] addr,
      input [2:0] size,
      input [7:0] len
    );
    reg [3:0] start;
    reg [P_MAX_RBUFFER_BYTES_LOG-1:0] addr_i;
    begin
      addr_i = addr;
      case (P_MI_SIZE)
        3: case (size)
          3'h0:    start = addr_i[ 0 +: 4];
          3'h1:    start = addr_i[ 1 +: 4];
          3'h2:    start = addr_i[ 2 +: 4];
          default: start = addr_i[ 3 +: 4];
        endcase
        4: case (size)
          3'h0:    start = addr_i[ 0 +: 4];
          3'h1:    start = addr_i[ 1 +: 4];
          3'h2:    start = addr_i[ 2 +: 4];
          3'h3:    start = addr_i[ 3 +: 4];
          default: start = addr_i[ 4 +: 4];
        endcase
        5: case (size)
          3'h0:    start = addr_i[ 0 +: 4];
          3'h1:    start = addr_i[ 1 +: 4];
          3'h2:    start = addr_i[ 2 +: 4];
          3'h3:    start = addr_i[ 3 +: 4];
          3'h4:    start = addr_i[ 4 +: 4];
          default: start = addr_i[ 5 +: 4];
        endcase
        6: case (size)
          3'h0:    start = addr_i[ 0 +: 4];
          3'h1:    start = addr_i[ 1 +: 4];
          3'h2:    start = addr_i[ 2 +: 4];
          3'h3:    start = addr_i[ 3 +: 4];
          3'h4:    start = addr_i[ 4 +: 4];
          3'h5:    start = addr_i[ 5 +: 4];
          default: start = addr_i[ 6 +: 4];
        endcase
        7: case (size)
          3'h0:    start = addr_i[ 0 +: 4];
          3'h1:    start = addr_i[ 1 +: 4];
          3'h2:    start = addr_i[ 2 +: 4];
          3'h3:    start = addr_i[ 3 +: 4];
          3'h4:    start = addr_i[ 4 +: 4];
          3'h5:    start = addr_i[ 5 +: 4];
          3'h6:    start = addr_i[ 6 +: 4];
          default: start = addr_i[ 7 +: 4];
        endcase
      endcase
      f_m_wrap_cnt = {len[3:1], 1'b1} & ~start;
    end
  endfunction
 
  // Mask of address bits used to point to first SI wrap transfer.
  function [P_M_RBUFFER_BYTES_LOG-1:0] f_s_wrap_mask
    (
      input [2:0] size,
      input [7:0] len
    );
    begin
      case (P_MI_SIZE)
        3: case (size)
          3'h0:    f_s_wrap_mask = {len[3:3], 3'b111    };
          3'h1:    f_s_wrap_mask = {len[3:2], 3'b110    };
          3'h2:    f_s_wrap_mask = {len[3:1], 3'b100    };
        endcase
        4: case (size)
          3'h0:    f_s_wrap_mask =            4'b1111    ;
          3'h1:    f_s_wrap_mask = {len[3:3], 4'b1110   };
          3'h2:    f_s_wrap_mask = {len[3:2], 4'b1100   };
          3'h3:    f_s_wrap_mask = {len[3:1], 4'b1000   };
        endcase
        5: case (size)
          3'h0:    f_s_wrap_mask =            5'b11111   ;
          3'h1:    f_s_wrap_mask =            5'b11110   ;
          3'h2:    f_s_wrap_mask = {len[3:3], 5'b11100  };
          3'h3:    f_s_wrap_mask = {len[3:2], 5'b11000  };
          3'h4:    f_s_wrap_mask = {len[3:1], 5'b10000  };
        endcase
        6: case (size)
          3'h0:    f_s_wrap_mask =            6'b111111  ;
          3'h1:    f_s_wrap_mask =            6'b111110  ;
          3'h2:    f_s_wrap_mask =            6'b111100  ;
          3'h3:    f_s_wrap_mask = {len[3:3], 6'b111000 };
          3'h4:    f_s_wrap_mask = {len[3:2], 6'b110000 };
          3'h5:    f_s_wrap_mask = {len[3:1], 6'b100000 };
        endcase
        7: case (size)
          3'h0:    f_s_wrap_mask =            7'b1111111 ;
          3'h1:    f_s_wrap_mask =            7'b1111110 ;
          3'h2:    f_s_wrap_mask =            7'b1111100 ;
          3'h3:    f_s_wrap_mask =            7'b1111000 ;
          3'h4:    f_s_wrap_mask = {len[3:3], 7'b1110000};
          3'h5:    f_s_wrap_mask = {len[3:2], 7'b1100000};
          3'h6:    f_s_wrap_mask = {len[3:1], 7'b1000000};
        endcase
      endcase
    end
  endfunction

  // Mask of address bits used to point to first MI wrap transfer.
  function [P_M_RBUFFER_BYTES_LOG-1:0] f_m_wrap_mask
    (
      input [2:0] size,
      input [7:0] len
    );
    begin
      case (P_MI_SIZE)
        3: case (size)
          3'h0:    f_m_wrap_mask = {len[3:3], 3'b111    };
          3'h1:    f_m_wrap_mask = {len[3:2], 3'b110    };
          3'h2:    f_m_wrap_mask = {len[3:1], 3'b100    };
          3'h3:    f_m_wrap_mask = {len[3:1], 4'b1000    };
        endcase
        4: case (size)                                   
          3'h0:    f_m_wrap_mask =            4'b1111     ;
          3'h1:    f_m_wrap_mask = {len[3:3], 4'b1110    };
          3'h2:    f_m_wrap_mask = {len[3:2], 4'b1100    };
          3'h3:    f_m_wrap_mask = {len[3:1], 4'b1000    };
          3'h4:    f_m_wrap_mask = {len[3:1], 5'b10000   };
        endcase                                          
        5: case (size)                                   
          3'h0:    f_m_wrap_mask =            5'b11111    ;
          3'h1:    f_m_wrap_mask =            5'b11110    ;
          3'h2:    f_m_wrap_mask = {len[3:3], 5'b11100   };
          3'h3:    f_m_wrap_mask = {len[3:2], 5'b11000   };
          3'h4:    f_m_wrap_mask = {len[3:1], 5'b10000   };
          3'h5:    f_m_wrap_mask = {len[3:1], 6'b100000  };
        endcase                                          
        6: case (size)                                   
          3'h0:    f_m_wrap_mask =            6'b111111   ;
          3'h1:    f_m_wrap_mask =            6'b111110   ;
          3'h2:    f_m_wrap_mask =            6'b111100   ;
          3'h3:    f_m_wrap_mask = {len[3:3], 6'b111000  };
          3'h4:    f_m_wrap_mask = {len[3:2], 6'b110000  };
          3'h5:    f_m_wrap_mask = {len[3:1], 6'b100000  };
          3'h6:    f_m_wrap_mask = {len[3:1], 7'b1000000 };
        endcase                                          
        7: case (size)                                   
          3'h0:    f_m_wrap_mask =            7'b1111111  ;
          3'h1:    f_m_wrap_mask =            7'b1111110  ;
          3'h2:    f_m_wrap_mask =            7'b1111100  ;
          3'h3:    f_m_wrap_mask =            7'b1111000  ;
          3'h4:    f_m_wrap_mask = {len[3:3], 7'b1110000 };
          3'h5:    f_m_wrap_mask = {len[3:2], 7'b1100000 };
          3'h6:    f_m_wrap_mask = {len[3:1], 7'b1000000 };
          3'h7:    f_m_wrap_mask = {len[3:1], 8'b10000000};
        endcase                                          
      endcase
    end
  endfunction

  // Address of SI transfer following wrap
  function [P_M_RBUFFER_BYTES_LOG-1:0] f_s_wrap_addr
    (
      input [P_M_RBUFFER_BYTES_LOG-1:0] addr,
      input [2:0] size,
      input [7:0] len
    );
    reg [P_M_RBUFFER_BYTES_LOG-1:0] mask;
    begin
      case (P_MI_SIZE)
        3: case (size)
          3'h0:    mask = {        ~len[2:1], 1'b0};
          3'h1:    mask = {        ~len[1:1], 2'b0};
          default: mask =                     3'b0 ;
        endcase
        4: case (size)
          3'h0:    mask = {        ~len[3:1], 1'b0};
          3'h1:    mask = {        ~len[2:1], 2'b0};
          3'h2:    mask = {        ~len[1:1], 3'b0};
          default: mask =                     4'b0 ;
        endcase
        5: case (size)
          3'h0:    mask = {1'b1  , ~len[3:1], 1'b0};
          3'h1:    mask = {        ~len[3:1], 2'b0};
          3'h2:    mask = {        ~len[2:1], 3'b0};
          3'h3:    mask = {        ~len[1:1], 4'b0};
          default: mask =                     5'b0 ;
        endcase
        6: case (size)
          3'h0:    mask = {2'b11 , ~len[3:1], 1'b0};
          3'h1:    mask = {1'b1  , ~len[3:1], 2'b0};
          3'h2:    mask = {        ~len[3:1], 3'b0};
          3'h3:    mask = {        ~len[2:1], 4'b0};
          3'h4:    mask = {        ~len[1:1], 5'b0};
          default: mask =                     6'b0 ;
        endcase
        7: case (size)
          3'h0:    mask = {3'b111, ~len[3:1], 1'b0};
          3'h1:    mask = {2'b11 , ~len[3:1], 2'b0};
          3'h2:    mask = {1'b1  , ~len[3:1], 3'b0};
          3'h3:    mask = {        ~len[3:1], 4'b0};
          3'h4:    mask = {        ~len[2:1], 5'b0};
          3'h5:    mask = {        ~len[1:1], 6'b0};
          default: mask =                     7'b0 ;
        endcase
      endcase
      f_s_wrap_addr = addr & mask;
    end
  endfunction
 
  // Address of MI transfer following wrap
  function [P_M_RBUFFER_BYTES_LOG-1:0] f_m_wrap_addr
    (
      input [P_M_RBUFFER_BYTES_LOG-1:0] addr,
      input [2:0] size,
      input [7:0] len
    );
    reg [P_M_RBUFFER_BYTES_LOG-1:0] mask;
    begin
      case (P_MI_SIZE)
        3: case (size)
          3'h0:    mask = {        ~len[2:1], 1'b0};
          3'h1:    mask = {        ~len[1:1], 2'b0};
          default: mask =                     3'b0 ;
        endcase
        4: case (size)
          3'h0:    mask = {        ~len[3:1], 1'b0};
          3'h1:    mask = {        ~len[2:1], 2'b0};
          3'h2:    mask = {        ~len[1:1], 3'b0};
          default: mask =                     4'b0 ;
        endcase
        5: case (size)
          3'h0:    mask = {1'b1  , ~len[3:1], 1'b0};
          3'h1:    mask = {        ~len[3:1], 2'b0};
          3'h2:    mask = {        ~len[2:1], 3'b0};
          3'h3:    mask = {        ~len[1:1], 4'b0};
          default: mask =                     5'b0 ;
        endcase
        6: case (size)
          3'h0:    mask = {2'b11 , ~len[3:1], 1'b0};
          3'h1:    mask = {1'b1  , ~len[3:1], 2'b0};
          3'h2:    mask = {        ~len[3:1], 3'b0};
          3'h3:    mask = {        ~len[2:1], 4'b0};
          3'h4:    mask = {        ~len[1:1], 5'b0};
          default: mask =                     6'b0 ;
        endcase
        7: case (size)
          3'h0:    mask = {3'b111, ~len[3:1], 1'b0};
          3'h1:    mask = {2'b11 , ~len[3:1], 2'b0};
          3'h2:    mask = {1'b1  , ~len[3:1], 3'b0};
          3'h3:    mask = {        ~len[3:1], 4'b0};
          3'h4:    mask = {        ~len[2:1], 5'b0};
          3'h5:    mask = {        ~len[1:1], 6'b0};
          default: mask =                     7'b0 ;
        endcase
      endcase
      f_m_wrap_addr = addr & mask;
    end
  endfunction
 
  // Mask of address bits used to point to first SI non-wrap transfer.
  function [P_M_RBUFFER_BYTES_LOG-1:0] f_s_size_mask
    (
      input [2:0] size
    );
    begin
      case (P_MI_SIZE)
        3: case (size)
          3'h0:    f_s_size_mask = 3'b111;
          3'h1:    f_s_size_mask = 3'b110;
          3'h2:    f_s_size_mask = 3'b100;
        endcase
        4: case (size)
          3'h0:    f_s_size_mask = 4'b1111;
          3'h1:    f_s_size_mask = 4'b1110;
          3'h2:    f_s_size_mask = 4'b1100;
          3'h3:    f_s_size_mask = 4'b1000;
        endcase
        5: case (size)
          3'h0:    f_s_size_mask = 5'b11111;
          3'h1:    f_s_size_mask = 5'b11110;
          3'h2:    f_s_size_mask = 5'b11100;
          3'h3:    f_s_size_mask = 5'b11000;
          3'h4:    f_s_size_mask = 5'b10000;
        endcase
        6: case (size)
          3'h0:    f_s_size_mask = 6'b111111;
          3'h1:    f_s_size_mask = 6'b111110;
          3'h2:    f_s_size_mask = 6'b111100;
          3'h3:    f_s_size_mask = 6'b111000;
          3'h4:    f_s_size_mask = 6'b110000;
          3'h5:    f_s_size_mask = 6'b100000;
        endcase
        7: case (size)
          3'h0:    f_s_size_mask = 7'b1111111;
          3'h1:    f_s_size_mask = 7'b1111110;
          3'h2:    f_s_size_mask = 7'b1111100;
          3'h3:    f_s_size_mask = 7'b1111000;
          3'h4:    f_s_size_mask = 7'b1110000;
          3'h5:    f_s_size_mask = 7'b1100000;
          3'h6:    f_s_size_mask = 7'b1000000;
        endcase
      endcase
    end
  endfunction

  // Mask of address bits used to point to first MI non-wrap transfer.
  function [P_M_RBUFFER_BYTES_LOG-1:0] f_m_size_mask
    (
      input [2:0] size
    );
    begin
      case (P_MI_SIZE)
        3: case (size)
          3'h0:    f_m_size_mask = 3'b111;
          3'h1:    f_m_size_mask = 3'b110;
          3'h2:    f_m_size_mask = 3'b100;
          3'h3:    f_m_size_mask = 3'b000;
        endcase
        4: case (size)
          3'h0:    f_m_size_mask = 4'b1111;
          3'h1:    f_m_size_mask = 4'b1110;
          3'h2:    f_m_size_mask = 4'b1100;
          3'h3:    f_m_size_mask = 4'b1000;
          3'h4:    f_m_size_mask = 4'b0000;
        endcase
        5: case (size)
          3'h0:    f_m_size_mask = 5'b11111;
          3'h1:    f_m_size_mask = 5'b11110;
          3'h2:    f_m_size_mask = 5'b11100;
          3'h3:    f_m_size_mask = 5'b11000;
          3'h4:    f_m_size_mask = 5'b10000;
          3'h5:    f_m_size_mask = 5'b00000;
        endcase
        6: case (size)
          3'h0:    f_m_size_mask = 6'b111111;
          3'h1:    f_m_size_mask = 6'b111110;
          3'h2:    f_m_size_mask = 6'b111100;
          3'h3:    f_m_size_mask = 6'b111000;
          3'h4:    f_m_size_mask = 6'b110000;
          3'h5:    f_m_size_mask = 6'b100000;
          3'h6:    f_m_size_mask = 6'b000000;
        endcase
        7: case (size)
          3'h0:    f_m_size_mask = 7'b1111111;
          3'h1:    f_m_size_mask = 7'b1111110;
          3'h2:    f_m_size_mask = 7'b1111100;
          3'h3:    f_m_size_mask = 7'b1111000;
          3'h4:    f_m_size_mask = 7'b1110000;
          3'h5:    f_m_size_mask = 7'b1100000;
          3'h6:    f_m_size_mask = 7'b1000000;
          3'h7:    f_m_size_mask = 7'b0000000;
        endcase
      endcase
    end
  endfunction

  // Address increment for SI non-wrap transfer.
  function [P_M_RBUFFER_BYTES_LOG-1:0] f_s_size_incr
    (
      input [2:0] size
    );
    begin
      case (P_SI_SIZE)
        2: case (size[1:0])
          2'h0:    f_s_size_incr = 4'b001;
          2'h1:    f_s_size_incr = 4'b010;
          2'h2:    f_s_size_incr = 4'b100;
        endcase
        3: case (size[1:0])
          2'h0:    f_s_size_incr = 4'b0001;
          2'h1:    f_s_size_incr = 4'b0010;
          2'h2:    f_s_size_incr = 4'b0100;
          2'h3:    f_s_size_incr = 4'b1000;
        endcase
        4: case (size)
          3'h0:    f_s_size_incr = 5'b00001;
          3'h1:    f_s_size_incr = 5'b00010;
          3'h2:    f_s_size_incr = 5'b00100;
          3'h3:    f_s_size_incr = 5'b01000;
          3'h4:    f_s_size_incr = 5'b10000;
        endcase
        5: case (size)
          3'h0:    f_s_size_incr = 6'b000001;
          3'h1:    f_s_size_incr = 6'b000010;
          3'h2:    f_s_size_incr = 6'b000100;
          3'h3:    f_s_size_incr = 6'b001000;
          3'h4:    f_s_size_incr = 6'b010000;
          3'h5:    f_s_size_incr = 6'b100000;
        endcase
        6: case (size)
          3'h0:    f_s_size_incr = 7'b0000001;
          3'h1:    f_s_size_incr = 7'b0000010;
          3'h2:    f_s_size_incr = 7'b0000100;
          3'h3:    f_s_size_incr = 7'b0001000;
          3'h4:    f_s_size_incr = 7'b0010000;
          3'h5:    f_s_size_incr = 7'b0100000;
          3'h6:    f_s_size_incr = 7'b1000000;
        endcase
      endcase
    end
  endfunction

  // Address increment for MI non-wrap transfer.
  function [P_M_RBUFFER_BYTES_LOG-1:0] f_m_size_incr
    (
      input [2:0] size
    );
    begin
      case (P_MI_SIZE)
        3: case (size)
          3'h0:    f_m_size_incr = 4'b0001;
          3'h1:    f_m_size_incr = 4'b0010;
          3'h2:    f_m_size_incr = 4'b0100;
          3'h3:    f_m_size_incr = 4'b1000;
        endcase
        4: case (size)
          3'h0:    f_m_size_incr = 5'b00001;
          3'h1:    f_m_size_incr = 5'b00010;
          3'h2:    f_m_size_incr = 5'b00100;
          3'h3:    f_m_size_incr = 5'b01000;
          3'h4:    f_m_size_incr = 5'b10000;
        endcase
        5: case (size)
          3'h0:    f_m_size_incr = 6'b000001;
          3'h1:    f_m_size_incr = 6'b000010;
          3'h2:    f_m_size_incr = 6'b000100;
          3'h3:    f_m_size_incr = 6'b001000;
          3'h4:    f_m_size_incr = 6'b010000;
          3'h5:    f_m_size_incr = 6'b100000;
        endcase
        6: case (size)
          3'h0:    f_m_size_incr = 7'b0000001;
          3'h1:    f_m_size_incr = 7'b0000010;
          3'h2:    f_m_size_incr = 7'b0000100;
          3'h3:    f_m_size_incr = 7'b0001000;
          3'h4:    f_m_size_incr = 7'b0010000;
          3'h5:    f_m_size_incr = 7'b0100000;
          3'h6:    f_m_size_incr = 7'b1000000;
        endcase
        7: case (size)
          3'h0:    f_m_size_incr = 8'b00000001;
          3'h1:    f_m_size_incr = 8'b00000010;
          3'h2:    f_m_size_incr = 8'b00000100;
          3'h3:    f_m_size_incr = 8'b00001000;
          3'h4:    f_m_size_incr = 8'b00010000;
          3'h5:    f_m_size_incr = 8'b00100000;
          3'h6:    f_m_size_incr = 8'b01000000;
          3'h7:    f_m_size_incr = 8'b10000000;
        endcase
      endcase
    end
  endfunction

  generate
  
  if (C_CLK_CONV) begin : gen_clock_conv
    if (C_AXI_IS_ACLK_ASYNC) begin : gen_async_conv

      assign m_aclk = M_AXI_ACLK;
      assign m_aresetn = M_AXI_ARESETN;
      assign s_aresetn = S_AXI_ARESETN;
      assign ar_fifo_s_aclk = S_AXI_ACLK;
      assign ar_fifo_m_aclk = M_AXI_ACLK;
      assign ar_fifo_aresetn = S_AXI_ARESETN & M_AXI_ARESETN;
      assign s_fifo_rst = ~S_AXI_ARESETN;
      assign m_fifo_rst = ~M_AXI_ARESETN;
      assign rresp_fifo_clk = 1'b0;
      assign rresp_fifo_wrclk = M_AXI_ACLK;
      assign rresp_fifo_rdclk = S_AXI_ACLK;
      assign rresp_fifo_rst = ~S_AXI_ARESETN | ~M_AXI_ARESETN;
      assign s_sample_cycle_early = 1'b1;
      assign s_sample_cycle       = 1'b1;
      assign m_sample_cycle_early = 1'b1;
      assign m_sample_cycle       = 1'b1;
      
    end else begin : gen_sync_conv
    
      if (P_SI_LT_MI) begin : gen_fastclk_mi
        assign fast_aclk = M_AXI_ACLK;
      end else begin : gen_fastclk_si
        assign fast_aclk = S_AXI_ACLK;
      end
    
      assign m_aclk = M_AXI_ACLK;
      assign m_aresetn = fast_aresetn_r;
      assign s_aresetn = fast_aresetn_r;
      assign ar_fifo_s_aclk = fast_aclk;
      assign ar_fifo_m_aclk = 1'b0;
      assign ar_fifo_aresetn = fast_aresetn_r;
      assign s_fifo_rst = fast_reset_r;
      assign m_fifo_rst = fast_reset_r;
      assign rresp_fifo_clk = fast_aclk;
      assign rresp_fifo_wrclk = 1'b0;
      assign rresp_fifo_rdclk = 1'b0;
      assign rresp_fifo_rst = fast_reset_r;
      assign s_sample_cycle_early = P_SI_LT_MI ? 1'b1 : SAMPLE_CYCLE_EARLY;
      assign s_sample_cycle       = P_SI_LT_MI ? 1'b1 : SAMPLE_CYCLE;
      assign m_sample_cycle_early = P_SI_LT_MI ? SAMPLE_CYCLE_EARLY : 1'b1;
      assign m_sample_cycle       = P_SI_LT_MI ? SAMPLE_CYCLE : 1'b1;
  
      always @(posedge fast_aclk) begin
        if (~S_AXI_ARESETN | ~M_AXI_ARESETN) begin
          fast_aresetn_r <= 1'b0;
          fast_reset_r <= 1'b1;
        end else if (S_AXI_ARESETN & M_AXI_ARESETN & SAMPLE_CYCLE_EARLY) begin
          fast_aresetn_r <= 1'b1;
          fast_reset_r <= 1'b0;
        end
      end
    end
  
  end else begin : gen_no_clk_conv
    
    assign m_aclk = S_AXI_ACLK;
    assign m_aresetn = S_AXI_ARESETN;
    assign s_aresetn = S_AXI_ARESETN;
    assign ar_fifo_s_aclk = S_AXI_ACLK;
    assign ar_fifo_m_aclk = 1'b0;
    assign ar_fifo_aresetn = S_AXI_ARESETN;
    assign s_fifo_rst = reset_r;
    assign m_fifo_rst = reset_r;
    assign rresp_fifo_clk = S_AXI_ACLK;
    assign rresp_fifo_wrclk = 1'b0;
    assign rresp_fifo_rdclk = 1'b0;
    assign rresp_fifo_rst = reset_r;
    assign fast_aclk = S_AXI_ACLK;
    assign s_sample_cycle_early = 1'b1;
    assign s_sample_cycle       = 1'b1;
    assign m_sample_cycle_early = 1'b1;
    assign m_sample_cycle       = 1'b1;
    
    always @(posedge S_AXI_ACLK) begin
      reset_r <= ~S_AXI_ARESETN;
    end
  
  end
  
  for (i=0; i<P_NUM_RAMB; i=i+1) begin : gen_rdata
    for (j=0; j<32; j=j+1) begin : gen_m_rdata
      assign m_rdata[i*32+j] = M_AXI_RDATA[j*P_NUM_RAMB+i];
    end
    for (j=0; j<P_S_RAMB_WIDTH; j=j+1) begin : gen_s_rdata
      assign S_AXI_RDATA[j*P_NUM_RAMB+i] = s_rdata[i*16+j];
    end
  end  // gen_rdata
  
  assign S_AXI_ARREADY = S_AXI_ARREADY_i;
  assign S_AXI_RVALID = s_rvalid_d2;
  assign S_AXI_RRESP = s_rresp_d2;
  assign S_AXI_RLAST = s_rlast_d2;
  assign S_AXI_RID    = s_id_d2;
  assign s_rbuf_en = ~s_rvalid_d2 | S_AXI_RREADY;
  assign buf_limit = buf_cnt == P_BUF_LIMIT;
  assign s_cmd_pop = (s_rbuf_en | ~s_rvalid) & (s_rcnt == 0) & ~s_cmd_empty & ~rresp_fifo_empty & ~s_rresp_fifo_stall;
  assign s_eol = f_s_eol(s_raddr, s_rsize, s_conv_size) | (s_rburst == P_FIXED);
  assign rresp_fifo_pop = (s_rbuf_en | ~s_rvalid) & (((s_rcnt == 0) ? ~s_cmd_empty : (s_eol & ~rresp_wrap)) | s_rresp_fifo_stall) &
           ~rresp_fifo_empty & m_sample_cycle;  // Sample strobe when RRESP FIFO is on faster M_AXI_ACLK.
  assign rresp_reuse = (s_rbuf_en | ~s_rvalid) & s_eol & rresp_wrap;
  assign ar_push = S_AXI_ARVALID & S_AXI_ARREADY_i & m_sample_cycle;  // Sample strobe when AR FIFO is on faster M_AXI_ACLK.
  assign s_cmd_push = S_AXI_ARVALID & S_AXI_ARREADY_i;
  assign s_ar_cmd = {cmd_si_addr[0 +: P_MI_SIZE+4], cmd_si_id, S_AXI_ARLEN[3:0], S_AXI_ARSIZE, cmd_si_len, cmd_si_size, cmd_si_burst};
  assign s_cmd_addr = s_r_cmd[(20+C_AXI_ID_WIDTH) +: P_MI_SIZE+4];
  assign s_cmd_id = s_r_cmd[20 +: C_AXI_ID_WIDTH];
  assign s_cmd_conv_len = s_r_cmd[16 +: 4];
  assign s_cmd_conv_size = s_r_cmd[13 +: 3];
  assign s_cmd_len = s_r_cmd[5 +: 8];
  assign s_cmd_size = s_r_cmd[2 +: 3];
  assign s_cmd_burst = s_r_cmd[0 +: 2];
  assign s_rbuf_addr = f_s_rbuf_addr(s_raddr, s_conv_size, s_rburst, s_buf);
  assign s_rresp = s_rresp_i[1:0];
 
  always @(posedge S_AXI_ACLK) begin
    if (~s_aresetn) begin
      S_AXI_ARREADY_i <= 1'b0;
      buf_cnt <= 0;
    end else begin
      if (ar_push) begin
        S_AXI_ARREADY_i <= 1'b0;
      end else if (ar_fifo_ready & ~s_cmd_full & ~buf_limit) begin
        S_AXI_ARREADY_i <= 1'b1;  // pre-assert READY
      end
      if (s_cmd_push & ~s_cmd_pop) begin
        buf_cnt <= buf_cnt + 1;
      end else if (~s_cmd_push & s_cmd_pop & (buf_cnt != 0)) begin
        buf_cnt <= buf_cnt - 1;
      end
    end
  end

  always @(posedge S_AXI_ACLK) begin
    if (~s_aresetn) begin
      s_rvalid <= 1'b0;
      s_rvalid_d1 <= 1'b0;
      s_rvalid_d2 <= 1'b0;
      first_rvalid_d1 <= 1'b0;
      s_rlast <= 1'b0;
      s_rlast_d1 <= 1'b0;
      s_rlast_d2 <= 1'b0;
      s_rcnt <= 0;
      s_buf <= 0;
      rresp_wrap <= 1'b0;
      s_rresp_fifo_stall <= 1'b0;
      s_rresp_d2 <= 2'b00;
      s_id_d2 <= {C_AXI_ID_WIDTH{1'b0}};
    end else begin
      if (s_rbuf_en) begin
        s_rvalid_d2 <= s_rvalid_d1;
        s_rvalid_d1 <= s_rvalid;
        s_rlast_d2 <= s_rlast_d1;
        s_rlast_d1 <= s_rlast;
        if (first_rvalid_d1) begin
          s_rresp_d2 <= s_rresp_d1;
          s_id_d2 <= s_id_d1;
        end
        if (s_rvalid) begin
          first_rvalid_d1 <= 1'b1;  // forever
        end
      end
      
      if (s_cmd_pop) begin
        s_rlast <= (s_cmd_len == 0);
      end else if (s_rvalid & s_rbuf_en & (s_rcnt != 0)) begin
        s_rlast <= (s_rcnt == 1);
      end

      if ((s_rcnt == 0) & ~s_rresp_fifo_stall) begin
        if (s_cmd_pop) begin
          s_rvalid <= 1'b1;
          s_rcnt <= s_cmd_len;
          rresp_wrap <= (s_cmd_burst == P_WRAP) & (s_cmd_conv_len == 0);
          s_buf <= s_buf + 1;
        end else if (s_rbuf_en) begin
          s_rvalid <= 1'b0;
        end
      end else begin
        if (s_rvalid & s_rbuf_en) begin
          s_rcnt <= s_rcnt - 1;
        end
        if ((s_eol & ~rresp_wrap) | s_rresp_fifo_stall) begin
          if (rresp_fifo_pop) begin
            rresp_wrap <= (s_rburst == P_WRAP) && (s_conv_len == 1);  // Last rresp pop of wrap burst
            s_rvalid <= 1'b1;
            s_rresp_fifo_stall <= 1'b0;
          end else if (s_rbuf_en) begin
            s_rvalid <= 1'b0;
            s_rresp_fifo_stall <= 1'b1;
          end
        end
      end
    end
  end

  always @(posedge S_AXI_ACLK) begin
    if (s_rbuf_en) begin
      s_rresp_d1 <= s_rresp_reg;
      s_id_d1 <= s_id_reg;
    end
    if (s_cmd_pop) begin
      if (s_cmd_burst == P_WRAP) begin
        s_raddr <= s_cmd_addr & f_s_wrap_mask(s_cmd_size, s_cmd_len);
      end else begin
        s_raddr <= s_cmd_addr & f_s_size_mask(s_cmd_size);
      end
      s_rsize <= s_cmd_size;
      s_rburst <= s_cmd_burst;
      s_id_reg <= s_cmd_id;
      s_wrap_cnt <= f_s_wrap_cnt(s_cmd_addr, s_cmd_size, s_cmd_len);
      s_wrap_addr <= f_s_wrap_addr(s_cmd_addr, s_cmd_size, s_cmd_len);
      s_conv_size <= s_cmd_conv_size;
      s_conv_len <= s_cmd_conv_len;  // MI len to count wrap beats for rresp reuse.
      s_rresp_first <= s_rresp;  // Save first beat of wrap burst.
    end else if (s_rvalid & s_rbuf_en & (s_rcnt != 0)) begin
      if ((s_rburst == P_WRAP) && (s_wrap_cnt == 0)) begin
        s_raddr <= s_wrap_addr;
      end else if (s_rburst == P_FIXED) begin
        s_raddr <= s_raddr + P_MI_BYTES;
      end else begin
        s_raddr <= s_raddr + f_s_size_incr(s_rsize);
      end
      s_wrap_cnt <= s_wrap_cnt - 1;
    end
    if (rresp_fifo_pop) begin
      s_rresp_reg <= s_rresp;
      if (~s_cmd_pop) begin
        s_conv_len <= s_conv_len - 1;  // Count rresp pops during wrap burst
      end
    end else if (rresp_reuse) begin  // SI wrap revisits first buffer line; reuse firt rresp.
      s_rresp_reg <= s_rresp_first;
    end
  end
  
  assign M_AXI_ARADDR = M_AXI_ARADDR_i;
  assign M_AXI_ARLEN = M_AXI_ARLEN_i;
  assign M_AXI_ARSIZE = M_AXI_ARSIZE_i;
  assign M_AXI_ARBURST = M_AXI_ARBURST_i;
  assign M_AXI_ARLOCK = {1'b0,M_AXI_ARLOCK_i};
  assign M_AXI_ARVALID = M_AXI_ARVALID_i;
  assign M_AXI_RREADY = M_AXI_RREADY_i;
  assign ar_pop = M_AXI_ARVALID_i & M_AXI_ARREADY & s_sample_cycle;  // Sample strobe when AR FIFO is on faster S_AXI_ACLK.
  assign m_cmd_push = M_AXI_ARVALID_i & M_AXI_ARREADY;
  assign m_transfer = M_AXI_RREADY_i & M_AXI_RVALID;
  assign rresp_fifo_push = (m_transfer | m_rresp_fifo_stall) & ~rresp_fifo_full & s_sample_cycle;  // Sample strobe when RRESP FIFO is on faster S_AXI_ACLK.
  assign m_cmd_pop = ((m_transfer & M_AXI_RLAST) | (~m_cmd_valid & ~rresp_fifo_full)) & ~m_cmd_empty;
  assign m_rresp = m_rresp_fifo_stall ? m_rresp_reg : M_AXI_RRESP;
  assign m_rresp_i = {2'b0, m_rresp};
  assign m_ar_cmd = {M_AXI_ARADDR_i[0 +: P_MI_SIZE+4], M_AXI_ARLEN_i, M_AXI_ARSIZE_i, M_AXI_ARBURST_i};
  assign m_cmd_addr = m_r_cmd[13 +: P_MI_SIZE+4];
  assign m_cmd_len = m_r_cmd[5 +: 8];
  assign m_cmd_size = m_r_cmd[2 +: 3];
  assign m_cmd_burst = m_r_cmd[0 +: 2];
  assign m_rbuf_addr = f_m_rbuf_addr(m_raddr, m_rsize, m_rburst, m_buf);
  assign m_rbuf_we = (large_incr_last ? large_incr_mask : 4'b1111) & f_m_rbuf_we(m_raddr, m_rsize);
  assign m_rbuf_en = f_m_rbuf_en(m_raddr, m_rsize) & {P_NUM_RAMB{m_transfer}};
  assign m_raddr_incr = m_raddr + f_m_size_incr(m_rsize);
  
  always @(posedge m_aclk) begin
    if (~m_aresetn) begin
      M_AXI_ARVALID_i <= 1'b0;
    end else begin
      if (ar_pop) begin
        M_AXI_ARVALID_i <= 1'b0;
      end else if (ar_fifo_valid & ~m_cmd_full) begin
        M_AXI_ARVALID_i <= 1'b1;
      end
    end
  end

  always @(posedge m_aclk) begin
    if (~m_aresetn) begin
      m_buf <= 0;
      M_AXI_RREADY_i <= 1'b0;
      m_cmd_valid <= 1'b0;
      m_rresp_fifo_stall <= 1'b0;
    end else begin
      if (M_AXI_RREADY_i) begin
        if (M_AXI_RVALID) begin
          m_rresp_reg <= M_AXI_RRESP;
          if (rresp_fifo_full) begin
            M_AXI_RREADY_i <= 1'b0;
            m_rresp_fifo_stall <= 1'b1;
          end
          if (M_AXI_RLAST & m_cmd_empty) begin
            M_AXI_RREADY_i <= 1'b0;
            m_cmd_valid <= 1'b0;
          end
        end
      end else if (~rresp_fifo_full) begin
        m_rresp_fifo_stall <= 1'b0;
        if (m_cmd_valid) begin
          M_AXI_RREADY_i <= 1'b1;
        end else if (~m_cmd_empty) begin
          m_cmd_valid <= 1'b1;
          M_AXI_RREADY_i <= 1'b1;
        end
      end
      if (m_cmd_pop) begin
        m_buf <= m_buf + 1;
      end
    end
  end
  
  always @(posedge m_aclk) begin
    if (m_cmd_pop) begin
      if (m_cmd_burst == P_WRAP) begin
        m_raddr <= m_cmd_addr & f_m_wrap_mask(m_cmd_size, m_cmd_len);
      end else begin
        m_raddr <= m_cmd_addr & f_m_size_mask(m_cmd_size);
      end
      m_rsize <= m_cmd_size;
      m_rburst <= m_cmd_burst;
      m_wrap_cnt <= f_m_wrap_cnt(m_cmd_addr, m_cmd_size, m_cmd_len);
      m_wrap_addr <= f_m_wrap_addr(m_cmd_addr, m_cmd_size, m_cmd_len);
      large_incr_last <= 1'b0;
      large_incr_mask <= f_large_incr_mask(m_cmd_addr);
    end else if (m_transfer) begin
      if ((m_rburst == P_WRAP) && (m_wrap_cnt == 0)) begin
        m_raddr <= m_wrap_addr;
      end else if (m_rburst == P_FIXED) begin
        m_raddr <= m_raddr + P_MI_BYTES;
      end else begin
        if (~|m_raddr_incr) begin  // Addr pointer is about to wrap to zero?
          large_incr_last <= 1'b1;
        end
        m_raddr <= m_raddr_incr;
      end
      m_wrap_cnt <= m_wrap_cnt - 1;
    end
  end

  for (i=0; i<P_NUM_RAMB; i=i+1) begin : gen_ramb
    RAMB18E1 #(
      .READ_WIDTH_A(P_S_RAMB_PWIDTH),
      .WRITE_WIDTH_B(36),
      .RDADDR_COLLISION_HWCONFIG("PERFORMANCE"),
      .SIM_COLLISION_CHECK("NONE"),
      .DOA_REG(1),
      .DOB_REG(1),
      .RAM_MODE("SDP"),
      .READ_WIDTH_B(0),
      .WRITE_WIDTH_A(0),
      .RSTREG_PRIORITY_A("RSTREG"),
      .RSTREG_PRIORITY_B("RSTREG"),
      .SRVAL_A(18'h00000),
      .SRVAL_B(18'h00000),
      .SIM_DEVICE("7SERIES"),
      .WRITE_MODE_A("WRITE_FIRST"),
      .WRITE_MODE_B("WRITE_FIRST")
    ) ramb_inst (
      .DOADO(s_rdata[(i*16) +: 16]),
      .DIADI(m_rdata[(i*32) +: 16]),
      .DIBDI(m_rdata[(i*32+16) +: 16]),
      .WEBWE(m_rbuf_we),
      .ADDRARDADDR(s_rbuf_addr),
      .ADDRBWRADDR(m_rbuf_addr),
      .ENARDEN(s_rbuf_en),
      .REGCEAREGCE(s_rbuf_en),
      .ENBWREN(m_rbuf_en[i]),
      .CLKARDCLK(S_AXI_ACLK),
      .CLKBWRCLK(m_aclk),
      .RSTRAMARSTRAM(1'b0),
      .RSTREGARSTREG(1'b0),
      .WEA(2'b0),
      .DIPADIP(2'b0),
      .DIPBDIP(2'b0),
      .REGCEB(1'b1),
      .RSTRAMB(1'b0),
      .RSTREGB(1'b0),
      .DOBDO(),
      .DOPADOP(),
      .DOPBDOP()
    );   
  end 
    
  fifo_generator_v13_1_4 #(
    .C_FAMILY(C_FAMILY),
    .C_COMMON_CLOCK(P_COMMON_CLOCK),
    .C_MEMORY_TYPE(1),
    .C_SYNCHRONIZER_STAGE(C_SYNCHRONIZER_STAGE),
    .C_INTERFACE_TYPE(2),
    .C_AXI_TYPE(1),
    .C_HAS_AXI_ID(0),
    .C_AXI_LEN_WIDTH(8),
    .C_AXI_LOCK_WIDTH(1),
    .C_DIN_WIDTH_WACH(P_ARFIFO_WIDTH),
    .C_DIN_WIDTH_WDCH(37),
    .C_DIN_WIDTH_WRCH(2),
    .C_DIN_WIDTH_RACH(P_ARFIFO_WIDTH),
    .C_DIN_WIDTH_RDCH(35),
    .C_AXIS_TYPE(0),
    .C_HAS_AXI_WR_CHANNEL(0),
    .C_HAS_AXI_RD_CHANNEL(1),
    .C_AXI_ID_WIDTH(1),
    .C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
    .C_AXI_DATA_WIDTH(32),
    .C_HAS_AXI_AWUSER(0),
    .C_HAS_AXI_WUSER(0),
    .C_HAS_AXI_BUSER(0),
    .C_HAS_AXI_ARUSER(0),
    .C_HAS_AXI_RUSER(0),
    .C_AXI_ARUSER_WIDTH(1),
    .C_AXI_AWUSER_WIDTH(1),
    .C_AXI_WUSER_WIDTH(1),
    .C_AXI_BUSER_WIDTH(1),
    .C_AXI_RUSER_WIDTH(1),
    .C_WACH_TYPE(0),
    .C_WDCH_TYPE(0),
    .C_WRCH_TYPE(0),
    .C_RACH_TYPE(0),
    .C_RDCH_TYPE(2),
    .C_IMPLEMENTATION_TYPE_WACH(P_COMMON_CLOCK ? 2 : 12),
    .C_IMPLEMENTATION_TYPE_WDCH(P_COMMON_CLOCK ? 1 : 11),
    .C_IMPLEMENTATION_TYPE_WRCH(P_COMMON_CLOCK ? 2 : 12),
    .C_IMPLEMENTATION_TYPE_RACH(P_COMMON_CLOCK ? 2 : 12),
    .C_IMPLEMENTATION_TYPE_RDCH(P_COMMON_CLOCK ? 1 : 11),
    .C_IMPLEMENTATION_TYPE_AXIS(1),
    .C_DIN_WIDTH_AXIS(1),
    .C_WR_DEPTH_WACH(16),
    .C_WR_DEPTH_WDCH(1024),
    .C_WR_DEPTH_WRCH(16),
    .C_WR_DEPTH_RACH(32),
    .C_WR_DEPTH_RDCH(1024),
    .C_WR_DEPTH_AXIS(1024),
    .C_WR_PNTR_WIDTH_WACH(4),
    .C_WR_PNTR_WIDTH_WDCH(10),
    .C_WR_PNTR_WIDTH_WRCH(4),
    .C_WR_PNTR_WIDTH_RACH(5),
    .C_WR_PNTR_WIDTH_RDCH(10),
    .C_WR_PNTR_WIDTH_AXIS(10),
    .C_APPLICATION_TYPE_WACH(0),
    .C_APPLICATION_TYPE_WDCH(0),
    .C_APPLICATION_TYPE_WRCH(0),
    .C_APPLICATION_TYPE_RACH(P_COMMON_CLOCK ? 2 : 0),
    .C_APPLICATION_TYPE_RDCH(0),
    .C_APPLICATION_TYPE_AXIS(0),
    .C_USE_ECC_WACH(0),
    .C_USE_ECC_WDCH(0),
    .C_USE_ECC_WRCH(0),
    .C_USE_ECC_RACH(0),
    .C_USE_ECC_RDCH(0),
    .C_USE_ECC_AXIS(0),
    .C_ERROR_INJECTION_TYPE_WACH(0),
    .C_ERROR_INJECTION_TYPE_WDCH(0),
    .C_ERROR_INJECTION_TYPE_WRCH(0),
    .C_ERROR_INJECTION_TYPE_RACH(0),
    .C_ERROR_INJECTION_TYPE_RDCH(0),
    .C_ERROR_INJECTION_TYPE_AXIS(0),
    .C_HAS_DATA_COUNTS_WACH(0),
    .C_HAS_DATA_COUNTS_WDCH(0),
    .C_HAS_DATA_COUNTS_WRCH(0),
    .C_HAS_DATA_COUNTS_RACH(0),
    .C_HAS_DATA_COUNTS_RDCH(0),
    .C_HAS_DATA_COUNTS_AXIS(0),
    .C_HAS_PROG_FLAGS_WACH(0),
    .C_HAS_PROG_FLAGS_WDCH(0),
    .C_HAS_PROG_FLAGS_WRCH(0),
    .C_HAS_PROG_FLAGS_RACH(0),
    .C_HAS_PROG_FLAGS_RDCH(0),
    .C_HAS_PROG_FLAGS_AXIS(0),
    .C_PROG_FULL_TYPE_WACH(0),
    .C_PROG_FULL_TYPE_WDCH(0),
    .C_PROG_FULL_TYPE_WRCH(0),
    .C_PROG_FULL_TYPE_RACH(0),
    .C_PROG_FULL_TYPE_RDCH(0),
    .C_PROG_FULL_TYPE_AXIS(0),
    .C_PROG_FULL_THRESH_ASSERT_VAL_WACH(31),
    .C_PROG_FULL_THRESH_ASSERT_VAL_WDCH(1023),
    .C_PROG_FULL_THRESH_ASSERT_VAL_WRCH(15),
    .C_PROG_FULL_THRESH_ASSERT_VAL_RACH(15),
    .C_PROG_FULL_THRESH_ASSERT_VAL_RDCH(1023),
    .C_PROG_FULL_THRESH_ASSERT_VAL_AXIS(1023),
    .C_PROG_EMPTY_TYPE_WACH(0),
    .C_PROG_EMPTY_TYPE_WDCH(0),
    .C_PROG_EMPTY_TYPE_WRCH(0),
    .C_PROG_EMPTY_TYPE_RACH(0),
    .C_PROG_EMPTY_TYPE_RDCH(0),
    .C_PROG_EMPTY_TYPE_AXIS(0),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_WACH(30),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_WDCH(1022),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_WRCH(14),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_RACH(14),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_RDCH(1022),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_AXIS(1022),
    .C_REG_SLICE_MODE_WACH(0),
    .C_REG_SLICE_MODE_WDCH(0),
    .C_REG_SLICE_MODE_WRCH(0),
    .C_REG_SLICE_MODE_RACH(0),
    .C_REG_SLICE_MODE_RDCH(0),
    .C_REG_SLICE_MODE_AXIS(0),
    .C_HAS_AXIS_TDATA(0),
    .C_HAS_AXIS_TID(0),
    .C_HAS_AXIS_TDEST(0),
    .C_HAS_AXIS_TUSER(0),
    .C_HAS_AXIS_TREADY(1),
    .C_HAS_AXIS_TLAST(0),
    .C_HAS_AXIS_TSTRB(0),
    .C_HAS_AXIS_TKEEP(0),
    .C_AXIS_TDATA_WIDTH(64),
    .C_AXIS_TID_WIDTH(8),
    .C_AXIS_TDEST_WIDTH(4),
    .C_AXIS_TUSER_WIDTH(4),
    .C_AXIS_TSTRB_WIDTH(4),
    .C_AXIS_TKEEP_WIDTH(4),
    .C_HAS_SLAVE_CE(0),
    .C_HAS_MASTER_CE(0),
    .C_ADD_NGC_CONSTRAINT(0),
    .C_USE_COMMON_OVERFLOW(0),
    .C_USE_COMMON_UNDERFLOW(0),
    .C_USE_DEFAULT_SETTINGS(0),
    .C_COUNT_TYPE(0),
    .C_DATA_COUNT_WIDTH(10),
    .C_DEFAULT_VALUE("BlankString"),
    .C_DIN_WIDTH(18),
    .C_DOUT_RST_VAL("0"),
    .C_DOUT_WIDTH(18),
    .C_ENABLE_RLOCS(0),
    .C_FULL_FLAGS_RST_VAL(1),
    .C_HAS_ALMOST_EMPTY(0),
    .C_HAS_ALMOST_FULL(0),
    .C_HAS_BACKUP(0),
    .C_HAS_DATA_COUNT(0),
    .C_HAS_INT_CLK(0),
    .C_HAS_MEMINIT_FILE(0),
    .C_HAS_OVERFLOW(0),
    .C_HAS_RD_DATA_COUNT(0),
    .C_HAS_RD_RST(0),
    .C_HAS_RST(1),
    .C_HAS_SRST(0),
    .C_HAS_UNDERFLOW(0),
    .C_HAS_VALID(0),
    .C_HAS_WR_ACK(0),
    .C_HAS_WR_DATA_COUNT(0),
    .C_HAS_WR_RST(0),
    .C_IMPLEMENTATION_TYPE(0),
    .C_INIT_WR_PNTR_VAL(0),
    .C_MIF_FILE_NAME("BlankString"),
    .C_OPTIMIZATION_MODE(0),
    .C_OVERFLOW_LOW(0),
    .C_PRELOAD_LATENCY(1),
    .C_PRELOAD_REGS(0),
    .C_PRIM_FIFO_TYPE("4kx4"),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL(2),
    .C_PROG_EMPTY_THRESH_NEGATE_VAL(3),
    .C_PROG_EMPTY_TYPE(0),
    .C_PROG_FULL_THRESH_ASSERT_VAL(1022),
    .C_PROG_FULL_THRESH_NEGATE_VAL(1021),
    .C_PROG_FULL_TYPE(0),
    .C_RD_DATA_COUNT_WIDTH(10),
    .C_RD_DEPTH(1024),
    .C_RD_FREQ(1),
    .C_RD_PNTR_WIDTH(10),
    .C_UNDERFLOW_LOW(0),
    .C_USE_DOUT_RST(1),
    .C_USE_ECC(0),
    .C_USE_EMBEDDED_REG(0),
    .C_USE_FIFO16_FLAGS(0),
    .C_USE_FWFT_DATA_COUNT(0),
    .C_VALID_LOW(0),
    .C_WR_ACK_LOW(0),
    .C_WR_DATA_COUNT_WIDTH(10),
    .C_WR_DEPTH(1024),
    .C_WR_FREQ(1),
    .C_WR_PNTR_WIDTH(10),
    .C_WR_RESPONSE_LATENCY(1),
    .C_MSGON_VAL(1),
    .C_ENABLE_RST_SYNC(1),
    .C_ERROR_INJECTION_TYPE(0)
  ) dw_fifogen_ar (
    .s_aclk(ar_fifo_s_aclk),
    .m_aclk(ar_fifo_m_aclk),
    .s_aresetn(ar_fifo_aresetn),
    .s_axi_arid     (1'b0),
    .s_axi_araddr   (S_AXI_ARADDR),  
    .s_axi_arlen    (S_AXI_ARLEN),   
    .s_axi_arsize   (S_AXI_ARSIZE),  
    .s_axi_arburst  (S_AXI_ARBURST), 
    .s_axi_arlock   (S_AXI_ARLOCK[0]),  
    .s_axi_arcache  (S_AXI_ARCACHE), 
    .s_axi_arprot   (S_AXI_ARPROT),  
    .s_axi_arqos    (S_AXI_ARQOS),
    .s_axi_arregion (S_AXI_ARREGION),   
    .s_axi_aruser   (1'b0),
    .s_axi_arvalid  (ar_push),
    .s_axi_arready  (ar_fifo_ready),
    .s_axi_rid(),
    .s_axi_rdata(),
    .s_axi_rresp(),
    .s_axi_rlast(),
    .s_axi_ruser(),
    .s_axi_rvalid(),
    .s_axi_rready(1'b0),
    .m_axi_arid      (),
    .m_axi_araddr    (M_AXI_ARADDR_i),
    .m_axi_arlen     (M_AXI_ARLEN_i),
    .m_axi_arsize    (M_AXI_ARSIZE_i),
    .m_axi_arburst   (M_AXI_ARBURST_i),
    .m_axi_arlock    (M_AXI_ARLOCK_i),
    .m_axi_arcache   (M_AXI_ARCACHE),
    .m_axi_arprot    (M_AXI_ARPROT),
    .m_axi_arqos     (M_AXI_ARQOS),
    .m_axi_arregion  (M_AXI_ARREGION),
    .m_axi_aruser    (),
    .m_axi_arvalid   (ar_fifo_valid),
    .m_axi_arready   (ar_pop),
    .m_axi_rid(1'b0),
    .m_axi_rdata(32'b0),
    .m_axi_rresp(2'b0),
    .m_axi_rlast(1'b0),
    .m_axi_ruser(1'b0),
    .m_axi_rvalid(1'b0),
    .m_axi_rready(),
    .s_axi_awid(1'b0),
    .s_axi_awaddr({C_AXI_ADDR_WIDTH{1'b0}}),
    .s_axi_awlen(8'b0),
    .s_axi_awsize(3'b0),
    .s_axi_awburst(2'b0),
    .s_axi_awlock(1'b0),
    .s_axi_awcache(4'b0),
    .s_axi_awprot(3'b0),
    .s_axi_awqos(4'b0),
    .s_axi_awregion(4'b0),
    .s_axi_awuser(1'b0),
    .s_axi_awvalid(1'b0),
    .s_axi_awready(),
    .s_axi_wid(1'b0),
    .s_axi_wdata(32'b0),
    .s_axi_wstrb(4'b0),
    .s_axi_wlast(1'b0),
    .s_axi_wuser(1'b0),
    .s_axi_wvalid(1'b0),
    .s_axi_wready(),
    .s_axi_bid(),
    .s_axi_bresp(),
    .s_axi_buser(),
    .s_axi_bvalid(),
    .s_axi_bready(1'b0),
    .m_axi_awid(),
    .m_axi_awaddr(),
    .m_axi_awlen(),
    .m_axi_awsize(),
    .m_axi_awburst(),
    .m_axi_awlock(),
    .m_axi_awcache(),
    .m_axi_awprot(),
    .m_axi_awqos(),
    .m_axi_awregion(),
    .m_axi_awuser(),
    .m_axi_awvalid(),
    .m_axi_awready(1'b0),
    .m_axi_wid(),
    .m_axi_wdata(),
    .m_axi_wstrb(),
    .m_axi_wuser(),
    .m_axi_wlast(),
    .m_axi_wvalid(),
    .m_axi_wready(1'b0),
    .m_axi_bid(1'b0),
    .m_axi_bresp(2'b0),
    .m_axi_buser(1'b0),
    .m_axi_bvalid(1'b0),
    .m_axi_bready(),
    .m_aclk_en(1'b0),
    .s_aclk_en(1'b0),
    .backup(1'b0),
    .backup_marker(1'b0),
    .clk(1'b0),
    .rst(1'b0),
    .srst(1'b0),
    .wr_clk(1'b0),
    .wr_rst(1'b0),
    .rd_clk(1'b0),
    .rd_rst(1'b0),
    .din(18'b0),
    .wr_en(1'b0),
    .rd_en(1'b0),
    .prog_empty_thresh(10'b0),
    .prog_empty_thresh_assert(10'b0),
    .prog_empty_thresh_negate(10'b0),
    .prog_full_thresh(10'b0),
    .prog_full_thresh_assert(10'b0),
    .prog_full_thresh_negate(10'b0),
    .int_clk(1'b0),
    .injectdbiterr(1'b0),
    .injectsbiterr(1'b0),
    .dout(),
    .full(),
    .almost_full(),
    .wr_ack(),
    .overflow(),
    .empty(),
    .almost_empty(),
    .valid(),
    .underflow(),
    .data_count(),
    .rd_data_count(),
    .wr_data_count(),
    .prog_full(),
    .prog_empty(),
    .sbiterr(),
    .dbiterr(),
    .s_axis_tvalid(1'b0),
    .s_axis_tready(),
    .s_axis_tdata(64'b0),
    .s_axis_tstrb(4'b0),
    .s_axis_tkeep(4'b0),
    .s_axis_tlast(1'b0),
    .s_axis_tid(8'b0),
    .s_axis_tdest(4'b0),
    .s_axis_tuser(4'b0),
    .m_axis_tvalid(),
    .m_axis_tready(1'b0),
    .m_axis_tdata(),
    .m_axis_tstrb(),
    .m_axis_tkeep(),
    .m_axis_tlast(),
    .m_axis_tid(),
    .m_axis_tdest(),
    .m_axis_tuser(),
    .axi_aw_injectsbiterr(1'b0),
    .axi_aw_injectdbiterr(1'b0),
    .axi_aw_prog_full_thresh(4'b0),
    .axi_aw_prog_empty_thresh(4'b0),
    .axi_aw_data_count(),
    .axi_aw_wr_data_count(),
    .axi_aw_rd_data_count(),
    .axi_aw_sbiterr(),
    .axi_aw_dbiterr(),
    .axi_aw_overflow(),
    .axi_aw_underflow(),
    .axi_aw_prog_full(),
    .axi_aw_prog_empty(),
    .axi_w_injectsbiterr(1'b0),
    .axi_w_injectdbiterr(1'b0),
    .axi_w_prog_full_thresh(10'b0),
    .axi_w_prog_empty_thresh(10'b0),
    .axi_w_data_count(),
    .axi_w_wr_data_count(),
    .axi_w_rd_data_count(),
    .axi_w_sbiterr(),
    .axi_w_dbiterr(),
    .axi_w_overflow(),
    .axi_w_underflow(),
    .axi_b_injectsbiterr(1'b0),
    .axi_w_prog_full(),
    .axi_w_prog_empty(),
    .axi_b_injectdbiterr(1'b0),
    .axi_b_prog_full_thresh(4'b0),
    .axi_b_prog_empty_thresh(4'b0),
    .axi_b_data_count(),
    .axi_b_wr_data_count(),
    .axi_b_rd_data_count(),
    .axi_b_sbiterr(),
    .axi_b_dbiterr(),
    .axi_b_overflow(),
    .axi_b_underflow(),
    .axi_ar_injectsbiterr(1'b0),
    .axi_b_prog_full(),
    .axi_b_prog_empty(),
    .axi_ar_injectdbiterr(1'b0),
    .axi_ar_prog_full_thresh(5'b0),
    .axi_ar_prog_empty_thresh(5'b0),
    .axi_ar_data_count(),
    .axi_ar_wr_data_count(),
    .axi_ar_rd_data_count(),
    .axi_ar_sbiterr(),
    .axi_ar_dbiterr(),
    .axi_ar_overflow(),
    .axi_ar_underflow(),
    .axi_ar_prog_full(),
    .axi_ar_prog_empty(),
    .axi_r_injectsbiterr(1'b0),
    .axi_r_injectdbiterr(1'b0),
    .axi_r_prog_full_thresh(10'b0),
    .axi_r_prog_empty_thresh(10'b0),
    .axi_r_data_count(),
    .axi_r_wr_data_count(),
    .axi_r_rd_data_count(),
    .axi_r_sbiterr(),
    .axi_r_dbiterr(),
    .axi_r_overflow(),
    .axi_r_underflow(),
    .axis_injectsbiterr(1'b0),
    .axi_r_prog_full(),
    .axi_r_prog_empty(),
    .axis_injectdbiterr(1'b0),
    .axis_prog_full_thresh(10'b0),
    .axis_prog_empty_thresh(10'b0),
    .axis_data_count(),
    .axis_wr_data_count(),
    .axis_rd_data_count(),
    .axis_sbiterr(),
    .axis_dbiterr(),
    .axis_overflow(),
    .axis_underflow(),
    .axis_prog_full(),
    .axis_prog_empty(),
    .wr_rst_busy(),
    .rd_rst_busy(),
    .sleep(1'b0)
  );
  
  fifo_generator_v13_1_4 #(
    .C_DIN_WIDTH(P_S_CMD_WIDTH),
    .C_DOUT_WIDTH(P_S_CMD_WIDTH),
    .C_RD_DEPTH(32),
    .C_RD_PNTR_WIDTH(5),
    .C_RD_DATA_COUNT_WIDTH(5),
    .C_WR_DEPTH(32),
    .C_WR_PNTR_WIDTH(5),
    .C_WR_DATA_COUNT_WIDTH(5),
    .C_DATA_COUNT_WIDTH(5),
    .C_COMMON_CLOCK(1),
    .C_COUNT_TYPE(0),
    .C_DEFAULT_VALUE("BlankString"),
    .C_DOUT_RST_VAL("0"),
    .C_ENABLE_RLOCS(0),
    .C_FAMILY(C_FAMILY),
    .C_FULL_FLAGS_RST_VAL(0),
    .C_HAS_ALMOST_EMPTY(0),
    .C_HAS_ALMOST_FULL(0),
    .C_HAS_BACKUP(0),
    .C_HAS_DATA_COUNT(0),
    .C_HAS_INT_CLK(0),
    .C_HAS_MEMINIT_FILE(0),
    .C_HAS_OVERFLOW(0),
    .C_HAS_RD_DATA_COUNT(0),
    .C_HAS_RD_RST(0),
    .C_HAS_RST(0),
    .C_HAS_SRST(1),
    .C_HAS_UNDERFLOW(0),
    .C_HAS_VALID(0),
    .C_HAS_WR_ACK(0),
    .C_HAS_WR_DATA_COUNT(0),
    .C_HAS_WR_RST(0),
    .C_IMPLEMENTATION_TYPE(0),
    .C_INIT_WR_PNTR_VAL(0),
    .C_MEMORY_TYPE(2),
    .C_MIF_FILE_NAME("BlankString"),
    .C_OPTIMIZATION_MODE(0),
    .C_OVERFLOW_LOW(0),
    .C_PRELOAD_LATENCY(0),
    .C_PRELOAD_REGS(1),
    .C_PRIM_FIFO_TYPE("512x36"),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL(4),
    .C_PROG_EMPTY_THRESH_NEGATE_VAL(5),
    .C_PROG_EMPTY_TYPE(0),
    .C_PROG_FULL_THRESH_ASSERT_VAL(31),
    .C_PROG_FULL_THRESH_NEGATE_VAL(30),
    .C_PROG_FULL_TYPE(0),
    .C_RD_FREQ(1),
    .C_UNDERFLOW_LOW(0),
    .C_USE_DOUT_RST(0),
    .C_USE_ECC(0),
    .C_USE_EMBEDDED_REG(0),
    .C_USE_FIFO16_FLAGS(0),
    .C_USE_FWFT_DATA_COUNT(1),
    .C_VALID_LOW(0),
    .C_WR_ACK_LOW(0),
    .C_WR_FREQ(1),
    .C_WR_RESPONSE_LATENCY(1),
    .C_MSGON_VAL(1),
    .C_ENABLE_RST_SYNC(1),
    .C_ERROR_INJECTION_TYPE(0),
    .C_SYNCHRONIZER_STAGE(C_SYNCHRONIZER_STAGE),
    .C_INTERFACE_TYPE(0),
    .C_AXI_TYPE(0),
    .C_HAS_AXI_WR_CHANNEL(0),
    .C_HAS_AXI_RD_CHANNEL(0),
    .C_HAS_SLAVE_CE(0),
    .C_HAS_MASTER_CE(0),
    .C_ADD_NGC_CONSTRAINT(0),
    .C_USE_COMMON_OVERFLOW(0),
    .C_USE_COMMON_UNDERFLOW(0),
    .C_USE_DEFAULT_SETTINGS(0),
    .C_AXI_ID_WIDTH(4),
    .C_AXI_ADDR_WIDTH(32),
    .C_AXI_DATA_WIDTH(64),
    .C_HAS_AXI_AWUSER(0),
    .C_HAS_AXI_WUSER(0),
    .C_HAS_AXI_BUSER(0),
    .C_HAS_AXI_ARUSER(0),
    .C_HAS_AXI_RUSER(0),
    .C_AXI_ARUSER_WIDTH(1),
    .C_AXI_AWUSER_WIDTH(1),
    .C_AXI_WUSER_WIDTH(1),
    .C_AXI_BUSER_WIDTH(1),
    .C_AXI_RUSER_WIDTH(1),
    .C_HAS_AXIS_TDATA(0),
    .C_HAS_AXIS_TID(0),
    .C_HAS_AXIS_TDEST(0),
    .C_HAS_AXIS_TUSER(0),
    .C_HAS_AXIS_TREADY(1),
    .C_HAS_AXIS_TLAST(0),
    .C_HAS_AXIS_TSTRB(0),
    .C_HAS_AXIS_TKEEP(0),
    .C_AXIS_TDATA_WIDTH(64),
    .C_AXIS_TID_WIDTH(8),
    .C_AXIS_TDEST_WIDTH(4),
    .C_AXIS_TUSER_WIDTH(4),
    .C_AXIS_TSTRB_WIDTH(4),
    .C_AXIS_TKEEP_WIDTH(4),
    .C_WACH_TYPE(0),
    .C_WDCH_TYPE(0),
    .C_WRCH_TYPE(0),
    .C_RACH_TYPE(0),
    .C_RDCH_TYPE(0),
    .C_AXIS_TYPE(0),
    .C_IMPLEMENTATION_TYPE_WACH(1),
    .C_IMPLEMENTATION_TYPE_WDCH(1),
    .C_IMPLEMENTATION_TYPE_WRCH(1),
    .C_IMPLEMENTATION_TYPE_RACH(1),
    .C_IMPLEMENTATION_TYPE_RDCH(1),
    .C_IMPLEMENTATION_TYPE_AXIS(1),
    .C_APPLICATION_TYPE_WACH(0),
    .C_APPLICATION_TYPE_WDCH(0),
    .C_APPLICATION_TYPE_WRCH(0),
    .C_APPLICATION_TYPE_RACH(0),
    .C_APPLICATION_TYPE_RDCH(0),
    .C_APPLICATION_TYPE_AXIS(0),
    .C_USE_ECC_WACH(0),
    .C_USE_ECC_WDCH(0),
    .C_USE_ECC_WRCH(0),
    .C_USE_ECC_RACH(0),
    .C_USE_ECC_RDCH(0),
    .C_USE_ECC_AXIS(0),
    .C_ERROR_INJECTION_TYPE_WACH(0),
    .C_ERROR_INJECTION_TYPE_WDCH(0),
    .C_ERROR_INJECTION_TYPE_WRCH(0),
    .C_ERROR_INJECTION_TYPE_RACH(0),
    .C_ERROR_INJECTION_TYPE_RDCH(0),
    .C_ERROR_INJECTION_TYPE_AXIS(0),
    .C_DIN_WIDTH_WACH(32),
    .C_DIN_WIDTH_WDCH(64),
    .C_DIN_WIDTH_WRCH(2),
    .C_DIN_WIDTH_RACH(32),
    .C_DIN_WIDTH_RDCH(64),
    .C_DIN_WIDTH_AXIS(1),
    .C_WR_DEPTH_WACH(16),
    .C_WR_DEPTH_WDCH(1024),
    .C_WR_DEPTH_WRCH(16),
    .C_WR_DEPTH_RACH(16),
    .C_WR_DEPTH_RDCH(1024),
    .C_WR_DEPTH_AXIS(1024),
    .C_WR_PNTR_WIDTH_WACH(4),
    .C_WR_PNTR_WIDTH_WDCH(10),
    .C_WR_PNTR_WIDTH_WRCH(4),
    .C_WR_PNTR_WIDTH_RACH(4),
    .C_WR_PNTR_WIDTH_RDCH(10),
    .C_WR_PNTR_WIDTH_AXIS(10),
    .C_HAS_DATA_COUNTS_WACH(0),
    .C_HAS_DATA_COUNTS_WDCH(0),
    .C_HAS_DATA_COUNTS_WRCH(0),
    .C_HAS_DATA_COUNTS_RACH(0),
    .C_HAS_DATA_COUNTS_RDCH(0),
    .C_HAS_DATA_COUNTS_AXIS(0),
    .C_HAS_PROG_FLAGS_WACH(0),
    .C_HAS_PROG_FLAGS_WDCH(0),
    .C_HAS_PROG_FLAGS_WRCH(0),
    .C_HAS_PROG_FLAGS_RACH(0),
    .C_HAS_PROG_FLAGS_RDCH(0),
    .C_HAS_PROG_FLAGS_AXIS(0),
    .C_PROG_FULL_TYPE_WACH(0),
    .C_PROG_FULL_TYPE_WDCH(0),
    .C_PROG_FULL_TYPE_WRCH(0),
    .C_PROG_FULL_TYPE_RACH(0),
    .C_PROG_FULL_TYPE_RDCH(0),
    .C_PROG_FULL_TYPE_AXIS(0),
    .C_PROG_FULL_THRESH_ASSERT_VAL_WACH(1023),
    .C_PROG_FULL_THRESH_ASSERT_VAL_WDCH(1023),
    .C_PROG_FULL_THRESH_ASSERT_VAL_WRCH(1023),
    .C_PROG_FULL_THRESH_ASSERT_VAL_RACH(1023),
    .C_PROG_FULL_THRESH_ASSERT_VAL_RDCH(1023),
    .C_PROG_FULL_THRESH_ASSERT_VAL_AXIS(1023),
    .C_PROG_EMPTY_TYPE_WACH(0),
    .C_PROG_EMPTY_TYPE_WDCH(0),
    .C_PROG_EMPTY_TYPE_WRCH(0),
    .C_PROG_EMPTY_TYPE_RACH(0),
    .C_PROG_EMPTY_TYPE_RDCH(0),
    .C_PROG_EMPTY_TYPE_AXIS(0),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_WACH(1022),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_WDCH(1022),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_WRCH(1022),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_RACH(1022),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_RDCH(1022),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_AXIS(1022),
    .C_REG_SLICE_MODE_WACH(0),
    .C_REG_SLICE_MODE_WDCH(0),
    .C_REG_SLICE_MODE_WRCH(0),
    .C_REG_SLICE_MODE_RACH(0),
    .C_REG_SLICE_MODE_RDCH(0),
    .C_REG_SLICE_MODE_AXIS(0),
    .C_AXI_LEN_WIDTH(8),
    .C_AXI_LOCK_WIDTH(2)
  ) s_cmd_fifo (
    .clk(S_AXI_ACLK),
    .srst(s_fifo_rst),
    .din(s_ar_cmd),
    .dout(s_r_cmd),
    .full(s_cmd_full),
    .empty(s_cmd_empty),
    .wr_en(s_cmd_push),
    .rd_en(s_cmd_pop),
    .backup(1'b0),
    .backup_marker(1'b0),
    .rst(1'b0),
    .wr_clk(1'b0),
    .wr_rst(1'b0),
    .rd_clk(1'b0),
    .rd_rst(1'b0),
    .prog_empty_thresh(5'b0),
    .prog_empty_thresh_assert(5'b0),
    .prog_empty_thresh_negate(5'b0),
    .prog_full_thresh(5'b0),
    .prog_full_thresh_assert(5'b0),
    .prog_full_thresh_negate(5'b0),
    .int_clk(1'b0),
    .injectdbiterr(1'b0),
    .injectsbiterr(1'b0),
    .almost_full(),
    .wr_ack(),
    .overflow(),
    .almost_empty(),
    .valid(),
    .underflow(),
    .data_count(),
    .rd_data_count(),
    .wr_data_count(),
    .prog_full(),
    .prog_empty(),
    .sbiterr(),
    .dbiterr(),
    .m_aclk(1'b0),
    .s_aclk(1'b0),
    .s_aresetn(1'b0),
    .m_aclk_en(1'b0),
    .s_aclk_en(1'b0),
    .s_axi_awid(4'b0),
    .s_axi_awaddr(32'b0),
    .s_axi_awlen(8'b0),
    .s_axi_awsize(3'b0),
    .s_axi_awburst(2'b0),
    .s_axi_awlock(2'b0),
    .s_axi_awcache(4'b0),
    .s_axi_awprot(3'b0),
    .s_axi_awqos(4'b0),
    .s_axi_awregion(4'b0),
    .s_axi_awuser(1'b0),
    .s_axi_awvalid(1'b0),
    .s_axi_awready(),
    .s_axi_wid(4'b0),
    .s_axi_wdata(64'b0),
    .s_axi_wstrb(8'b0),
    .s_axi_wlast(1'b0),
    .s_axi_wuser(1'b0),
    .s_axi_wvalid(1'b0),
    .s_axi_wready(),
    .s_axi_bid(),
    .s_axi_bresp(),
    .s_axi_buser(),
    .s_axi_bvalid(),
    .s_axi_bready(1'b0),
    .m_axi_awid(),
    .m_axi_awaddr(),
    .m_axi_awlen(),
    .m_axi_awsize(),
    .m_axi_awburst(),
    .m_axi_awlock(),
    .m_axi_awcache(),
    .m_axi_awprot(),
    .m_axi_awqos(),
    .m_axi_awregion(),
    .m_axi_awuser(),
    .m_axi_awvalid(),
    .m_axi_awready(1'b0),
    .m_axi_wid(),
    .m_axi_wdata(),
    .m_axi_wstrb(),
    .m_axi_wlast(),
    .m_axi_wuser(),
    .m_axi_wvalid(),
    .m_axi_wready(1'b0),
    .m_axi_bid(4'b0),
    .m_axi_bresp(2'b0),
    .m_axi_buser(1'b0),
    .m_axi_bvalid(1'b0),
    .m_axi_bready(),
    .s_axi_arid(4'b0),
    .s_axi_araddr(32'b0),
    .s_axi_arlen(8'b0),
    .s_axi_arsize(3'b0),
    .s_axi_arburst(2'b0),
    .s_axi_arlock(2'b0),
    .s_axi_arcache(4'b0),
    .s_axi_arprot(3'b0),
    .s_axi_arqos(4'b0),
    .s_axi_arregion(4'b0),
    .s_axi_aruser(1'b0),
    .s_axi_arvalid(1'b0),
    .s_axi_arready(),
    .s_axi_rid(),
    .s_axi_rdata(),
    .s_axi_rresp(),
    .s_axi_rlast(),
    .s_axi_ruser(),
    .s_axi_rvalid(),
    .s_axi_rready(1'b0),
    .m_axi_arid(),
    .m_axi_araddr(),
    .m_axi_arlen(),
    .m_axi_arsize(),
    .m_axi_arburst(),
    .m_axi_arlock(),
    .m_axi_arcache(),
    .m_axi_arprot(),
    .m_axi_arqos(),
    .m_axi_arregion(),
    .m_axi_aruser(),
    .m_axi_arvalid(),
    .m_axi_arready(1'b0),
    .m_axi_rid(4'b0),
    .m_axi_rdata(64'b0),
    .m_axi_rresp(2'b0),
    .m_axi_rlast(1'b0),
    .m_axi_ruser(1'b0),
    .m_axi_rvalid(1'b0),
    .m_axi_rready(),
    .s_axis_tvalid(1'b0),
    .s_axis_tready(),
    .s_axis_tdata(64'b0),
    .s_axis_tstrb(4'b0),
    .s_axis_tkeep(4'b0),
    .s_axis_tlast(1'b0),
    .s_axis_tid(8'b0),
    .s_axis_tdest(4'b0),
    .s_axis_tuser(4'b0),
    .m_axis_tvalid(),
    .m_axis_tready(1'b0),
    .m_axis_tdata(),
    .m_axis_tstrb(),
    .m_axis_tkeep(),
    .m_axis_tlast(),
    .m_axis_tid(),
    .m_axis_tdest(),
    .m_axis_tuser(),
    .axi_aw_injectsbiterr(1'b0),
    .axi_aw_injectdbiterr(1'b0),
    .axi_aw_prog_full_thresh(4'b0),
    .axi_aw_prog_empty_thresh(4'b0),
    .axi_aw_data_count(),
    .axi_aw_wr_data_count(),
    .axi_aw_rd_data_count(),
    .axi_aw_sbiterr(),
    .axi_aw_dbiterr(),
    .axi_aw_overflow(),
    .axi_aw_underflow(),
    .axi_aw_prog_full(),
    .axi_aw_prog_empty(),
    .axi_w_injectsbiterr(1'b0),
    .axi_w_injectdbiterr(1'b0),
    .axi_w_prog_full_thresh(10'b0),
    .axi_w_prog_empty_thresh(10'b0),
    .axi_w_data_count(),
    .axi_w_wr_data_count(),
    .axi_w_rd_data_count(),
    .axi_w_sbiterr(),
    .axi_w_dbiterr(),
    .axi_w_overflow(),
    .axi_w_underflow(),
    .axi_b_injectsbiterr(1'b0),
    .axi_w_prog_full(),
    .axi_w_prog_empty(),
    .axi_b_injectdbiterr(1'b0),
    .axi_b_prog_full_thresh(4'b0),
    .axi_b_prog_empty_thresh(4'b0),
    .axi_b_data_count(),
    .axi_b_wr_data_count(),
    .axi_b_rd_data_count(),
    .axi_b_sbiterr(),
    .axi_b_dbiterr(),
    .axi_b_overflow(),
    .axi_b_underflow(),
    .axi_ar_injectsbiterr(1'b0),
    .axi_b_prog_full(),
    .axi_b_prog_empty(),
    .axi_ar_injectdbiterr(1'b0),
    .axi_ar_prog_full_thresh(4'b0),
    .axi_ar_prog_empty_thresh(4'b0),
    .axi_ar_data_count(),
    .axi_ar_wr_data_count(),
    .axi_ar_rd_data_count(),
    .axi_ar_sbiterr(),
    .axi_ar_dbiterr(),
    .axi_ar_overflow(),
    .axi_ar_underflow(),
    .axi_ar_prog_full(),
    .axi_ar_prog_empty(),
    .axi_r_injectsbiterr(1'b0),
    .axi_r_injectdbiterr(1'b0),
    .axi_r_prog_full_thresh(10'b0),
    .axi_r_prog_empty_thresh(10'b0),
    .axi_r_data_count(),
    .axi_r_wr_data_count(),
    .axi_r_rd_data_count(),
    .axi_r_sbiterr(),
    .axi_r_dbiterr(),
    .axi_r_overflow(),
    .axi_r_underflow(),
    .axis_injectsbiterr(1'b0),
    .axi_r_prog_full(),
    .axi_r_prog_empty(),
    .axis_injectdbiterr(1'b0),
    .axis_prog_full_thresh(10'b0),
    .axis_prog_empty_thresh(10'b0),
    .axis_data_count(),
    .axis_wr_data_count(),
    .axis_rd_data_count(),
    .axis_sbiterr(),
    .axis_dbiterr(),
    .axis_overflow(),
    .axis_underflow(),
    .axis_prog_full(),
    .axis_prog_empty(),
    .wr_rst_busy(),
    .rd_rst_busy(),
    .sleep(1'b0)
  );

  fifo_generator_v13_1_4 #(
    .C_DIN_WIDTH(P_M_CMD_WIDTH),
    .C_DOUT_WIDTH(P_M_CMD_WIDTH),
    .C_RD_DEPTH(32),
    .C_RD_PNTR_WIDTH(5),
    .C_RD_DATA_COUNT_WIDTH(5),
    .C_WR_DEPTH(32),
    .C_WR_PNTR_WIDTH(5),
    .C_WR_DATA_COUNT_WIDTH(5),
    .C_DATA_COUNT_WIDTH(5),
    .C_COMMON_CLOCK(1),
    .C_COUNT_TYPE(0),
    .C_DEFAULT_VALUE("BlankString"),
    .C_DOUT_RST_VAL("0"),
    .C_ENABLE_RLOCS(0),
    .C_FAMILY(C_FAMILY),
    .C_FULL_FLAGS_RST_VAL(0),
    .C_HAS_ALMOST_EMPTY(0),
    .C_HAS_ALMOST_FULL(0),
    .C_HAS_BACKUP(0),
    .C_HAS_DATA_COUNT(0),
    .C_HAS_INT_CLK(0),
    .C_HAS_MEMINIT_FILE(0),
    .C_HAS_OVERFLOW(0),
    .C_HAS_RD_DATA_COUNT(0),
    .C_HAS_RD_RST(0),
    .C_HAS_RST(0),
    .C_HAS_SRST(1),
    .C_HAS_UNDERFLOW(0),
    .C_HAS_VALID(0),
    .C_HAS_WR_ACK(0),
    .C_HAS_WR_DATA_COUNT(0),
    .C_HAS_WR_RST(0),
    .C_IMPLEMENTATION_TYPE(0),
    .C_INIT_WR_PNTR_VAL(0),
    .C_MEMORY_TYPE(2),
    .C_MIF_FILE_NAME("BlankString"),
    .C_OPTIMIZATION_MODE(0),
    .C_OVERFLOW_LOW(0),
    .C_PRELOAD_LATENCY(0),
    .C_PRELOAD_REGS(1),
    .C_PRIM_FIFO_TYPE("512x36"),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL(4),
    .C_PROG_EMPTY_THRESH_NEGATE_VAL(5),
    .C_PROG_EMPTY_TYPE(0),
    .C_PROG_FULL_THRESH_ASSERT_VAL(31),
    .C_PROG_FULL_THRESH_NEGATE_VAL(30),
    .C_PROG_FULL_TYPE(0),
    .C_RD_FREQ(1),
    .C_UNDERFLOW_LOW(0),
    .C_USE_DOUT_RST(0),
    .C_USE_ECC(0),
    .C_USE_EMBEDDED_REG(0),
    .C_USE_FIFO16_FLAGS(0),
    .C_USE_FWFT_DATA_COUNT(1),
    .C_VALID_LOW(0),
    .C_WR_ACK_LOW(0),
    .C_WR_FREQ(1),
    .C_WR_RESPONSE_LATENCY(1),
    .C_MSGON_VAL(1),
    .C_ENABLE_RST_SYNC(1),
    .C_ERROR_INJECTION_TYPE(0),
    .C_SYNCHRONIZER_STAGE(C_SYNCHRONIZER_STAGE),
    .C_INTERFACE_TYPE(0),
    .C_AXI_TYPE(0),
    .C_HAS_AXI_WR_CHANNEL(0),
    .C_HAS_AXI_RD_CHANNEL(0),
    .C_HAS_SLAVE_CE(0),
    .C_HAS_MASTER_CE(0),
    .C_ADD_NGC_CONSTRAINT(0),
    .C_USE_COMMON_OVERFLOW(0),
    .C_USE_COMMON_UNDERFLOW(0),
    .C_USE_DEFAULT_SETTINGS(0),
    .C_AXI_ID_WIDTH(4),
    .C_AXI_ADDR_WIDTH(32),
    .C_AXI_DATA_WIDTH(64),
    .C_HAS_AXI_AWUSER(0),
    .C_HAS_AXI_WUSER(0),
    .C_HAS_AXI_BUSER(0),
    .C_HAS_AXI_ARUSER(0),
    .C_HAS_AXI_RUSER(0),
    .C_AXI_ARUSER_WIDTH(1),
    .C_AXI_AWUSER_WIDTH(1),
    .C_AXI_WUSER_WIDTH(1),
    .C_AXI_BUSER_WIDTH(1),
    .C_AXI_RUSER_WIDTH(1),
    .C_HAS_AXIS_TDATA(0),
    .C_HAS_AXIS_TID(0),
    .C_HAS_AXIS_TDEST(0),
    .C_HAS_AXIS_TUSER(0),
    .C_HAS_AXIS_TREADY(1),
    .C_HAS_AXIS_TLAST(0),
    .C_HAS_AXIS_TSTRB(0),
    .C_HAS_AXIS_TKEEP(0),
    .C_AXIS_TDATA_WIDTH(64),
    .C_AXIS_TID_WIDTH(8),
    .C_AXIS_TDEST_WIDTH(4),
    .C_AXIS_TUSER_WIDTH(4),
    .C_AXIS_TSTRB_WIDTH(4),
    .C_AXIS_TKEEP_WIDTH(4),
    .C_WACH_TYPE(0),
    .C_WDCH_TYPE(0),
    .C_WRCH_TYPE(0),
    .C_RACH_TYPE(0),
    .C_RDCH_TYPE(0),
    .C_AXIS_TYPE(0),
    .C_IMPLEMENTATION_TYPE_WACH(1),
    .C_IMPLEMENTATION_TYPE_WDCH(1),
    .C_IMPLEMENTATION_TYPE_WRCH(1),
    .C_IMPLEMENTATION_TYPE_RACH(1),
    .C_IMPLEMENTATION_TYPE_RDCH(1),
    .C_IMPLEMENTATION_TYPE_AXIS(1),
    .C_APPLICATION_TYPE_WACH(0),
    .C_APPLICATION_TYPE_WDCH(0),
    .C_APPLICATION_TYPE_WRCH(0),
    .C_APPLICATION_TYPE_RACH(0),
    .C_APPLICATION_TYPE_RDCH(0),
    .C_APPLICATION_TYPE_AXIS(0),
    .C_USE_ECC_WACH(0),
    .C_USE_ECC_WDCH(0),
    .C_USE_ECC_WRCH(0),
    .C_USE_ECC_RACH(0),
    .C_USE_ECC_RDCH(0),
    .C_USE_ECC_AXIS(0),
    .C_ERROR_INJECTION_TYPE_WACH(0),
    .C_ERROR_INJECTION_TYPE_WDCH(0),
    .C_ERROR_INJECTION_TYPE_WRCH(0),
    .C_ERROR_INJECTION_TYPE_RACH(0),
    .C_ERROR_INJECTION_TYPE_RDCH(0),
    .C_ERROR_INJECTION_TYPE_AXIS(0),
    .C_DIN_WIDTH_WACH(32),
    .C_DIN_WIDTH_WDCH(64),
    .C_DIN_WIDTH_WRCH(2),
    .C_DIN_WIDTH_RACH(32),
    .C_DIN_WIDTH_RDCH(64),
    .C_DIN_WIDTH_AXIS(1),
    .C_WR_DEPTH_WACH(16),
    .C_WR_DEPTH_WDCH(1024),
    .C_WR_DEPTH_WRCH(16),
    .C_WR_DEPTH_RACH(16),
    .C_WR_DEPTH_RDCH(1024),
    .C_WR_DEPTH_AXIS(1024),
    .C_WR_PNTR_WIDTH_WACH(4),
    .C_WR_PNTR_WIDTH_WDCH(10),
    .C_WR_PNTR_WIDTH_WRCH(4),
    .C_WR_PNTR_WIDTH_RACH(4),
    .C_WR_PNTR_WIDTH_RDCH(10),
    .C_WR_PNTR_WIDTH_AXIS(10),
    .C_HAS_DATA_COUNTS_WACH(0),
    .C_HAS_DATA_COUNTS_WDCH(0),
    .C_HAS_DATA_COUNTS_WRCH(0),
    .C_HAS_DATA_COUNTS_RACH(0),
    .C_HAS_DATA_COUNTS_RDCH(0),
    .C_HAS_DATA_COUNTS_AXIS(0),
    .C_HAS_PROG_FLAGS_WACH(0),
    .C_HAS_PROG_FLAGS_WDCH(0),
    .C_HAS_PROG_FLAGS_WRCH(0),
    .C_HAS_PROG_FLAGS_RACH(0),
    .C_HAS_PROG_FLAGS_RDCH(0),
    .C_HAS_PROG_FLAGS_AXIS(0),
    .C_PROG_FULL_TYPE_WACH(0),
    .C_PROG_FULL_TYPE_WDCH(0),
    .C_PROG_FULL_TYPE_WRCH(0),
    .C_PROG_FULL_TYPE_RACH(0),
    .C_PROG_FULL_TYPE_RDCH(0),
    .C_PROG_FULL_TYPE_AXIS(0),
    .C_PROG_FULL_THRESH_ASSERT_VAL_WACH(1023),
    .C_PROG_FULL_THRESH_ASSERT_VAL_WDCH(1023),
    .C_PROG_FULL_THRESH_ASSERT_VAL_WRCH(1023),
    .C_PROG_FULL_THRESH_ASSERT_VAL_RACH(1023),
    .C_PROG_FULL_THRESH_ASSERT_VAL_RDCH(1023),
    .C_PROG_FULL_THRESH_ASSERT_VAL_AXIS(1023),
    .C_PROG_EMPTY_TYPE_WACH(0),
    .C_PROG_EMPTY_TYPE_WDCH(0),
    .C_PROG_EMPTY_TYPE_WRCH(0),
    .C_PROG_EMPTY_TYPE_RACH(0),
    .C_PROG_EMPTY_TYPE_RDCH(0),
    .C_PROG_EMPTY_TYPE_AXIS(0),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_WACH(1022),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_WDCH(1022),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_WRCH(1022),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_RACH(1022),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_RDCH(1022),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_AXIS(1022),
    .C_REG_SLICE_MODE_WACH(0),
    .C_REG_SLICE_MODE_WDCH(0),
    .C_REG_SLICE_MODE_WRCH(0),
    .C_REG_SLICE_MODE_RACH(0),
    .C_REG_SLICE_MODE_RDCH(0),
    .C_REG_SLICE_MODE_AXIS(0),
    .C_AXI_LEN_WIDTH(8),
    .C_AXI_LOCK_WIDTH(2)
  ) m_cmd_fifo (
    .clk(m_aclk),
    .srst(m_fifo_rst),
    .din(m_ar_cmd),
    .dout(m_r_cmd),
    .full(m_cmd_full),
    .empty(m_cmd_empty),
    .wr_en(m_cmd_push),
    .rd_en(m_cmd_pop),
    .backup(1'b0),
    .backup_marker(1'b0),
    .rst(1'b0),
    .wr_clk(1'b0),
    .wr_rst(1'b0),
    .rd_clk(1'b0),
    .rd_rst(1'b0),
    .prog_empty_thresh(5'b0),
    .prog_empty_thresh_assert(5'b0),
    .prog_empty_thresh_negate(5'b0),
    .prog_full_thresh(5'b0),
    .prog_full_thresh_assert(5'b0),
    .prog_full_thresh_negate(5'b0),
    .int_clk(1'b0),
    .injectdbiterr(1'b0),
    .injectsbiterr(1'b0),
    .almost_full(),
    .wr_ack(),
    .overflow(),
    .almost_empty(),
    .valid(),
    .underflow(),
    .data_count(),
    .rd_data_count(),
    .wr_data_count(),
    .prog_full(),
    .prog_empty(),
    .sbiterr(),
    .dbiterr(),
    .m_aclk(1'b0),
    .s_aclk(1'b0),
    .s_aresetn(1'b0),
    .m_aclk_en(1'b0),
    .s_aclk_en(1'b0),
    .s_axi_awid(4'b0),
    .s_axi_awaddr(32'b0),
    .s_axi_awlen(8'b0),
    .s_axi_awsize(3'b0),
    .s_axi_awburst(2'b0),
    .s_axi_awlock(2'b0),
    .s_axi_awcache(4'b0),
    .s_axi_awprot(3'b0),
    .s_axi_awqos(4'b0),
    .s_axi_awregion(4'b0),
    .s_axi_awuser(1'b0),
    .s_axi_awvalid(1'b0),
    .s_axi_awready(),
    .s_axi_wid(4'b0),
    .s_axi_wdata(64'b0),
    .s_axi_wstrb(8'b0),
    .s_axi_wlast(1'b0),
    .s_axi_wuser(1'b0),
    .s_axi_wvalid(1'b0),
    .s_axi_wready(),
    .s_axi_bid(),
    .s_axi_bresp(),
    .s_axi_buser(),
    .s_axi_bvalid(),
    .s_axi_bready(1'b0),
    .m_axi_awid(),
    .m_axi_awaddr(),
    .m_axi_awlen(),
    .m_axi_awsize(),
    .m_axi_awburst(),
    .m_axi_awlock(),
    .m_axi_awcache(),
    .m_axi_awprot(),
    .m_axi_awqos(),
    .m_axi_awregion(),
    .m_axi_awuser(),
    .m_axi_awvalid(),
    .m_axi_awready(1'b0),
    .m_axi_wid(),
    .m_axi_wdata(),
    .m_axi_wstrb(),
    .m_axi_wlast(),
    .m_axi_wuser(),
    .m_axi_wvalid(),
    .m_axi_wready(1'b0),
    .m_axi_bid(4'b0),
    .m_axi_bresp(2'b0),
    .m_axi_buser(1'b0),
    .m_axi_bvalid(1'b0),
    .m_axi_bready(),
    .s_axi_arid(4'b0),
    .s_axi_araddr(32'b0),
    .s_axi_arlen(8'b0),
    .s_axi_arsize(3'b0),
    .s_axi_arburst(2'b0),
    .s_axi_arlock(2'b0),
    .s_axi_arcache(4'b0),
    .s_axi_arprot(3'b0),
    .s_axi_arqos(4'b0),
    .s_axi_arregion(4'b0),
    .s_axi_aruser(1'b0),
    .s_axi_arvalid(1'b0),
    .s_axi_arready(),
    .s_axi_rid(),
    .s_axi_rdata(),
    .s_axi_rresp(),
    .s_axi_rlast(),
    .s_axi_ruser(),
    .s_axi_rvalid(),
    .s_axi_rready(1'b0),
    .m_axi_arid(),
    .m_axi_araddr(),
    .m_axi_arlen(),
    .m_axi_arsize(),
    .m_axi_arburst(),
    .m_axi_arlock(),
    .m_axi_arcache(),
    .m_axi_arprot(),
    .m_axi_arqos(),
    .m_axi_arregion(),
    .m_axi_aruser(),
    .m_axi_arvalid(),
    .m_axi_arready(1'b0),
    .m_axi_rid(4'b0),
    .m_axi_rdata(64'b0),
    .m_axi_rresp(2'b0),
    .m_axi_rlast(1'b0),
    .m_axi_ruser(1'b0),
    .m_axi_rvalid(1'b0),
    .m_axi_rready(),
    .s_axis_tvalid(1'b0),
    .s_axis_tready(),
    .s_axis_tdata(64'b0),
    .s_axis_tstrb(4'b0),
    .s_axis_tkeep(4'b0),
    .s_axis_tlast(1'b0),
    .s_axis_tid(8'b0),
    .s_axis_tdest(4'b0),
    .s_axis_tuser(4'b0),
    .m_axis_tvalid(),
    .m_axis_tready(1'b0),
    .m_axis_tdata(),
    .m_axis_tstrb(),
    .m_axis_tkeep(),
    .m_axis_tlast(),
    .m_axis_tid(),
    .m_axis_tdest(),
    .m_axis_tuser(),
    .axi_aw_injectsbiterr(1'b0),
    .axi_aw_injectdbiterr(1'b0),
    .axi_aw_prog_full_thresh(4'b0),
    .axi_aw_prog_empty_thresh(4'b0),
    .axi_aw_data_count(),
    .axi_aw_wr_data_count(),
    .axi_aw_rd_data_count(),
    .axi_aw_sbiterr(),
    .axi_aw_dbiterr(),
    .axi_aw_overflow(),
    .axi_aw_underflow(),
    .axi_aw_prog_full(),
    .axi_aw_prog_empty(),
    .axi_w_injectsbiterr(1'b0),
    .axi_w_injectdbiterr(1'b0),
    .axi_w_prog_full_thresh(10'b0),
    .axi_w_prog_empty_thresh(10'b0),
    .axi_w_data_count(),
    .axi_w_wr_data_count(),
    .axi_w_rd_data_count(),
    .axi_w_sbiterr(),
    .axi_w_dbiterr(),
    .axi_w_overflow(),
    .axi_w_underflow(),
    .axi_b_injectsbiterr(1'b0),
    .axi_w_prog_full(),
    .axi_w_prog_empty(),
    .axi_b_injectdbiterr(1'b0),
    .axi_b_prog_full_thresh(4'b0),
    .axi_b_prog_empty_thresh(4'b0),
    .axi_b_data_count(),
    .axi_b_wr_data_count(),
    .axi_b_rd_data_count(),
    .axi_b_sbiterr(),
    .axi_b_dbiterr(),
    .axi_b_overflow(),
    .axi_b_underflow(),
    .axi_ar_injectsbiterr(1'b0),
    .axi_b_prog_full(),
    .axi_b_prog_empty(),
    .axi_ar_injectdbiterr(1'b0),
    .axi_ar_prog_full_thresh(4'b0),
    .axi_ar_prog_empty_thresh(4'b0),
    .axi_ar_data_count(),
    .axi_ar_wr_data_count(),
    .axi_ar_rd_data_count(),
    .axi_ar_sbiterr(),
    .axi_ar_dbiterr(),
    .axi_ar_overflow(),
    .axi_ar_underflow(),
    .axi_ar_prog_full(),
    .axi_ar_prog_empty(),
    .axi_r_injectsbiterr(1'b0),
    .axi_r_injectdbiterr(1'b0),
    .axi_r_prog_full_thresh(10'b0),
    .axi_r_prog_empty_thresh(10'b0),
    .axi_r_data_count(),
    .axi_r_wr_data_count(),
    .axi_r_rd_data_count(),
    .axi_r_sbiterr(),
    .axi_r_dbiterr(),
    .axi_r_overflow(),
    .axi_r_underflow(),
    .axis_injectsbiterr(1'b0),
    .axi_r_prog_full(),
    .axi_r_prog_empty(),
    .axis_injectdbiterr(1'b0),
    .axis_prog_full_thresh(10'b0),
    .axis_prog_empty_thresh(10'b0),
    .axis_data_count(),
    .axis_wr_data_count(),
    .axis_rd_data_count(),
    .axis_sbiterr(),
    .axis_dbiterr(),
    .axis_overflow(),
    .axis_underflow(),
    .axis_prog_full(),
    .axis_prog_empty(),
    .wr_rst_busy(),
    .rd_rst_busy(),
    .sleep(1'b0)
  );

  fifo_generator_v13_1_4 #(
    .C_DIN_WIDTH(4),
    .C_DOUT_WIDTH(4),
    .C_RD_DEPTH(512),
    .C_RD_PNTR_WIDTH(9),
    .C_RD_DATA_COUNT_WIDTH(9),
    .C_WR_DEPTH(512),
    .C_WR_PNTR_WIDTH(9),
    .C_WR_DATA_COUNT_WIDTH(9),
    .C_DATA_COUNT_WIDTH(9),
    .C_COMMON_CLOCK(P_COMMON_CLOCK),
    .C_COUNT_TYPE(0),
    .C_DEFAULT_VALUE("BlankString"),
    .C_DOUT_RST_VAL("0"),
    .C_ENABLE_RLOCS(0),
    .C_FAMILY(C_FAMILY),
    .C_FULL_FLAGS_RST_VAL(0),
    .C_HAS_ALMOST_EMPTY(0),
    .C_HAS_ALMOST_FULL(0),
    .C_HAS_BACKUP(0),
    .C_HAS_DATA_COUNT(0),
    .C_HAS_INT_CLK(0),
    .C_HAS_MEMINIT_FILE(0),
    .C_HAS_OVERFLOW(0),
    .C_HAS_RD_DATA_COUNT(0),
    .C_HAS_RD_RST(0),
    .C_HAS_RST(P_COMMON_CLOCK ? 0 : 1),
    .C_HAS_SRST(P_COMMON_CLOCK ? 1 : 0),
    .C_HAS_UNDERFLOW(0),
    .C_HAS_VALID(0),
    .C_HAS_WR_ACK(0),
    .C_HAS_WR_DATA_COUNT(0),
    .C_HAS_WR_RST(0),
    .C_IMPLEMENTATION_TYPE(P_COMMON_CLOCK ? 0 : 2),
    .C_INIT_WR_PNTR_VAL(0),
    .C_MEMORY_TYPE(2),
    .C_MIF_FILE_NAME("BlankString"),
    .C_OPTIMIZATION_MODE(0),
    .C_OVERFLOW_LOW(0),
    .C_PRELOAD_LATENCY(0),
    .C_PRELOAD_REGS(1),
    .C_PRIM_FIFO_TYPE("512x36"),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL(4),
    .C_PROG_EMPTY_THRESH_NEGATE_VAL(5),
    .C_PROG_EMPTY_TYPE(0),
    .C_PROG_FULL_THRESH_ASSERT_VAL(31),
    .C_PROG_FULL_THRESH_NEGATE_VAL(30),
    .C_PROG_FULL_TYPE(0),
    .C_RD_FREQ(1),
    .C_UNDERFLOW_LOW(0),
    .C_USE_DOUT_RST(0),
    .C_USE_ECC(0),
    .C_USE_EMBEDDED_REG(0),
    .C_USE_FIFO16_FLAGS(0),
    .C_USE_FWFT_DATA_COUNT(1),
    .C_VALID_LOW(0),
    .C_WR_ACK_LOW(0),
    .C_WR_FREQ(1),
    .C_WR_RESPONSE_LATENCY(1),
    .C_MSGON_VAL(1),
    .C_ENABLE_RST_SYNC(1),
    .C_ERROR_INJECTION_TYPE(0),
    .C_SYNCHRONIZER_STAGE(C_SYNCHRONIZER_STAGE),
    .C_INTERFACE_TYPE(0),
    .C_AXI_TYPE(0),
    .C_HAS_AXI_WR_CHANNEL(0),
    .C_HAS_AXI_RD_CHANNEL(0),
    .C_HAS_SLAVE_CE(0),
    .C_HAS_MASTER_CE(0),
    .C_ADD_NGC_CONSTRAINT(0),
    .C_USE_COMMON_OVERFLOW(0),
    .C_USE_COMMON_UNDERFLOW(0),
    .C_USE_DEFAULT_SETTINGS(0),
    .C_AXI_ID_WIDTH(4),
    .C_AXI_ADDR_WIDTH(32),
    .C_AXI_DATA_WIDTH(64),
    .C_HAS_AXI_AWUSER(0),
    .C_HAS_AXI_WUSER(0),
    .C_HAS_AXI_BUSER(0),
    .C_HAS_AXI_ARUSER(0),
    .C_HAS_AXI_RUSER(0),
    .C_AXI_ARUSER_WIDTH(1),
    .C_AXI_AWUSER_WIDTH(1),
    .C_AXI_WUSER_WIDTH(1),
    .C_AXI_BUSER_WIDTH(1),
    .C_AXI_RUSER_WIDTH(1),
    .C_HAS_AXIS_TDATA(0),
    .C_HAS_AXIS_TID(0),
    .C_HAS_AXIS_TDEST(0),
    .C_HAS_AXIS_TUSER(0),
    .C_HAS_AXIS_TREADY(1),
    .C_HAS_AXIS_TLAST(0),
    .C_HAS_AXIS_TSTRB(0),
    .C_HAS_AXIS_TKEEP(0),
    .C_AXIS_TDATA_WIDTH(64),
    .C_AXIS_TID_WIDTH(8),
    .C_AXIS_TDEST_WIDTH(4),
    .C_AXIS_TUSER_WIDTH(4),
    .C_AXIS_TSTRB_WIDTH(4),
    .C_AXIS_TKEEP_WIDTH(4),
    .C_WACH_TYPE(0),
    .C_WDCH_TYPE(0),
    .C_WRCH_TYPE(0),
    .C_RACH_TYPE(0),
    .C_RDCH_TYPE(0),
    .C_AXIS_TYPE(0),
    .C_IMPLEMENTATION_TYPE_WACH(1),
    .C_IMPLEMENTATION_TYPE_WDCH(1),
    .C_IMPLEMENTATION_TYPE_WRCH(1),
    .C_IMPLEMENTATION_TYPE_RACH(1),
    .C_IMPLEMENTATION_TYPE_RDCH(1),
    .C_IMPLEMENTATION_TYPE_AXIS(1),
    .C_APPLICATION_TYPE_WACH(0),
    .C_APPLICATION_TYPE_WDCH(0),
    .C_APPLICATION_TYPE_WRCH(0),
    .C_APPLICATION_TYPE_RACH(0),
    .C_APPLICATION_TYPE_RDCH(0),
    .C_APPLICATION_TYPE_AXIS(0),
    .C_USE_ECC_WACH(0),
    .C_USE_ECC_WDCH(0),
    .C_USE_ECC_WRCH(0),
    .C_USE_ECC_RACH(0),
    .C_USE_ECC_RDCH(0),
    .C_USE_ECC_AXIS(0),
    .C_ERROR_INJECTION_TYPE_WACH(0),
    .C_ERROR_INJECTION_TYPE_WDCH(0),
    .C_ERROR_INJECTION_TYPE_WRCH(0),
    .C_ERROR_INJECTION_TYPE_RACH(0),
    .C_ERROR_INJECTION_TYPE_RDCH(0),
    .C_ERROR_INJECTION_TYPE_AXIS(0),
    .C_DIN_WIDTH_WACH(32),
    .C_DIN_WIDTH_WDCH(64),
    .C_DIN_WIDTH_WRCH(2),
    .C_DIN_WIDTH_RACH(32),
    .C_DIN_WIDTH_RDCH(64),
    .C_DIN_WIDTH_AXIS(1),
    .C_WR_DEPTH_WACH(16),
    .C_WR_DEPTH_WDCH(1024),
    .C_WR_DEPTH_WRCH(16),
    .C_WR_DEPTH_RACH(16),
    .C_WR_DEPTH_RDCH(1024),
    .C_WR_DEPTH_AXIS(1024),
    .C_WR_PNTR_WIDTH_WACH(4),
    .C_WR_PNTR_WIDTH_WDCH(10),
    .C_WR_PNTR_WIDTH_WRCH(4),
    .C_WR_PNTR_WIDTH_RACH(4),
    .C_WR_PNTR_WIDTH_RDCH(10),
    .C_WR_PNTR_WIDTH_AXIS(10),
    .C_HAS_DATA_COUNTS_WACH(0),
    .C_HAS_DATA_COUNTS_WDCH(0),
    .C_HAS_DATA_COUNTS_WRCH(0),
    .C_HAS_DATA_COUNTS_RACH(0),
    .C_HAS_DATA_COUNTS_RDCH(0),
    .C_HAS_DATA_COUNTS_AXIS(0),
    .C_HAS_PROG_FLAGS_WACH(0),
    .C_HAS_PROG_FLAGS_WDCH(0),
    .C_HAS_PROG_FLAGS_WRCH(0),
    .C_HAS_PROG_FLAGS_RACH(0),
    .C_HAS_PROG_FLAGS_RDCH(0),
    .C_HAS_PROG_FLAGS_AXIS(0),
    .C_PROG_FULL_TYPE_WACH(0),
    .C_PROG_FULL_TYPE_WDCH(0),
    .C_PROG_FULL_TYPE_WRCH(0),
    .C_PROG_FULL_TYPE_RACH(0),
    .C_PROG_FULL_TYPE_RDCH(0),
    .C_PROG_FULL_TYPE_AXIS(0),
    .C_PROG_FULL_THRESH_ASSERT_VAL_WACH(1023),
    .C_PROG_FULL_THRESH_ASSERT_VAL_WDCH(1023),
    .C_PROG_FULL_THRESH_ASSERT_VAL_WRCH(1023),
    .C_PROG_FULL_THRESH_ASSERT_VAL_RACH(1023),
    .C_PROG_FULL_THRESH_ASSERT_VAL_RDCH(1023),
    .C_PROG_FULL_THRESH_ASSERT_VAL_AXIS(1023),
    .C_PROG_EMPTY_TYPE_WACH(0),
    .C_PROG_EMPTY_TYPE_WDCH(0),
    .C_PROG_EMPTY_TYPE_WRCH(0),
    .C_PROG_EMPTY_TYPE_RACH(0),
    .C_PROG_EMPTY_TYPE_RDCH(0),
    .C_PROG_EMPTY_TYPE_AXIS(0),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_WACH(1022),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_WDCH(1022),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_WRCH(1022),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_RACH(1022),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_RDCH(1022),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_AXIS(1022),
    .C_REG_SLICE_MODE_WACH(0),
    .C_REG_SLICE_MODE_WDCH(0),
    .C_REG_SLICE_MODE_WRCH(0),
    .C_REG_SLICE_MODE_RACH(0),
    .C_REG_SLICE_MODE_RDCH(0),
    .C_REG_SLICE_MODE_AXIS(0),
    .C_AXI_LEN_WIDTH(8),
    .C_AXI_LOCK_WIDTH(2)
  ) dw_fifogen_rresp (
    .clk(rresp_fifo_clk),
    .wr_clk(rresp_fifo_wrclk),
    .rd_clk(rresp_fifo_rdclk),
    .srst(P_COMMON_CLOCK ? rresp_fifo_rst : 1'b0),
    .rst(P_COMMON_CLOCK ? 1'b0 : rresp_fifo_rst),
    .wr_rst(1'b0),
    .rd_rst(1'b0),
    .din(m_rresp_i),
    .dout(s_rresp_i),
    .full(rresp_fifo_full),
    .empty(rresp_fifo_empty),
    .wr_en(rresp_fifo_push),
    .rd_en(rresp_fifo_pop),
    .backup(1'b0),
    .backup_marker(1'b0),
    .prog_empty_thresh(9'b0),
    .prog_empty_thresh_assert(9'b0),
    .prog_empty_thresh_negate(9'b0),
    .prog_full_thresh(9'b0),
    .prog_full_thresh_assert(9'b0),
    .prog_full_thresh_negate(9'b0),
    .int_clk(1'b0),
    .injectdbiterr(1'b0),
    .injectsbiterr(1'b0),
    .almost_full(),
    .wr_ack(),
    .overflow(),
    .almost_empty(),
    .valid(),
    .underflow(),
    .data_count(),
    .rd_data_count(),
    .wr_data_count(),
    .prog_full(),
    .prog_empty(),
    .sbiterr(),
    .dbiterr(),
    .m_aclk(1'b0),
    .s_aclk(1'b0),
    .s_aresetn(1'b0),
    .m_aclk_en(1'b0),
    .s_aclk_en(1'b0),
    .s_axi_awid(4'b0),
    .s_axi_awaddr(32'b0),
    .s_axi_awlen(8'b0),
    .s_axi_awsize(3'b0),
    .s_axi_awburst(2'b0),
    .s_axi_awlock(2'b0),
    .s_axi_awcache(4'b0),
    .s_axi_awprot(3'b0),
    .s_axi_awqos(4'b0),
    .s_axi_awregion(4'b0),
    .s_axi_awuser(1'b0),
    .s_axi_awvalid(1'b0),
    .s_axi_awready(),
    .s_axi_wid(4'b0),
    .s_axi_wdata(64'b0),
    .s_axi_wstrb(8'b0),
    .s_axi_wlast(1'b0),
    .s_axi_wuser(1'b0),
    .s_axi_wvalid(1'b0),
    .s_axi_wready(),
    .s_axi_bid(),
    .s_axi_bresp(),
    .s_axi_buser(),
    .s_axi_bvalid(),
    .s_axi_bready(1'b0),
    .m_axi_awid(),
    .m_axi_awaddr(),
    .m_axi_awlen(),
    .m_axi_awsize(),
    .m_axi_awburst(),
    .m_axi_awlock(),
    .m_axi_awcache(),
    .m_axi_awprot(),
    .m_axi_awqos(),
    .m_axi_awregion(),
    .m_axi_awuser(),
    .m_axi_awvalid(),
    .m_axi_awready(1'b0),
    .m_axi_wid(),
    .m_axi_wdata(),
    .m_axi_wstrb(),
    .m_axi_wlast(),
    .m_axi_wuser(),
    .m_axi_wvalid(),
    .m_axi_wready(1'b0),
    .m_axi_bid(4'b0),
    .m_axi_bresp(2'b0),
    .m_axi_buser(1'b0),
    .m_axi_bvalid(1'b0),
    .m_axi_bready(),
    .s_axi_arid(4'b0),
    .s_axi_araddr(32'b0),
    .s_axi_arlen(8'b0),
    .s_axi_arsize(3'b0),
    .s_axi_arburst(2'b0),
    .s_axi_arlock(2'b0),
    .s_axi_arcache(4'b0),
    .s_axi_arprot(3'b0),
    .s_axi_arqos(4'b0),
    .s_axi_arregion(4'b0),
    .s_axi_aruser(1'b0),
    .s_axi_arvalid(1'b0),
    .s_axi_arready(),
    .s_axi_rid(),
    .s_axi_rdata(),
    .s_axi_rresp(),
    .s_axi_rlast(),
    .s_axi_ruser(),
    .s_axi_rvalid(),
    .s_axi_rready(1'b0),
    .m_axi_arid(),
    .m_axi_araddr(),
    .m_axi_arlen(),
    .m_axi_arsize(),
    .m_axi_arburst(),
    .m_axi_arlock(),
    .m_axi_arcache(),
    .m_axi_arprot(),
    .m_axi_arqos(),
    .m_axi_arregion(),
    .m_axi_aruser(),
    .m_axi_arvalid(),
    .m_axi_arready(1'b0),
    .m_axi_rid(4'b0),
    .m_axi_rdata(64'b0),
    .m_axi_rresp(2'b0),
    .m_axi_rlast(1'b0),
    .m_axi_ruser(1'b0),
    .m_axi_rvalid(1'b0),
    .m_axi_rready(),
    .s_axis_tvalid(1'b0),
    .s_axis_tready(),
    .s_axis_tdata(64'b0),
    .s_axis_tstrb(4'b0),
    .s_axis_tkeep(4'b0),
    .s_axis_tlast(1'b0),
    .s_axis_tid(8'b0),
    .s_axis_tdest(4'b0),
    .s_axis_tuser(4'b0),
    .m_axis_tvalid(),
    .m_axis_tready(1'b0),
    .m_axis_tdata(),
    .m_axis_tstrb(),
    .m_axis_tkeep(),
    .m_axis_tlast(),
    .m_axis_tid(),
    .m_axis_tdest(),
    .m_axis_tuser(),
    .axi_aw_injectsbiterr(1'b0),
    .axi_aw_injectdbiterr(1'b0),
    .axi_aw_prog_full_thresh(4'b0),
    .axi_aw_prog_empty_thresh(4'b0),
    .axi_aw_data_count(),
    .axi_aw_wr_data_count(),
    .axi_aw_rd_data_count(),
    .axi_aw_sbiterr(),
    .axi_aw_dbiterr(),
    .axi_aw_overflow(),
    .axi_aw_underflow(),
    .axi_aw_prog_full(),
    .axi_aw_prog_empty(),
    .axi_w_injectsbiterr(1'b0),
    .axi_w_injectdbiterr(1'b0),
    .axi_w_prog_full_thresh(10'b0),
    .axi_w_prog_empty_thresh(10'b0),
    .axi_w_data_count(),
    .axi_w_wr_data_count(),
    .axi_w_rd_data_count(),
    .axi_w_sbiterr(),
    .axi_w_dbiterr(),
    .axi_w_overflow(),
    .axi_w_underflow(),
    .axi_b_injectsbiterr(1'b0),
    .axi_w_prog_full(),
    .axi_w_prog_empty(),
    .axi_b_injectdbiterr(1'b0),
    .axi_b_prog_full_thresh(4'b0),
    .axi_b_prog_empty_thresh(4'b0),
    .axi_b_data_count(),
    .axi_b_wr_data_count(),
    .axi_b_rd_data_count(),
    .axi_b_sbiterr(),
    .axi_b_dbiterr(),
    .axi_b_overflow(),
    .axi_b_underflow(),
    .axi_ar_injectsbiterr(1'b0),
    .axi_b_prog_full(),
    .axi_b_prog_empty(),
    .axi_ar_injectdbiterr(1'b0),
    .axi_ar_prog_full_thresh(4'b0),
    .axi_ar_prog_empty_thresh(4'b0),
    .axi_ar_data_count(),
    .axi_ar_wr_data_count(),
    .axi_ar_rd_data_count(),
    .axi_ar_sbiterr(),
    .axi_ar_dbiterr(),
    .axi_ar_overflow(),
    .axi_ar_underflow(),
    .axi_ar_prog_full(),
    .axi_ar_prog_empty(),
    .axi_r_injectsbiterr(1'b0),
    .axi_r_injectdbiterr(1'b0),
    .axi_r_prog_full_thresh(10'b0),
    .axi_r_prog_empty_thresh(10'b0),
    .axi_r_data_count(),
    .axi_r_wr_data_count(),
    .axi_r_rd_data_count(),
    .axi_r_sbiterr(),
    .axi_r_dbiterr(),
    .axi_r_overflow(),
    .axi_r_underflow(),
    .axis_injectsbiterr(1'b0),
    .axi_r_prog_full(),
    .axi_r_prog_empty(),
    .axis_injectdbiterr(1'b0),
    .axis_prog_full_thresh(10'b0),
    .axis_prog_empty_thresh(10'b0),
    .axis_data_count(),
    .axis_wr_data_count(),
    .axis_rd_data_count(),
    .axis_sbiterr(),
    .axis_dbiterr(),
    .axis_overflow(),
    .axis_underflow(),
    .axis_prog_full(),
    .axis_prog_empty(),
    .wr_rst_busy(),
    .rd_rst_busy(),
    .sleep(1'b0)
  );

  endgenerate

endmodule


//-----------------------------------------------------------------------------
//-- (c) Copyright 2010 Xilinx, Inc. All rights reserved.
//--
//-- This file contains confidential and proprietary information
//-- of Xilinx, Inc. and is protected under U.S. and
//-- international copyright and other intellectual property
//-- laws.
//--
//-- DISCLAIMER
//-- This disclaimer is not a license and does not grant any
//-- rights to the materials distributed herewith. Except as
//-- otherwise provided in a valid license issued to you by
//-- Xilinx, and to the maximum extent permitted by applicable
//-- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
//-- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
//-- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
//-- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
//-- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
//-- (2) Xilinx shall not be liable (whether in contract or tort,
//-- including negligence, or under any other theory of
//-- liability) for any loss or damage of any kind or nature
//-- related to, arising under or in connection with these
//-- materials, including for any direct, or any indirect,
//-- special, incidental, or consequential loss or damage
//-- (including loss of data, profits, goodwill, or any type of
//-- loss or damage suffered as a result of any action brought
//-- by a third party) even if such damage or loss was
//-- reasonably foreseeable or Xilinx had been advised of the
//-- possibility of the same.
//--
//-- CRITICAL APPLICATIONS
//-- Xilinx products are not designed or intended to be fail-
//-- safe, or for use in any application requiring fail-safe
//-- performance, such as life-support or safety devices or
//-- systems, Class III medical devices, nuclear facilities,
//-- applications related to the deployment of airbags, or any
//-- other applications that could lead to death, personal
//-- injury, or severe property or environmental damage
//-- (individually and collectively, "Critical
//-- Applications"). Customer assumes the sole risk and
//-- liability of any use of Xilinx products in Critical
//-- Applications, subject only to applicable laws and
//-- regulations governing limitations on product liability.
//--
//-- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
//-- PART OF THIS FILE AT ALL TIMES.
//-----------------------------------------------------------------------------
//
// Description: Up-Sizer
// Up-Sizer for generic SI- and MI-side data widths. This module instantiates
// Address, Write Data and Read Data Up-Sizer modules, each one taking care
// of the channel specific tasks.
// The Address Up-Sizer can handle both AR and AW channels.
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   axi_upsizer
//     a_upsizer
//       fifo
//         fifo_gen
//           fifo_coregen
//     w_upsizer
//     r_upsizer
//
//--------------------------------------------------------------------------
`timescale 1ps/1ps
`default_nettype none

(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_dwidth_converter_v2_1_12_axi_upsizer #
  (
   parameter         C_FAMILY                         = "virtex7", 
                       // FPGA Family. Current version: virtex6 or spartan6.
   parameter integer C_AXI_PROTOCOL = 0, 
                       // Protocol of SI and MI (0=AXI4, 1=AXI3).
   parameter integer C_S_AXI_ID_WIDTH                   = 1, 
                       // Width of all ID signals on SI side of converter.
                       // Range: 1 - 32.
   parameter integer C_SUPPORTS_ID                    = 0, 
                       // Indicates whether SI-side ID needs to be stored and compared.
                       // 0 = No, SI is single-threaded, propagate all transactions.
                       // 1 = Yes, stall any transaction with ID different than outstanding transactions.
   parameter integer C_AXI_ADDR_WIDTH                 = 32, 
                       // Width of all ADDR signals on SI and MI.
                       // Range (AXI4, AXI3): 12 - 64.
   parameter integer C_S_AXI_DATA_WIDTH               = 32,
                       // Width of s_axi_wdata and s_axi_rdata.
                       // Range: 32, 64, 128, 256, 512, 1024.
   parameter integer C_M_AXI_DATA_WIDTH               = 64,
                       // Width of m_axi_wdata and m_axi_rdata. 
                       // Assume always >= than C_S_AXI_DATA_WIDTH.
                       // Range: 32, 64, 128, 256, 512, 1024.
   parameter integer C_AXI_SUPPORTS_WRITE             = 1,
   parameter integer C_AXI_SUPPORTS_READ              = 1,
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//   parameter integer C_FIFO_MODE                        = 0,
   parameter integer C_FIFO_MODE                        = 1,
                       // 0=None, 1=Packet_FIFO, 2=Clock_conversion_Packet_FIFO, 3=Simple_FIFO (FUTURE), 4=Clock_conversion_Simple_FIFO (FUTURE)
   parameter integer C_S_AXI_ACLK_RATIO = 1,     // Clock frequency ratio of SI w.r.t. MI.
                                                 // Range = [1..16].
   parameter integer C_M_AXI_ACLK_RATIO = 2,     // Clock frequency ratio of MI w.r.t. SI.
                                                 // Range = [2..16] if C_S_AXI_ACLK_RATIO = 1; else must be 1.
   parameter integer C_AXI_IS_ACLK_ASYNC = 0,    // Indicates whether S and M clocks are asynchronous.
                                                 // FUTURE FEATURE
                                                 // Range = [0, 1].
   parameter integer C_PACKING_LEVEL                    = 1,
                       // 0 = Never pack (expander only); packing logic is omitted.
                       // 1 = Pack only when CACHE[1] (Modifiable) is high.
                       // 2 = Always pack, regardless of sub-size transaction or Modifiable bit.
                       //     (Required when used as helper-core by mem-con. Same size AXI interfaces
                       //      should only be used when always packing)
   parameter integer C_SYNCHRONIZER_STAGE = 3
   )
  (

   // Slave Interface
   input  wire                                  s_axi_aresetn,
   input  wire                                  s_axi_aclk,
   
   // Slave Interface Write Address Ports
   input  wire [C_S_AXI_ID_WIDTH-1:0]             s_axi_awid,
   input  wire [C_AXI_ADDR_WIDTH-1:0]           s_axi_awaddr,
   input  wire [8-1:0]                          s_axi_awlen,
   input  wire [3-1:0]                          s_axi_awsize,
   input  wire [2-1:0]                          s_axi_awburst,
   input  wire [2-1:0]                          s_axi_awlock,
   input  wire [4-1:0]                          s_axi_awcache,
   input  wire [3-1:0]                          s_axi_awprot,
   input  wire [4-1:0]                          s_axi_awregion,
   input  wire [4-1:0]                          s_axi_awqos,
   input  wire                                  s_axi_awvalid,
   output wire                                  s_axi_awready,
   // Slave Interface Write Data Ports
   input  wire [C_S_AXI_DATA_WIDTH-1:0]         s_axi_wdata,
   input  wire [C_S_AXI_DATA_WIDTH/8-1:0]       s_axi_wstrb,
   input  wire                                  s_axi_wlast,
   input  wire                                  s_axi_wvalid,
   output wire                                  s_axi_wready,
   // Slave Interface Write Response Ports
   output wire [C_S_AXI_ID_WIDTH-1:0]             s_axi_bid,
   output wire [2-1:0]                          s_axi_bresp,
   output wire                                  s_axi_bvalid,
   input  wire                                  s_axi_bready,
   // Slave Interface Read Address Ports
   input  wire [C_S_AXI_ID_WIDTH-1:0]             s_axi_arid,
   input  wire [C_AXI_ADDR_WIDTH-1:0]           s_axi_araddr,
   input  wire [8-1:0]                          s_axi_arlen,
   input  wire [3-1:0]                          s_axi_arsize,
   input  wire [2-1:0]                          s_axi_arburst,
   input  wire [2-1:0]                          s_axi_arlock,
   input  wire [4-1:0]                          s_axi_arcache,
   input  wire [3-1:0]                          s_axi_arprot,
   input  wire [4-1:0]                          s_axi_arregion,
   input  wire [4-1:0]                          s_axi_arqos,
   input  wire                                  s_axi_arvalid,
   output wire                                  s_axi_arready,
   // Slave Interface Read Data Ports
   output wire [C_S_AXI_ID_WIDTH-1:0]             s_axi_rid,
   output wire [C_S_AXI_DATA_WIDTH-1:0]         s_axi_rdata,
   output wire [2-1:0]                          s_axi_rresp,
   output wire                                  s_axi_rlast,
   output wire                                  s_axi_rvalid,
   input  wire                                  s_axi_rready,

   // Master Interface
   input  wire                                  m_axi_aresetn,
   input  wire                                  m_axi_aclk,
   
   // Master Interface Write Address Port
   output wire [C_AXI_ADDR_WIDTH-1:0]          m_axi_awaddr,
   output wire [8-1:0]                         m_axi_awlen,
   output wire [3-1:0]                         m_axi_awsize,
   output wire [2-1:0]                         m_axi_awburst,
   output wire [2-1:0]                         m_axi_awlock,
   output wire [4-1:0]                         m_axi_awcache,
   output wire [3-1:0]                         m_axi_awprot,
   output wire [4-1:0]                         m_axi_awregion,
   output wire [4-1:0]                         m_axi_awqos,
   output wire                                 m_axi_awvalid,
   input  wire                                 m_axi_awready,
   // Master Interface Write Data Ports
   output wire [C_M_AXI_DATA_WIDTH-1:0]    m_axi_wdata,
   output wire [C_M_AXI_DATA_WIDTH/8-1:0]  m_axi_wstrb,
   output wire                                                   m_axi_wlast,
   output wire                                                   m_axi_wvalid,
   input  wire                                                   m_axi_wready,
   // Master Interface Write Response Ports
   input  wire [2-1:0]                         m_axi_bresp,
   input  wire                                                   m_axi_bvalid,
   output wire                                                   m_axi_bready,
   // Master Interface Read Address Port
   output wire [C_AXI_ADDR_WIDTH-1:0]          m_axi_araddr,
   output wire [8-1:0]                         m_axi_arlen,
   output wire [3-1:0]                         m_axi_arsize,
   output wire [2-1:0]                         m_axi_arburst,
   output wire [2-1:0]                         m_axi_arlock,
   output wire [4-1:0]                         m_axi_arcache,
   output wire [3-1:0]                         m_axi_arprot,
   output wire [4-1:0]                         m_axi_arregion,
   output wire [4-1:0]                         m_axi_arqos,
   output wire                                                   m_axi_arvalid,
   input  wire                                                   m_axi_arready,
   // Master Interface Read Data Ports
   input  wire [C_M_AXI_DATA_WIDTH-1:0]      m_axi_rdata,
   input  wire [2-1:0]                       m_axi_rresp,
   input  wire                               m_axi_rlast,
   input  wire                               m_axi_rvalid,
   output wire                               m_axi_rready
   );

  // Log2 of number of 32bit word on SI-side.
  localparam integer C_S_AXI_BYTES_LOG                = log2(C_S_AXI_DATA_WIDTH/8);
  
  // Log2 of number of 32bit word on MI-side.
  localparam integer C_M_AXI_BYTES_LOG                = log2(C_M_AXI_DATA_WIDTH/8);
  
  // Log2 of Up-Sizing ratio for data.
  localparam integer C_RATIO                          = C_M_AXI_DATA_WIDTH / C_S_AXI_DATA_WIDTH;
  localparam integer C_RATIO_LOG                      = log2(C_RATIO);
  localparam P_BYPASS = 32'h0;
  localparam P_LIGHTWT = 32'h7;
  localparam P_FWD_REV = 32'h1;
  localparam integer P_CONV_LIGHT_WT = 0;
  localparam integer P_AXI4 = 0;
  localparam integer C_FIFO_DEPTH_LOG    = 5;
  localparam  P_SI_LT_MI = (C_S_AXI_ACLK_RATIO < C_M_AXI_ACLK_RATIO);
  localparam integer P_ACLK_RATIO = P_SI_LT_MI ? (C_M_AXI_ACLK_RATIO / C_S_AXI_ACLK_RATIO) : (C_S_AXI_ACLK_RATIO / C_M_AXI_ACLK_RATIO);
   localparam integer P_NO_FIFO = 0;
   localparam integer P_PKTFIFO = 1;
   localparam integer P_PKTFIFO_CLK = 2;
   localparam integer P_DATAFIFO = 3;
   localparam integer P_DATAFIFO_CLK = 4;
   localparam         P_CLK_CONV = ((C_FIFO_MODE == P_PKTFIFO_CLK) || (C_FIFO_MODE == P_DATAFIFO_CLK));
   localparam integer C_M_AXI_AW_REGISTER              = 0;
                       // Simple register AW output.
                       // Range: 0, 1
   localparam integer C_M_AXI_W_REGISTER               = 1;  // Parameter not used; W reg always implemented.
   localparam integer C_M_AXI_AR_REGISTER              = 0;
                       // Simple register AR output.
                       // Range: 0, 1
   localparam integer C_S_AXI_R_REGISTER               = 0;
                       // Simple register R output (SI).
                       // Range: 0, 1
   localparam integer C_M_AXI_R_REGISTER               = 1;
                       // Register slice on R input (MI) side.
                       // 0 = Bypass (not recommended due to combinatorial M_RVALID -> M_RREADY path)
                       // 1 = Fully-registered (needed only when upsizer propagates bursts at 1:1 width ratio)
                       // 7 = Light-weight (safe when upsizer always packs at 1:n width ratio, as in interconnect)
   localparam integer P_RID_QUEUE = ((C_SUPPORTS_ID != 0) && !((C_FIFO_MODE == P_PKTFIFO) || (C_FIFO_MODE == P_PKTFIFO_CLK))) ? 1 : 0;
   
  /////////////////////////////////////////////////////////////////////////////
  // Functions
  /////////////////////////////////////////////////////////////////////////////
  
  // Log2.
  function integer log2
    (
     input integer x
     );
    integer acc;
    begin
      acc=0;
      while ((2**acc) < x)
        acc = acc + 1;
      log2 = acc;
    end
  endfunction
    
  /////////////////////////////////////////////////////////////////////////////
  // Internal signals
  /////////////////////////////////////////////////////////////////////////////
  
  wire aclk;
  wire m_aclk;
  wire sample_cycle;
  wire sample_cycle_early;
  wire sm_aresetn;
  wire s_aresetn_i;
  
  wire [C_S_AXI_ID_WIDTH-1:0]        sr_awid      ;   
  wire [C_AXI_ADDR_WIDTH-1:0]        sr_awaddr    ;   
  wire [8-1:0]                       sr_awlen     ;   
  wire [3-1:0]                       sr_awsize    ;   
  wire [2-1:0]                       sr_awburst   ;   
  wire [2-1:0]                       sr_awlock    ;   
  wire [4-1:0]                       sr_awcache   ;   
  wire [3-1:0]                       sr_awprot    ;   
  wire [4-1:0]                       sr_awregion  ;   
  wire [4-1:0]                       sr_awqos     ;   
  wire                               sr_awvalid   ;   
  wire                               sr_awready   ;   
  wire [C_S_AXI_ID_WIDTH-1:0]        sr_arid      ;    
  wire [C_AXI_ADDR_WIDTH-1:0]        sr_araddr    ;    
  wire [8-1:0]                       sr_arlen     ;    
  wire [3-1:0]                       sr_arsize    ;    
  wire [2-1:0]                       sr_arburst   ;    
  wire [2-1:0]                       sr_arlock    ;    
  wire [4-1:0]                       sr_arcache   ;    
  wire [3-1:0]                       sr_arprot    ;    
  wire [4-1:0]                       sr_arregion  ;    
  wire [4-1:0]                       sr_arqos     ;    
  wire                               sr_arvalid   ;    
  wire                               sr_arready   ;    
  
  wire [C_S_AXI_DATA_WIDTH-1:0]      sr_wdata     ;
  wire [(C_S_AXI_DATA_WIDTH/8)-1:0]  sr_wstrb     ;
  wire                               sr_wlast     ;
  wire                               sr_wvalid    ;
  wire                               sr_wready    ;
  
  wire [C_M_AXI_DATA_WIDTH-1:0]      mr_rdata     ;  
  wire [2-1:0]                       mr_rresp     ;  
  wire                               mr_rlast     ;  
  wire                               mr_rvalid    ;  
  wire                               mr_rready    ;   
  wire                               m_axi_rready_i;
  
  wire [((C_AXI_PROTOCOL==P_AXI4)?8:4)-1:0] s_axi_awlen_i  ;
  wire [((C_AXI_PROTOCOL==P_AXI4)?8:4)-1:0] s_axi_arlen_i  ;
  wire [((C_AXI_PROTOCOL==P_AXI4)?1:2)-1:0] s_axi_awlock_i ;
  wire [((C_AXI_PROTOCOL==P_AXI4)?1:2)-1:0] s_axi_arlock_i ;
  wire [((C_AXI_PROTOCOL==P_AXI4)?8:4)-1:0] s_axi_awlen_ii  ;
  wire [((C_AXI_PROTOCOL==P_AXI4)?8:4)-1:0] s_axi_arlen_ii  ;
  wire [((C_AXI_PROTOCOL==P_AXI4)?1:2)-1:0] s_axi_awlock_ii ;
  wire [((C_AXI_PROTOCOL==P_AXI4)?1:2)-1:0] s_axi_arlock_ii ;
  wire [3:0] s_axi_awregion_ii;
  wire [3:0] s_axi_arregion_ii;
  assign s_axi_awlen_i = (C_AXI_PROTOCOL == P_AXI4) ? s_axi_awlen : s_axi_awlen[3:0];
  assign s_axi_awlock_i = (C_AXI_PROTOCOL == P_AXI4) ? s_axi_awlock[0] : s_axi_awlock;
  assign s_axi_arlen_i = (C_AXI_PROTOCOL == P_AXI4) ? s_axi_arlen : s_axi_arlen[3:0];
  assign s_axi_arlock_i = (C_AXI_PROTOCOL == P_AXI4) ? s_axi_arlock[0] : s_axi_arlock;
  assign sr_awlen = (C_AXI_PROTOCOL == P_AXI4) ? s_axi_awlen_ii: {4'b0, s_axi_awlen_ii};
  assign sr_awlock = (C_AXI_PROTOCOL == P_AXI4) ? {1'b0, s_axi_awlock_ii} : s_axi_awlock_ii;
  assign sr_arlen = (C_AXI_PROTOCOL == P_AXI4) ? s_axi_arlen_ii: {4'b0, s_axi_arlen_ii};
  assign sr_arlock = (C_AXI_PROTOCOL == P_AXI4) ? {1'b0, s_axi_arlock_ii} : s_axi_arlock_ii;
  assign sr_awregion = (C_AXI_PROTOCOL == P_AXI4) ? s_axi_awregion_ii : 4'b0;
  assign sr_arregion = (C_AXI_PROTOCOL == P_AXI4) ? s_axi_arregion_ii : 4'b0;
  
  assign aclk = s_axi_aclk;
  assign sm_aresetn = s_axi_aresetn & m_axi_aresetn;
  
  generate

    if (P_CLK_CONV) begin : gen_clock_conv
      if (C_AXI_IS_ACLK_ASYNC) begin : gen_async_conv
        
        assign m_aclk = m_axi_aclk;
        assign s_aresetn_i = s_axi_aresetn;
        assign sample_cycle_early = 1'b1;
        assign sample_cycle = 1'b1;
        
      end else begin : gen_sync_conv

        wire fast_aclk;
        wire slow_aclk;
        reg s_aresetn_r = 1'b0;
        
        if (P_SI_LT_MI) begin : gen_fastclk_mi
          assign fast_aclk = m_axi_aclk;
          assign slow_aclk = s_axi_aclk;
        end else begin : gen_fastclk_si
          assign fast_aclk = s_axi_aclk;
          assign slow_aclk = m_axi_aclk;
        end
        
        assign m_aclk = m_axi_aclk;
        assign s_aresetn_i = s_aresetn_r;
    
        always @(negedge sm_aresetn, posedge fast_aclk) begin
          if (~sm_aresetn) begin
            s_aresetn_r <= 1'b0;
          end else if (s_axi_aresetn & m_axi_aresetn & sample_cycle_early) begin
            s_aresetn_r <= 1'b1;
          end
        end
        
        // Sample cycle used to determine when to assert a signal on a fast clock
        // to be flopped onto a slow clock.
        axi_clock_converter_v2_1_11_axic_sample_cycle_ratio #(
          .C_RATIO ( P_ACLK_RATIO )
        )
        axic_sample_cycle_inst (
          .SLOW_ACLK          ( slow_aclk               ) ,
          .FAST_ACLK          ( fast_aclk               ) ,
          .SAMPLE_CYCLE_EARLY ( sample_cycle_early ) ,
          .SAMPLE_CYCLE       ( sample_cycle       )
        );
        
      end
        
    end else begin : gen_no_clk_conv
      
      assign m_aclk = s_axi_aclk;
      assign s_aresetn_i = s_axi_aresetn;
      assign sample_cycle_early = 1'b1;
      assign sample_cycle = 1'b1;
      
    end  // gen_clock_conv

    axi_register_slice_v2_1_12_axi_register_slice #
      (
        .C_FAMILY                         (C_FAMILY),
        .C_AXI_PROTOCOL                   (C_AXI_PROTOCOL),
        .C_AXI_ID_WIDTH                   (C_S_AXI_ID_WIDTH),
        .C_AXI_ADDR_WIDTH                 (C_AXI_ADDR_WIDTH),
        .C_AXI_DATA_WIDTH                 (C_S_AXI_DATA_WIDTH),
        .C_AXI_SUPPORTS_USER_SIGNALS      (0),
        .C_REG_CONFIG_AW                  (C_AXI_SUPPORTS_WRITE ? P_LIGHTWT : P_BYPASS),
        .C_REG_CONFIG_AR                  (C_AXI_SUPPORTS_READ ? P_LIGHTWT : P_BYPASS)
      )
      si_register_slice_inst 
      (
        .aresetn                          (s_aresetn_i),
        .aclk                             (aclk),
        .s_axi_awid                       (s_axi_awid     ),
        .s_axi_awaddr                     (s_axi_awaddr   ),
        .s_axi_awlen                      (s_axi_awlen_i    ),
        .s_axi_awsize                     (s_axi_awsize   ),
        .s_axi_awburst                    (s_axi_awburst  ),
        .s_axi_awlock                     (s_axi_awlock_i   ),
        .s_axi_awcache                    (s_axi_awcache  ),
        .s_axi_awprot                     (s_axi_awprot   ),
        .s_axi_awregion                   (s_axi_awregion ),
        .s_axi_awqos                      (s_axi_awqos    ),
        .s_axi_awuser                     (1'b0   ),
        .s_axi_awvalid                    (s_axi_awvalid  ),
        .s_axi_awready                    (s_axi_awready  ),
        .s_axi_wid                        ( {C_S_AXI_ID_WIDTH{1'b0}}),
        .s_axi_wdata                      ( {C_S_AXI_DATA_WIDTH{1'b0}}    ),
        .s_axi_wstrb                      ( {C_S_AXI_DATA_WIDTH/8{1'b0}}  ),
        .s_axi_wlast                      ( 1'b0 ),
        .s_axi_wuser                      ( 1'b0  ),
        .s_axi_wvalid                     ( 1'b0 ),
        .s_axi_wready                     ( ),
        .s_axi_bid                        ( ),
        .s_axi_bresp                      ( ),
        .s_axi_buser                      ( ),
        .s_axi_bvalid                     ( ),
        .s_axi_bready                     ( 1'b0 ),
        .s_axi_arid                       (s_axi_arid     ),
        .s_axi_araddr                     (s_axi_araddr   ),
        .s_axi_arlen                      (s_axi_arlen_i    ),
        .s_axi_arsize                     (s_axi_arsize   ),
        .s_axi_arburst                    (s_axi_arburst  ),
        .s_axi_arlock                     (s_axi_arlock_i   ),
        .s_axi_arcache                    (s_axi_arcache  ),
        .s_axi_arprot                     (s_axi_arprot   ),
        .s_axi_arregion                   (s_axi_arregion ),
        .s_axi_arqos                      (s_axi_arqos    ),
        .s_axi_aruser                     (1'b0   ),
        .s_axi_arvalid                    (s_axi_arvalid  ),
        .s_axi_arready                    (s_axi_arready  ),
        .s_axi_rid                        ( ) ,
        .s_axi_rdata                      ( ) ,
        .s_axi_rresp                      ( ) ,
        .s_axi_rlast                      ( ) ,
        .s_axi_ruser                      ( ) ,
        .s_axi_rvalid                     ( ) ,
        .s_axi_rready                     ( 1'b0 ) ,
        .m_axi_awid                       (sr_awid     ),
        .m_axi_awaddr                     (sr_awaddr   ),
        .m_axi_awlen                      (s_axi_awlen_ii),
        .m_axi_awsize                     (sr_awsize   ),
        .m_axi_awburst                    (sr_awburst  ),
        .m_axi_awlock                     (s_axi_awlock_ii),
        .m_axi_awcache                    (sr_awcache  ),
        .m_axi_awprot                     (sr_awprot   ),
        .m_axi_awregion                   (s_axi_awregion_ii ),
        .m_axi_awqos                      (sr_awqos    ),
        .m_axi_awuser                     (),
        .m_axi_awvalid                    (sr_awvalid  ),
        .m_axi_awready                    (sr_awready  ),
        .m_axi_wid                        () ,
        .m_axi_wdata                      (),
        .m_axi_wstrb                      (),
        .m_axi_wlast                      (),
        .m_axi_wuser                      (),
        .m_axi_wvalid                     (),
        .m_axi_wready                     (1'b0),
        .m_axi_bid                        ( {C_S_AXI_ID_WIDTH{1'b0}} ) ,
        .m_axi_bresp                      ( 2'b0 ) ,
        .m_axi_buser                      ( 1'b0 ) ,
        .m_axi_bvalid                     ( 1'b0 ) ,
        .m_axi_bready                     ( ) ,
        .m_axi_arid                       (sr_arid     ),
        .m_axi_araddr                     (sr_araddr   ),
        .m_axi_arlen                      (s_axi_arlen_ii),
        .m_axi_arsize                     (sr_arsize   ),
        .m_axi_arburst                    (sr_arburst  ),
        .m_axi_arlock                     (s_axi_arlock_ii),
        .m_axi_arcache                    (sr_arcache  ),
        .m_axi_arprot                     (sr_arprot   ),
        .m_axi_arregion                   (s_axi_arregion_ii ),
        .m_axi_arqos                      (sr_arqos    ),
        .m_axi_aruser                     (),
        .m_axi_arvalid                    (sr_arvalid  ),
        .m_axi_arready                    (sr_arready  ),
        .m_axi_rid                        ( {C_S_AXI_ID_WIDTH{1'b0}}),
        .m_axi_rdata                      ( {C_S_AXI_DATA_WIDTH{1'b0}}    ),
        .m_axi_rresp                      ( 2'b00 ),
        .m_axi_rlast                      ( 1'b0  ),
        .m_axi_ruser                      ( 1'b0  ),
        .m_axi_rvalid                     ( 1'b0  ),
        .m_axi_rready                     (  )
      );
  
  /////////////////////////////////////////////////////////////////////////////
  // Handle Write Channels (AW/W/B)
  /////////////////////////////////////////////////////////////////////////////
    if (C_AXI_SUPPORTS_WRITE == 1) begin : USE_WRITE
    
      wire [C_AXI_ADDR_WIDTH-1:0]          m_axi_awaddr_i    ;
      wire [8-1:0]                         m_axi_awlen_i     ;
      wire [3-1:0]                         m_axi_awsize_i    ;
      wire [2-1:0]                         m_axi_awburst_i   ;
      wire [2-1:0]                         m_axi_awlock_i    ;
      wire [4-1:0]                         m_axi_awcache_i   ;
      wire [3-1:0]                         m_axi_awprot_i    ;
      wire [4-1:0]                         m_axi_awregion_i  ;
      wire [4-1:0]                         m_axi_awqos_i     ;
      wire                                 m_axi_awvalid_i   ;
      wire                                 m_axi_awready_i   ;
      
      wire                                 s_axi_bvalid_i   ;
      wire [2-1:0]                         s_axi_bresp_i   ;
      
      wire [C_AXI_ADDR_WIDTH-1:0]       wr_cmd_si_addr;
      wire [8-1:0]                      wr_cmd_si_len;
      wire [3-1:0]                      wr_cmd_si_size;
      wire [2-1:0]                      wr_cmd_si_burst;
  
      // Write Channel Signals for Commands Queue Interface.
      wire                              wr_cmd_valid;
      wire                              wr_cmd_fix;
      wire                              wr_cmd_modified;
      wire                              wr_cmd_complete_wrap;
      wire                              wr_cmd_packed_wrap;
      wire [C_M_AXI_BYTES_LOG-1:0]      wr_cmd_first_word;
      wire [C_M_AXI_BYTES_LOG-1:0]      wr_cmd_next_word;
      wire [C_M_AXI_BYTES_LOG-1:0]      wr_cmd_last_word;
      wire [C_M_AXI_BYTES_LOG-1:0]      wr_cmd_offset;
      wire [C_M_AXI_BYTES_LOG-1:0]      wr_cmd_mask;
      wire [C_S_AXI_BYTES_LOG:0]        wr_cmd_step;
      wire [8-1:0]                      wr_cmd_length;
      wire                              wr_cmd_ready;
      wire                              wr_cmd_id_ready;
      wire [C_S_AXI_ID_WIDTH-1:0]       wr_cmd_id;

      // Write Address Channel.
      axi_dwidth_converter_v2_1_12_a_upsizer #
      (
       .C_FAMILY                    ("rtl"),
       .C_AXI_PROTOCOL              (C_AXI_PROTOCOL),
       .C_AXI_ID_WIDTH              (C_S_AXI_ID_WIDTH),
       .C_SUPPORTS_ID               (C_SUPPORTS_ID),
       .C_AXI_ADDR_WIDTH            (C_AXI_ADDR_WIDTH),
       .C_S_AXI_DATA_WIDTH          (C_S_AXI_DATA_WIDTH),
       .C_M_AXI_DATA_WIDTH          (C_M_AXI_DATA_WIDTH),
       .C_M_AXI_REGISTER            (C_M_AXI_AW_REGISTER),
       .C_AXI_CHANNEL               (0),
       .C_PACKING_LEVEL             (C_PACKING_LEVEL),
       .C_FIFO_MODE                 (C_FIFO_MODE),
       .C_ID_QUEUE                  (C_SUPPORTS_ID),
       .C_S_AXI_BYTES_LOG           (C_S_AXI_BYTES_LOG),
       .C_M_AXI_BYTES_LOG           (C_M_AXI_BYTES_LOG)
        ) write_addr_inst
       (
        // Global Signals
        .ARESET                     (~s_aresetn_i),
        .ACLK                       (aclk),
    
        // Command Interface
        .cmd_valid                  (wr_cmd_valid),
        .cmd_fix                    (wr_cmd_fix),
        .cmd_modified               (wr_cmd_modified),
        .cmd_complete_wrap          (wr_cmd_complete_wrap),
        .cmd_packed_wrap            (wr_cmd_packed_wrap),
        .cmd_first_word             (wr_cmd_first_word),
        .cmd_next_word              (wr_cmd_next_word),
        .cmd_last_word              (wr_cmd_last_word),
        .cmd_offset                 (wr_cmd_offset),
        .cmd_mask                   (wr_cmd_mask),
        .cmd_step                   (wr_cmd_step),
        .cmd_length                 (wr_cmd_length),
        .cmd_ready                  (wr_cmd_ready),
        .cmd_id                     (wr_cmd_id),
        .cmd_id_ready               (wr_cmd_id_ready),
        .cmd_si_addr                (wr_cmd_si_addr ),
        .cmd_si_id                  (),
        .cmd_si_len                 (wr_cmd_si_len  ),
        .cmd_si_size                (wr_cmd_si_size ),
        .cmd_si_burst               (wr_cmd_si_burst),
       
        // Slave Interface Write Address Ports
        .S_AXI_AID                  (sr_awid),
        .S_AXI_AADDR                (sr_awaddr),
        .S_AXI_ALEN                 (sr_awlen),
        .S_AXI_ASIZE                (sr_awsize),
        .S_AXI_ABURST               (sr_awburst),
        .S_AXI_ALOCK                (sr_awlock),
        .S_AXI_ACACHE               (sr_awcache),
        .S_AXI_APROT                (sr_awprot),
        .S_AXI_AREGION              (sr_awregion),
        .S_AXI_AQOS                 (sr_awqos),
        .S_AXI_AVALID               (sr_awvalid),
        .S_AXI_AREADY               (sr_awready),
        
        // Master Interface Write Address Port
        .M_AXI_AADDR                (m_axi_awaddr_i    ),
        .M_AXI_ALEN                 (m_axi_awlen_i     ),
        .M_AXI_ASIZE                (m_axi_awsize_i    ),
        .M_AXI_ABURST               (m_axi_awburst_i   ),
        .M_AXI_ALOCK                (m_axi_awlock_i    ),
        .M_AXI_ACACHE               (m_axi_awcache_i   ),
        .M_AXI_APROT                (m_axi_awprot_i    ),
        .M_AXI_AREGION              (m_axi_awregion_i  ),
        .M_AXI_AQOS                 (m_axi_awqos_i     ),
        .M_AXI_AVALID               (m_axi_awvalid_i   ),
        .M_AXI_AREADY               (m_axi_awready_i   )
       );
       
      if ((C_FIFO_MODE == P_PKTFIFO) || (C_FIFO_MODE == P_PKTFIFO_CLK)) begin : gen_pktfifo_w_upsizer
        // Packet FIFO Write Data channel.
        axi_dwidth_converter_v2_1_12_w_upsizer_pktfifo #
        (
         .C_FAMILY                    (C_FAMILY),
         .C_S_AXI_DATA_WIDTH          (C_S_AXI_DATA_WIDTH),
         .C_M_AXI_DATA_WIDTH          (C_M_AXI_DATA_WIDTH),
         .C_AXI_ADDR_WIDTH            (C_AXI_ADDR_WIDTH),
         .C_S_AXI_BYTES_LOG           (C_S_AXI_BYTES_LOG),
         .C_M_AXI_BYTES_LOG           (C_M_AXI_BYTES_LOG),
         .C_RATIO                     (C_RATIO),
         .C_RATIO_LOG                 (C_RATIO_LOG),
         .C_CLK_CONV                  (P_CLK_CONV),
         .C_S_AXI_ACLK_RATIO   (C_S_AXI_ACLK_RATIO),
         .C_M_AXI_ACLK_RATIO   (C_M_AXI_ACLK_RATIO),
         .C_AXI_IS_ACLK_ASYNC   (C_AXI_IS_ACLK_ASYNC),
         .C_SYNCHRONIZER_STAGE (C_SYNCHRONIZER_STAGE)
          ) pktfifo_write_data_inst
         (
          .S_AXI_ARESETN              ( s_axi_aresetn        ) ,
          .S_AXI_ACLK                 ( s_axi_aclk          ) ,
          .M_AXI_ARESETN              ( m_axi_aresetn        ) ,
          .M_AXI_ACLK                 ( m_axi_aclk          ) ,

          // Command Interface
          .cmd_si_addr                 (wr_cmd_si_addr ),
          .cmd_si_len                  (wr_cmd_si_len  ),
          .cmd_si_size                 (wr_cmd_si_size ),
          .cmd_si_burst                (wr_cmd_si_burst),
          .cmd_ready                   (wr_cmd_ready),

          // Slave Interface Write Address Ports
          .S_AXI_AWADDR                (m_axi_awaddr_i    ),  
          .S_AXI_AWLEN                 (m_axi_awlen_i     ),  
          .S_AXI_AWSIZE                (m_axi_awsize_i    ),  
          .S_AXI_AWBURST               (m_axi_awburst_i   ),  
          .S_AXI_AWLOCK                (m_axi_awlock_i    ),  
          .S_AXI_AWCACHE               (m_axi_awcache_i   ),  
          .S_AXI_AWPROT                (m_axi_awprot_i    ),  
          .S_AXI_AWREGION              (m_axi_awregion_i  ),  
          .S_AXI_AWQOS                 (m_axi_awqos_i     ),  
          .S_AXI_AWVALID               (m_axi_awvalid_i   ),  
          .S_AXI_AWREADY               (m_axi_awready_i   ),   
          
          // Master Interface Write Address Port
          .M_AXI_AWADDR                (m_axi_awaddr),
          .M_AXI_AWLEN                 (m_axi_awlen),
          .M_AXI_AWSIZE                (m_axi_awsize),
          .M_AXI_AWBURST               (m_axi_awburst),
          .M_AXI_AWLOCK                (m_axi_awlock),
          .M_AXI_AWCACHE               (m_axi_awcache),
          .M_AXI_AWPROT                (m_axi_awprot),
          .M_AXI_AWREGION              (m_axi_awregion),
          .M_AXI_AWQOS                 (m_axi_awqos),
          .M_AXI_AWVALID               (m_axi_awvalid),
          .M_AXI_AWREADY               (m_axi_awready),
         
          // Slave Interface Write Data Ports
          .S_AXI_WDATA                (s_axi_wdata),
          .S_AXI_WSTRB                (s_axi_wstrb),
          .S_AXI_WLAST                (s_axi_wlast),
          .S_AXI_WVALID               (s_axi_wvalid),
          .S_AXI_WREADY               (s_axi_wready),
          
          // Master Interface Write Data Ports
          .M_AXI_WDATA                (m_axi_wdata),
          .M_AXI_WSTRB                (m_axi_wstrb),
          .M_AXI_WLAST                (m_axi_wlast),
          .M_AXI_WVALID               (m_axi_wvalid),
          .M_AXI_WREADY               (m_axi_wready),
          
          .SAMPLE_CYCLE               (sample_cycle),
          .SAMPLE_CYCLE_EARLY         (sample_cycle_early)
         );
        
      end else begin : gen_non_fifo_w_upsizer
        // Write Data channel.
        axi_dwidth_converter_v2_1_12_w_upsizer #
        (
         .C_FAMILY                    ("rtl"),
         .C_S_AXI_DATA_WIDTH          (C_S_AXI_DATA_WIDTH),
         .C_M_AXI_DATA_WIDTH          (C_M_AXI_DATA_WIDTH),
         .C_M_AXI_REGISTER            (1),
         .C_PACKING_LEVEL             (C_PACKING_LEVEL),
         .C_S_AXI_BYTES_LOG           (C_S_AXI_BYTES_LOG),
         .C_M_AXI_BYTES_LOG           (C_M_AXI_BYTES_LOG),
         .C_RATIO                     (C_RATIO),
         .C_RATIO_LOG                 (C_RATIO_LOG)
          ) write_data_inst
         (
          // Global Signals
          .ARESET                     (~s_aresetn_i),
          .ACLK                       (aclk),
      
          // Command Interface
          .cmd_valid                  (wr_cmd_valid),
          .cmd_fix                    (wr_cmd_fix),
          .cmd_modified               (wr_cmd_modified),
          .cmd_complete_wrap          (wr_cmd_complete_wrap),
          .cmd_packed_wrap            (wr_cmd_packed_wrap),
          .cmd_first_word             (wr_cmd_first_word),
          .cmd_next_word              (wr_cmd_next_word),
          .cmd_last_word              (wr_cmd_last_word),
          .cmd_offset                 (wr_cmd_offset),
          .cmd_mask                   (wr_cmd_mask),
          .cmd_step                   (wr_cmd_step),
          .cmd_length                 (wr_cmd_length),
          .cmd_ready                  (wr_cmd_ready),
         
          // Slave Interface Write Data Ports
          .S_AXI_WDATA                (s_axi_wdata),
          .S_AXI_WSTRB                (s_axi_wstrb),
          .S_AXI_WLAST                (s_axi_wlast),
          .S_AXI_WVALID               (s_axi_wvalid),
          .S_AXI_WREADY               (s_axi_wready),
          
          // Master Interface Write Data Ports
          .M_AXI_WDATA                (m_axi_wdata),
          .M_AXI_WSTRB                (m_axi_wstrb),
          .M_AXI_WLAST                (m_axi_wlast),
          .M_AXI_WVALID               (m_axi_wvalid),
          .M_AXI_WREADY               (m_axi_wready)
         );
        
        assign m_axi_awaddr   = m_axi_awaddr_i   ;
        assign m_axi_awlen    = m_axi_awlen_i    ;
        assign m_axi_awsize   = m_axi_awsize_i   ;
        assign m_axi_awburst  = m_axi_awburst_i  ;
        assign m_axi_awlock   = m_axi_awlock_i   ;
        assign m_axi_awcache  = m_axi_awcache_i  ;
        assign m_axi_awprot   = m_axi_awprot_i   ;
        assign m_axi_awregion = m_axi_awregion_i ;
        assign m_axi_awqos    = m_axi_awqos_i    ;
        assign m_axi_awvalid  = m_axi_awvalid_i  ;
        assign m_axi_awready_i  = m_axi_awready  ;
        
      end // gen_w_upsizer
      
      // Write Response channel.
      assign wr_cmd_id_ready = s_axi_bvalid_i & s_axi_bready;
      assign s_axi_bid     = wr_cmd_id;
      assign s_axi_bresp   = s_axi_bresp_i;
      assign s_axi_bvalid  = s_axi_bvalid_i;
      
      if (P_CLK_CONV) begin : gen_b_clk_conv
        if (C_AXI_IS_ACLK_ASYNC == 0) begin : gen_b_sync_conv

          axi_clock_converter_v2_1_11_axic_sync_clock_converter #(
            .C_FAMILY         ( C_FAMILY ) ,
            .C_PAYLOAD_WIDTH ( 2 ) ,
            .C_M_ACLK_RATIO   ( P_SI_LT_MI ? 1 : P_ACLK_RATIO ) ,
            .C_S_ACLK_RATIO   ( P_SI_LT_MI ? P_ACLK_RATIO : 1 ) ,
            .C_MODE(P_CONV_LIGHT_WT)
          )
          b_sync_clock_converter (
            .SAMPLE_CYCLE (sample_cycle),
            .SAMPLE_CYCLE_EARLY (sample_cycle_early),
            .S_ACLK     ( m_axi_aclk     ) ,
            .S_ARESETN  ( m_axi_aresetn ) ,
            .S_PAYLOAD ( m_axi_bresp ) ,
            .S_VALID   ( m_axi_bvalid   ) ,
            .S_READY   ( m_axi_bready   ) ,
            .M_ACLK     ( s_axi_aclk     ) ,
            .M_ARESETN  ( s_axi_aresetn ) ,
            .M_PAYLOAD ( s_axi_bresp_i ) ,
            .M_VALID   ( s_axi_bvalid_i   ) ,
            .M_READY   ( s_axi_bready   )
          );
        
        end else begin : gen_b_async_conv
          
          fifo_generator_v13_1_4 #(
            .C_COMMON_CLOCK(0),
            .C_SYNCHRONIZER_STAGE(C_SYNCHRONIZER_STAGE),
            .C_INTERFACE_TYPE(2),
            .C_AXI_TYPE(1),
            .C_HAS_AXI_ID(1),
            .C_AXI_LEN_WIDTH(8),
            .C_AXI_LOCK_WIDTH(2),
            .C_DIN_WIDTH_WACH(63),
            .C_DIN_WIDTH_WDCH(38),
            .C_DIN_WIDTH_WRCH(3),
            .C_DIN_WIDTH_RACH(63),
            .C_DIN_WIDTH_RDCH(36),
            .C_COUNT_TYPE(0),
            .C_DATA_COUNT_WIDTH(10),
            .C_DEFAULT_VALUE("BlankString"),
            .C_DIN_WIDTH(18),
            .C_DOUT_RST_VAL("0"),
            .C_DOUT_WIDTH(18),
            .C_ENABLE_RLOCS(0),
            .C_FAMILY(C_FAMILY),
            .C_FULL_FLAGS_RST_VAL(1),
            .C_HAS_ALMOST_EMPTY(0),
            .C_HAS_ALMOST_FULL(0),
            .C_HAS_BACKUP(0),
            .C_HAS_DATA_COUNT(0),
            .C_HAS_INT_CLK(0),
            .C_HAS_MEMINIT_FILE(0),
            .C_HAS_OVERFLOW(0),
            .C_HAS_RD_DATA_COUNT(0),
            .C_HAS_RD_RST(0),
            .C_HAS_RST(1),
            .C_HAS_SRST(0),
            .C_HAS_UNDERFLOW(0),
            .C_HAS_VALID(0),
            .C_HAS_WR_ACK(0),
            .C_HAS_WR_DATA_COUNT(0),
            .C_HAS_WR_RST(0),
            .C_IMPLEMENTATION_TYPE(0),
            .C_INIT_WR_PNTR_VAL(0),
            .C_MEMORY_TYPE(1),
            .C_MIF_FILE_NAME("BlankString"),
            .C_OPTIMIZATION_MODE(0),
            .C_OVERFLOW_LOW(0),
            .C_PRELOAD_LATENCY(1),
            .C_PRELOAD_REGS(0),
            .C_PRIM_FIFO_TYPE("4kx4"),
            .C_PROG_EMPTY_THRESH_ASSERT_VAL(2),
            .C_PROG_EMPTY_THRESH_NEGATE_VAL(3),
            .C_PROG_EMPTY_TYPE(0),
            .C_PROG_FULL_THRESH_ASSERT_VAL(1022),
            .C_PROG_FULL_THRESH_NEGATE_VAL(1021),
            .C_PROG_FULL_TYPE(0),
            .C_RD_DATA_COUNT_WIDTH(10),
            .C_RD_DEPTH(1024),
            .C_RD_FREQ(1),
            .C_RD_PNTR_WIDTH(10),
            .C_UNDERFLOW_LOW(0),
            .C_USE_DOUT_RST(1),
            .C_USE_ECC(0),
            .C_USE_EMBEDDED_REG(0),
            .C_USE_FIFO16_FLAGS(0),
            .C_USE_FWFT_DATA_COUNT(0),
            .C_VALID_LOW(0),
            .C_WR_ACK_LOW(0),
            .C_WR_DATA_COUNT_WIDTH(10),
            .C_WR_DEPTH(1024),
            .C_WR_FREQ(1),
            .C_WR_PNTR_WIDTH(10),
            .C_WR_RESPONSE_LATENCY(1),
            .C_MSGON_VAL(1),
            .C_ENABLE_RST_SYNC(1),
            .C_ERROR_INJECTION_TYPE(0),
            .C_HAS_AXI_WR_CHANNEL(1),
            .C_HAS_AXI_RD_CHANNEL(0),
            .C_HAS_SLAVE_CE(0),
            .C_HAS_MASTER_CE(0),
            .C_ADD_NGC_CONSTRAINT(0),
            .C_USE_COMMON_OVERFLOW(0),
            .C_USE_COMMON_UNDERFLOW(0),
            .C_USE_DEFAULT_SETTINGS(0),
            .C_AXI_ID_WIDTH(1),
            .C_AXI_ADDR_WIDTH(32),
            .C_AXI_DATA_WIDTH(32),
            .C_HAS_AXI_AWUSER(0),
            .C_HAS_AXI_WUSER(0),
            .C_HAS_AXI_BUSER(0),
            .C_HAS_AXI_ARUSER(0),
            .C_HAS_AXI_RUSER(0),
            .C_AXI_ARUSER_WIDTH(1),
            .C_AXI_AWUSER_WIDTH(1),
            .C_AXI_WUSER_WIDTH(1),
            .C_AXI_BUSER_WIDTH(1),
            .C_AXI_RUSER_WIDTH(1),
            .C_HAS_AXIS_TDATA(0),
            .C_HAS_AXIS_TID(0),
            .C_HAS_AXIS_TDEST(0),
            .C_HAS_AXIS_TUSER(0),
            .C_HAS_AXIS_TREADY(1),
            .C_HAS_AXIS_TLAST(0),
            .C_HAS_AXIS_TSTRB(0),
            .C_HAS_AXIS_TKEEP(0),
            .C_AXIS_TDATA_WIDTH(64),
            .C_AXIS_TID_WIDTH(8),
            .C_AXIS_TDEST_WIDTH(4),
            .C_AXIS_TUSER_WIDTH(4),
            .C_AXIS_TSTRB_WIDTH(4),
            .C_AXIS_TKEEP_WIDTH(4),
            .C_WACH_TYPE(2),
            .C_WDCH_TYPE(2),
            .C_WRCH_TYPE(0),
            .C_RACH_TYPE(0),
            .C_RDCH_TYPE(0),
            .C_AXIS_TYPE(0),
            .C_IMPLEMENTATION_TYPE_WACH(12),
            .C_IMPLEMENTATION_TYPE_WDCH(11),
            .C_IMPLEMENTATION_TYPE_WRCH(12),
            .C_IMPLEMENTATION_TYPE_RACH(12),
            .C_IMPLEMENTATION_TYPE_RDCH(11),
            .C_IMPLEMENTATION_TYPE_AXIS(11),
            .C_APPLICATION_TYPE_WACH(0),
            .C_APPLICATION_TYPE_WDCH(0),
            .C_APPLICATION_TYPE_WRCH(0),
            .C_APPLICATION_TYPE_RACH(0),
            .C_APPLICATION_TYPE_RDCH(0),
            .C_APPLICATION_TYPE_AXIS(0),
            .C_USE_ECC_WACH(0),
            .C_USE_ECC_WDCH(0),
            .C_USE_ECC_WRCH(0),
            .C_USE_ECC_RACH(0),
            .C_USE_ECC_RDCH(0),
            .C_USE_ECC_AXIS(0),
            .C_ERROR_INJECTION_TYPE_WACH(0),
            .C_ERROR_INJECTION_TYPE_WDCH(0),
            .C_ERROR_INJECTION_TYPE_WRCH(0),
            .C_ERROR_INJECTION_TYPE_RACH(0),
            .C_ERROR_INJECTION_TYPE_RDCH(0),
            .C_ERROR_INJECTION_TYPE_AXIS(0),
            .C_DIN_WIDTH_AXIS(1),
            .C_WR_DEPTH_WACH(16),
            .C_WR_DEPTH_WDCH(1024),
            .C_WR_DEPTH_WRCH(32),
            .C_WR_DEPTH_RACH(16),
            .C_WR_DEPTH_RDCH(1024),
            .C_WR_DEPTH_AXIS(1024),
            .C_WR_PNTR_WIDTH_WACH(4),
            .C_WR_PNTR_WIDTH_WDCH(10),
            .C_WR_PNTR_WIDTH_WRCH(5),
            .C_WR_PNTR_WIDTH_RACH(4),
            .C_WR_PNTR_WIDTH_RDCH(10),
            .C_WR_PNTR_WIDTH_AXIS(10),
            .C_HAS_DATA_COUNTS_WACH(0),
            .C_HAS_DATA_COUNTS_WDCH(0),
            .C_HAS_DATA_COUNTS_WRCH(0),
            .C_HAS_DATA_COUNTS_RACH(0),
            .C_HAS_DATA_COUNTS_RDCH(0),
            .C_HAS_DATA_COUNTS_AXIS(0),
            .C_HAS_PROG_FLAGS_WACH(0),
            .C_HAS_PROG_FLAGS_WDCH(0),
            .C_HAS_PROG_FLAGS_WRCH(0),
            .C_HAS_PROG_FLAGS_RACH(0),
            .C_HAS_PROG_FLAGS_RDCH(0),
            .C_HAS_PROG_FLAGS_AXIS(0),
            .C_PROG_FULL_TYPE_WACH(0),
            .C_PROG_FULL_TYPE_WDCH(0),
            .C_PROG_FULL_TYPE_WRCH(0),
            .C_PROG_FULL_TYPE_RACH(0),
            .C_PROG_FULL_TYPE_RDCH(0),
            .C_PROG_FULL_TYPE_AXIS(0),
            .C_PROG_FULL_THRESH_ASSERT_VAL_WACH(15),
            .C_PROG_FULL_THRESH_ASSERT_VAL_WDCH(1023),
            .C_PROG_FULL_THRESH_ASSERT_VAL_WRCH(31),
            .C_PROG_FULL_THRESH_ASSERT_VAL_RACH(15),
            .C_PROG_FULL_THRESH_ASSERT_VAL_RDCH(1023),
            .C_PROG_FULL_THRESH_ASSERT_VAL_AXIS(1023),
            .C_PROG_EMPTY_TYPE_WACH(0),
            .C_PROG_EMPTY_TYPE_WDCH(0),
            .C_PROG_EMPTY_TYPE_WRCH(0),
            .C_PROG_EMPTY_TYPE_RACH(0),
            .C_PROG_EMPTY_TYPE_RDCH(0),
            .C_PROG_EMPTY_TYPE_AXIS(0),
            .C_PROG_EMPTY_THRESH_ASSERT_VAL_WACH(13),
            .C_PROG_EMPTY_THRESH_ASSERT_VAL_WDCH(1021),
            .C_PROG_EMPTY_THRESH_ASSERT_VAL_WRCH(29),
            .C_PROG_EMPTY_THRESH_ASSERT_VAL_RACH(13),
            .C_PROG_EMPTY_THRESH_ASSERT_VAL_RDCH(1021),
            .C_PROG_EMPTY_THRESH_ASSERT_VAL_AXIS(1021),
            .C_REG_SLICE_MODE_WACH(0),
            .C_REG_SLICE_MODE_WDCH(0),
            .C_REG_SLICE_MODE_WRCH(0),
            .C_REG_SLICE_MODE_RACH(0),
            .C_REG_SLICE_MODE_RDCH(0),
            .C_REG_SLICE_MODE_AXIS(0)
          ) dw_fifogen_b_async (
            .m_aclk(m_axi_aclk),
            .s_aclk(s_axi_aclk),
            .s_aresetn(sm_aresetn),
            .s_axi_awid(1'b0),
            .s_axi_awaddr(32'b0),
            .s_axi_awlen(8'b0),
            .s_axi_awsize(3'b0),
            .s_axi_awburst(2'b0),
            .s_axi_awlock(2'b0),
            .s_axi_awcache(4'b0),
            .s_axi_awprot(3'b0),
            .s_axi_awqos(4'b0),
            .s_axi_awregion(4'b0),
            .s_axi_awuser(1'b0),
            .s_axi_awvalid(1'b0),
            .s_axi_awready(),
            .s_axi_wid(1'b0),
            .s_axi_wdata(32'b0),
            .s_axi_wstrb(4'b0),
            .s_axi_wlast(1'b0),
            .s_axi_wuser(1'b0),
            .s_axi_wvalid(1'b0),
            .s_axi_wready(),
            .s_axi_bid(),
            .s_axi_bresp(s_axi_bresp_i),
            .s_axi_buser(),
            .s_axi_bvalid(s_axi_bvalid_i),
            .s_axi_bready(s_axi_bready),
            .m_axi_awid(),
            .m_axi_awaddr(),
            .m_axi_awlen(),
            .m_axi_awsize(),
            .m_axi_awburst(),
            .m_axi_awlock(),
            .m_axi_awcache(),
            .m_axi_awprot(),
            .m_axi_awqos(),
            .m_axi_awregion(),
            .m_axi_awuser(),
            .m_axi_awvalid(),
            .m_axi_awready(1'b0),
            .m_axi_wid(),
            .m_axi_wdata(),
            .m_axi_wstrb(),
            .m_axi_wlast(),
            .m_axi_wuser(),
            .m_axi_wvalid(),
            .m_axi_wready(1'b0),
            .m_axi_bid(1'b0),
            .m_axi_bresp(m_axi_bresp),
            .m_axi_buser(1'b0),
            .m_axi_bvalid(m_axi_bvalid),
            .m_axi_bready(m_axi_bready),
            .s_axi_arid(1'b0),
            .s_axi_araddr(32'b0),
            .s_axi_arlen(8'b0),
            .s_axi_arsize(3'b0),
            .s_axi_arburst(2'b0),
            .s_axi_arlock(2'b0),
            .s_axi_arcache(4'b0),
            .s_axi_arprot(3'b0),
            .s_axi_arqos(4'b0),
            .s_axi_arregion(4'b0),
            .s_axi_aruser(1'b0),
            .s_axi_arvalid(1'b0),
            .s_axi_arready(),
            .s_axi_rid(),
            .s_axi_rdata(),
            .s_axi_rresp(),
            .s_axi_rlast(),
            .s_axi_ruser(),
            .s_axi_rvalid(),
            .s_axi_rready(1'b0),
            .m_axi_arid(),
            .m_axi_araddr(),
            .m_axi_arlen(),
            .m_axi_arsize(),
            .m_axi_arburst(),
            .m_axi_arlock(),
            .m_axi_arcache(),
            .m_axi_arprot(),
            .m_axi_arqos(),
            .m_axi_arregion(),
            .m_axi_aruser(),
            .m_axi_arvalid(),
            .m_axi_arready(1'b0),
            .m_axi_rid(1'b0),
            .m_axi_rdata(32'b0),
            .m_axi_rresp(2'b0),
            .m_axi_rlast(1'b0),
            .m_axi_ruser(1'b0),
            .m_axi_rvalid(1'b0),
            .m_axi_rready(),
            .m_aclk_en(1'b0),
            .s_aclk_en(1'b0),
            .backup(1'b0),
            .backup_marker(1'b0),
            .clk(1'b0),
            .rst(1'b0),
            .srst(1'b0),
            .wr_clk(1'b0),
            .wr_rst(1'b0),
            .rd_clk(1'b0),
            .rd_rst(1'b0),
            .din(18'b0),
            .wr_en(1'b0),
            .rd_en(1'b0),
            .prog_empty_thresh(10'b0),
            .prog_empty_thresh_assert(10'b0),
            .prog_empty_thresh_negate(10'b0),
            .prog_full_thresh(10'b0),
            .prog_full_thresh_assert(10'b0),
            .prog_full_thresh_negate(10'b0),
            .int_clk(1'b0),
            .injectdbiterr(1'b0),
            .injectsbiterr(1'b0),
            .dout(),
            .full(),
            .almost_full(),
            .wr_ack(),
            .overflow(),
            .empty(),
            .almost_empty(),
            .valid(),
            .underflow(),
            .data_count(),
            .rd_data_count(),
            .wr_data_count(),
            .prog_full(),
            .prog_empty(),
            .sbiterr(),
            .dbiterr(),
            .s_axis_tvalid(1'b0),
            .s_axis_tready(),
            .s_axis_tdata(64'b0),
            .s_axis_tstrb(4'b0),
            .s_axis_tkeep(4'b0),
            .s_axis_tlast(1'b0),
            .s_axis_tid(8'b0),
            .s_axis_tdest(4'b0),
            .s_axis_tuser(4'b0),
            .m_axis_tvalid(),
            .m_axis_tready(1'b0),
            .m_axis_tdata(),
            .m_axis_tstrb(),
            .m_axis_tkeep(),
            .m_axis_tlast(),
            .m_axis_tid(),
            .m_axis_tdest(),
            .m_axis_tuser(),
            .axi_aw_injectsbiterr(1'b0),
            .axi_aw_injectdbiterr(1'b0),
            .axi_aw_prog_full_thresh(4'b0),
            .axi_aw_prog_empty_thresh(4'b0),
            .axi_aw_data_count(),
            .axi_aw_wr_data_count(),
            .axi_aw_rd_data_count(),
            .axi_aw_sbiterr(),
            .axi_aw_dbiterr(),
            .axi_aw_overflow(),
            .axi_aw_underflow(),
            .axi_aw_prog_full(),
            .axi_aw_prog_empty(),
            .axi_w_injectsbiterr(1'b0),
            .axi_w_injectdbiterr(1'b0),
            .axi_w_prog_full_thresh(10'b0),
            .axi_w_prog_empty_thresh(10'b0),
            .axi_w_data_count(),
            .axi_w_wr_data_count(),
            .axi_w_rd_data_count(),
            .axi_w_sbiterr(),
            .axi_w_dbiterr(),
            .axi_w_overflow(),
            .axi_w_underflow(),
            .axi_b_injectsbiterr(1'b0),
            .axi_w_prog_full(),
            .axi_w_prog_empty(),
            .axi_b_injectdbiterr(1'b0),
            .axi_b_prog_full_thresh(5'b0),
            .axi_b_prog_empty_thresh(5'b0),
            .axi_b_data_count(),
            .axi_b_wr_data_count(),
            .axi_b_rd_data_count(),
            .axi_b_sbiterr(),
            .axi_b_dbiterr(),
            .axi_b_overflow(),
            .axi_b_underflow(),
            .axi_ar_injectsbiterr(1'b0),
            .axi_b_prog_full(),
            .axi_b_prog_empty(),
            .axi_ar_injectdbiterr(1'b0),
            .axi_ar_prog_full_thresh(4'b0),
            .axi_ar_prog_empty_thresh(4'b0),
            .axi_ar_data_count(),
            .axi_ar_wr_data_count(),
            .axi_ar_rd_data_count(),
            .axi_ar_sbiterr(),
            .axi_ar_dbiterr(),
            .axi_ar_overflow(),
            .axi_ar_underflow(),
            .axi_ar_prog_full(),
            .axi_ar_prog_empty(),
            .axi_r_injectsbiterr(1'b0),
            .axi_r_injectdbiterr(1'b0),
            .axi_r_prog_full_thresh(10'b0),
            .axi_r_prog_empty_thresh(10'b0),
            .axi_r_data_count(),
            .axi_r_wr_data_count(),
            .axi_r_rd_data_count(),
            .axi_r_sbiterr(),
            .axi_r_dbiterr(),
            .axi_r_overflow(),
            .axi_r_underflow(),
            .axis_injectsbiterr(1'b0),
            .axi_r_prog_full(),
            .axi_r_prog_empty(),
            .axis_injectdbiterr(1'b0),
            .axis_prog_full_thresh(10'b0),
            .axis_prog_empty_thresh(10'b0),
            .axis_data_count(),
            .axis_wr_data_count(),
            .axis_rd_data_count(),
            .axis_sbiterr(),
            .axis_dbiterr(),
            .axis_overflow(),
            .axis_underflow(),
            .axis_prog_full(),
            .axis_prog_empty(),
            .wr_rst_busy(),
            .rd_rst_busy(),
            .sleep(1'b0)
          );
          
        end
          
      end else begin : gen_b_passthru
        assign m_axi_bready  = s_axi_bready;
        assign s_axi_bresp_i = m_axi_bresp;
        assign s_axi_bvalid_i = m_axi_bvalid;
      end  // gen_b
    
    end else begin : NO_WRITE
      assign sr_awready = 1'b0;
      assign s_axi_wready  = 1'b0;
      assign s_axi_bid     = {C_S_AXI_ID_WIDTH{1'b0}};
      assign s_axi_bresp   = 2'b0;
      assign s_axi_bvalid  = 1'b0;
      
      assign m_axi_awaddr  = {C_AXI_ADDR_WIDTH{1'b0}};
      assign m_axi_awlen   = 8'b0;
      assign m_axi_awsize  = 3'b0;
      assign m_axi_awburst = 2'b0;
      assign m_axi_awlock  = 2'b0;
      assign m_axi_awcache = 4'b0;
      assign m_axi_awprot  = 3'b0;
      assign m_axi_awregion =  4'b0;
      assign m_axi_awqos   = 4'b0;
      assign m_axi_awvalid = 1'b0;
      assign m_axi_wdata   = {C_M_AXI_DATA_WIDTH{1'b0}};
      assign m_axi_wstrb   = {C_M_AXI_DATA_WIDTH/8{1'b0}};
      assign m_axi_wlast   = 1'b0;
      assign m_axi_wvalid  = 1'b0;
      assign m_axi_bready  = 1'b0;
      
    end
  endgenerate
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Handle Read Channels (AR/R)
  /////////////////////////////////////////////////////////////////////////////
  generate
    if (C_AXI_SUPPORTS_READ == 1) begin : USE_READ
      wire [C_AXI_ADDR_WIDTH-1:0]          m_axi_araddr_i    ;
      wire [8-1:0]                         m_axi_arlen_i     ;
      wire [3-1:0]                         m_axi_arsize_i    ;
      wire [2-1:0]                         m_axi_arburst_i   ;
      wire [2-1:0]                         m_axi_arlock_i    ;
      wire [4-1:0]                         m_axi_arcache_i   ;
      wire [3-1:0]                         m_axi_arprot_i    ;
      wire [4-1:0]                         m_axi_arregion_i  ;
      wire [4-1:0]                         m_axi_arqos_i     ;
      wire                                 m_axi_arvalid_i   ;
      wire                                 m_axi_arready_i   ;
    
      // Read Channel Signals for Commands Queue Interface.
      wire                              rd_cmd_valid;
      wire                              rd_cmd_fix;
      wire                              rd_cmd_modified;
      wire                              rd_cmd_complete_wrap;
      wire                              rd_cmd_packed_wrap;
      wire [C_M_AXI_BYTES_LOG-1:0]      rd_cmd_first_word;
      wire [C_M_AXI_BYTES_LOG-1:0]      rd_cmd_next_word;
      wire [C_M_AXI_BYTES_LOG-1:0]      rd_cmd_last_word;
      wire [C_M_AXI_BYTES_LOG-1:0]      rd_cmd_offset;
      wire [C_M_AXI_BYTES_LOG-1:0]      rd_cmd_mask;
      wire [C_S_AXI_BYTES_LOG:0]        rd_cmd_step;
      wire [8-1:0]                      rd_cmd_length;
      wire                              rd_cmd_ready;
      wire [C_S_AXI_ID_WIDTH-1:0]       rd_cmd_id;
      wire [C_AXI_ADDR_WIDTH-1:0]       rd_cmd_si_addr;
      wire [C_S_AXI_ID_WIDTH-1:0]       rd_cmd_si_id;
      wire [8-1:0]                      rd_cmd_si_len;
      wire [3-1:0]                      rd_cmd_si_size;
      wire [2-1:0]                      rd_cmd_si_burst;
      
      // Read Address Channel.
      axi_dwidth_converter_v2_1_12_a_upsizer #
      (
       .C_FAMILY                    ("rtl"),
       .C_AXI_PROTOCOL              (C_AXI_PROTOCOL),
       .C_AXI_ID_WIDTH              (C_S_AXI_ID_WIDTH),
       .C_SUPPORTS_ID               (C_SUPPORTS_ID),
       .C_AXI_ADDR_WIDTH            (C_AXI_ADDR_WIDTH),
       .C_S_AXI_DATA_WIDTH          (C_S_AXI_DATA_WIDTH),
       .C_M_AXI_DATA_WIDTH          (C_M_AXI_DATA_WIDTH),
       .C_M_AXI_REGISTER            (C_M_AXI_AR_REGISTER),
       .C_AXI_CHANNEL               (1),
       .C_PACKING_LEVEL             (C_PACKING_LEVEL),
//       .C_FIFO_MODE                 (0),
       .C_FIFO_MODE                 (C_FIFO_MODE),
       .C_ID_QUEUE                  (P_RID_QUEUE),
       .C_S_AXI_BYTES_LOG           (C_S_AXI_BYTES_LOG),
       .C_M_AXI_BYTES_LOG           (C_M_AXI_BYTES_LOG)
        ) read_addr_inst
       (
        // Global Signals
        .ARESET                     (~s_aresetn_i),
        .ACLK                       (aclk),
    
        // Command Interface
        .cmd_valid                  (rd_cmd_valid),
        .cmd_fix                    (rd_cmd_fix),
        .cmd_modified               (rd_cmd_modified),
        .cmd_complete_wrap          (rd_cmd_complete_wrap),
        .cmd_packed_wrap            (rd_cmd_packed_wrap),
        .cmd_first_word             (rd_cmd_first_word),
        .cmd_next_word              (rd_cmd_next_word),
        .cmd_last_word              (rd_cmd_last_word),
        .cmd_offset                 (rd_cmd_offset),
        .cmd_mask                   (rd_cmd_mask),
        .cmd_step                   (rd_cmd_step),
        .cmd_length                 (rd_cmd_length),
        .cmd_ready                  (rd_cmd_ready),
        .cmd_id_ready               (rd_cmd_ready),
        .cmd_id                     (rd_cmd_id),
        .cmd_si_addr                (rd_cmd_si_addr ),
        .cmd_si_id                  (rd_cmd_si_id ),
        .cmd_si_len                 (rd_cmd_si_len  ),
        .cmd_si_size                (rd_cmd_si_size ),
        .cmd_si_burst               (rd_cmd_si_burst),
       
        // Slave Interface Write Address Ports
        .S_AXI_AID                  (sr_arid),
        .S_AXI_AADDR                (sr_araddr),
        .S_AXI_ALEN                 (sr_arlen),
        .S_AXI_ASIZE                (sr_arsize),
        .S_AXI_ABURST               (sr_arburst),
        .S_AXI_ALOCK                (sr_arlock),
        .S_AXI_ACACHE               (sr_arcache),
        .S_AXI_APROT                (sr_arprot),
        .S_AXI_AREGION              (sr_arregion),
        .S_AXI_AQOS                 (sr_arqos),
        .S_AXI_AVALID               (sr_arvalid),
        .S_AXI_AREADY               (sr_arready),
        
        // Master Interface Write Address Port
        .M_AXI_AADDR                (m_axi_araddr_i    ),
        .M_AXI_ALEN                 (m_axi_arlen_i     ),
        .M_AXI_ASIZE                (m_axi_arsize_i    ),
        .M_AXI_ABURST               (m_axi_arburst_i   ),
        .M_AXI_ALOCK                (m_axi_arlock_i    ),
        .M_AXI_ACACHE               (m_axi_arcache_i   ),
        .M_AXI_APROT                (m_axi_arprot_i    ),
        .M_AXI_AREGION              (m_axi_arregion_i  ),
        .M_AXI_AQOS                 (m_axi_arqos_i     ),
        .M_AXI_AVALID               (m_axi_arvalid_i   ),
        .M_AXI_AREADY               (m_axi_arready_i   )
       );
       
      if ((C_FIFO_MODE == P_PKTFIFO) || (C_FIFO_MODE == P_PKTFIFO_CLK)) begin : gen_pktfifo_r_upsizer
        // Packet FIFO Read Data channel.
        axi_dwidth_converter_v2_1_12_r_upsizer_pktfifo #
        (
         .C_FAMILY                    (C_FAMILY),
         .C_S_AXI_DATA_WIDTH          (C_S_AXI_DATA_WIDTH),
         .C_M_AXI_DATA_WIDTH          (C_M_AXI_DATA_WIDTH),
         .C_AXI_ADDR_WIDTH            (C_AXI_ADDR_WIDTH),
         .C_AXI_ID_WIDTH              (C_S_AXI_ID_WIDTH),
         .C_S_AXI_BYTES_LOG           (C_S_AXI_BYTES_LOG),
         .C_M_AXI_BYTES_LOG           (C_M_AXI_BYTES_LOG),
         .C_RATIO                     (C_RATIO),
         .C_RATIO_LOG                 (C_RATIO_LOG),
         .C_CLK_CONV                  (P_CLK_CONV),
         .C_S_AXI_ACLK_RATIO   (C_S_AXI_ACLK_RATIO),
         .C_M_AXI_ACLK_RATIO   (C_M_AXI_ACLK_RATIO),
         .C_AXI_IS_ACLK_ASYNC   (C_AXI_IS_ACLK_ASYNC),
         .C_SYNCHRONIZER_STAGE (C_SYNCHRONIZER_STAGE)
          ) pktfifo_read_data_inst
         (
          .S_AXI_ARESETN              ( s_axi_aresetn        ) ,
          .S_AXI_ACLK                 ( s_axi_aclk          ) ,
          .M_AXI_ARESETN              ( m_axi_aresetn        ) ,
          .M_AXI_ACLK                 ( m_axi_aclk          ) ,

          // Command Interface
          .cmd_si_addr                 (rd_cmd_si_addr ),
          .cmd_si_id                   (rd_cmd_si_id ),
          .cmd_si_len                  (rd_cmd_si_len  ),
          .cmd_si_size                 (rd_cmd_si_size ),
          .cmd_si_burst                (rd_cmd_si_burst),
          .cmd_ready                   (rd_cmd_ready),

          // Slave Interface Write Address Ports
          .S_AXI_ARADDR                (m_axi_araddr_i    ),  
          .S_AXI_ARLEN                 (m_axi_arlen_i     ),  
          .S_AXI_ARSIZE                (m_axi_arsize_i    ),  
          .S_AXI_ARBURST               (m_axi_arburst_i   ),  
          .S_AXI_ARLOCK                (m_axi_arlock_i    ),  
          .S_AXI_ARCACHE               (m_axi_arcache_i   ),  
          .S_AXI_ARPROT                (m_axi_arprot_i    ),  
          .S_AXI_ARREGION              (m_axi_arregion_i  ),  
          .S_AXI_ARQOS                 (m_axi_arqos_i     ),  
          .S_AXI_ARVALID               (m_axi_arvalid_i   ),  
          .S_AXI_ARREADY               (m_axi_arready_i   ),   
          
          // Master Interface Write Address Port
          .M_AXI_ARADDR                (m_axi_araddr),
          .M_AXI_ARLEN                 (m_axi_arlen),
          .M_AXI_ARSIZE                (m_axi_arsize),
          .M_AXI_ARBURST               (m_axi_arburst),
          .M_AXI_ARLOCK                (m_axi_arlock),
          .M_AXI_ARCACHE               (m_axi_arcache),
          .M_AXI_ARPROT                (m_axi_arprot),
          .M_AXI_ARREGION              (m_axi_arregion),
          .M_AXI_ARQOS                 (m_axi_arqos),
          .M_AXI_ARVALID               (m_axi_arvalid),
          .M_AXI_ARREADY               (m_axi_arready),
         
          // Slave Interface Write Data Ports
          .S_AXI_RID                  (s_axi_rid),
          .S_AXI_RDATA                (s_axi_rdata),
          .S_AXI_RRESP                (s_axi_rresp),
          .S_AXI_RLAST                (s_axi_rlast),
          .S_AXI_RVALID               (s_axi_rvalid),
          .S_AXI_RREADY               (s_axi_rready),
          
          // Master Interface Write Data Ports
          .M_AXI_RDATA                (m_axi_rdata),
          .M_AXI_RRESP                (m_axi_rresp),
          .M_AXI_RLAST                (m_axi_rlast),
          .M_AXI_RVALID               (m_axi_rvalid),
          .M_AXI_RREADY               (m_axi_rready),
          
          .SAMPLE_CYCLE               (sample_cycle),
          .SAMPLE_CYCLE_EARLY         (sample_cycle_early)
         );
        
      end else begin : gen_non_fifo_r_upsizer
        // Read Data channel.
        axi_dwidth_converter_v2_1_12_r_upsizer #
        (
         .C_FAMILY                    ("rtl"),
         .C_AXI_ID_WIDTH              (C_S_AXI_ID_WIDTH),
         .C_S_AXI_DATA_WIDTH          (C_S_AXI_DATA_WIDTH),
         .C_M_AXI_DATA_WIDTH          (C_M_AXI_DATA_WIDTH),
         .C_S_AXI_REGISTER            (C_S_AXI_R_REGISTER),
         .C_PACKING_LEVEL             (C_PACKING_LEVEL),
         .C_S_AXI_BYTES_LOG           (C_S_AXI_BYTES_LOG),
         .C_M_AXI_BYTES_LOG           (C_M_AXI_BYTES_LOG),
         .C_RATIO                     (C_RATIO),
         .C_RATIO_LOG                 (C_RATIO_LOG)
          ) read_data_inst
         (
          // Global Signals
          .ARESET                     (~s_aresetn_i),
          .ACLK                       (aclk),
      
          // Command Interface
          .cmd_valid                  (rd_cmd_valid),
          .cmd_fix                    (rd_cmd_fix),
          .cmd_modified               (rd_cmd_modified),
          .cmd_complete_wrap          (rd_cmd_complete_wrap),
          .cmd_packed_wrap            (rd_cmd_packed_wrap),
          .cmd_first_word             (rd_cmd_first_word),
          .cmd_next_word              (rd_cmd_next_word),
          .cmd_last_word              (rd_cmd_last_word),
          .cmd_offset                 (rd_cmd_offset),
          .cmd_mask                   (rd_cmd_mask),
          .cmd_step                   (rd_cmd_step),
          .cmd_length                 (rd_cmd_length),
          .cmd_ready                  (rd_cmd_ready),
          .cmd_id                     (rd_cmd_id),
         
          // Slave Interface Read Data Ports
          .S_AXI_RID                  (s_axi_rid),
          .S_AXI_RDATA                (s_axi_rdata),
          .S_AXI_RRESP                (s_axi_rresp),
          .S_AXI_RLAST                (s_axi_rlast),
          .S_AXI_RVALID               (s_axi_rvalid),
          .S_AXI_RREADY               (s_axi_rready),
          
          // Master Interface Read Data Ports
          .M_AXI_RDATA                (mr_rdata),
          .M_AXI_RRESP                (mr_rresp),
          .M_AXI_RLAST                (mr_rlast),
          .M_AXI_RVALID               (mr_rvalid),
          .M_AXI_RREADY               (mr_rready)
         );
         
        axi_register_slice_v2_1_12_axi_register_slice #
          (
            .C_FAMILY                         (C_FAMILY),
            .C_AXI_PROTOCOL                   (0),
            .C_AXI_ID_WIDTH                   (1),
            .C_AXI_ADDR_WIDTH                 (C_AXI_ADDR_WIDTH),
            .C_AXI_DATA_WIDTH                 (C_M_AXI_DATA_WIDTH),
            .C_AXI_SUPPORTS_USER_SIGNALS      (0),
            .C_REG_CONFIG_R                   (C_M_AXI_R_REGISTER)
          )
          mi_register_slice_inst 
          (
            .aresetn                          (s_aresetn_i),
            .aclk                             (m_aclk),
            .s_axi_awid                       ( 1'b0     ),
            .s_axi_awaddr                     ( {C_AXI_ADDR_WIDTH{1'b0}} ),
            .s_axi_awlen                      ( 8'b0 ),
            .s_axi_awsize                     ( 3'b0 ),
            .s_axi_awburst                    ( 2'b0 ),
            .s_axi_awlock                     ( 1'b0 ),
            .s_axi_awcache                    ( 4'b0 ),
            .s_axi_awprot                     ( 3'b0 ),
            .s_axi_awregion                   ( 4'b0 ),
            .s_axi_awqos                      ( 4'b0 ),
            .s_axi_awuser                     ( 1'b0 ),
            .s_axi_awvalid                    ( 1'b0 ),
            .s_axi_awready                    (     ),
            .s_axi_wid                        ( 1'b0 ),
            .s_axi_wdata                      ( {C_M_AXI_DATA_WIDTH{1'b0}}  ),
            .s_axi_wstrb                      ( {C_M_AXI_DATA_WIDTH/8{1'b0}}  ),
            .s_axi_wlast                      ( 1'b0 ),
            .s_axi_wuser                      ( 1'b0  ),
            .s_axi_wvalid                     ( 1'b0 ),
            .s_axi_wready                     ( ),
            .s_axi_bid                        ( ),
            .s_axi_bresp                      ( ),
            .s_axi_buser                      ( ),
            .s_axi_bvalid                     ( ),
            .s_axi_bready                     ( 1'b0 ),
            .s_axi_arid                       ( 1'b0     ),
            .s_axi_araddr                     ( {C_AXI_ADDR_WIDTH{1'b0}} ),
            .s_axi_arlen                      ( 8'b0 ),
            .s_axi_arsize                     ( 3'b0 ),
            .s_axi_arburst                    ( 2'b0 ),
            .s_axi_arlock                     ( 1'b0 ),
            .s_axi_arcache                    ( 4'b0 ),
            .s_axi_arprot                     ( 3'b0 ),
            .s_axi_arregion                   ( 4'b0 ),
            .s_axi_arqos                      ( 4'b0 ),
            .s_axi_aruser                     ( 1'b0 ),
            .s_axi_arvalid                    ( 1'b0 ),
            .s_axi_arready                    (     ),
            .s_axi_rid                        (),
            .s_axi_rdata                      (mr_rdata     ),
            .s_axi_rresp                      (mr_rresp     ),
            .s_axi_rlast                      (mr_rlast     ),
            .s_axi_ruser                      (),
            .s_axi_rvalid                     (mr_rvalid    ),
            .s_axi_rready                     (mr_rready    ),
            .m_axi_awid                       (),
            .m_axi_awaddr                     (),
            .m_axi_awlen                      (),
            .m_axi_awsize                     (),
            .m_axi_awburst                    (),
            .m_axi_awlock                     (),
            .m_axi_awcache                    (),
            .m_axi_awprot                     (),
            .m_axi_awregion                   (),
            .m_axi_awqos                      (),
            .m_axi_awuser                     (),
            .m_axi_awvalid                    (),
            .m_axi_awready                    (1'b0),
            .m_axi_wid                        () ,
            .m_axi_wdata                      (),
            .m_axi_wstrb                      (),
            .m_axi_wlast                      (),
            .m_axi_wuser                      (),
            .m_axi_wvalid                     (),
            .m_axi_wready                     (1'b0),
            .m_axi_bid                        ( 1'b0 ) ,
            .m_axi_bresp                      ( 2'b0 ) ,
            .m_axi_buser                      ( 1'b0 ) ,
            .m_axi_bvalid                     ( 1'b0 ) ,
            .m_axi_bready                     ( ) ,
            .m_axi_arid                       (),
            .m_axi_araddr                     (),
            .m_axi_arlen                      (),
            .m_axi_arsize                     (),
            .m_axi_arburst                    (),
            .m_axi_arlock                     (),
            .m_axi_arcache                    (),
            .m_axi_arprot                     (),
            .m_axi_arregion                   (),
            .m_axi_arqos                      (),
            .m_axi_aruser                     (),
            .m_axi_arvalid                    (),
            .m_axi_arready                    (1'b0),
            .m_axi_rid                        (1'b0   ),
            .m_axi_rdata                      (m_axi_rdata  ),
            .m_axi_rresp                      (m_axi_rresp  ),
            .m_axi_rlast                      (m_axi_rlast  ),
            .m_axi_ruser                      (1'b0  ),
            .m_axi_rvalid                     (m_axi_rvalid ),
            .m_axi_rready                     (m_axi_rready_i )
          );
        
        assign m_axi_araddr   = m_axi_araddr_i   ;
        assign m_axi_arlen    = m_axi_arlen_i    ;
        assign m_axi_arsize   = m_axi_arsize_i   ;
        assign m_axi_arburst  = m_axi_arburst_i  ;
        assign m_axi_arlock   = m_axi_arlock_i   ;
        assign m_axi_arcache  = m_axi_arcache_i  ;
        assign m_axi_arprot   = m_axi_arprot_i   ;
        assign m_axi_arregion = m_axi_arregion_i ;
        assign m_axi_arqos    = m_axi_arqos_i    ;
        assign m_axi_arvalid  = m_axi_arvalid_i  ;
        assign m_axi_arready_i  = m_axi_arready  ;
        assign m_axi_rready = m_axi_rready_i;
        
      end // gen_r_upsizer
       
    end else begin : NO_READ
      assign sr_arready = 1'b0;
      assign s_axi_rid     = {C_S_AXI_ID_WIDTH{1'b0}};
      assign s_axi_rdata   = {C_S_AXI_DATA_WIDTH{1'b0}};
      assign s_axi_rresp   = 2'b0;
      assign s_axi_rlast   = 1'b0;
      assign s_axi_rvalid  = 1'b0;
      
      assign m_axi_araddr  = {C_AXI_ADDR_WIDTH{1'b0}};
      assign m_axi_arlen   = 8'b0;
      assign m_axi_arsize  = 3'b0;
      assign m_axi_arburst = 2'b0;
      assign m_axi_arlock  = 2'b0;
      assign m_axi_arcache = 4'b0;
      assign m_axi_arprot  = 3'b0;
      assign m_axi_arregion =  4'b0;
      assign m_axi_arqos   = 4'b0;
      assign m_axi_arvalid = 1'b0;
      assign mr_rready  = 1'b0;
      
    end
  endgenerate
  
  
endmodule
`default_nettype wire


// -- (c) Copyright 2010 - 2011 Xilinx, Inc. All rights reserved.
// --
// -- This file contains confidential and proprietary information
// -- of Xilinx, Inc. and is protected under U.S. and 
// -- international copyright and other intellectual property
// -- laws.
// --
// -- DISCLAIMER
// -- This disclaimer is not a license and does not grant any
// -- rights to the materials distributed herewith. Except as
// -- otherwise provided in a valid license issued to you by
// -- Xilinx, and to the maximum extent permitted by applicable
// -- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// -- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// -- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// -- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// -- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// -- (2) Xilinx shall not be liable (whether in contract or tort,
// -- including negligence, or under any other theory of
// -- liability) for any loss or damage of any kind or nature
// -- related to, arising under or in connection with these
// -- materials, including for any direct, or any indirect,
// -- special, incidental, or consequential loss or damage
// -- (including loss of data, profits, goodwill, or any type of
// -- loss or damage suffered as a result of any action brought
// -- by a third party) even if such damage or loss was
// -- reasonably foreseeable or Xilinx had been advised of the
// -- possibility of the same.
// --
// -- CRITICAL APPLICATIONS
// -- Xilinx products are not designed or intended to be fail-
// -- safe, or for use in any application requiring fail-safe
// -- performance, such as life-support or safety devices or
// -- systems, Class III medical devices, nuclear facilities,
// -- applications related to the deployment of airbags, or any
// -- other applications that could lead to death, personal
// -- injury, or severe property or environmental damage
// -- (individually and collectively, "Critical
// -- Applications"). Customer assumes the sole risk and
// -- liability of any use of Xilinx products in Critical
// -- Applications, subject only to applicable laws and
// -- regulations governing limitations on product liability.
// --
// -- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// -- PART OF THIS FILE AT ALL TIMES.
//-----------------------------------------------------------------------------
//
// Description: axi_dwidth_converter
// AXI Memory-mapped data-width converter.
// This module instantiates downsizer and upsizer.
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   top
//     axi_downsizer
//       a_downsizer
//         axic_fifo
//           fifo_gen
//             fifo_coregen
//       w_downsizer
//       b_downsizer
//       r_downsizer
//     axi_upsizer
//       a_upsizer
//         fifo
//           fifo_gen
//             fifo_coregen
//       w_upsizer
//       w_upsizer_pktfifo
//       r_upsizer
//       r_upsizer_pktfifo
//
//--------------------------------------------------------------------------
`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_dwidth_converter_v2_1_12_top #
  (
   parameter         C_FAMILY                         = "virtex7", 
                       // FPGA Family.
   parameter integer C_AXI_PROTOCOL = 0,
                       // Protocol of SI and MI (0=AXI4, 1=AXI3, 2=AXI4LITE).
   parameter integer C_S_AXI_ID_WIDTH                   = 1, 
                       // Width of all ID signals on SI side of converter.
                       // Range: 1 - 32.
   parameter integer C_SUPPORTS_ID                    = 0, 
                       // Indicates whether SI-side ID needs to be stored and compared.
                       // 0 = No, SI is single-threaded, propagate all transactions.
                       // 1 = Yes, stall any transaction with ID different than outstanding transactions.
   parameter integer C_AXI_ADDR_WIDTH                 = 32, 
                       // Width of all ADDR signals on SI and MI.
                       // Range (AXI4, AXI3): 12 - 64.
                       // Range (AXI4LITE): 1 - 64.
   parameter integer C_S_AXI_DATA_WIDTH               = 32,
                       // Width of s_axi_wdata and s_axi_rdata.
                       // Range (AXI4, AXI3): 32, 64, 128, 256, 512, 1024.
                       // Range (AXILITE): 32, 64.
   parameter integer C_M_AXI_DATA_WIDTH               = 64,
                       // Width of m_axi_wdata and m_axi_rdata. 
                       // Range (AXI4, AXI3): 32, 64, 128, 256, 512, 1024.
                       // Range (AXILITE): 32, 64.
                       // S_DATA_WIDTH = M_DATA_WIDTH allowed only when AXI4/AXI3 and PACKING_LEVEL=2.
   parameter integer C_AXI_SUPPORTS_WRITE             = 1,
   parameter integer C_AXI_SUPPORTS_READ              = 1,
   parameter integer C_FIFO_MODE                        = 0,
                       // 0=None, 1=Packet_FIFO, 2=Clock_conversion_Packet_FIFO, 3=Simple_FIFO (FUTURE), 4=Clock_conversion_Simple_FIFO (FUTURE)
   parameter integer C_S_AXI_ACLK_RATIO = 1,     // Clock frequency ratio of SI w.r.t. MI.
                                                 // Range = [1..16].
   parameter integer C_M_AXI_ACLK_RATIO = 2,     // Clock frequency ratio of MI w.r.t. SI.
                                                 // Range = [2..16] if C_S_AXI_ACLK_RATIO = 1; else must be 1.
   parameter integer C_AXI_IS_ACLK_ASYNC = 0,    // Indicates whether S and M clocks are asynchronous.
                                                 // FUTURE FEATURE
                                                 // Range = [0, 1].
   parameter integer C_MAX_SPLIT_BEATS              = 256,
                       // Max burst length after transaction splitting due to downsizing.
                       // Range: 0 (no splitting), 1 (convert to singles), 16, 256.
   parameter integer C_PACKING_LEVEL                    = 1,
                       // Upsizer packing mode.
                       // 0 = Never pack (expander only); packing logic is omitted.
                       // 1 = Pack only when CACHE[1] (Modifiable) is high.
                       // 2 = Always pack, regardless of sub-size transaction or Modifiable bit.
                       //     (Required when used as helper-core by mem-con. Same size AXI interfaces
                       //      should only be used when always packing)
   parameter integer C_SYNCHRONIZER_STAGE = 3
   )
  (
   // Global Signals
   (* KEEP = "TRUE" *) input  wire        s_axi_aclk,
   (* KEEP = "TRUE" *) input  wire        s_axi_aresetn,

   // Slave Interface Write Address Ports
   input  wire [C_S_AXI_ID_WIDTH-1:0]       s_axi_awid,
   input  wire [C_AXI_ADDR_WIDTH-1:0]       s_axi_awaddr,
   input  wire [((C_AXI_PROTOCOL == 1) ? 4 : 8)-1:0] s_axi_awlen,
   input  wire [3-1:0]                      s_axi_awsize,
   input  wire [2-1:0]                      s_axi_awburst,
   input  wire [((C_AXI_PROTOCOL == 1) ? 2 : 1)-1:0] s_axi_awlock,
   input  wire [4-1:0]                      s_axi_awcache,
   input  wire [3-1:0]                      s_axi_awprot,
   input  wire [4-1:0]                      s_axi_awregion,
   input  wire [4-1:0]                      s_axi_awqos,
   input  wire                              s_axi_awvalid,
   output wire                              s_axi_awready,
   // Slave Interface Write Data Ports
   input  wire [C_S_AXI_DATA_WIDTH-1:0]     s_axi_wdata,
   input  wire [C_S_AXI_DATA_WIDTH/8-1:0]   s_axi_wstrb,
   input  wire                              s_axi_wlast,
   input  wire                              s_axi_wvalid,
   output wire                              s_axi_wready,
   // Slave Interface Write Response Ports
   output wire [C_S_AXI_ID_WIDTH-1:0]       s_axi_bid,
   output wire [2-1:0]                      s_axi_bresp,
   output wire                              s_axi_bvalid,
   input  wire                              s_axi_bready,
   // Slave Interface Read Address Ports
   input  wire [C_S_AXI_ID_WIDTH-1:0]       s_axi_arid,
   input  wire [C_AXI_ADDR_WIDTH-1:0]       s_axi_araddr,
   input  wire [((C_AXI_PROTOCOL == 1) ? 4 : 8)-1:0] s_axi_arlen,
   input  wire [3-1:0]                      s_axi_arsize,
   input  wire [2-1:0]                      s_axi_arburst,
   input  wire [((C_AXI_PROTOCOL == 1) ? 2 : 1)-1:0] s_axi_arlock,
   input  wire [4-1:0]                      s_axi_arcache,
   input  wire [3-1:0]                      s_axi_arprot,
   input  wire [4-1:0]                      s_axi_arregion,
   input  wire [4-1:0]                      s_axi_arqos,
   input  wire                              s_axi_arvalid,
   output wire                              s_axi_arready,
   // Slave Interface Read Data Ports
   output wire [C_S_AXI_ID_WIDTH-1:0]       s_axi_rid,
   output wire [C_S_AXI_DATA_WIDTH-1:0]     s_axi_rdata,
   output wire [2-1:0]                      s_axi_rresp,
   output wire                              s_axi_rlast,
   output wire                              s_axi_rvalid,
   input  wire                              s_axi_rready,

   // Master Interface System Signals
   (* KEEP = "TRUE" *) input  wire        m_axi_aclk,
   (* KEEP = "TRUE" *) input  wire        m_axi_aresetn,

   // Master Interface Write Address Port
   output wire [C_AXI_ADDR_WIDTH-1:0]       m_axi_awaddr,
   output wire [((C_AXI_PROTOCOL == 1) ? 4 : 8)-1:0] m_axi_awlen,
   output wire [3-1:0]                      m_axi_awsize,
   output wire [2-1:0]                      m_axi_awburst,
   output wire [((C_AXI_PROTOCOL == 1) ? 2 : 1)-1:0] m_axi_awlock,
   output wire [4-1:0]                      m_axi_awcache,
   output wire [3-1:0]                      m_axi_awprot,
   output wire [4-1:0]                      m_axi_awregion,
   output wire [4-1:0]                      m_axi_awqos,
   output wire                              m_axi_awvalid,
   input  wire                              m_axi_awready,
   // Master Interface Write Data Ports
   output wire [C_M_AXI_DATA_WIDTH-1:0]     m_axi_wdata,
   output wire [C_M_AXI_DATA_WIDTH/8-1:0]   m_axi_wstrb,
   output wire                              m_axi_wlast,
   output wire                              m_axi_wvalid,
   input  wire                              m_axi_wready,
   // Master Interface Write Response Ports
   input  wire [2-1:0]                      m_axi_bresp,
   input  wire                              m_axi_bvalid,
   output wire                              m_axi_bready,
   // Master Interface Read Address Port
   output wire [C_AXI_ADDR_WIDTH-1:0]       m_axi_araddr,
   output wire [((C_AXI_PROTOCOL == 1) ? 4 : 8)-1:0] m_axi_arlen,
   output wire [3-1:0]                      m_axi_arsize,
   output wire [2-1:0]                      m_axi_arburst,
   output wire [((C_AXI_PROTOCOL == 1) ? 2 : 1)-1:0] m_axi_arlock,
   output wire [4-1:0]                      m_axi_arcache,
   output wire [3-1:0]                      m_axi_arprot,
   output wire [4-1:0]                      m_axi_arregion,
   output wire [4-1:0]                      m_axi_arqos,
   output wire                              m_axi_arvalid,
   input  wire                              m_axi_arready,
   // Master Interface Read Data Ports
   input  wire [C_M_AXI_DATA_WIDTH-1:0]     m_axi_rdata,
   input  wire [2-1:0]                      m_axi_rresp,
   input  wire                              m_axi_rlast,
   input  wire                              m_axi_rvalid,
   output wire                              m_axi_rready
   );



  wire aclk = s_axi_aclk;
  wire aresetn = s_axi_aresetn;

  /////////////////////////////////////////////////////////////////////////////
  // Functions
  /////////////////////////////////////////////////////////////////////////////
  
  // Log2.
  function integer log2
    (
     input integer x
     );
    integer acc;
    begin
      acc=0;
      while ((2**acc) < x)
        acc = acc + 1;
      log2 = acc;
    end
  endfunction
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Local params
  /////////////////////////////////////////////////////////////////////////////
  
  // Log2 of number of 32bit word on SI-side.
  localparam integer C_S_AXI_BYTES_LOG                = log2(C_S_AXI_DATA_WIDTH/8);
  
  // Log2 of number of 32bit word on MI-side.
  localparam integer C_M_AXI_BYTES_LOG                = log2(C_M_AXI_DATA_WIDTH/8);
  
  // Log2 of Up-Sizing ratio for data.
  localparam integer C_RATIO                          = C_S_AXI_DATA_WIDTH / C_M_AXI_DATA_WIDTH;
  localparam integer C_RATIO_LOG                      = log2(C_RATIO);
  localparam integer P_AXI4 = 0;
  localparam integer P_AXI3 = 1;
  localparam integer P_AXILITE = 2;
  localparam integer P_CONVERSION = 2;
  
  localparam integer P_MAX_SPLIT_BEATS = (C_MAX_SPLIT_BEATS >= 16) ? C_MAX_SPLIT_BEATS :
    (C_AXI_PROTOCOL == P_AXI4) ? 256 : 16;

  wire [8-1:0]                  s_axi_awlen_i;
  wire [2-1:0]                  s_axi_awlock_i;
  wire [8-1:0]                  s_axi_arlen_i;
  wire [2-1:0]                  s_axi_arlock_i;
  wire [8-1:0]                  m_axi_awlen_i;
  wire [2-1:0]                  m_axi_awlock_i;
  wire [8-1:0]                  m_axi_arlen_i;
  wire [2-1:0]                  m_axi_arlock_i;
  wire [4-1:0]                  s_axi_awregion_i;
  wire [4-1:0]                  s_axi_arregion_i;
  wire [4-1:0]                  m_axi_awregion_i;
  wire [4-1:0]                  m_axi_arregion_i;
  
  generate
    if (C_AXI_PROTOCOL == P_AXILITE) begin : gen_lite_tieoff
      assign s_axi_bid          = {C_S_AXI_ID_WIDTH{1'b0}} ;
      assign s_axi_rid          = {C_S_AXI_ID_WIDTH{1'b0}} ;
      assign s_axi_rlast        = 1'b0 ;
      assign m_axi_awlen        = 8'b0 ;
      assign m_axi_awsize       = 3'b0 ;
      assign m_axi_awburst      = 2'b0 ;
      assign m_axi_awlock       = 1'b0 ;
      assign m_axi_awcache      = 4'b0 ;
      assign m_axi_awregion     = 4'b0 ;
      assign m_axi_awqos        = 4'b0 ;
      assign m_axi_wlast        = 1'b0 ;
      assign m_axi_arlen        = 8'b0 ;
      assign m_axi_arsize       = 3'b0 ;
      assign m_axi_arburst      = 2'b0 ;
      assign m_axi_arlock       = 1'b0 ;
      assign m_axi_arcache      = 4'b0 ;
      assign m_axi_arregion     = 4'b0 ;
      assign m_axi_arqos        = 4'b0 ;
    end else begin : gen_full_tieoff
      assign s_axi_awlen_i = (C_AXI_PROTOCOL == P_AXI3) ? {4'b0000, s_axi_awlen}: s_axi_awlen;
      assign s_axi_awlock_i = (C_AXI_PROTOCOL == P_AXI3) ? s_axi_awlock : {1'b0, s_axi_awlock};
      assign s_axi_arlen_i = (C_AXI_PROTOCOL == P_AXI3) ? {4'b0000, s_axi_arlen}: s_axi_arlen;
      assign s_axi_arlock_i = (C_AXI_PROTOCOL == P_AXI3) ? s_axi_arlock : {1'b0, s_axi_arlock};
      assign m_axi_awlen = (C_AXI_PROTOCOL == P_AXI3) ? m_axi_awlen_i[3:0]: m_axi_awlen_i;
      assign m_axi_awlock = (C_AXI_PROTOCOL == P_AXI3) ? m_axi_awlock_i : m_axi_awlock_i[0];
      assign m_axi_arlen = (C_AXI_PROTOCOL == P_AXI3) ? m_axi_arlen_i[3:0]: m_axi_arlen_i;
      assign m_axi_arlock = (C_AXI_PROTOCOL == P_AXI3) ? m_axi_arlock_i : m_axi_arlock_i[0];
      assign s_axi_awregion_i = (C_AXI_PROTOCOL == P_AXI3) ? 4'b0 : s_axi_awregion;
      assign s_axi_arregion_i = (C_AXI_PROTOCOL == P_AXI3) ? 4'b0 : s_axi_arregion;
      assign m_axi_awregion = (C_AXI_PROTOCOL == P_AXI3) ? 4'b0 : m_axi_awregion_i;
      assign m_axi_arregion = (C_AXI_PROTOCOL == P_AXI3) ? 4'b0 : m_axi_arregion_i;
    end
    
    if (C_S_AXI_DATA_WIDTH > C_M_AXI_DATA_WIDTH) begin : gen_downsizer
      if (C_AXI_PROTOCOL == P_AXILITE) begin : gen_lite_downsizer
        
        axi_dwidth_converter_v2_1_12_axi4lite_downsizer #(
          .C_FAMILY                    ( C_FAMILY                    ) ,
          .C_AXI_ADDR_WIDTH            ( C_AXI_ADDR_WIDTH            ) ,
          .C_AXI_SUPPORTS_WRITE        ( C_AXI_SUPPORTS_WRITE        ) ,
          .C_AXI_SUPPORTS_READ         ( C_AXI_SUPPORTS_READ         ) 
        )
        lite_downsizer_inst
        (
          .aresetn                    ( aresetn        ) ,
          .aclk                       ( aclk          ) ,
          .s_axi_awaddr               ( s_axi_awaddr  ) ,
          .s_axi_awprot               ( s_axi_awprot  ) ,
          .s_axi_awvalid              ( s_axi_awvalid ) ,
          .s_axi_awready              ( s_axi_awready ) ,
          .s_axi_wdata                ( s_axi_wdata   ) ,
          .s_axi_wstrb                ( s_axi_wstrb   ) ,
          .s_axi_wvalid               ( s_axi_wvalid  ) ,
          .s_axi_wready               ( s_axi_wready  ) ,
          .s_axi_bresp                ( s_axi_bresp   ) ,
          .s_axi_bvalid               ( s_axi_bvalid  ) ,
          .s_axi_bready               ( s_axi_bready  ) ,
          .s_axi_araddr               ( s_axi_araddr  ) ,
          .s_axi_arprot               ( s_axi_arprot  ) ,
          .s_axi_arvalid              ( s_axi_arvalid ) ,
          .s_axi_arready              ( s_axi_arready ) ,
          .s_axi_rdata                ( s_axi_rdata   ) ,
          .s_axi_rresp                ( s_axi_rresp   ) ,
          .s_axi_rvalid               ( s_axi_rvalid  ) ,
          .s_axi_rready               ( s_axi_rready  ) ,
          .m_axi_awaddr               ( m_axi_awaddr  ) ,
          .m_axi_awprot               ( m_axi_awprot  ) ,
          .m_axi_awvalid              ( m_axi_awvalid ) ,
          .m_axi_awready              ( m_axi_awready ) ,
          .m_axi_wdata                ( m_axi_wdata   ) ,
          .m_axi_wstrb                ( m_axi_wstrb   ) ,
          .m_axi_wvalid               ( m_axi_wvalid  ) ,
          .m_axi_wready               ( m_axi_wready  ) ,
          .m_axi_bresp                ( m_axi_bresp   ) ,
          .m_axi_bvalid               ( m_axi_bvalid  ) ,
          .m_axi_bready               ( m_axi_bready  ) ,
          .m_axi_araddr               ( m_axi_araddr  ) ,
          .m_axi_arprot               ( m_axi_arprot  ) ,
          .m_axi_arvalid              ( m_axi_arvalid ) ,
          .m_axi_arready              ( m_axi_arready ) ,
          .m_axi_rdata                ( m_axi_rdata   ) ,
          .m_axi_rresp                ( m_axi_rresp   ) ,
          .m_axi_rvalid               ( m_axi_rvalid  ) ,
          .m_axi_rready               ( m_axi_rready  )
        );
        
      end else if (((C_AXI_PROTOCOL == P_AXI3) && (P_MAX_SPLIT_BEATS > 0)) || (P_MAX_SPLIT_BEATS < 256) || (C_RATIO > 16)) begin : gen_cascaded_downsizer
        
        localparam integer P_DATA_WIDTH_I = (C_RATIO > 16) ? 64 : C_M_AXI_DATA_WIDTH;
        
        wire [C_AXI_ADDR_WIDTH-1:0]       awaddr_i     ;
        wire [8-1:0]                      awlen_i     ;
        wire [3-1:0]                      awsize_i     ;
        wire [2-1:0]                      awburst_i     ;
        wire [2-1:0]                      awlock_i     ;
        wire [4-1:0]                      awcache_i     ;
        wire [3-1:0]                      awprot_i     ;
        wire [4-1:0]                      awregion_i     ;
        wire [4-1:0]                      awqos_i     ;
        wire                              awvalid_i     ;
        wire                              awready_i     ;
        wire [P_DATA_WIDTH_I-1:0]         wdata_i     ;
        wire [P_DATA_WIDTH_I/8-1:0]       wstrb_i     ;
        wire                              wlast_i     ;
        wire                              wvalid_i     ;
        wire                              wready_i     ;
        wire [2-1:0]                      bresp_i     ;
        wire                              bvalid_i     ;
        wire                              bready_i     ;
        wire [C_AXI_ADDR_WIDTH-1:0]       araddr_i     ;
        wire [8-1:0]                      arlen_i     ;
        wire [3-1:0]                      arsize_i     ;
        wire [2-1:0]                      arburst_i     ;
        wire [2-1:0]                      arlock_i     ;
        wire [4-1:0]                      arcache_i     ;
        wire [3-1:0]                      arprot_i     ;
        wire [4-1:0]                      arregion_i     ;
        wire [4-1:0]                      arqos_i     ;
        wire                              arvalid_i     ;
        wire                              arready_i     ;
        wire [P_DATA_WIDTH_I-1:0]         rdata_i     ;
        wire [2-1:0]                      rresp_i     ;
        wire                              rlast_i     ;
        wire                              rvalid_i     ;
        wire                              rready_i    ;
        wire [4-1:0]                      m_axi_awlen_ii;
        wire [4-1:0]                      m_axi_arlen_ii;
        wire [1-1:0]                      awlock_ii;
        wire [1-1:0]                      arlock_ii;
        
        axi_dwidth_converter_v2_1_12_axi_downsizer #(
          .C_FAMILY                    ( C_FAMILY                    ) ,
          .C_AXI_PROTOCOL              ( C_AXI_PROTOCOL              ) ,
          .C_S_AXI_ID_WIDTH            ( C_S_AXI_ID_WIDTH              ) ,
          .C_SUPPORTS_ID               ( C_SUPPORTS_ID ),
          .C_AXI_ADDR_WIDTH            ( C_AXI_ADDR_WIDTH            ) ,
          .C_S_AXI_DATA_WIDTH          ( C_S_AXI_DATA_WIDTH          ) ,
          .C_M_AXI_DATA_WIDTH          ( P_DATA_WIDTH_I          ) ,
          .C_AXI_SUPPORTS_WRITE        ( C_AXI_SUPPORTS_WRITE        ) ,
          .C_AXI_SUPPORTS_READ         ( C_AXI_SUPPORTS_READ         ) ,
          .C_MAX_SPLIT_BEATS           ( 256         ) 
        )
        first_downsizer_inst
        (
          .aresetn                    ( aresetn        ) ,
          .aclk                       ( aclk          ) ,
          .s_axi_awid                 ( s_axi_awid    ) ,
          .s_axi_awaddr               ( s_axi_awaddr  ) ,
          .s_axi_awlen                ( s_axi_awlen_i   ) ,
          .s_axi_awsize               ( s_axi_awsize  ) ,
          .s_axi_awburst              ( s_axi_awburst ) ,
          .s_axi_awlock               ( s_axi_awlock_i  ) ,
          .s_axi_awcache              ( s_axi_awcache ) ,
          .s_axi_awprot               ( s_axi_awprot  ) ,
          .s_axi_awregion             ( s_axi_awregion_i) ,
          .s_axi_awqos                ( s_axi_awqos   ) ,
          .s_axi_awvalid              ( s_axi_awvalid ) ,
          .s_axi_awready              ( s_axi_awready ) ,
          .s_axi_wdata                ( s_axi_wdata   ) ,
          .s_axi_wstrb                ( s_axi_wstrb   ) ,
          .s_axi_wlast                ( s_axi_wlast   ) ,
          .s_axi_wvalid               ( s_axi_wvalid  ) ,
          .s_axi_wready               ( s_axi_wready  ) ,
          .s_axi_bid                  ( s_axi_bid     ) ,
          .s_axi_bresp                ( s_axi_bresp   ) ,
          .s_axi_bvalid               ( s_axi_bvalid  ) ,
          .s_axi_bready               ( s_axi_bready  ) ,
          .s_axi_arid                 ( s_axi_arid    ) ,
          .s_axi_araddr               ( s_axi_araddr  ) ,
          .s_axi_arlen                ( s_axi_arlen_i   ) ,
          .s_axi_arsize               ( s_axi_arsize  ) ,
          .s_axi_arburst              ( s_axi_arburst ) ,
          .s_axi_arlock               ( s_axi_arlock_i  ) ,
          .s_axi_arcache              ( s_axi_arcache ) ,
          .s_axi_arprot               ( s_axi_arprot  ) ,
          .s_axi_arregion             ( s_axi_arregion_i) ,
          .s_axi_arqos                ( s_axi_arqos   ) ,
          .s_axi_arvalid              ( s_axi_arvalid ) ,
          .s_axi_arready              ( s_axi_arready ) ,
          .s_axi_rid                  ( s_axi_rid     ) ,
          .s_axi_rdata                ( s_axi_rdata   ) ,
          .s_axi_rresp                ( s_axi_rresp   ) ,
          .s_axi_rlast                ( s_axi_rlast   ) ,
          .s_axi_rvalid               ( s_axi_rvalid  ) ,
          .s_axi_rready               ( s_axi_rready  ) ,
          .m_axi_awaddr               ( awaddr_i      ) ,
          .m_axi_awlen                ( awlen_i       ) ,
          .m_axi_awsize               ( awsize_i      ) ,
          .m_axi_awburst              ( awburst_i     ) ,
          .m_axi_awlock               ( awlock_i      ) ,
          .m_axi_awcache              ( awcache_i     ) ,
          .m_axi_awprot               ( awprot_i      ) ,
          .m_axi_awregion             ( awregion_i    ) ,
          .m_axi_awqos                ( awqos_i       ) ,
          .m_axi_awvalid              ( awvalid_i     ) ,
          .m_axi_awready              ( awready_i     ) ,
          .m_axi_wdata                ( wdata_i       ) ,
          .m_axi_wstrb                ( wstrb_i       ) ,
          .m_axi_wlast                ( wlast_i       ) ,
          .m_axi_wvalid               ( wvalid_i      ) ,
          .m_axi_wready               ( wready_i      ) ,
          .m_axi_bresp                ( bresp_i       ) ,
          .m_axi_bvalid               ( bvalid_i      ) ,
          .m_axi_bready               ( bready_i      ) ,
          .m_axi_araddr               ( araddr_i      ) ,
          .m_axi_arlen                ( arlen_i       ) ,
          .m_axi_arsize               ( arsize_i      ) ,
          .m_axi_arburst              ( arburst_i     ) ,
          .m_axi_arlock               ( arlock_i      ) ,
          .m_axi_arcache              ( arcache_i     ) ,
          .m_axi_arprot               ( arprot_i      ) ,
          .m_axi_arregion             ( arregion_i    ) ,
          .m_axi_arqos                ( arqos_i       ) ,
          .m_axi_arvalid              ( arvalid_i     ) ,
          .m_axi_arready              ( arready_i     ) ,
          .m_axi_rdata                ( rdata_i       ) ,
          .m_axi_rresp                ( rresp_i       ) ,
          .m_axi_rlast                ( rlast_i       ) ,
          .m_axi_rvalid               ( rvalid_i      ) ,
          .m_axi_rready               ( rready_i      ) 
        );
        
        if (C_RATIO > 16) begin : gen_second_downsizer
          
          axi_dwidth_converter_v2_1_12_axi_downsizer #(
            .C_FAMILY                    ( C_FAMILY                    ) ,
            .C_AXI_PROTOCOL              ( C_AXI_PROTOCOL              ) ,
            .C_S_AXI_ID_WIDTH            ( 1              ) ,
            .C_SUPPORTS_ID               ( 0 ),
            .C_AXI_ADDR_WIDTH            ( C_AXI_ADDR_WIDTH            ) ,
            .C_S_AXI_DATA_WIDTH          ( P_DATA_WIDTH_I          ) ,
            .C_M_AXI_DATA_WIDTH          ( C_M_AXI_DATA_WIDTH          ) ,
            .C_AXI_SUPPORTS_WRITE        ( C_AXI_SUPPORTS_WRITE        ) ,
            .C_AXI_SUPPORTS_READ         ( C_AXI_SUPPORTS_READ         ) ,
            .C_MAX_SPLIT_BEATS           ( P_MAX_SPLIT_BEATS         ) 
          )
          second_downsizer_inst
          (
            .aresetn                    ( aresetn       ) ,
            .aclk                       ( aclk          ) ,
            .s_axi_awid                 ( 1'b0          ) ,
            .s_axi_awaddr               ( awaddr_i      ) ,  
            .s_axi_awlen                ( awlen_i       ) ,  
            .s_axi_awsize               ( awsize_i      ) ,  
            .s_axi_awburst              ( awburst_i     ) ,  
            .s_axi_awlock               ( awlock_i      ) ,  
            .s_axi_awcache              ( awcache_i     ) ,  
            .s_axi_awprot               ( awprot_i      ) ,  
            .s_axi_awregion             ( awregion_i    ) ,  
            .s_axi_awqos                ( awqos_i       ) ,  
            .s_axi_awvalid              ( awvalid_i     ) ,  
            .s_axi_awready              ( awready_i     ) ,  
            .s_axi_wdata                ( wdata_i       ) ,  
            .s_axi_wstrb                ( wstrb_i       ) ,  
            .s_axi_wlast                ( wlast_i       ) ,  
            .s_axi_wvalid               ( wvalid_i      ) ,  
            .s_axi_wready               ( wready_i      ) ,  
            .s_axi_bid                  (               ) ,
            .s_axi_bresp                ( bresp_i       ) ,   
            .s_axi_bvalid               ( bvalid_i      ) ,   
            .s_axi_bready               ( bready_i      ) ,    
            .s_axi_arid                 ( 1'b0          ) ,  
            .s_axi_araddr               ( araddr_i      ) , 
            .s_axi_arlen                ( arlen_i       ) ,  
            .s_axi_arsize               ( arsize_i      ) ,  
            .s_axi_arburst              ( arburst_i     ) ,  
            .s_axi_arlock               ( arlock_i      ) ,  
            .s_axi_arcache              ( arcache_i     ) ,  
            .s_axi_arprot               ( arprot_i      ) ,  
            .s_axi_arregion             ( arregion_i    ) , 
            .s_axi_arqos                ( arqos_i       ) ,  
            .s_axi_arvalid              ( arvalid_i     ) ,  
            .s_axi_arready              ( arready_i     ) , 
            .s_axi_rid                  (               ) ,
            .s_axi_rdata                ( rdata_i       ) ,   
            .s_axi_rresp                ( rresp_i       ) ,   
            .s_axi_rlast                ( rlast_i       ) ,   
            .s_axi_rvalid               ( rvalid_i      ) ,   
            .s_axi_rready               ( rready_i      ) ,
            .m_axi_awaddr               ( m_axi_awaddr  ) ,
            .m_axi_awlen                ( m_axi_awlen_i   ) ,
            .m_axi_awsize               ( m_axi_awsize  ) ,
            .m_axi_awburst              ( m_axi_awburst ) ,
            .m_axi_awlock               ( m_axi_awlock_i  ) ,
            .m_axi_awcache              ( m_axi_awcache ) ,
            .m_axi_awprot               ( m_axi_awprot  ) ,
            .m_axi_awregion             ( m_axi_awregion_i) ,
            .m_axi_awqos                ( m_axi_awqos   ) ,
            .m_axi_awvalid              ( m_axi_awvalid ) ,
            .m_axi_awready              ( m_axi_awready ) ,
            .m_axi_wdata                ( m_axi_wdata   ) ,
            .m_axi_wstrb                ( m_axi_wstrb   ) ,
            .m_axi_wlast                ( m_axi_wlast   ) ,
            .m_axi_wvalid               ( m_axi_wvalid  ) ,
            .m_axi_wready               ( m_axi_wready  ) ,
            .m_axi_bresp                ( m_axi_bresp   ) ,
            .m_axi_bvalid               ( m_axi_bvalid  ) ,
            .m_axi_bready               ( m_axi_bready  ) ,
            .m_axi_araddr               ( m_axi_araddr  ) ,
            .m_axi_arlen                ( m_axi_arlen_i   ) ,
            .m_axi_arsize               ( m_axi_arsize  ) ,
            .m_axi_arburst              ( m_axi_arburst ) ,
            .m_axi_arlock               ( m_axi_arlock_i  ) ,
            .m_axi_arcache              ( m_axi_arcache ) ,
            .m_axi_arprot               ( m_axi_arprot  ) ,
            .m_axi_arregion             ( m_axi_arregion_i) ,
            .m_axi_arqos                ( m_axi_arqos   ) ,
            .m_axi_arvalid              ( m_axi_arvalid ) ,
            .m_axi_arready              ( m_axi_arready ) ,
            .m_axi_rdata                ( m_axi_rdata   ) ,
            .m_axi_rresp                ( m_axi_rresp   ) ,
            .m_axi_rlast                ( m_axi_rlast   ) ,
            .m_axi_rvalid               ( m_axi_rvalid  ) ,
            .m_axi_rready               ( m_axi_rready  )
          );
          
        end else begin : gen_axi3_conv
          
          axi_protocol_converter_v2_1_12_axi_protocol_converter #(
            .C_FAMILY                    ( C_FAMILY                    ) ,
            .C_S_AXI_PROTOCOL            ( P_AXI4              ) ,
            .C_M_AXI_PROTOCOL            ( P_AXI3              ) ,
            .C_AXI_ID_WIDTH              ( 1              ) ,
            .C_AXI_ADDR_WIDTH            ( C_AXI_ADDR_WIDTH            ) ,
            .C_AXI_DATA_WIDTH            ( C_M_AXI_DATA_WIDTH          ) ,
            .C_AXI_SUPPORTS_WRITE        ( C_AXI_SUPPORTS_WRITE        ) ,
            .C_AXI_SUPPORTS_READ         ( C_AXI_SUPPORTS_READ         ) ,
            .C_AXI_SUPPORTS_USER_SIGNALS (0) ,
            .C_TRANSLATION_MODE          ( P_CONVERSION         ) 
          )
          axi3_conv_inst
          (
            .aresetn                    ( aresetn       ) ,
            .aclk                       ( aclk          ) ,
            .s_axi_awid                 ( 1'b0          ) ,
            .s_axi_awaddr               ( awaddr_i      ) ,  
            .s_axi_awlen                ( awlen_i       ) ,  
            .s_axi_awsize               ( awsize_i      ) ,  
            .s_axi_awburst              ( awburst_i     ) ,  
            .s_axi_awlock               ( awlock_ii      ) ,  
            .s_axi_awcache              ( awcache_i     ) ,  
            .s_axi_awprot               ( awprot_i      ) ,  
            .s_axi_awregion             ( awregion_i    ) ,  
            .s_axi_awqos                ( awqos_i       ) ,  
            .s_axi_awvalid              ( awvalid_i     ) ,  
            .s_axi_awready              ( awready_i     ) ,  
            .s_axi_wdata                ( wdata_i       ) ,  
            .s_axi_wstrb                ( wstrb_i       ) ,  
            .s_axi_wlast                ( wlast_i       ) ,  
            .s_axi_wvalid               ( wvalid_i      ) ,  
            .s_axi_wready               ( wready_i      ) ,  
            .s_axi_bid                  (               ) ,
            .s_axi_bresp                ( bresp_i       ) ,   
            .s_axi_bvalid               ( bvalid_i      ) ,   
            .s_axi_bready               ( bready_i      ) ,    
            .s_axi_arid                 ( 1'b0          ) ,  
            .s_axi_araddr               ( araddr_i      ) , 
            .s_axi_arlen                ( arlen_i       ) ,  
            .s_axi_arsize               ( arsize_i      ) ,  
            .s_axi_arburst              ( arburst_i     ) ,  
            .s_axi_arlock               ( arlock_ii      ) ,  
            .s_axi_arcache              ( arcache_i     ) ,  
            .s_axi_arprot               ( arprot_i      ) ,  
            .s_axi_arregion             ( arregion_i    ) , 
            .s_axi_arqos                ( arqos_i       ) ,  
            .s_axi_arvalid              ( arvalid_i     ) ,  
            .s_axi_arready              ( arready_i     ) , 
            .s_axi_rid                  (               ) ,
            .s_axi_rdata                ( rdata_i       ) ,   
            .s_axi_rresp                ( rresp_i       ) ,   
            .s_axi_rlast                ( rlast_i       ) ,   
            .s_axi_rvalid               ( rvalid_i      ) ,   
            .s_axi_rready               ( rready_i      ) ,
            .m_axi_awaddr               ( m_axi_awaddr  ) ,
            .m_axi_awlen                ( m_axi_awlen_ii   ) ,
            .m_axi_awsize               ( m_axi_awsize  ) ,
            .m_axi_awburst              ( m_axi_awburst ) ,
            .m_axi_awlock               ( m_axi_awlock_i  ) ,
            .m_axi_awcache              ( m_axi_awcache ) ,
            .m_axi_awprot               ( m_axi_awprot  ) ,
            .m_axi_awregion             ( m_axi_awregion_i) ,
            .m_axi_awqos                ( m_axi_awqos   ) ,
            .m_axi_awvalid              ( m_axi_awvalid ) ,
            .m_axi_awready              ( m_axi_awready ) ,
            .m_axi_wdata                ( m_axi_wdata   ) ,
            .m_axi_wstrb                ( m_axi_wstrb   ) ,
            .m_axi_wlast                ( m_axi_wlast   ) ,
            .m_axi_wvalid               ( m_axi_wvalid  ) ,
            .m_axi_wready               ( m_axi_wready  ) ,
            .m_axi_bresp                ( m_axi_bresp   ) ,
            .m_axi_bvalid               ( m_axi_bvalid  ) ,
            .m_axi_bready               ( m_axi_bready  ) ,
            .m_axi_araddr               ( m_axi_araddr  ) ,
            .m_axi_arlen                ( m_axi_arlen_ii   ) ,
            .m_axi_arsize               ( m_axi_arsize  ) ,
            .m_axi_arburst              ( m_axi_arburst ) ,
            .m_axi_arlock               ( m_axi_arlock_i  ) ,
            .m_axi_arcache              ( m_axi_arcache ) ,
            .m_axi_arprot               ( m_axi_arprot  ) ,
            .m_axi_arregion             ( m_axi_arregion_i) ,
            .m_axi_arqos                ( m_axi_arqos   ) ,
            .m_axi_arvalid              ( m_axi_arvalid ) ,
            .m_axi_arready              ( m_axi_arready ) ,
            .m_axi_rdata                ( m_axi_rdata   ) ,
            .m_axi_rresp                ( m_axi_rresp   ) ,
            .m_axi_rlast                ( m_axi_rlast   ) ,
            .m_axi_rvalid               ( m_axi_rvalid  ) ,
            .m_axi_rready               ( m_axi_rready  ) ,
            .m_axi_awid                 ( ) ,
            .m_axi_wid                  ( ) ,
            .m_axi_bid                  ( 1'b0 ) ,
            .m_axi_arid                 ( ) ,
            .m_axi_rid                  ( 1'b0 ) ,
            .s_axi_wid                  ( 1'b0 ) ,
            .s_axi_awuser               ( 1'b0 ) ,
            .s_axi_wuser                ( 1'b0 ) ,
            .s_axi_buser                ( ) ,
            .s_axi_aruser               ( 1'b0 ) ,
            .s_axi_ruser                ( ) ,
            .m_axi_awuser               ( ) ,
            .m_axi_wuser                ( ) ,
            .m_axi_buser                ( 1'b0 ) ,
            .m_axi_aruser               ( ) ,
            .m_axi_ruser                ( 1'b0 ) 
          );
          
          assign awlock_ii = awlock_i[0];
          assign arlock_ii = arlock_i[0];
          assign m_axi_awlen_i = {4'b0, m_axi_awlen_ii};
          assign m_axi_arlen_i = {4'b0, m_axi_arlen_ii};
        end
        
      end else begin : gen_simple_downsizer
        
        axi_dwidth_converter_v2_1_12_axi_downsizer #(
          .C_FAMILY                    ( C_FAMILY                    ) ,
          .C_AXI_PROTOCOL              ( C_AXI_PROTOCOL              ) ,
          .C_S_AXI_ID_WIDTH            ( C_S_AXI_ID_WIDTH              ) ,
          .C_SUPPORTS_ID               ( C_SUPPORTS_ID ),
          .C_AXI_ADDR_WIDTH            ( C_AXI_ADDR_WIDTH            ) ,
          .C_S_AXI_DATA_WIDTH          ( C_S_AXI_DATA_WIDTH          ) ,
          .C_M_AXI_DATA_WIDTH          ( C_M_AXI_DATA_WIDTH          ) ,
          .C_AXI_SUPPORTS_WRITE        ( C_AXI_SUPPORTS_WRITE        ) ,
          .C_AXI_SUPPORTS_READ         ( C_AXI_SUPPORTS_READ         ) ,
          .C_MAX_SPLIT_BEATS           ( P_MAX_SPLIT_BEATS         ) 
        )
        axi_downsizer_inst
        (
          .aresetn                    ( aresetn        ) ,
          .aclk                       ( aclk          ) ,
          .s_axi_awid                 ( s_axi_awid    ) ,
          .s_axi_awaddr               ( s_axi_awaddr  ) ,
          .s_axi_awlen                ( s_axi_awlen_i   ) ,
          .s_axi_awsize               ( s_axi_awsize  ) ,
          .s_axi_awburst              ( s_axi_awburst ) ,
          .s_axi_awlock               ( s_axi_awlock_i  ) ,
          .s_axi_awcache              ( s_axi_awcache ) ,
          .s_axi_awprot               ( s_axi_awprot  ) ,
          .s_axi_awregion             ( s_axi_awregion_i) ,
          .s_axi_awqos                ( s_axi_awqos   ) ,
          .s_axi_awvalid              ( s_axi_awvalid ) ,
          .s_axi_awready              ( s_axi_awready ) ,
          .s_axi_wdata                ( s_axi_wdata   ) ,
          .s_axi_wstrb                ( s_axi_wstrb   ) ,
          .s_axi_wlast                ( s_axi_wlast   ) ,
          .s_axi_wvalid               ( s_axi_wvalid  ) ,
          .s_axi_wready               ( s_axi_wready  ) ,
          .s_axi_bid                  ( s_axi_bid     ) ,
          .s_axi_bresp                ( s_axi_bresp   ) ,
          .s_axi_bvalid               ( s_axi_bvalid  ) ,
          .s_axi_bready               ( s_axi_bready  ) ,
          .s_axi_arid                 ( s_axi_arid    ) ,
          .s_axi_araddr               ( s_axi_araddr  ) ,
          .s_axi_arlen                ( s_axi_arlen_i   ) ,
          .s_axi_arsize               ( s_axi_arsize  ) ,
          .s_axi_arburst              ( s_axi_arburst ) ,
          .s_axi_arlock               ( s_axi_arlock_i  ) ,
          .s_axi_arcache              ( s_axi_arcache ) ,
          .s_axi_arprot               ( s_axi_arprot  ) ,
          .s_axi_arregion             ( s_axi_arregion_i) ,
          .s_axi_arqos                ( s_axi_arqos   ) ,
          .s_axi_arvalid              ( s_axi_arvalid ) ,
          .s_axi_arready              ( s_axi_arready ) ,
          .s_axi_rid                  ( s_axi_rid     ) ,
          .s_axi_rdata                ( s_axi_rdata   ) ,
          .s_axi_rresp                ( s_axi_rresp   ) ,
          .s_axi_rlast                ( s_axi_rlast   ) ,
          .s_axi_rvalid               ( s_axi_rvalid  ) ,
          .s_axi_rready               ( s_axi_rready  ) ,
          .m_axi_awaddr               ( m_axi_awaddr  ) ,
          .m_axi_awlen                ( m_axi_awlen_i   ) ,
          .m_axi_awsize               ( m_axi_awsize  ) ,
          .m_axi_awburst              ( m_axi_awburst ) ,
          .m_axi_awlock               ( m_axi_awlock_i  ) ,
          .m_axi_awcache              ( m_axi_awcache ) ,
          .m_axi_awprot               ( m_axi_awprot  ) ,
          .m_axi_awregion             ( m_axi_awregion_i) ,
          .m_axi_awqos                ( m_axi_awqos   ) ,
          .m_axi_awvalid              ( m_axi_awvalid ) ,
          .m_axi_awready              ( m_axi_awready ) ,
          .m_axi_wdata                ( m_axi_wdata   ) ,
          .m_axi_wstrb                ( m_axi_wstrb   ) ,
          .m_axi_wlast                ( m_axi_wlast   ) ,
          .m_axi_wvalid               ( m_axi_wvalid  ) ,
          .m_axi_wready               ( m_axi_wready  ) ,
          .m_axi_bresp                ( m_axi_bresp   ) ,
          .m_axi_bvalid               ( m_axi_bvalid  ) ,
          .m_axi_bready               ( m_axi_bready  ) ,
          .m_axi_araddr               ( m_axi_araddr  ) ,
          .m_axi_arlen                ( m_axi_arlen_i   ) ,
          .m_axi_arsize               ( m_axi_arsize  ) ,
          .m_axi_arburst              ( m_axi_arburst ) ,
          .m_axi_arlock               ( m_axi_arlock_i  ) ,
          .m_axi_arcache              ( m_axi_arcache ) ,
          .m_axi_arprot               ( m_axi_arprot  ) ,
          .m_axi_arregion             ( m_axi_arregion_i) ,
          .m_axi_arqos                ( m_axi_arqos   ) ,
          .m_axi_arvalid              ( m_axi_arvalid ) ,
          .m_axi_arready              ( m_axi_arready ) ,
          .m_axi_rdata                ( m_axi_rdata   ) ,
          .m_axi_rresp                ( m_axi_rresp   ) ,
          .m_axi_rlast                ( m_axi_rlast   ) ,
          .m_axi_rvalid               ( m_axi_rvalid  ) ,
          .m_axi_rready               ( m_axi_rready  )
        );
      end
      
    end else begin : gen_upsizer
      
      if (C_AXI_PROTOCOL == P_AXILITE) begin : gen_lite_upsizer
        
        axi_dwidth_converter_v2_1_12_axi4lite_upsizer #(
          .C_FAMILY                    ( C_FAMILY                    ) ,
          .C_AXI_ADDR_WIDTH            ( C_AXI_ADDR_WIDTH            ) ,
          .C_AXI_SUPPORTS_WRITE        ( C_AXI_SUPPORTS_WRITE        ) ,
          .C_AXI_SUPPORTS_READ         ( C_AXI_SUPPORTS_READ         ) 
        )
        lite_upsizer_inst
        (
          .aresetn                    ( aresetn        ) ,
          .aclk                       ( aclk          ) ,
          .s_axi_awaddr               ( s_axi_awaddr  ) ,
          .s_axi_awprot               ( s_axi_awprot  ) ,
          .s_axi_awvalid              ( s_axi_awvalid ) ,
          .s_axi_awready              ( s_axi_awready ) ,
          .s_axi_wdata                ( s_axi_wdata   ) ,
          .s_axi_wstrb                ( s_axi_wstrb   ) ,
          .s_axi_wvalid               ( s_axi_wvalid  ) ,
          .s_axi_wready               ( s_axi_wready  ) ,
          .s_axi_bresp                ( s_axi_bresp   ) ,
          .s_axi_bvalid               ( s_axi_bvalid  ) ,
          .s_axi_bready               ( s_axi_bready  ) ,
          .s_axi_araddr               ( s_axi_araddr  ) ,
          .s_axi_arprot               ( s_axi_arprot  ) ,
          .s_axi_arvalid              ( s_axi_arvalid ) ,
          .s_axi_arready              ( s_axi_arready ) ,
          .s_axi_rdata                ( s_axi_rdata   ) ,
          .s_axi_rresp                ( s_axi_rresp   ) ,
          .s_axi_rvalid               ( s_axi_rvalid  ) ,
          .s_axi_rready               ( s_axi_rready  ) ,
          .m_axi_awaddr               ( m_axi_awaddr  ) ,
          .m_axi_awprot               ( m_axi_awprot  ) ,
          .m_axi_awvalid              ( m_axi_awvalid ) ,
          .m_axi_awready              ( m_axi_awready ) ,
          .m_axi_wdata                ( m_axi_wdata   ) ,
          .m_axi_wstrb                ( m_axi_wstrb   ) ,
          .m_axi_wvalid               ( m_axi_wvalid  ) ,
          .m_axi_wready               ( m_axi_wready  ) ,
          .m_axi_bresp                ( m_axi_bresp   ) ,
          .m_axi_bvalid               ( m_axi_bvalid  ) ,
          .m_axi_bready               ( m_axi_bready  ) ,
          .m_axi_araddr               ( m_axi_araddr  ) ,
          .m_axi_arprot               ( m_axi_arprot  ) ,
          .m_axi_arvalid              ( m_axi_arvalid ) ,
          .m_axi_arready              ( m_axi_arready ) ,
          .m_axi_rdata                ( m_axi_rdata   ) ,
          .m_axi_rresp                ( m_axi_rresp   ) ,
          .m_axi_rvalid               ( m_axi_rvalid  ) ,
          .m_axi_rready               ( m_axi_rready  )
        );
        
      end else begin : gen_full_upsizer
      
        axi_dwidth_converter_v2_1_12_axi_upsizer #(
          .C_FAMILY                    ( C_FAMILY                    ) ,
          .C_AXI_PROTOCOL              ( C_AXI_PROTOCOL              ) ,
          .C_S_AXI_ID_WIDTH            ( C_S_AXI_ID_WIDTH              ) ,
          .C_SUPPORTS_ID               ( C_SUPPORTS_ID ),
          .C_AXI_ADDR_WIDTH            ( C_AXI_ADDR_WIDTH            ) ,
          .C_S_AXI_DATA_WIDTH          ( C_S_AXI_DATA_WIDTH          ) ,
          .C_M_AXI_DATA_WIDTH          ( C_M_AXI_DATA_WIDTH          ) ,
          .C_AXI_SUPPORTS_WRITE        ( C_AXI_SUPPORTS_WRITE        ) ,
          .C_AXI_SUPPORTS_READ         ( C_AXI_SUPPORTS_READ         ) ,
          .C_FIFO_MODE   (C_FIFO_MODE),
          .C_S_AXI_ACLK_RATIO   (C_S_AXI_ACLK_RATIO),
          .C_M_AXI_ACLK_RATIO   (C_M_AXI_ACLK_RATIO),
          .C_AXI_IS_ACLK_ASYNC   (C_AXI_IS_ACLK_ASYNC),
          .C_PACKING_LEVEL             ( C_PACKING_LEVEL         ),
          .C_SYNCHRONIZER_STAGE (C_SYNCHRONIZER_STAGE)
        )
        axi_upsizer_inst
        (
          .s_axi_aresetn              ( s_axi_aresetn        ) ,
          .s_axi_aclk                 ( s_axi_aclk          ) ,
          .s_axi_awid                 ( s_axi_awid    ) ,
          .s_axi_awaddr               ( s_axi_awaddr  ) ,
          .s_axi_awlen                ( s_axi_awlen_i   ) ,
          .s_axi_awsize               ( s_axi_awsize  ) ,
          .s_axi_awburst              ( s_axi_awburst ) ,
          .s_axi_awlock               ( s_axi_awlock_i  ) ,
          .s_axi_awcache              ( s_axi_awcache ) ,
          .s_axi_awprot               ( s_axi_awprot  ) ,
          .s_axi_awregion             ( s_axi_awregion_i) ,
          .s_axi_awqos                ( s_axi_awqos   ) ,
          .s_axi_awvalid              ( s_axi_awvalid ) ,
          .s_axi_awready              ( s_axi_awready ) ,
          .s_axi_wdata                ( s_axi_wdata   ) ,
          .s_axi_wstrb                ( s_axi_wstrb   ) ,
          .s_axi_wlast                ( s_axi_wlast   ) ,
          .s_axi_wvalid               ( s_axi_wvalid  ) ,
          .s_axi_wready               ( s_axi_wready  ) ,
          .s_axi_bid                  ( s_axi_bid     ) ,
          .s_axi_bresp                ( s_axi_bresp   ) ,
          .s_axi_bvalid               ( s_axi_bvalid  ) ,
          .s_axi_bready               ( s_axi_bready  ) ,
          .s_axi_arid                 ( s_axi_arid    ) ,
          .s_axi_araddr               ( s_axi_araddr  ) ,
          .s_axi_arlen                ( s_axi_arlen_i   ) ,
          .s_axi_arsize               ( s_axi_arsize  ) ,
          .s_axi_arburst              ( s_axi_arburst ) ,
          .s_axi_arlock               ( s_axi_arlock_i  ) ,
          .s_axi_arcache              ( s_axi_arcache ) ,
          .s_axi_arprot               ( s_axi_arprot  ) ,
          .s_axi_arregion             ( s_axi_arregion_i) ,
          .s_axi_arqos                ( s_axi_arqos   ) ,
          .s_axi_arvalid              ( s_axi_arvalid ) ,
          .s_axi_arready              ( s_axi_arready ) ,
          .s_axi_rid                  ( s_axi_rid     ) ,
          .s_axi_rdata                ( s_axi_rdata   ) ,
          .s_axi_rresp                ( s_axi_rresp   ) ,
          .s_axi_rlast                ( s_axi_rlast   ) ,
          .s_axi_rvalid               ( s_axi_rvalid  ) ,
          .s_axi_rready               ( s_axi_rready  ) ,
          .m_axi_aresetn              ( m_axi_aresetn        ) ,
          .m_axi_aclk                 ( m_axi_aclk          ) ,
          .m_axi_awaddr               ( m_axi_awaddr  ) ,
          .m_axi_awlen                ( m_axi_awlen_i   ) ,
          .m_axi_awsize               ( m_axi_awsize  ) ,
          .m_axi_awburst              ( m_axi_awburst ) ,
          .m_axi_awlock               ( m_axi_awlock_i  ) ,
          .m_axi_awcache              ( m_axi_awcache ) ,
          .m_axi_awprot               ( m_axi_awprot  ) ,
          .m_axi_awregion             ( m_axi_awregion_i) ,
          .m_axi_awqos                ( m_axi_awqos   ) ,
          .m_axi_awvalid              ( m_axi_awvalid ) ,
          .m_axi_awready              ( m_axi_awready ) ,
          .m_axi_wdata                ( m_axi_wdata   ) ,
          .m_axi_wstrb                ( m_axi_wstrb   ) ,
          .m_axi_wlast                ( m_axi_wlast   ) ,
          .m_axi_wvalid               ( m_axi_wvalid  ) ,
          .m_axi_wready               ( m_axi_wready  ) ,
          .m_axi_bresp                ( m_axi_bresp   ) ,
          .m_axi_bvalid               ( m_axi_bvalid  ) ,
          .m_axi_bready               ( m_axi_bready  ) ,
          .m_axi_araddr               ( m_axi_araddr  ) ,
          .m_axi_arlen                ( m_axi_arlen_i   ) ,
          .m_axi_arsize               ( m_axi_arsize  ) ,
          .m_axi_arburst              ( m_axi_arburst ) ,
          .m_axi_arlock               ( m_axi_arlock_i  ) ,
          .m_axi_arcache              ( m_axi_arcache ) ,
          .m_axi_arprot               ( m_axi_arprot  ) ,
          .m_axi_arregion             ( m_axi_arregion_i) ,
          .m_axi_arqos                ( m_axi_arqos   ) ,
          .m_axi_arvalid              ( m_axi_arvalid ) ,
          .m_axi_arready              ( m_axi_arready ) ,
          .m_axi_rdata                ( m_axi_rdata   ) ,
          .m_axi_rresp                ( m_axi_rresp   ) ,
          .m_axi_rlast                ( m_axi_rlast   ) ,
          .m_axi_rvalid               ( m_axi_rvalid  ) ,
          .m_axi_rready               ( m_axi_rready  )
        );
      end
    end
  endgenerate
      
endmodule


