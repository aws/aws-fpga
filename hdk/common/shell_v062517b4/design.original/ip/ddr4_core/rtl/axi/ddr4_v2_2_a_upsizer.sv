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
//  /   /         Filename           : ddr4_v2_2_0_a_upsizer.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Apr 17 2014
//  \___\/\___\
//
//Device: UltraScale 
//Design Name: AXI Upsizer
//Purpose:
// Description: Address Up-Sizer
//--------------------------------------------------------------------------
//
// Structure:
//   ddr_a_upsizer
//     generic_baseblocks/*
//
//--------------------------------------------------------------------------
//Reference:
//Revision History:
//*****************************************************************************
`timescale 1ps/1ps


module ddr4_v2_2_0_a_upsizer #
  (
   parameter         C_FAMILY                         = "rtl", 
                       // FPGA Family. Current version: virtex6 or spartan6.
   parameter integer C_AXI_ID_WIDTH                 = 4, 
                       // Width of all ID signals on SI and MI side of converter.
                       // Range: >= 1.
   parameter integer C_AXI_ADDR_WIDTH                 = 32, 
                       // Width of all ADDR signals on SI and MI side of converter.
                       // Range: 32.
   parameter         C_S_AXI_DATA_WIDTH               = 32'h00000020, 
                       // Width of S_AXI_WDATA and S_AXI_RDATA.
                       // Format: Bit32; 
                       // Range: 'h00000020, 'h00000040, 'h00000080, 'h00000100.
   parameter         C_M_AXI_DATA_WIDTH               = 32'h00000040, 
                       // Width of M_AXI_WDATA and M_AXI_RDATA.
                       // Assume greater than or equal to C_S_AXI_DATA_WIDTH.
                       // Format: Bit32;
                       // Range: 'h00000020, 'h00000040, 'h00000080, 'h00000100.
   parameter integer C_M_AXI_REGISTER                 = 0,
                       // Clock output data.
                       // Range: 0, 1
   parameter integer C_AXI_SUPPORTS_USER_SIGNALS      = 0,
                       // 1 = Propagate all USER signals, 0 = Dont propagate.
   parameter integer C_AXI_AUSER_WIDTH                = 1,
                       // Width of AWUSER/ARUSER signals. 
                       // Range: >= 1.
   parameter integer C_AXI_CHANNEL                      = 0,
                       // 0 = AXI AW Channel.
                       // 1 = AXI AR Channel.
   parameter integer C_PACKING_LEVEL                    = 1,
                       // 0 = Never pack (expander only); packing logic is omitted.
                       // 1 = Pack only when CACHE[1] (Modifiable) is high.
                       // 2 = Always pack, regardless of sub-size transaction or Modifiable bit.
                       //     (Required when used as helper-core by mem-con.)
   parameter integer C_SUPPORT_BURSTS                 = 1,
                       // Disabled when all connected masters and slaves are AxiLite,
                       //   allowing logic to be simplified.
   parameter integer C_SINGLE_THREAD                  = 1,
                       // 0 = Ignore ID when propagating transactions (assume all responses are in order).
                       // 1 = Allow multiple outstanding transactions only if the IDs are the same
                       //   to prevent response reordering.
                       //   (If ID mismatches, stall until outstanding transaction counter = 0.)
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
   input  wire                              cmd_ready,
   
   // Slave Interface Write Address Ports
   input  wire [C_AXI_ID_WIDTH-1:0]          S_AXI_AID,
   input  wire [C_AXI_ADDR_WIDTH-1:0]          S_AXI_AADDR,
   input  wire [8-1:0]                         S_AXI_ALEN,
   input  wire [3-1:0]                         S_AXI_ASIZE,
   input  wire [2-1:0]                         S_AXI_ABURST,
   input  wire [2-1:0]                         S_AXI_ALOCK,
   input  wire [4-1:0]                         S_AXI_ACACHE,
   input  wire [3-1:0]                         S_AXI_APROT,
   input  wire [4-1:0]                         S_AXI_AREGION,
   input  wire [4-1:0]                         S_AXI_AQOS,
   input  wire [C_AXI_AUSER_WIDTH-1:0]         S_AXI_AUSER,
   input  wire                                                   S_AXI_AVALID,
   output wire                                                   S_AXI_AREADY,

   // Master Interface Write Address Port
   output wire [C_AXI_ID_WIDTH-1:0]          M_AXI_AID,
   output wire [C_AXI_ADDR_WIDTH-1:0]          M_AXI_AADDR,
   output wire [8-1:0]                         M_AXI_ALEN,
   output wire [3-1:0]                         M_AXI_ASIZE,
   output wire [2-1:0]                         M_AXI_ABURST,
   output wire [2-1:0]                         M_AXI_ALOCK,
   output wire [4-1:0]                         M_AXI_ACACHE,
   output wire [3-1:0]                         M_AXI_APROT,
   output wire [4-1:0]                         M_AXI_AREGION,
   output wire [4-1:0]                         M_AXI_AQOS,
   output wire [C_AXI_AUSER_WIDTH-1:0]         M_AXI_AUSER,
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
  reg  [C_AXI_ID_WIDTH-1:0]           queue_id;
  wire                                id_match;
  wire                                cmd_id_check;
  wire                                s_ready;
  wire                                cmd_full;
  wire                                allow_new_cmd;
  wire                                cmd_push;
  reg                                 cmd_push_block;
  
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
  wire [C_AXI_ID_WIDTH-1:0]           M_AXI_AID_I;
  reg  [C_AXI_ADDR_WIDTH-1:0]         M_AXI_AADDR_I;
  reg  [8-1:0]                        M_AXI_ALEN_I;
  reg  [3-1:0]                        M_AXI_ASIZE_I;
  reg  [2-1:0]                        M_AXI_ABURST_I;
  wire [2-1:0]                        M_AXI_ALOCK_I;
  wire [4-1:0]                        M_AXI_ACACHE_I;
  wire [3-1:0]                        M_AXI_APROT_I;
  wire [4-1:0]                        M_AXI_AREGION_I;
  wire [4-1:0]                        M_AXI_AQOS_I;
  wire [C_AXI_AUSER_WIDTH-1:0]        M_AXI_AUSER_I;
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
    if ( C_SUPPORT_BURSTS == 1 ) begin
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
    end else begin
      mi_word_intra_len = {C_M_AXI_BYTES_LOG{1'b0}};
    end
  end
  
  // Get MI-side length after upsizing.
  always @ *
  begin
    if ( C_SUPPORT_BURSTS == 1 ) begin
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
    end else begin
      upsized_length = 8'b0;
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
    if ( sub_sized_wrap & ( C_SUPPORT_BURSTS == 1 ) ) begin
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
  assign sub_sized_wrap         = access_is_wrap & ( S_AXI_ALEN <= si_maximum_length ) & 
                                  ( C_SUPPORT_BURSTS == 1);
  
  // See if entite burst can fit inside one MI-side word.
  assign cmd_complete_wrap_i    = cmd_modified_i & sub_sized_wrap;
  
  // Detect if this is a packed WRAP (multiple MI-side words).
  assign cmd_packed_wrap_i      = cmd_modified_i & access_is_wrap & ( S_AXI_ALEN > si_maximum_length ) & 
                                  access_is_unaligned & ( C_SUPPORT_BURSTS == 1);
  
  // Get unalignment address bits (including aligning it inside covered area).
  assign cmd_first_word_ii      = S_AXI_AADDR[C_M_AXI_BYTES_LOG-1:0];
  assign cmd_first_word_i       = cmd_first_word_ii & cmd_mask_i & size_mask;
  
  // Generate next word address.
  assign cmd_next_word_ii       = cmd_first_word_ii + cmd_step_ii[C_M_AXI_BYTES_LOG-1:0]; // spyglass disable W164a
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
      assign adjusted_length        = upsized_length + access_need_extra_word; // spyglass disable W164a
          
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
        
        ddr4_v2_2_0_carry_latch_and #
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
      
      ddr4_v2_2_0_carry_and #
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
    if ( C_FAMILY == "rtl" || ( C_SINGLE_THREAD == 0 ) ) begin : USE_RTL_AVALID
      // Only allowed to forward translated command when command queue is ok with it.
      assign M_AXI_AVALID_I = allow_new_cmd & S_AXI_AVALID;
      
    end else begin : USE_FPGA_AVALID
      
      wire sel_s_axi_avalid;
      
      assign sel_s_axi_avalid = S_AXI_AVALID & ~ARESET;
      
      ddr4_v2_2_0_carry_and #
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
  
  assign M_AXI_AID_I      = S_AXI_AID;
  assign M_AXI_ALOCK_I    = S_AXI_ALOCK;
  assign M_AXI_ACACHE_I   = S_AXI_ACACHE;
  assign M_AXI_APROT_I    = S_AXI_APROT;
  assign M_AXI_AREGION_I  = S_AXI_AREGION;
  assign M_AXI_AQOS_I     = S_AXI_AQOS;
  assign M_AXI_AUSER_I    = ( C_AXI_SUPPORTS_USER_SIGNALS ) ? S_AXI_AUSER : {C_AXI_AUSER_WIDTH{1'b0}};
  
  
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
  
  // Keep track of current ID in queue.
  always @ (posedge ACLK) begin
    if (ARESET) begin
      queue_id <= {C_AXI_ID_WIDTH{1'b0}};
    end else begin
      if ( cmd_push ) begin
        // Store ID (it will be matching ID or a "new beginning").
        queue_id <= S_AXI_AID;
      end
    end
  end
  
  // Select RTL or Optimized implementation.
  generate
    if ( C_FAMILY == "rtl" || ( C_SINGLE_THREAD == 0 ) ) begin : USE_RTL_ID_MATCH
      // Check ID to make sure this command is allowed.
      assign id_match       = ( C_SINGLE_THREAD == 0 ) | ( queue_id == S_AXI_AID);
      assign cmd_id_check   = cmd_empty | ( id_match & ~cmd_empty );
      
      // Check if it is allowed to push more commands (ID is allowed and there is room in the queue).
      assign allow_new_cmd  = (~cmd_full & cmd_id_check) | cmd_push_block;
      
      // Push new command when allowed and MI-side is able to receive the command.
      assign cmd_push       = M_AXI_AVALID_I & ~cmd_push_block;
      
    end else begin : USE_FPGA_ID_MATCH
      
      wire cmd_id_check_i;
      wire allow_new_cmd_i;
      wire sel_cmd_id_check;
      wire sel_cmd_push;
      
      ddr4_v2_2_0_comparator #
        (
         .C_FAMILY(C_FAMILY),
         .C_DATA_WIDTH(C_AXI_ID_WIDTH)
         ) id_match_inst
        (
         .CIN(1'b1),
         .A(queue_id),
         .B(S_AXI_AID),
         .COUT(id_match)
         );
         
      assign sel_cmd_id_check = ~cmd_empty;
      
      ddr4_v2_2_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) cmd_id_check_inst_1
        (
         .CIN(id_match),
         .S(sel_cmd_id_check),
         .COUT(cmd_id_check_i)
         );

      ddr4_v2_2_0_carry_or #
        (
         .C_FAMILY(C_FAMILY)
         ) cmd_id_check_inst_2
        (
         .CIN(cmd_id_check_i),
         .S(cmd_empty),
         .COUT(cmd_id_check)
         );
         
      ddr4_v2_2_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) allow_new_cmd_inst_1
        (
         .CIN(cmd_id_check),
         .S(s_ready),
         .COUT(allow_new_cmd_i)
         );

      ddr4_v2_2_0_carry_or #
        (
         .C_FAMILY(C_FAMILY)
         ) allow_new_cmd_inst_2
        (
         .CIN(allow_new_cmd_i),
         .S(cmd_push_block),
         .COUT(allow_new_cmd)
         );
         
      assign sel_cmd_push = ~cmd_push_block;
      
      ddr4_v2_2_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) cmd_push_inst
        (
         .CIN(M_AXI_AVALID_I),
         .S(sel_cmd_push),
         .COUT(cmd_push)
         );

    end
  endgenerate
  
  // Block furter push until command has been forwarded to MI-side.
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
  
  // Instantiated queue.
  generate
    if (C_SUPPORT_BURSTS == 1) begin : USE_BURSTS
      ddr4_v2_2_0_command_fifo #
      (
       .C_FAMILY                    (C_FAMILY),
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
    end else begin : NO_BURSTS
    
      wire [C_M_AXI_BYTES_LOG-1:0]        cmd_first_word_out;
  
      ddr4_v2_2_0_command_fifo #
      (
       .C_FAMILY                    (C_FAMILY),
       .C_ENABLE_S_VALID_CARRY      (1),
       .C_ENABLE_REGISTERED_OUTPUT  (1),
       .C_FIFO_DEPTH_LOG            (C_FIFO_DEPTH_LOG),
       .C_FIFO_WIDTH                (1+C_M_AXI_BYTES_LOG+C_S_AXI_BYTES_LOG+1)
       ) 
       cmd_queue
      (
       .ACLK    (ACLK),
       .ARESET  (ARESET),
       .EMPTY   (cmd_empty),
       .S_MESG  ({cmd_fix_i, cmd_first_word_i, cmd_step_i}),
       .S_VALID (cmd_push),
       .S_READY (s_ready),
       .M_MESG  ({cmd_fix, cmd_first_word_out, cmd_step}),
       .M_VALID (cmd_valid_i),
       .M_READY (cmd_ready)
       );
       
       assign cmd_modified      = ( C_PACKING_LEVEL == C_ALWAYS_PACK ) ? 1'b1 : 1'b0;
       assign cmd_complete_wrap = 1'b0;
       assign cmd_packed_wrap   = 1'b0;
       assign cmd_first_word    = cmd_first_word_out;
       assign cmd_next_word     = cmd_first_word_out;
       assign cmd_last_word     = cmd_first_word_out;
       assign cmd_offset        = {C_M_AXI_BYTES_LOG{1'b0}};
       assign cmd_mask          = {C_M_AXI_BYTES_LOG{1'b1}};
       assign cmd_length        = 8'b0;
    end
  endgenerate

  // Queue is concidered full when not ready.
  assign cmd_full = ~s_ready;
  
  // Assign external signal.
  assign cmd_valid = cmd_valid_i;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // MI-side output handling
  /////////////////////////////////////////////////////////////////////////////
  
  generate
    if ( C_M_AXI_REGISTER ) begin : USE_REGISTER
    
      reg  [C_AXI_ID_WIDTH-1:0]           M_AXI_AID_q;
      reg  [C_AXI_ADDR_WIDTH-1:0]         M_AXI_AADDR_q;
      reg  [8-1:0]                        M_AXI_ALEN_q;
      reg  [3-1:0]                        M_AXI_ASIZE_q;
      reg  [2-1:0]                        M_AXI_ABURST_q;
      reg  [2-1:0]                        M_AXI_ALOCK_q;
      reg  [4-1:0]                        M_AXI_ACACHE_q;
      reg  [3-1:0]                        M_AXI_APROT_q;
      reg  [4-1:0]                        M_AXI_AREGION_q;
      reg  [4-1:0]                        M_AXI_AQOS_q;
      reg  [C_AXI_AUSER_WIDTH-1:0]        M_AXI_AUSER_q;
      reg                                 M_AXI_AVALID_q;
    
      // Register MI-side Data.
      always @ (posedge ACLK) begin
        if (ARESET) begin
          M_AXI_AVALID_q    <= 1'b0;
        end else if ( M_AXI_AREADY_I ) begin
          M_AXI_AVALID_q    <= M_AXI_AVALID_I;
        end

        if ( M_AXI_AREADY_I ) begin
          M_AXI_AID_q       <= M_AXI_AID_I;
          M_AXI_AADDR_q     <= M_AXI_AADDR_I;
          M_AXI_ALEN_q      <= M_AXI_ALEN_I;
          M_AXI_ASIZE_q     <= M_AXI_ASIZE_I;
          M_AXI_ABURST_q    <= M_AXI_ABURST_I;
          M_AXI_ALOCK_q     <= M_AXI_ALOCK_I;
          M_AXI_ACACHE_q    <= M_AXI_ACACHE_I;
          M_AXI_APROT_q     <= M_AXI_APROT_I;
          M_AXI_AREGION_q   <= M_AXI_AREGION_I;
          M_AXI_AQOS_q      <= M_AXI_AQOS_I;
          M_AXI_AUSER_q     <= M_AXI_AUSER_I;
        end
      end
      
      assign M_AXI_AID        = M_AXI_AID_q;
      assign M_AXI_AADDR      = M_AXI_AADDR_q;
      assign M_AXI_ALEN       = M_AXI_ALEN_q;
      assign M_AXI_ASIZE      = M_AXI_ASIZE_q;
      assign M_AXI_ABURST     = M_AXI_ABURST_q;
      assign M_AXI_ALOCK      = M_AXI_ALOCK_q;
      assign M_AXI_ACACHE     = M_AXI_ACACHE_q;
      assign M_AXI_APROT      = M_AXI_APROT_q;
      assign M_AXI_AREGION    = M_AXI_AREGION_q;
      assign M_AXI_AQOS       = M_AXI_AQOS_q;
      assign M_AXI_AUSER      = M_AXI_AUSER_q;
      assign M_AXI_AVALID     = M_AXI_AVALID_q;
      assign M_AXI_AREADY_I = ( M_AXI_AVALID_q & M_AXI_AREADY) | ~M_AXI_AVALID_q;
      
    end else begin : NO_REGISTER
    
      // Combinatorial MI-side Data.
      assign M_AXI_AID      = M_AXI_AID_I;
      assign M_AXI_AADDR    = M_AXI_AADDR_I;
      assign M_AXI_ALEN     = M_AXI_ALEN_I;
      assign M_AXI_ASIZE    = M_AXI_ASIZE_I;
      assign M_AXI_ABURST   = M_AXI_ABURST_I;
      assign M_AXI_ALOCK    = M_AXI_ALOCK_I;
      assign M_AXI_ACACHE   = M_AXI_ACACHE_I;
      assign M_AXI_APROT    = M_AXI_APROT_I;
      assign M_AXI_AREGION  = M_AXI_AREGION_I;
      assign M_AXI_AQOS     = M_AXI_AQOS_I;
      assign M_AXI_AUSER    = M_AXI_AUSER_I;
      assign M_AXI_AVALID   = M_AXI_AVALID_I;
      assign M_AXI_AREADY_I = M_AXI_AREADY;
                          
    end
  endgenerate
  
  
endmodule

