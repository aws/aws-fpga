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
//  /   /         Filename           : ddr4_v2_2_0_w_upsizer.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Apr 17 2014
//  \___\/\___\
//
//Device: UltraScale
//Design Name: AXI Upsizer
//Purpose:
//
// Description: Write Data Up-Sizer
// Mirror data for simple accesses.
// Merge data for burst.
//--------------------------------------------------------------------------
//Reference:
//Revision History:
//*****************************************************************************
`timescale 1ps/1ps


module ddr4_v2_2_0_w_upsizer #
  (
   parameter         C_FAMILY                         = "rtl", 
                       // FPGA Family. Current version: virtex6 or spartan6.
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
   parameter integer C_AXI_WUSER_WIDTH                = 1,
                       // Width of WUSER signals. 
                       // Range: >= 1.
   parameter integer C_PACKING_LEVEL                    = 1,
                       // 0 = Never pack (expander only); packing logic is omitted.
                       // 1 = Pack only when CACHE[1] (Modifiable) is high.
                       // 2 = Always pack, regardless of sub-size transaction or Modifiable bit.
                       //     (Required when used as helper-core by mem-con.)
   parameter integer C_SUPPORT_BURSTS                 = 1,
                       // Disabled when all connected masters and slaves are AxiLite,
                       //   allowing logic to be simplified.
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
   input  wire [C_AXI_WUSER_WIDTH-1:0]          S_AXI_WUSER,
   input  wire                                                    S_AXI_WVALID,
   output wire                                                    S_AXI_WREADY,

   // Master Interface Write Data Ports
   output wire [C_M_AXI_DATA_WIDTH-1:0]    M_AXI_WDATA,
   output wire [C_M_AXI_DATA_WIDTH/8-1:0]  M_AXI_WSTRB,
   output wire                                                   M_AXI_WLAST,
   output wire [C_AXI_WUSER_WIDTH-1:0]         M_AXI_WUSER,
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
  reg  [C_AXI_WUSER_WIDTH-1:0]    M_AXI_WUSER_II;
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
  reg  [C_AXI_WUSER_WIDTH-1:0]    M_AXI_WUSER_I;
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
      assign cmd_step_i = cmd_step; // spyglass disable W164a
    end
  endgenerate
  
  generate
    if ( C_FAMILY == "rtl" || ( C_SUPPORT_BURSTS == 0 ) || 
       ( C_PACKING_LEVEL == C_NEVER_PACK ) ) begin : USE_RTL_WORD_COMPLETED
      
      // Detect when MI-side word is completely assembled.
      assign word_completed = ( cmd_fix ) |
                              ( ~cmd_fix & ~cmd_complete_wrap & next_word == {C_M_AXI_BYTES_LOG{1'b0}} ) | 
                              ( ~cmd_fix & last_word ) | 
                              ( ~cmd_modified ) |
                              ( C_PACKING_LEVEL == C_NEVER_PACK ) | 
                              ( C_SUPPORT_BURSTS == 0 );
      
      assign word_completed_qualified   = word_completed & cmd_valid & ~store_in_wrap_buffer_enabled;
      
      // RTL equivalent of optimized partial extressions (address wrap for next word).
      assign word_complete_next_wrap        = ( ~cmd_fix & ~cmd_complete_wrap & 
                                                next_word == {C_M_AXI_BYTES_LOG{1'b0}} ) | 
                                              ( C_PACKING_LEVEL == C_NEVER_PACK ) | 
                                              ( C_SUPPORT_BURSTS == 0 );
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
      ddr4_v2_2_0_comparator_sel_static #
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
      
      ddr4_v2_2_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_next_wrap_inst
        (
         .CIN(next_word_wrap),
         .S(sel_word_complete_next_wrap),
         .COUT(word_complete_next_wrap)
         );
         
      assign sel_word_complete_next_wrap_qual = cmd_valid & ~store_in_wrap_buffer_enabled;
      
      ddr4_v2_2_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_next_wrap_valid_inst
        (
         .CIN(word_complete_next_wrap),
         .S(sel_word_complete_next_wrap_qual),
         .COUT(word_complete_next_wrap_qual)
         );
         
      ddr4_v2_2_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_next_wrap_qual_inst
        (
         .CIN(word_complete_next_wrap_qual),
         .S(S_AXI_WVALID),
         .COUT(word_complete_next_wrap_valid)
         );
         
      ddr4_v2_2_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_next_wrap_pop_inst
        (
         .CIN(word_complete_next_wrap_valid),
         .S(M_AXI_WREADY_I),
         .COUT(word_complete_next_wrap_pop)
         );
         
      assign sel_word_complete_next_wrap_stall = ~M_AXI_WREADY_I;
      
      ddr4_v2_2_0_carry_latch_and #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_next_wrap_stall_inst
        (
         .CIN(word_complete_next_wrap_valid),
         .I(sel_word_complete_next_wrap_stall),
         .O(word_complete_next_wrap_stall)
         );
         
      ddr4_v2_2_0_carry_and #
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
      
      ddr4_v2_2_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) last_word_inst_2
        (
         .CIN(last_word_extra_carry),
         .S(sel_last_word),
         .COUT(word_complete_last_word)
         );
      
      assign sel_word_complete_rest = cmd_fix | ~cmd_modified;
      
      ddr4_v2_2_0_carry_or #
        (
         .C_FAMILY(C_FAMILY)
         ) pop_si_data_inst
        (
         .CIN(word_complete_last_word),
         .S(sel_word_complete_rest),
         .COUT(word_complete_rest)
         );
      
      assign sel_word_complete_rest_qual = cmd_valid & ~store_in_wrap_buffer_enabled;
      
      ddr4_v2_2_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_rest_valid_inst
        (
         .CIN(word_complete_rest),
         .S(sel_word_complete_rest_qual),
         .COUT(word_complete_rest_qual)
         );
         
      ddr4_v2_2_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_rest_qual_inst
        (
         .CIN(word_complete_rest_qual),
         .S(S_AXI_WVALID),
         .COUT(word_complete_rest_valid)
         );
         
      ddr4_v2_2_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_rest_pop_inst
        (
         .CIN(word_complete_rest_valid),
         .S(M_AXI_WREADY_I),
         .COUT(word_complete_rest_pop)
         );
         
      assign sel_word_complete_rest_stall = ~M_AXI_WREADY_I;
      
      ddr4_v2_2_0_carry_latch_and #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_rest_stall_inst
        (
         .CIN(word_complete_rest_valid),
         .I(sel_word_complete_rest_stall),
         .O(word_complete_rest_stall)
         );
         
      ddr4_v2_2_0_carry_and #
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
    if ( C_M_AXI_REGISTER == 1 ) begin : USE_REGISTER_SI_POP
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
      assign pre_next_word_i  = ( next_word_i + cmd_step_i ); // spyglass disable W164a
      
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
    if ( C_FAMILY == "rtl" || (C_M_AXI_REGISTER == 1) ) begin : USE_RTL_CURR_WORD
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
    if ( C_FAMILY == "rtl" || C_SUPPORT_BURSTS == 0 ) begin : USE_RTL_LAST_WORD
      // Detect last beat in a burst.
      assign last_beat = ( length_counter == 8'b0 );
      
      // Determine if this last word that shall be assembled into this MI-side word.
      assign last_word = ( cmd_modified & last_beat & ( current_word == cmd_last_word ) ) |
                         ( C_SUPPORT_BURSTS == 0 );
      
    end else begin : USE_FPGA_LAST_WORD
      wire last_beat_curr_word;
      
      ddr4_v2_2_0_comparator_sel_static #
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
      
      ddr4_v2_2_0_comparator_sel #
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
      
      ddr4_v2_2_0_carry_and #
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
    
      ddr4_v2_2_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) last_word_inst2
        (
         .CIN(last_word),
         .S(1'b1),
         .COUT(last_word_carry)
         );

      ddr4_v2_2_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) last_word_inst3
        (
         .CIN(last_word_carry),
         .S(1'b1),
         .COUT(last_word_extra_carry)
         );

      ddr4_v2_2_0_carry_latch_and #
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
  // Handle USER bits:
  // 
  // The USER bits are always propagated from the least significant SI-side 
  // beat to the Up-Sized MI-side data beat. That means:
  // * FIX transactions propagate all USER data (1:1 SI- vs MI-side beat ratio).
  // * INCR transactions uses the first SI-side beat that goes into a MI-side
  //   data word.
  // * WRAP always propagates the USER bits from the most zero aligned SI-side 
  //   data word, regardless if the data is packed or not. For unpacked data 
  //   this would be a 1:1 ratio.
  /////////////////////////////////////////////////////////////////////////////
  
  // Detect first SI-side word per MI-side word.
  assign first_si_in_mi = cmd_fix | 
                          first_word |
                          ~cmd_modified |
                          (cmd_modified & current_word == {C_M_AXI_BYTES_LOG{1'b0}}) |
                          ( C_SUPPORT_BURSTS == 0 );
  
  // Select USER bits combinatorially when expanding or fix.
  always @ *
  begin
    if ( C_AXI_SUPPORTS_USER_SIGNALS ) begin
      if ( first_si_in_mi ) begin
        M_AXI_WUSER_I = S_AXI_WUSER;
      end else begin
        M_AXI_WUSER_I = M_AXI_WUSER_II;
      end
    end else begin
      M_AXI_WUSER_I = {C_AXI_WUSER_WIDTH{1'b0}};
    end
  end
  
  // Capture user bits.
  always @ (posedge ACLK) begin
    if (ARESET) begin
      M_AXI_WUSER_II <= {C_AXI_WUSER_WIDTH{1'b0}};
    end else begin
      if ( first_si_in_mi & pop_si_data ) begin
        M_AXI_WUSER_II <= S_AXI_WUSER;
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
      
      if ( ( C_PACKING_LEVEL == C_NEVER_PACK ) | ( C_SUPPORT_BURSTS == 0 ) ) begin : USE_EXPANDER
        // Expander only functionality.
      
        if ( C_M_AXI_REGISTER == 1 ) begin : USE_REGISTER
            
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
            
            if ( C_M_AXI_REGISTER == 1 ) begin : USE_REGISTER
              
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
             
            if ( C_M_AXI_REGISTER == 1 ) begin : USE_REGISTER
            
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
    if ( C_M_AXI_REGISTER == 1 ) begin : USE_REGISTER
      reg                             M_AXI_WLAST_q;
      reg  [C_AXI_WUSER_WIDTH-1:0]    M_AXI_WUSER_q;
      reg                             M_AXI_WVALID_q;
    
      // Register MI-side Data.
      always @ (posedge ACLK) begin
        if (ARESET) begin
          M_AXI_WLAST_q     <= 1'b0;
          M_AXI_WUSER_q     <= {C_AXI_WUSER_WIDTH{1'b0}};
          M_AXI_WVALID_q    <= 1'b0;
          
        end else begin
          if ( M_AXI_WREADY_I ) begin
            M_AXI_WLAST_q     <= M_AXI_WLAST_I;
            M_AXI_WUSER_q     <= M_AXI_WUSER_I;
            M_AXI_WVALID_q    <= M_AXI_WVALID_I;
          end
          
        end
      end
      
      assign M_AXI_WDATA    = M_AXI_WDATA_I;
      assign M_AXI_WSTRB    = M_AXI_WSTRB_I;
      assign M_AXI_WLAST    = M_AXI_WLAST_q;
      assign M_AXI_WUSER    = M_AXI_WUSER_q;
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
      assign M_AXI_WUSER    = M_AXI_WUSER_I;
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

