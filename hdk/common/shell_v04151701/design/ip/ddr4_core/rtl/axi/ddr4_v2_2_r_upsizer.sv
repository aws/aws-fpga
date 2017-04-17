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
//  /   /         Filename           : ddr4_v2_2_0_r_upsizer.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Apr 17 2014
//  \___\/\___\
//
//Device: UltraScale
//Design Name: AXI Upsizer
//Purpose:
// Description: Read Data Response Up-Sizer
// Extract SI-side Data from packed and unpacked MI-side data.
//--------------------------------------------------------------------------
//
//Reference:
//Revision History:
//*****************************************************************************

`timescale 1ps/1ps


module ddr4_v2_2_0_r_upsizer #
  (
   parameter         C_FAMILY                         = "rtl", 
                       // FPGA Family. Current version: virtex6 or spartan6.
   parameter integer C_AXI_ID_WIDTH                   = 4, 
                       // Width of all ID signals on SI and MI side of converter.
                       // Range: >= 1.
   parameter         C_S_AXI_DATA_WIDTH               = 32'h00000020, 
                       // Width of S_AXI_WDATA and S_AXI_RDATA.
                       // Format: Bit32; 
                       // Range: 'h00000020, 'h00000040, 'h00000080, 'h00000100.
   parameter         C_M_AXI_DATA_WIDTH               = 32'h00000040, 
                       // Width of M_AXI_WDATA and M_AXI_RDATA.
                       // Assume greater than or equal to C_S_AXI_DATA_WIDTH.
                       // Format: Bit32;
                       // Range: 'h00000020, 'h00000040, 'h00000080, 'h00000100.
   parameter integer C_S_AXI_REGISTER                 = 0,
                       // Clock output data.
                       // Range: 0, 1
   parameter integer C_AXI_SUPPORTS_USER_SIGNALS      = 0,
                       // 1 = Propagate all USER signals, 0 = Dont propagate.
   parameter integer C_AXI_RUSER_WIDTH                = 1,
                       // Width of RUSER signals. 
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
   
   // Slave Interface Read Data Ports
   output wire [C_AXI_ID_WIDTH-1:0]           S_AXI_RID,
   output wire [C_S_AXI_DATA_WIDTH-1:0]    S_AXI_RDATA,
   output wire [2-1:0]                          S_AXI_RRESP,
   output wire                                                    S_AXI_RLAST,
   output wire [C_AXI_RUSER_WIDTH-1:0]          S_AXI_RUSER,
   output wire                                                    S_AXI_RVALID,
   input  wire                                                    S_AXI_RREADY,

   // Master Interface Read Data Ports
   input  wire [C_AXI_ID_WIDTH-1:0]          M_AXI_RID,
   input  wire [C_M_AXI_DATA_WIDTH-1:0]    M_AXI_RDATA,
   input  wire [2-1:0]                         M_AXI_RRESP,
   input  wire                                                   M_AXI_RLAST,
   input  wire [C_AXI_RUSER_WIDTH-1:0]         M_AXI_RUSER,
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
  reg [C_AXI_ID_WIDTH-1:0]        rid_wrap_buffer;
  reg [2-1:0]                     rresp_wrap_buffer;
  reg [C_AXI_RUSER_WIDTH-1:0]     ruser_wrap_buffer;
  
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
  wire [C_AXI_RUSER_WIDTH-1:0]    S_AXI_RUSER_I;
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
      assign cmd_step_i = cmd_step;  // spyglass disable W164a
    end
  endgenerate
  
  generate
    if ( C_FAMILY == "rtl" || ( C_SUPPORT_BURSTS == 0 ) || 
       ( C_PACKING_LEVEL == C_NEVER_PACK ) ) begin : USE_RTL_WORD_COMPLETED
      // Detect when MI-side word is completely used.
      assign word_completed = cmd_valid & 
                              ( ( cmd_fix ) |
                                ( ~cmd_fix & ~cmd_complete_wrap & next_word == {C_M_AXI_BYTES_LOG{1'b0}} ) | 
                                ( ~cmd_fix & last_word & ~use_wrap_buffer ) | 
                                ( ~cmd_modified & ( C_PACKING_LEVEL == C_DEFAULT_PACK ) ) |
                                ( C_PACKING_LEVEL == C_NEVER_PACK ) |
                                ( C_SUPPORT_BURSTS == 0 ) );
      
      // RTL equivalent of optimized partial extressions (address wrap for next word).
      assign word_complete_next_wrap       = ( ~cmd_fix & ~cmd_complete_wrap & next_word == {C_M_AXI_BYTES_LOG{1'b0}} ) | 
                                            ( C_PACKING_LEVEL == C_NEVER_PACK ) |
                                            ( C_SUPPORT_BURSTS == 0 );
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
         
      assign sel_m_axi_rready = cmd_valid & S_AXI_RREADY_I;
      
      ddr4_v2_2_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_next_wrap_ready_inst
        (
         .CIN(word_complete_next_wrap),
         .S(sel_m_axi_rready),
         .COUT(word_complete_next_wrap_ready)
         );
      
      ddr4_v2_2_0_carry_and #
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
      
      ddr4_v2_2_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_last_word_inst
        (
         .CIN(last_word),
         .S(sel_word_complete_last_word),
         .COUT(word_complete_last_word)
         );
      
      assign sel_word_complete_rest = cmd_fix | ( ~cmd_modified & ( C_PACKING_LEVEL == C_DEFAULT_PACK ) );
      
      ddr4_v2_2_0_carry_or #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_rest_inst
        (
         .CIN(word_complete_last_word),
         .S(sel_word_complete_rest),
         .COUT(word_complete_rest)
         );
         
      ddr4_v2_2_0_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) word_complete_rest_ready_inst
        (
         .CIN(word_complete_rest),
         .S(sel_m_axi_rready),
         .COUT(word_complete_rest_ready)
         );
      
      ddr4_v2_2_0_carry_and #
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
    
      ddr4_v2_2_0_carry_latch_and #
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
      assign pre_next_word_i  = ( next_word_i + cmd_step_i );  // spyglass disable W164a
      
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
    if ( C_FAMILY == "rtl" || C_SUPPORT_BURSTS == 0 ) begin : USE_RTL_LAST_WORD
      // Detect last beat in a burst.
      assign last_beat = ( length_counter == 8'b0 );
      
      // Determine if this last word that shall be extracted from this MI-side word.
      assign last_word = ( last_beat & ( current_word == cmd_last_word ) & ~wrap_buffer_available & ( current_word == cmd_last_word ) ) |
                         ( use_wrap_buffer & ( current_word == cmd_last_word ) ) |
                         ( last_beat & ( current_word == cmd_last_word ) & ( C_PACKING_LEVEL == C_NEVER_PACK ) ) |
                         ( C_SUPPORT_BURSTS == 0 );
  
    end else begin : USE_FPGA_LAST_WORD
    
      wire sel_last_word;
      wire last_beat_ii;
      
      
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
      
      if ( C_PACKING_LEVEL != C_NEVER_PACK  ) begin : USE_FPGA_PACK
        // 
        //
        wire sel_last_beat;
        wire last_beat_i;
        
        assign sel_last_beat = ~wrap_buffer_available;
        
        ddr4_v2_2_0_carry_and #
          (
           .C_FAMILY(C_FAMILY)
           ) last_beat_inst_1
          (
           .CIN(last_beat),
           .S(sel_last_beat),
           .COUT(last_beat_i)
           );
  
        ddr4_v2_2_0_carry_or #
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
        
      ddr4_v2_2_0_comparator_sel #
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
      rid_wrap_buffer   <= {C_AXI_ID_WIDTH{1'b0}};
      rresp_wrap_buffer <= 2'b0;
      ruser_wrap_buffer <= {C_AXI_ID_WIDTH{1'b0}};
    end else begin
      if ( store_in_wrap_buffer ) begin
        M_AXI_RDATA_I     <= M_AXI_RDATA;
        rid_wrap_buffer   <= M_AXI_RID;
        rresp_wrap_buffer <= M_AXI_RRESP;
        ruser_wrap_buffer <= M_AXI_RUSER;
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
  assign S_AXI_RID_I    = ( use_wrap_buffer & ( C_SUPPORT_BURSTS == 1 ) ) ? 
                          rid_wrap_buffer :
                          M_AXI_RID;
  assign S_AXI_RRESP_I  = ( use_wrap_buffer & ( C_SUPPORT_BURSTS == 1 ) ) ? 
                          rresp_wrap_buffer :
                          M_AXI_RRESP;
  assign S_AXI_RUSER_I  = ( C_AXI_SUPPORTS_USER_SIGNALS ) ? 
                            ( use_wrap_buffer & ( C_SUPPORT_BURSTS == 1 ) ) ? 
                            ruser_wrap_buffer :
                            M_AXI_RUSER :
                          {C_AXI_RUSER_WIDTH{1'b0}};
                          
  // Data has to be multiplexed.
  generate
    if ( C_RATIO == 1 ) begin : SINGLE_WORD
      assign S_AXI_RDATA_I  = ( use_wrap_buffer & ( C_SUPPORT_BURSTS == 1 ) ) ? 
                              M_AXI_RDATA_I :
                              M_AXI_RDATA;
    end else begin : MULTIPLE_WORD
      // Get the ratio bits (MI-side words vs SI-side words).
      wire [C_RATIO_LOG-1:0]          current_index;
      assign current_index  = current_word_adjusted[C_M_AXI_BYTES_LOG-C_RATIO_LOG +: C_RATIO_LOG];
      
      assign S_AXI_RDATA_I  = ( use_wrap_buffer & ( C_SUPPORT_BURSTS == 1 ) ) ? 
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
      reg  [C_AXI_RUSER_WIDTH-1:0]    S_AXI_RUSER_q;
      reg                             S_AXI_RVALID_q;
      reg                             S_AXI_RREADY_q;
    
      // Register SI-side Data.
      always @ (posedge ACLK) begin
        if (ARESET) begin
          S_AXI_RID_q       <= {C_AXI_ID_WIDTH{1'b0}};
          S_AXI_RDATA_q     <= {C_S_AXI_DATA_WIDTH{1'b0}};
          S_AXI_RRESP_q     <= 2'b0;
          S_AXI_RLAST_q     <= 1'b0;
          S_AXI_RUSER_q     <= {C_AXI_RUSER_WIDTH{1'b0}};
          S_AXI_RVALID_q    <= 1'b0;
        end else begin
          if ( S_AXI_RREADY_I ) begin
            S_AXI_RID_q       <= S_AXI_RID_I;
            S_AXI_RDATA_q     <= S_AXI_RDATA_I;
            S_AXI_RRESP_q     <= S_AXI_RRESP_I;
            S_AXI_RLAST_q     <= S_AXI_RLAST_I;
            S_AXI_RUSER_q     <= S_AXI_RUSER_I;
            S_AXI_RVALID_q    <= S_AXI_RVALID_I;
          end
          
        end
      end
      
      assign S_AXI_RID      = S_AXI_RID_q;
      assign S_AXI_RDATA    = S_AXI_RDATA_q;
      assign S_AXI_RRESP    = S_AXI_RRESP_q;
      assign S_AXI_RLAST    = S_AXI_RLAST_q;
      assign S_AXI_RUSER    = S_AXI_RUSER_q;
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
      assign S_AXI_RUSER    = S_AXI_RUSER_I;
  
    end
  endgenerate
  
  
endmodule

