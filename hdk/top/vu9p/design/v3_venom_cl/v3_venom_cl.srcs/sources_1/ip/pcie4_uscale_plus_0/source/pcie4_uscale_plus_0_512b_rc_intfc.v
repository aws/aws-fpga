//-----------------------------------------------------------------------------
//
// (c) Copyright 2012-2012 Xilinx, Inc. All rights reserved.
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
//
//-----------------------------------------------------------------------------
//
// Project    : UltraScale+ FPGA PCI Express v4.0 Integrated Block
// File       : pcie4_uscale_plus_0_512b_rc_intfc.v
// Version    : 1.1 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------
`timescale 1ps/1ps
(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie4_uscale_plus_0_512b_rc_intfc #(
   parameter TCQ = 100,
   parameter IMPL_TARGET = "SOFT",
   parameter AXISTEN_IF_EXT_512_INTFC_RAM_STYLE = "SRL",
   parameter AXI4_USER_DATA_WIDTH = 512,
   parameter AXI4_CORE_DATA_WIDTH = 256,
   parameter AXI4_USER_RC_TUSER_WIDTH = 161,                
   parameter AXI4_CORE_RC_TUSER_WIDTH = 75,
   parameter AXI4_USER_RC_TKEEP_WIDTH = 16,
   parameter AXI4_CORE_RC_TKEEP_WIDTH = 8,                
   parameter AXI4_CORE_RC_TREADY_WIDTH = 22,
   parameter PARITY_ENABLE = 0                
     ) 
  (
    input  wire           user_clk2_i // 500 MHz clock for core-facing interfaces
   ,input  wire           user_clk_i // 250 MHz clock for client-facing interfaces
   ,input  wire           user_clk_en_i // User clock enable for clock domain crossing
   ,input  wire           reset_n_user_clk_i // Reset in the user clock domain
   ,input  wire           reset_n_user_clk2_i // Reset in the user clock2 domain
   ,input  wire           link_down_reset_i // Link went down
   // Attributes
   ,input  wire           attr_straddle_en_i // Enable straddle
   ,input  wire           attr_4tlp_straddle_en_i  // Enable 4-tlp straddle
   ,input wire [1:0]      attr_alignment_mode_i // Payload alignment mode
                                                // (00= Dword-aligned, 10 = 128b address-aligned)
   //-----------------------------------------------------------------------------------------------
   // Client-side signals
   //-----------------------------------------------------------------------------------------------
   ,output wire [511:0]   m_axis_rc_tdata_o
   ,output wire           m_axis_rc_tvalid_o
   ,output wire [160:0]   m_axis_rc_tuser_o
   ,output wire           m_axis_rc_tlast_o
   ,output wire [15:0]    m_axis_rc_tkeep_o
   ,input  wire           m_axis_rc_tready_i
   //-----------------------------------------------------------------------------------------------
   // Core-side signals
   //-----------------------------------------------------------------------------------------------
   ,input  wire [255:0]   core_rc_tdata_i
   ,input  wire           core_rc_tvalid_i
   ,input  wire [74:0]    core_rc_tuser_i
   ,input  wire           core_rc_tlast_i
   ,input  wire [7:0]     core_rc_tkeep_i
   ,output wire [21:0]     core_rc_tready_o
   // Completion delivered indications
   ,output reg [1:0]      compl_delivered_o // Completions delivered to user
                                            // 00 = No Compl, 01 = 1 Compl, 11 = 2 Completions
   ,output reg [7:0]      compl_delivered_tag0_o// Tag associated with first delivered Completion
   ,output reg [7:0]      compl_delivered_tag1_o// Tag associated with second delivered Completion
   );

   localparam FIFO_WIDTH = PARITY_ENABLE? (AXI4_CORE_DATA_WIDTH + (AXI4_CORE_RC_TUSER_WIDTH+1) +
                       AXI4_CORE_RC_TKEEP_WIDTH + 1)*2 +2 :
               (AXI4_CORE_DATA_WIDTH + (AXI4_CORE_RC_TUSER_WIDTH+1) + 
                AXI4_CORE_RC_TKEEP_WIDTH + 1)*2 +2 -64;

   localparam TUSER_LOWER_OFFSET = AXI4_CORE_DATA_WIDTH + AXI4_CORE_RC_TKEEP_WIDTH;
   localparam TUSER_UPPER_OFFSET = PARITY_ENABLE? AXI4_CORE_DATA_WIDTH*2 + AXI4_CORE_RC_TKEEP_WIDTH*2 +
                   (AXI4_CORE_RC_TUSER_WIDTH+1) +2:
                   AXI4_CORE_DATA_WIDTH*2 + AXI4_CORE_RC_TKEEP_WIDTH*2 +
                   (AXI4_CORE_RC_TUSER_WIDTH+1) +2 -32;
   
  localparam FIFO_READ_DATA_UPPER_OFFSET = PARITY_ENABLE?
                   AXI4_CORE_DATA_WIDTH + AXI4_CORE_RC_TKEEP_WIDTH + (AXI4_CORE_RC_TUSER_WIDTH+1) +2:
                   AXI4_CORE_DATA_WIDTH + AXI4_CORE_RC_TKEEP_WIDTH + (AXI4_CORE_RC_TUSER_WIDTH+1) +2 -32;
  
  localparam FIFO_READ_TKEEP_UPPER_OFFSET = PARITY_ENABLE?
                    AXI4_CORE_DATA_WIDTH*2 + AXI4_CORE_RC_TKEEP_WIDTH + (AXI4_CORE_RC_TUSER_WIDTH+1) +2:
                                    AXI4_CORE_DATA_WIDTH*2 + AXI4_CORE_RC_TKEEP_WIDTH + (AXI4_CORE_RC_TUSER_WIDTH+1) +2 -32;

   localparam OUTPUT_MUX_IN_DATA_WIDTH = AXI4_USER_DATA_WIDTH +
                     AXI4_USER_RC_TKEEP_WIDTH +
                     AXI4_USER_RC_TUSER_WIDTH + 1;


   (* KEEP = "true" *) reg [AXI4_CORE_RC_TREADY_WIDTH-1:0] core_rc_tready_reg;
   (* KEEP = "true" *) reg core_rc_tready_user_clk2;

   reg [AXI4_CORE_DATA_WIDTH-1:0] core_rc_tdata_reg_upper;
   reg [AXI4_CORE_DATA_WIDTH-1:0] core_rc_tdata_reg_lower;
   reg [AXI4_CORE_RC_TUSER_WIDTH-1:0] core_rc_tuser_reg_upper;
   reg [AXI4_CORE_RC_TUSER_WIDTH-1:0] core_rc_tuser_reg_lower;
   reg                       core_rc_tlast_reg_upper;
   reg                       core_rc_tlast_reg_lower;
   reg [AXI4_CORE_RC_TKEEP_WIDTH-1:0] core_rc_tkeep_reg_upper;
   reg [AXI4_CORE_RC_TKEEP_WIDTH-1:0] core_rc_tkeep_reg_lower;
   reg                       core_rc_tvalid_reg_upper;
   reg                       core_rc_tvalid_reg_lower;

   reg [AXI4_CORE_DATA_WIDTH-1:0] core_rc_tdata_reg_upper_user_clk;
   reg [AXI4_CORE_DATA_WIDTH-1:0] core_rc_tdata_reg_lower_user_clk;
   reg [AXI4_CORE_RC_TUSER_WIDTH-1:0] core_rc_tuser_reg_upper_user_clk;
   reg [AXI4_CORE_RC_TUSER_WIDTH-1:0] core_rc_tuser_reg_lower_user_clk;
   reg                       core_rc_tlast_reg_upper_user_clk;
   reg                       core_rc_tlast_reg_lower_user_clk;
   reg [AXI4_CORE_RC_TKEEP_WIDTH-1:0] core_rc_tkeep_reg_upper_user_clk;
   reg [AXI4_CORE_RC_TKEEP_WIDTH-1:0] core_rc_tkeep_reg_lower_user_clk;
   reg                       core_rc_tvalid_reg_upper_user_clk;
   reg                       core_rc_tvalid_reg_lower_user_clk;
   wire [2:0]                core_rc_eop_ptr_upper;
   wire [2:0]                core_rc_eop_ptr_lower;
   wire [AXI4_CORE_RC_TUSER_WIDTH-1:0] core_rc_tuser_reg_upper_user_clk_int;
   wire [AXI4_CORE_RC_TUSER_WIDTH-1:0] core_rc_tuser_reg_lower_user_clk_int;


   wire                   fifo_almost_full_user_clk;

  reg                       core_rc_pkt_in_progress;
  wire                       core_rc_pkt_in_progress_upper;
  wire                       core_rc_tuser_sop0_lower;
  wire                       core_rc_tuser_sop1_lower;
  wire                       core_rc_tuser_eop0_lower;
  wire                       core_rc_tuser_eop1_lower;
  wire                       core_rc_tuser_sop0_upper;
  wire                       core_rc_tuser_sop1_upper;
  wire                       core_rc_tuser_eop0_upper;
  wire                       core_rc_tuser_eop1_upper;
  
  wire                       core_rc_tuser_reg_sop0_ptr_lower;
  wire                       core_rc_tuser_reg_sop0_ptr_upper;

   wire [FIFO_WIDTH-1:0]           fifo_in_data;
   reg                       fifo_in_data_valid;
   reg                       fifo_read_en;
   wire                   fifo_read_data_valid;
   wire [FIFO_WIDTH-1:0]           fifo_read_data;

   wire                   read_sop0_lower;
   wire                    read_sop0_ptr_lower;
   wire                   read_sop1_lower;
   wire                   read_discontinue_lower;
   wire                    read_eop0_lower;
   wire                    read_eop1_lower;
   wire                    read_eop_lower;
   wire                   read_tlast_lower;
   wire                   read_tlast_upper;
   wire                   read_data_valid_lower;
   wire                   read_data_valid_upper;

   wire                   read_sop0_upper;
   wire                    read_sop0_ptr_upper;
   wire                   read_sop1_upper;
   wire                   read_sop_upper;
   wire                   read_discontinue_upper;
   wire                    read_eop0_upper;
   wire                    read_eop1_upper;
   wire                    read_eop_upper;

   reg [1:0]                   read_data_valid_reg;
   reg [FIFO_WIDTH-1:0]           read_data_reg;
   reg [FIFO_WIDTH/2-1:0]           saved_data_reg;
   reg                       saved_eop;
   reg                       saved_err;
   
   wire [31:0]                   read_data_reg_byte_en_lower;
   wire                    read_data_reg_sop0_lower;
   wire                    read_data_reg_sop0_ptr_lower;
   wire                    read_data_reg_sop1_lower;
   wire                    read_data_reg_discontinue_lower;
   wire [31:0]                   read_data_reg_parity_lower;
   wire                    read_data_reg_eop0_lower;
   wire [2:0]                   read_data_reg_eop0_ptr_lower;
   wire                    read_data_reg_eop1_lower;
   wire [2:0]                   read_data_reg_eop1_ptr_lower;

   wire [31:0]                   read_data_reg_byte_en_upper;
   wire                    read_data_reg_sop0_upper;
   wire                    read_data_reg_sop0_ptr_upper;
   wire                    read_data_reg_sop1_upper;
   wire                    read_data_reg_discontinue_upper;
   wire [31:0]                   read_data_reg_parity_upper;
   wire                    read_data_reg_eop0_upper;
   wire [2:0]                   read_data_reg_eop0_ptr_upper;
   wire                    read_data_reg_eop1_upper;
   wire [2:0]                   read_data_reg_eop1_ptr_upper;

  wire                       read_data_reg_tlast_lower;
  wire                       read_data_reg_tlast_upper;

   wire [63:0]                   read_data_out_byte_en;
   wire [3:0]                   read_data_out_is_sop;
   wire [1:0]                   read_data_out_is_sop0_ptr;
   wire [1:0]                   read_data_out_is_sop1_ptr;
   wire [1:0]                   read_data_out_is_sop2_ptr;
   wire [1:0]                   read_data_out_is_sop3_ptr;
   wire [3:0]                   read_data_out_is_eop;
   wire [3:0]                   read_data_out_is_eop0_ptr;
   wire [3:0]                   read_data_out_is_eop1_ptr;
   wire [3:0]                   read_data_out_is_eop2_ptr;
   wire [3:0]                   read_data_out_is_eop3_ptr;
   wire                   read_data_out_discontinue;
   wire [63:0]                   read_data_out_parity;
   
   wire [ AXI4_USER_RC_TUSER_WIDTH-1:0] read_data_out_tuser;
   wire [ AXI4_USER_DATA_WIDTH-1:0]     read_data_out_tdata;
   wire [ AXI4_USER_RC_TKEEP_WIDTH-1:0] read_data_out_tkeep;
   wire                 read_data_out_tlast;
   
   wire [OUTPUT_MUX_IN_DATA_WIDTH-1:0]     output_mux_in_data;

   wire                 output_mux_ready;
   
  wire [3:0]                 pcie_compl_delivered_user_clk;
  wire [7:0]                 pcie_compl_delivered_tag0_user_clk;
  wire [7:0]                 pcie_compl_delivered_tag1_user_clk;
  wire [7:0]                 pcie_compl_delivered_tag2_user_clk;
  wire [7:0]                 pcie_compl_delivered_tag3_user_clk;

   // Read State Machine states
   localparam                           IDLE = 2'd0;
   localparam                           EXPECT_NEW_WORD = 2'd1;
   localparam                           SEND_SAVED_HALF_WORD = 2'd2;
   localparam                           WAIT_FOR_UPPER_HALF = 2'd3;
   reg [1:0]                 read_state;

   // Capture incoming data from core at 500 MHz into upper and lower registers
   always @(posedge user_clk2_i)
     if (~reset_n_user_clk2_i)
       begin
      core_rc_tdata_reg_upper <= #TCQ {AXI4_CORE_DATA_WIDTH{1'b0}};
      core_rc_tdata_reg_lower <= #TCQ {AXI4_CORE_DATA_WIDTH{1'b0}};
      core_rc_tuser_reg_upper <= #TCQ {AXI4_CORE_RC_TUSER_WIDTH{1'b0}};
      core_rc_tuser_reg_lower <= #TCQ {AXI4_CORE_RC_TUSER_WIDTH{1'b0}};
      core_rc_tkeep_reg_upper <= #TCQ {AXI4_CORE_RC_TKEEP_WIDTH{1'b0}};
      core_rc_tkeep_reg_lower <= #TCQ {AXI4_CORE_RC_TKEEP_WIDTH{1'b0}};
      core_rc_tlast_reg_upper <= #TCQ 1'b0;
      core_rc_tlast_reg_lower <= #TCQ 1'b0;
       core_rc_tvalid_reg_upper <= #TCQ 1'b0;
      core_rc_tvalid_reg_lower <= #TCQ 1'b0;
       end // if (~reset_n_user_clk_i)
     else
       if (user_clk_en_i)
     begin
        core_rc_tdata_reg_lower <= #TCQ core_rc_tdata_i;
        core_rc_tuser_reg_lower <= #TCQ core_rc_tuser_i;
        core_rc_tkeep_reg_lower <= #TCQ core_rc_tkeep_i;
        core_rc_tlast_reg_lower <= #TCQ core_rc_tlast_i;
        core_rc_tvalid_reg_lower <= #TCQ core_rc_tvalid_i & core_rc_tready_user_clk2;
     end
       else
     begin
        core_rc_tdata_reg_upper <= #TCQ core_rc_tdata_i;
        core_rc_tuser_reg_upper <= #TCQ core_rc_tuser_i;
        core_rc_tkeep_reg_upper <= #TCQ core_rc_tkeep_i;
        core_rc_tlast_reg_upper <= #TCQ core_rc_tlast_i;
        core_rc_tvalid_reg_upper <= #TCQ core_rc_tvalid_i & core_rc_tready_user_clk2;
     end // else: !if(user_clk_en_i)

  // Transfer to 250 MHz user_clk domain
     always @(posedge user_clk_i)
     if (~reset_n_user_clk_i)
       begin
     core_rc_tdata_reg_upper_user_clk <= #TCQ {AXI4_CORE_DATA_WIDTH{1'b0}};
     core_rc_tdata_reg_lower_user_clk <= #TCQ {AXI4_CORE_DATA_WIDTH{1'b0}};
     core_rc_tuser_reg_upper_user_clk <= #TCQ {AXI4_CORE_RC_TUSER_WIDTH{1'b0}};
     core_rc_tuser_reg_lower_user_clk <= #TCQ {AXI4_CORE_RC_TUSER_WIDTH{1'b0}};
     core_rc_tkeep_reg_upper_user_clk <= #TCQ {AXI4_CORE_RC_TKEEP_WIDTH{1'b0}};
     core_rc_tkeep_reg_lower_user_clk <= #TCQ {AXI4_CORE_RC_TKEEP_WIDTH{1'b0}};
     core_rc_tlast_reg_upper_user_clk <= #TCQ 1'b0;
     core_rc_tlast_reg_lower_user_clk <= #TCQ 1'b0;
      core_rc_tvalid_reg_upper_user_clk <= #TCQ 1'b0;
     core_rc_tvalid_reg_lower_user_clk <= #TCQ 1'b0;
     fifo_in_data_valid <= #TCQ 1'b0;
       end // if (~reset_n_user_clk_i)
     else
       begin
            core_rc_tdata_reg_upper_user_clk <= #TCQ core_rc_tdata_reg_upper;
     core_rc_tdata_reg_lower_user_clk <= #TCQ core_rc_tdata_reg_lower;
     core_rc_tuser_reg_upper_user_clk <= #TCQ core_rc_tuser_reg_upper;
     core_rc_tuser_reg_lower_user_clk <= #TCQ core_rc_tuser_reg_lower;
     core_rc_tkeep_reg_upper_user_clk <= #TCQ core_rc_tkeep_reg_upper;
     core_rc_tkeep_reg_lower_user_clk <= #TCQ core_rc_tkeep_reg_lower;
     core_rc_tlast_reg_upper_user_clk <= #TCQ core_rc_tlast_reg_upper;
     core_rc_tlast_reg_lower_user_clk <= #TCQ core_rc_tlast_reg_lower;
      core_rc_tvalid_reg_upper_user_clk <= #TCQ core_rc_tvalid_reg_upper;
     core_rc_tvalid_reg_lower_user_clk <= #TCQ core_rc_tvalid_reg_lower;
     fifo_in_data_valid <= #TCQ core_rc_tvalid_reg_upper | core_rc_tvalid_reg_lower;
       end // else: !if(~reset_n_user_clk_i)
  
  assign core_rc_eop_ptr_lower   = (core_rc_tkeep_reg_lower_user_clk[7])? 3'd7:
                                   (core_rc_tkeep_reg_lower_user_clk[6])? 3'd6:
                                   (core_rc_tkeep_reg_lower_user_clk[5])? 3'd5:
                                   (core_rc_tkeep_reg_lower_user_clk[4])? 3'd4:
                                   (core_rc_tkeep_reg_lower_user_clk[3])? 3'd3:
                                   (core_rc_tkeep_reg_lower_user_clk[2])? 3'd2:
                                   (core_rc_tkeep_reg_lower_user_clk[1])? 3'd1: 3'd0;
  assign core_rc_eop_ptr_upper   = (core_rc_tkeep_reg_upper_user_clk[7])? 3'd7:
                                   (core_rc_tkeep_reg_upper_user_clk[6])? 3'd6:
                                   (core_rc_tkeep_reg_upper_user_clk[5])? 3'd5:
                                   (core_rc_tkeep_reg_upper_user_clk[4])? 3'd4:
                                   (core_rc_tkeep_reg_upper_user_clk[3])? 3'd3:
                                   (core_rc_tkeep_reg_upper_user_clk[2])? 3'd2:
                                   (core_rc_tkeep_reg_upper_user_clk[1])? 3'd1: 3'd0;
  assign core_rc_tuser_reg_lower_user_clk_int   = (~attr_4tlp_straddle_en_i)? {core_rc_tuser_reg_lower_user_clk[AXI4_CORE_RC_TUSER_WIDTH-1:42],
                                                                               4'd0,   // [41:38], is_eop_1[3:0]
                                                                               core_rc_eop_ptr_lower, // [37:35]
                                                                               core_rc_tlast_reg_lower_user_clk,  // [34]
                                                                               1'b0,   // [33], is_sop_1
                                                                               core_rc_tuser_reg_lower_user_clk[32:0]}:
                                                                              core_rc_tuser_reg_lower_user_clk;
  assign core_rc_tuser_reg_upper_user_clk_int   = (~attr_4tlp_straddle_en_i)? {core_rc_tuser_reg_upper_user_clk[AXI4_CORE_RC_TUSER_WIDTH-1:42],
                                                                               4'd0,   // [41:38], is_eop_1[3:0]
                                                                               core_rc_eop_ptr_upper, // [37:35]
                                                                               core_rc_tlast_reg_upper_user_clk,  // [34]
                                                                               1'b0,   // [33], is_sop_1
                                                                               core_rc_tuser_reg_upper_user_clk[32:0]}:
                                                                              core_rc_tuser_reg_upper_user_clk;
  // Generate SOP0 Pointer for lower and upper halves.
  // This requires keeping track of whether a packet is continuing from the last beat.
  assign core_rc_tuser_sop0_lower = core_rc_tuser_reg_lower_user_clk_int[32];
  assign core_rc_tuser_sop1_lower = core_rc_tuser_reg_lower_user_clk_int[33];
  assign core_rc_tuser_eop0_lower = core_rc_tuser_reg_lower_user_clk_int[34];
  assign core_rc_tuser_eop1_lower = core_rc_tuser_reg_lower_user_clk_int[38];

  assign core_rc_tuser_sop0_upper = core_rc_tuser_reg_upper_user_clk_int[32];
  assign core_rc_tuser_sop1_upper = core_rc_tuser_reg_upper_user_clk_int[33];
  assign core_rc_tuser_eop0_upper = core_rc_tuser_reg_upper_user_clk_int[34];
  assign core_rc_tuser_eop1_upper = core_rc_tuser_reg_upper_user_clk_int[38];

  always @(posedge user_clk_i)
    if (~reset_n_user_clk_i)
      core_rc_pkt_in_progress <= #TCQ 1'b0;
    else if (link_down_reset_i)
      core_rc_pkt_in_progress <= #TCQ 1'b0;
    else
      if (~core_rc_pkt_in_progress)
    begin
      case({core_rc_tvalid_reg_upper_user_clk, core_rc_tvalid_reg_lower_user_clk})
        2'b00:
          begin
          end
        2'b01:
          begin
        core_rc_pkt_in_progress <= #TCQ 1'b0;
          end
        2'b10:
          begin
        core_rc_pkt_in_progress <= #TCQ ~core_rc_tuser_eop0_upper |
                       (core_rc_tuser_sop1_upper & ~core_rc_tuser_eop1_upper);
          end
        2'b11:
          begin
        core_rc_pkt_in_progress <= #TCQ ((~core_rc_tuser_eop0_lower |
                          (core_rc_tuser_sop1_lower & ~core_rc_tuser_eop1_lower)) &
                          (~core_rc_tuser_eop0_upper |
                           (core_rc_tuser_sop0_upper & ~core_rc_tuser_eop1_upper))) |
                       (((core_rc_tuser_eop0_lower & ~core_rc_tuser_sop1_lower) |
                         core_rc_tuser_eop1_lower) &
                        (~core_rc_tuser_eop0_upper |
                         (core_rc_tuser_sop1_upper & ~core_rc_tuser_eop1_upper)));
          end // case: 2'b11
      endcase // case({core_rc_tvalid_reg_upper_user_clk, core_rc_tvalid_reg_lower_user_clk})
    end // if (~core_rc_pkt_in_progress)
      else
      begin      
      case({core_rc_tvalid_reg_upper_user_clk, core_rc_tvalid_reg_lower_user_clk})
        2'b00:
          begin
          end
        2'b01:
          begin
        core_rc_pkt_in_progress <= #TCQ 1'b0;
          end
        2'b10:
          begin
        // Invalid case
        core_rc_pkt_in_progress <= #TCQ 1'b0;
          end
         2'b11:
           begin
         core_rc_pkt_in_progress <= #TCQ ((~core_rc_tuser_eop0_lower |
                           (core_rc_tuser_sop0_lower & ~core_rc_tuser_eop1_lower)) &
                          (~core_rc_tuser_eop0_upper |
                           (core_rc_tuser_sop0_upper & ~core_rc_tuser_eop1_upper))) |
                        (((core_rc_tuser_eop0_lower & ~core_rc_tuser_sop0_lower) |
                          core_rc_tuser_eop1_lower) &
                         (~core_rc_tuser_eop0_upper |
                          (core_rc_tuser_sop1_upper & ~core_rc_tuser_eop1_upper)));
           end // case: 2'b11
      endcase // case({core_rc_tvalid_reg_upper_user_clk, core_rc_tvalid_reg_lower_user_clk})
    end // else: !if(~core_rc_pkt_in_progress)

  assign core_rc_pkt_in_progress_upper = ~core_rc_tvalid_reg_lower_user_clk? 1'b0:
                     core_rc_pkt_in_progress? (~core_rc_tuser_eop0_lower |
                                   (core_rc_tuser_sop0_lower & ~core_rc_tuser_eop1_lower)):
                     (~core_rc_tuser_eop0_lower |
                      (core_rc_tuser_sop1_lower & ~core_rc_tuser_eop1_lower));

  assign core_rc_tuser_reg_sop0_ptr_lower = ~attr_straddle_en_i? 1'b0:
     core_rc_pkt_in_progress? 
     core_rc_tvalid_reg_lower_user_clk & core_rc_tuser_sop0_lower : 1'b0;

  assign core_rc_tuser_reg_sop0_ptr_upper = ~attr_straddle_en_i? 1'b0:
     core_rc_pkt_in_progress_upper? 
         core_rc_tvalid_reg_upper_user_clk & core_rc_tuser_sop0_upper : 1'b0;
  
   // Write data into FIFO using 250 MHz user_clk

  generate
    if (PARITY_ENABLE)
      assign fifo_in_data =
          {
       core_rc_tvalid_reg_upper_user_clk,
       core_rc_tlast_reg_upper_user_clk,
       core_rc_tuser_reg_sop0_ptr_upper, 
       core_rc_tuser_reg_upper_user_clk_int,
       core_rc_tkeep_reg_upper_user_clk,
       core_rc_tdata_reg_upper_user_clk,
       core_rc_tvalid_reg_lower_user_clk,
       core_rc_tlast_reg_lower_user_clk,
       core_rc_tuser_reg_sop0_ptr_lower, 
       core_rc_tuser_reg_lower_user_clk_int,
       core_rc_tkeep_reg_lower_user_clk,
       core_rc_tdata_reg_lower_user_clk
       };
    else
      assign fifo_in_data =
          {
       core_rc_tvalid_reg_upper_user_clk,
       core_rc_tlast_reg_upper_user_clk,
       core_rc_tuser_reg_sop0_ptr_upper, 
       core_rc_tuser_reg_upper_user_clk_int[42:0],
       core_rc_tkeep_reg_upper_user_clk,
       core_rc_tdata_reg_upper_user_clk,
       core_rc_tvalid_reg_lower_user_clk,
       core_rc_tlast_reg_lower_user_clk,
       core_rc_tuser_reg_sop0_ptr_lower, 
       core_rc_tuser_reg_lower_user_clk_int[42:0],
       core_rc_tkeep_reg_lower_user_clk,
       core_rc_tdata_reg_lower_user_clk
       };
  endgenerate

   // Generate ready to core in the user_clk2 domain
   always @(posedge user_clk2_i)
     if (~reset_n_user_clk2_i)
       begin
      core_rc_tready_user_clk2 <= #TCQ 1'b0;
      core_rc_tready_reg <= #TCQ {AXI4_CORE_RC_TREADY_WIDTH{1'b0}};
       end
     else
       begin
             core_rc_tready_user_clk2 <= #TCQ ~fifo_almost_full_user_clk;
      core_rc_tready_reg <= #TCQ {AXI4_CORE_RC_TREADY_WIDTH{~fifo_almost_full_user_clk}};
       end

   assign core_rc_tready_o = core_rc_tready_reg;
 

   // Main FIFO instance
   pcie4_uscale_plus_0_512b_sync_fifo #
     (
      .TCQ(TCQ),
      .IMPL_TARGET(IMPL_TARGET),
      .AXISTEN_IF_EXT_512_INTFC_RAM_STYLE(AXISTEN_IF_EXT_512_INTFC_RAM_STYLE),
      .FIFO_WIDTH(FIFO_WIDTH),
      .FIFO_DEPTH(8),
      .FIFO_ALMOST_FULL_THRESHOLD(5)
      )
     pcie_4_0_512b_sync_fifo_blk
       (
        .clk_i(user_clk_i),
        .reset_n_i(reset_n_user_clk_i),
        .link_down_reset_i(link_down_reset_i),
    .write_data_i(fifo_in_data),
    .write_en_i(fifo_in_data_valid),
    .read_en_i(fifo_read_en),
    .read_data_o(fifo_read_data),
    .read_data_valid_o(fifo_read_data_valid),
    .fifo_almost_full(fifo_almost_full_user_clk)
    );
   
   // Read-side logic

   assign read_sop0_lower = fifo_read_data[TUSER_LOWER_OFFSET + 32];
   assign read_sop1_lower = fifo_read_data[TUSER_LOWER_OFFSET + 33];
   assign  read_eop0_lower = fifo_read_data[TUSER_LOWER_OFFSET + 34];
   assign  read_eop1_lower = fifo_read_data[TUSER_LOWER_OFFSET + 38];
   assign read_discontinue_lower = fifo_read_data[TUSER_LOWER_OFFSET + 42];

   assign read_sop0_upper = fifo_read_data[TUSER_UPPER_OFFSET + 32];
   assign read_sop1_upper = fifo_read_data[TUSER_UPPER_OFFSET + 33];
   assign  read_eop0_upper = fifo_read_data[TUSER_UPPER_OFFSET + 34];
   assign  read_eop1_upper = fifo_read_data[TUSER_UPPER_OFFSET + 38];
   assign read_discontinue_upper = fifo_read_data[TUSER_UPPER_OFFSET + 42];

  generate
    if (PARITY_ENABLE)
      begin
    assign read_sop0_ptr_lower = fifo_read_data[TUSER_LOWER_OFFSET + AXI4_CORE_RC_TUSER_WIDTH];
    assign read_sop0_ptr_upper = fifo_read_data[TUSER_UPPER_OFFSET + AXI4_CORE_RC_TUSER_WIDTH];
    assign read_tlast_lower = fifo_read_data[AXI4_CORE_DATA_WIDTH + AXI4_CORE_RC_TKEEP_WIDTH +
                         AXI4_CORE_RC_TUSER_WIDTH+1];
    assign read_tlast_upper = fifo_read_data[AXI4_CORE_DATA_WIDTH*2 + AXI4_CORE_RC_TKEEP_WIDTH*2 +
                         (AXI4_CORE_RC_TUSER_WIDTH+1)*2 +2];
      end
    else
      begin
    assign read_sop0_ptr_lower = fifo_read_data[TUSER_LOWER_OFFSET + AXI4_CORE_RC_TUSER_WIDTH-32];
    assign read_sop0_ptr_upper = fifo_read_data[TUSER_UPPER_OFFSET + AXI4_CORE_RC_TUSER_WIDTH-64];
    assign read_tlast_lower = fifo_read_data[AXI4_CORE_DATA_WIDTH + AXI4_CORE_RC_TKEEP_WIDTH +
                         (AXI4_CORE_RC_TUSER_WIDTH+1) -32];
    assign read_tlast_upper = fifo_read_data[AXI4_CORE_DATA_WIDTH*2 + AXI4_CORE_RC_TKEEP_WIDTH*2 +
                         (AXI4_CORE_RC_TUSER_WIDTH+1)*2 +2 -64];
      end // else: !if(PARITY_ENABLE)
  endgenerate

    assign        read_data_valid_lower = fifo_read_data[FIFO_WIDTH/2-1] & fifo_read_data_valid;
    assign        read_data_valid_upper = fifo_read_data[FIFO_WIDTH-1] & fifo_read_data_valid;

  assign        read_sop_upper = read_sop0_upper;

  assign        read_eop_lower = ~attr_straddle_en_i? read_tlast_lower:
           ~read_sop0_lower? // No new TLP starting
           read_eop0_lower:
           (read_sop0_lower & ~read_sop0_ptr_lower)? // New TLP starting on DW 0
           ((read_eop0_lower & ~read_sop1_lower) | read_eop1_lower):
           (read_sop0_lower & read_sop0_ptr_lower)? // TLP contiuning from last beat, new TLP starting on DW 4
           read_eop1_lower: 1'b0;
  
  assign        read_eop_upper = ~attr_straddle_en_i? read_tlast_upper:
           ~read_sop0_upper? // No new TLP starting
           read_eop0_upper:
           (read_sop0_upper & ~read_sop0_ptr_upper)? // New TLP starting on DW 0
           ((read_eop0_upper & ~read_sop1_upper) | read_eop1_upper):
           (read_sop0_upper & read_sop0_ptr_upper)? // TLP contiuning from last beat, new TLP starting on DW 4
           read_eop1_upper: 1'b0;

   // Read State Machine States
   //
   // IDLE: Currently not forwarding a packet.  Read data register is either empty, or contains the last beat of a packet.
   // EXPECT_NEW_WORD: Currently forwarding a packet, and there is no data saved from a previous beat
   // SEND_SAVED_HALF_WORD: There is a half-word saved from a previous beat in the saved data register.
   // WAIT_FOR_UPPER_HALF: There is a half-word saved from a previous beat in the read data register which does not end with an EOP.
   
   always @(posedge user_clk_i)
     if (~reset_n_user_clk_i)
       begin
      read_data_valid_reg <= #TCQ 2'b00;
      read_state <= #TCQ IDLE;
       end
     else if (link_down_reset_i)
       begin
      read_data_valid_reg <= #TCQ 2'b00;
      read_state <= #TCQ IDLE;
       end
     else
    case(read_state)
      IDLE:
        begin
           // IDLE: Currently not forwarding a packet.  Read data register is either empty, or contains the last beat of a packet.
           if ((read_data_valid_reg == 2'b00) | output_mux_ready)
         begin
            if (read_data_valid_lower)
              // New TLP starting in the lower half of the incoming word.
              // Update the lower half of the data register with the lower half of the incoming word.
              begin
             if (read_data_valid_upper)
               // Both halves of the incoming word have valid data in them.
               begin
                  // If straddle is not enabled and the packet in the upper half is a new one,
                  // Save it for next cycle.
                  // Also, if the packet in the lower half ends with an error, do not fill the upper half.
                  if ((~attr_straddle_en_i & read_sop_upper)|
                  read_discontinue_lower)
                begin
                   read_data_valid_reg <= #TCQ 2'b01;
                   read_state <= #TCQ SEND_SAVED_HALF_WORD;
                end
                  else
                begin
                   read_data_valid_reg <= #TCQ 2'b11;
                  if (read_eop_upper)
                     read_state <= #TCQ IDLE;
                   else
                     read_state <= #TCQ EXPECT_NEW_WORD;
                end // else: !if(~attr_straddle_en_i & read_sop_upper)
               end // if (read_data_valid_upper)
             else
               begin
                  // New TLP started in the lower half, but there is no valid data in the upper half.
                  if (read_eop_lower)
                // We have a complete TLP in the lower half, send it.
                begin
                   read_data_valid_reg <= #TCQ 2'b01;
                   read_state <= #TCQ IDLE;
                end
                  else
                begin
                   // Wait for more data to fill upper half of read data register.
                   read_data_valid_reg <= #TCQ 2'b00;
                   read_state <= #TCQ WAIT_FOR_UPPER_HALF;
                end // else: !if(read_eop_lower)
               end // else: !if(read_data_valid_upper)
              end // if (read_data_valid_lower)
            else
              if (read_data_valid_upper)
            begin
               // No valid data in the lower half of the incoming word, but there is a packet starting in the upper half.
               if (read_eop_upper)
                 // We have a complete packet, send it in the lower half.
                 begin
                read_data_valid_reg <= #TCQ 2'b01;
                read_state <= #TCQ IDLE;
                 end
               else
                 begin
                // Save the upper half of the incoming word
                // and wait for more data.
                read_data_valid_reg <= #TCQ 2'b00;
                read_state <= #TCQ WAIT_FOR_UPPER_HALF;
                 end // else: !if(read_eop_upper)
            end // if (read_data_valid_upper)
              else
            // No valid data from FIFO
            begin
               if (output_mux_ready)
                 read_data_valid_reg <= #TCQ 2'b00;
               read_state <= #TCQ IDLE;
            end // else: !if(read_data_valid_upper)
         end // if ((read_data_valid_reg == 2'b00) | output_mux_ready)
        end // case: IDLE
      
      EXPECT_NEW_WORD:
        begin
           // Currently forwarding a packet.  There is no saved data.
           if ((read_data_valid_reg == 2'b00) | output_mux_ready)
         begin
            if (read_data_valid_lower)
              // New data starting in the lower half of the incoming word.
              // Update the lower half of the data register with the lower half of the incoming word.
              begin
             if (read_data_valid_upper)
               // Both halves of the incoming word have valid data in them.
               begin
                  // If straddle is not enabled and the packet in the upper half is a new one,
                  // Save it for next cycle.
                  // Also, if the packet in the lower half ends with an error, do not fill the upper half.
                  if ((~attr_straddle_en_i & read_sop_upper)|
                  read_discontinue_lower)
                begin
                   read_data_valid_reg <= #TCQ 2'b01;
                   read_state <= #TCQ SEND_SAVED_HALF_WORD;
                end
                  else
                begin
                   read_data_valid_reg <= #TCQ 2'b11;
                  if (read_eop_upper)
                     read_state <= #TCQ IDLE;
                  else
                     read_state <= #TCQ EXPECT_NEW_WORD;
                end // else: !if((~attr_straddle_en_i & read_sop_upper)|...
               end // if (read_data_valid_upper)
             else
               begin
                  // Valid data in the lower half, but no valid data in the upper half.
                  if (read_eop_lower)
                // We have the packet ending in the lower half, send it.
                begin
                   read_data_valid_reg <= #TCQ 2'b01;
                   read_state <= #TCQ IDLE;
                end
                  else
                begin
                   // Wait for more data to fill upper half of read data register.
                   read_data_valid_reg <= #TCQ 2'b00;
                   read_state <= #TCQ WAIT_FOR_UPPER_HALF;
                end // else: !if(read_eop_lower)
               end // else: !if(read_data_valid_upper)
              end // if (read_data_valid_lower)
            else
              if (read_data_valid_upper)
            begin
               // No valid data in the lower half of the incoming word, but there is data in the upper half.
               if (read_eop_upper)
                 // We have a complete packet, send it in the lower half.
                 begin
                read_data_valid_reg <= #TCQ 2'b01;
                read_state <= #TCQ IDLE;
                 end
               else
                 begin
                // Save the upper half of the incoming word
                // and wait for more data.
                read_data_valid_reg <= #TCQ 2'b00;
                read_state <= #TCQ WAIT_FOR_UPPER_HALF;
                 end // else: !if(read_eop_upper)
            end // if (read_data_valid_upper)
              else
            // No valid data from FIFO
            begin
               if (output_mux_ready)
                 read_data_valid_reg <= #TCQ 2'b00;
               read_state <= #TCQ EXPECT_NEW_WORD;
            end // else: !if(read_data_valid_upper)
         end // if ((read_data_valid_reg == 2'b00) | output_mux_ready)
        end // case: EXPECT_NEW_WORD

      SEND_SAVED_HALF_WORD:
        begin
           // There is a half-word saved from a previous beat in the saved data register.
           if ((read_data_valid_reg == 2'b00) | output_mux_ready)
         begin
            if ((~attr_straddle_en_i & saved_eop) | saved_err)
              // Saved data is the last beat of a packet and straddle is disabled.
              // Do not fill the upper half of read data register.
              begin
            read_data_valid_reg <= #TCQ 2'b01;
            read_state <= #TCQ IDLE;
              end
            else
              if (read_data_valid_lower)
            // New data starting in the lower half of the incoming word.
            // Update the upper half of the data register with the lower half of the incoming word.
            begin
               if (read_data_valid_upper)
                 // Both halves of the incoming word have valid data in them.
                 begin
                read_data_valid_reg <= #TCQ 2'b11;
                read_state <= #TCQ SEND_SAVED_HALF_WORD;
                 end
               else
                 begin
                read_data_valid_reg <= #TCQ 2'b11;
                if (read_eop_lower)
                  read_state <= #TCQ IDLE;
                else
                  read_state <= #TCQ EXPECT_NEW_WORD;
                 end // else: !if(read_data_valid_upper)
            end // if (read_data_valid_lower)
              else
            if (read_data_valid_upper)
              begin
                 // No valid data in the lower half of the incoming word, but there is data in the upper half.
                 if (read_eop_upper)
                   // We have a complete packet, send it in the upper half.
                   begin
                  read_data_valid_reg <= #TCQ 2'b11;
                  read_state <= #TCQ IDLE;
                   end
                 else
                   begin
                  read_data_valid_reg <= #TCQ 2'b11;
                  read_state <= #TCQ EXPECT_NEW_WORD;
                   end // else: !if(read_eop_upper)
              end // if (read_data_valid_upper)
            else
              // No valid data from FIFO
              begin
                read_data_valid_reg <= #TCQ 2'b01;
                read_state <= #TCQ IDLE;
              end // else: !if(read_data_valid_upper)
         end // if ((read_data_valid_reg == 2'b00) | output_mux_ready)
        end // case: SEND_SAVED_HALF_WORD

      WAIT_FOR_UPPER_HALF:
        begin
           // There is a half-word saved from a previous beat in the read data register which does not end with an EOP.
           if ((read_data_valid_reg == 2'b00) | output_mux_ready)
         begin
            if (read_data_valid_lower)
              // New data starting in the lower half of the incoming word.
              // Update the upper half of the data register with the lower half of the incoming word.
              begin
             read_data_valid_reg <= #TCQ 2'b11;
             if (read_data_valid_upper)
               // Both halves of the incoming word have valid data in them.
               begin
                 if (read_eop_upper)
                   read_state <= #TCQ SEND_SAVED_HALF_WORD;
                 else
                   read_state <= #TCQ WAIT_FOR_UPPER_HALF;
               end
             else
               begin
                 if (read_eop_lower)
                   read_state <= #TCQ IDLE;
                 else
                   read_state <= #TCQ EXPECT_NEW_WORD;
               end // else: !if(read_data_valid_upper)
              end // if (read_data_valid_lower)
            else
              if (read_data_valid_upper)
            begin
               // No valid data in the lower half of the incoming word, but there is data in the upper half.
               read_data_valid_reg <= #TCQ 2'b11;
               if (read_eop_upper)
                 read_state <= #TCQ IDLE;
               else
                 read_state <= #TCQ EXPECT_NEW_WORD;
            end // if (read_data_valid_upper)
              else
            begin
               read_data_valid_reg <= #TCQ 2'b00;
               read_state <= #TCQ WAIT_FOR_UPPER_HALF;
            end // else: !if(read_data_valid_upper)
         end // if ((read_data_valid_reg == 2'b00) | output_mux_ready)
        end // case: WAIT_FOR_UPPER_HALF
    endcase // case(read_state)

   always @(posedge user_clk_i)
     if (~reset_n_user_clk_i)
       begin
      read_data_reg <= #TCQ {FIFO_WIDTH{1'b0}};
      saved_data_reg <= #TCQ {FIFO_WIDTH/2{1'b0}};
      saved_eop <= #TCQ 1'b0;
      saved_err <= #TCQ 1'b0;
       end
     else
    case(read_state)
      IDLE:
        begin
           // IDLE: Currently not forwarding a packet.  Read data register is either empty, or contains the last beat of a packet.
           if ((read_data_valid_reg == 2'b00) | output_mux_ready)
         begin
            if (read_data_valid_lower)
              read_data_reg[FIFO_WIDTH/2-1:0] <= #TCQ fifo_read_data[FIFO_WIDTH/2-1:0];
            else
              read_data_reg[FIFO_WIDTH/2-1:0] <= #TCQ fifo_read_data[FIFO_WIDTH-1: FIFO_WIDTH/2];
            read_data_reg[FIFO_WIDTH-1: FIFO_WIDTH/2] <= #TCQ fifo_read_data[FIFO_WIDTH-1: FIFO_WIDTH/2];
            saved_data_reg <= #TCQ fifo_read_data[FIFO_WIDTH-1:FIFO_WIDTH/2];
            saved_eop <= #TCQ read_eop_upper;
            saved_err <= #TCQ read_discontinue_upper;
         end
        end // case: IDLE

      EXPECT_NEW_WORD:
        begin
           // Currently not forwarding a packet.  
           // Read data register is either empty, or contains the last beat of a packet.           
           if ((read_data_valid_reg == 2'b00) | output_mux_ready)
         begin
            if (read_data_valid_lower)
              read_data_reg[FIFO_WIDTH/2-1:0] <= #TCQ fifo_read_data[FIFO_WIDTH/2-1:0];
            else
              read_data_reg[FIFO_WIDTH/2-1:0] <= #TCQ fifo_read_data[FIFO_WIDTH-1: FIFO_WIDTH/2];
            read_data_reg[FIFO_WIDTH-1: FIFO_WIDTH/2] <= #TCQ fifo_read_data[FIFO_WIDTH-1: FIFO_WIDTH/2];
            saved_data_reg <= #TCQ fifo_read_data[FIFO_WIDTH-1:FIFO_WIDTH/2];
            saved_eop <= #TCQ read_eop_upper;
            saved_err <= #TCQ read_discontinue_upper;
         end
        end // case: EXPECT_NEW_WORD
      
      SEND_SAVED_HALF_WORD:
        begin
           // There is a half-word saved from a previous beat in the saved data register.
           if ((read_data_valid_reg == 2'b00) | output_mux_ready)
         begin
            read_data_reg[FIFO_WIDTH/2-1:0] <= #TCQ saved_data_reg[FIFO_WIDTH/2-1: 0];
            if (read_data_valid_lower)
              read_data_reg[FIFO_WIDTH-1: FIFO_WIDTH/2] <= #TCQ fifo_read_data[FIFO_WIDTH/2-1: 0];
            else
              read_data_reg[FIFO_WIDTH-1: FIFO_WIDTH/2] <= #TCQ fifo_read_data[FIFO_WIDTH-1: FIFO_WIDTH/2];
            

            if ((~attr_straddle_en_i & saved_eop) | saved_err)
              // Save incoming data for next cycle.
              begin
             if (read_data_valid_lower)
               begin
                  saved_data_reg <= #TCQ fifo_read_data[FIFO_WIDTH/2-1: 0];
                  saved_eop <= #TCQ read_eop_lower;
                  saved_err <= #TCQ read_discontinue_lower;
               end
             else
               begin
                  saved_data_reg <= #TCQ fifo_read_data[FIFO_WIDTH-1: FIFO_WIDTH/2];
                  saved_eop <= #TCQ read_eop_upper;
                  saved_err <= #TCQ read_discontinue_upper;
               end
              end
            else
              begin
             saved_data_reg <= #TCQ fifo_read_data[FIFO_WIDTH-1: FIFO_WIDTH/2];
             saved_eop <= #TCQ read_eop_upper;
             saved_err <= #TCQ read_discontinue_upper;
              end // else: !if((~attr_straddle_en_i & saved_eop) | saved_err)
         end // if ((read_data_valid_reg == 2'b00) | output_mux_ready)
        end // case: SEND_SAVED_HALF_WORD
      WAIT_FOR_UPPER_HALF:
        begin
           // There is a half-word saved from a previous beat in the read data register which does not end with an EOP.
           if ((read_data_valid_reg == 2'b00) | output_mux_ready)
         begin
           read_data_reg[FIFO_WIDTH/2-1:0] <= #TCQ saved_data_reg[FIFO_WIDTH/2-1:0];
            if (read_data_valid_lower)
              read_data_reg[FIFO_WIDTH-1: FIFO_WIDTH/2] <= #TCQ fifo_read_data[FIFO_WIDTH/2-1: 0];
            else
              read_data_reg[FIFO_WIDTH-1: FIFO_WIDTH/2] <= #TCQ {FIFO_WIDTH/2{1'b0}};
              // Save incoming data for next cycle.
            saved_data_reg <= #TCQ fifo_read_data[FIFO_WIDTH-1: FIFO_WIDTH/2];
            saved_eop <= #TCQ read_eop_upper;
            saved_err <= #TCQ read_discontinue_upper;
         end
        end // case: WAIT_FOR_UPPER_HALF
    endcase // case(read_state)
         
   // Generate upstream ready
   always @(*)
     begin
    case(read_state)
      IDLE:
        begin
           fifo_read_en = (read_data_valid_reg == 2'b00) | output_mux_ready;
        end
      
      EXPECT_NEW_WORD:
        begin
           fifo_read_en = (read_data_valid_reg == 2'b00) | output_mux_ready;
        end

      SEND_SAVED_HALF_WORD:
        begin
           // There is a half-word saved from a previous beat in the saved data register.
           if ((read_data_valid_reg == 2'b00) | output_mux_ready)
         begin
            if ((~attr_straddle_en_i & saved_eop) | saved_err)
              // Saved data is the last beat of a packet and straddle is disabled.
              // Do not fill the upper half of read data register.
              fifo_read_en = 1'b0;
            else
              fifo_read_en = 1'b1;
         end
           else
         fifo_read_en = 1'b0;
        end // case: SEND_SAVED_HALF_WORD

      WAIT_FOR_UPPER_HALF:
        begin
           // There is a half-word saved from a previous beat in the read data register which does not end with an EOP.
           fifo_read_en = (read_data_valid_reg == 2'b00) | output_mux_ready;
        end
    endcase // case(read_state)
     end // always @ (*)
   
   assign read_data_reg_byte_en_lower = read_data_reg[TUSER_LOWER_OFFSET +31:
                                 TUSER_LOWER_OFFSET];
   assign read_data_reg_sop0_lower = read_data_reg[TUSER_LOWER_OFFSET + 32];
  assign  read_data_reg_sop1_lower = attr_straddle_en_i? read_data_reg[TUSER_LOWER_OFFSET + 33]: 1'b0;
   assign read_data_reg_eop0_lower = attr_straddle_en_i? read_data_reg[TUSER_LOWER_OFFSET + 34]:
      read_data_reg_tlast_lower;
   assign read_data_reg_eop0_ptr_lower[2:0] = read_data_reg[TUSER_LOWER_OFFSET + 37:
                                TUSER_LOWER_OFFSET + 35];
  assign  read_data_reg_eop1_lower = attr_straddle_en_i? read_data_reg[TUSER_LOWER_OFFSET + 38]: 1'b0;
   assign read_data_reg_eop1_ptr_lower[2:0] = attr_straddle_en_i? read_data_reg[TUSER_LOWER_OFFSET + 41:
                                        TUSER_LOWER_OFFSET + 39]: 3'd0;
   assign read_data_reg_discontinue_lower = read_data_reg[TUSER_LOWER_OFFSET + 42];

  generate
    if (PARITY_ENABLE)
      begin
    assign read_data_reg_parity_lower = read_data_reg[TUSER_LOWER_OFFSET + 74:   
                                   TUSER_LOWER_OFFSET + 43];
    assign read_data_reg_sop0_ptr_lower = read_data_reg[TUSER_LOWER_OFFSET + 75];
      end
    else
      begin
    assign read_data_reg_parity_lower = 32'd0;
    assign read_data_reg_sop0_ptr_lower = read_data_reg[TUSER_LOWER_OFFSET + 43];
      end // else: !if(PARITY_ENABLE)
  endgenerate
  
  assign     read_data_reg_byte_en_upper = read_data_reg[TUSER_UPPER_OFFSET +31:
                                 TUSER_UPPER_OFFSET];
   assign read_data_reg_sop0_upper = read_data_reg[TUSER_UPPER_OFFSET + 32];
  assign  read_data_reg_sop1_upper = attr_straddle_en_i? read_data_reg[TUSER_UPPER_OFFSET + 33]: 1'b0;
   assign read_data_reg_eop0_upper = attr_straddle_en_i? read_data_reg[TUSER_UPPER_OFFSET + 34]:
      read_data_reg_tlast_upper;
   assign read_data_reg_eop0_ptr_upper[2:0] = read_data_reg[TUSER_UPPER_OFFSET + 37:
                                TUSER_UPPER_OFFSET + 35];
   assign read_data_reg_eop1_upper = attr_straddle_en_i? read_data_reg[TUSER_UPPER_OFFSET + 38]: 1'b0;
   assign read_data_reg_eop1_ptr_upper[2:0] = attr_straddle_en_i? read_data_reg[TUSER_UPPER_OFFSET + 41:
                                        TUSER_UPPER_OFFSET + 39]: 3'd0;
   assign read_data_reg_discontinue_upper = read_data_reg[TUSER_UPPER_OFFSET + 42];

  generate
    if (PARITY_ENABLE)
      begin
    assign read_data_reg_parity_upper = read_data_reg[TUSER_UPPER_OFFSET + 74:   
                                   TUSER_UPPER_OFFSET + 43];
    assign read_data_reg_sop0_ptr_upper = read_data_reg[TUSER_UPPER_OFFSET + 75];
      end
    else
      begin
    assign read_data_reg_parity_upper = 32'd0;
    assign read_data_reg_sop0_ptr_upper = read_data_reg[TUSER_UPPER_OFFSET + 43];
      end // else: !if(PARITY_ENABLE)
  endgenerate

  generate
    if (PARITY_ENABLE)
      begin
    assign  read_data_reg_tlast_lower = read_data_reg[AXI4_CORE_DATA_WIDTH + AXI4_CORE_RC_TKEEP_WIDTH +
                              AXI4_CORE_RC_TUSER_WIDTH+1];
    assign     read_data_reg_tlast_upper = read_data_reg[AXI4_CORE_DATA_WIDTH*2 + AXI4_CORE_RC_TKEEP_WIDTH*2 +
                              (AXI4_CORE_RC_TUSER_WIDTH+1)*2 +2];
      end
    else
      begin
    assign  read_data_reg_tlast_lower = read_data_reg[AXI4_CORE_DATA_WIDTH + AXI4_CORE_RC_TKEEP_WIDTH +
                              AXI4_CORE_RC_TUSER_WIDTH+1 -32];
    assign     read_data_reg_tlast_upper = read_data_reg[AXI4_CORE_DATA_WIDTH*2 + AXI4_CORE_RC_TKEEP_WIDTH*2 +
                              (AXI4_CORE_RC_TUSER_WIDTH+1)*2 +2 -64];
      end // else: !if(PARITY_ENABLE)
  endgenerate

   assign read_data_out_byte_en[31:0] = read_data_valid_reg[0]? read_data_reg_byte_en_lower: 32'd0;
   assign read_data_out_byte_en[63:32] = read_data_valid_reg[1]? read_data_reg_byte_en_upper: 32'd0;

  assign  read_data_out_is_sop[0] = ((read_data_valid_reg[0] & (read_data_reg_sop0_lower | 
                                read_data_reg_sop1_lower))) |
      ((read_data_valid_reg[1] & (read_data_reg_sop0_upper | read_data_reg_sop1_upper)));
  
  assign  read_data_out_is_sop[1] = (read_data_valid_reg[0] & read_data_reg_sop1_lower) | 
      (read_data_valid_reg[1] & read_data_reg_sop1_upper) | 
      (read_data_valid_reg[0] & read_data_reg_sop0_lower & read_data_valid_reg[1] &
       read_data_reg_sop0_upper);

  assign  read_data_out_is_sop[2] = read_data_valid_reg[0] & read_data_valid_reg[1] & 
      ((read_data_reg_sop1_lower & read_data_reg_sop0_upper) |
       (read_data_reg_sop0_lower & read_data_reg_sop1_upper));
  
  assign  read_data_out_is_sop[3] = read_data_valid_reg[0] & read_data_valid_reg[1] & 
      read_data_reg_sop1_lower & read_data_reg_sop1_upper;

  assign  read_data_out_is_sop0_ptr[1:0] = (read_data_valid_reg[0] & read_data_reg_sop0_lower)?
      {1'b0, read_data_reg_sop0_ptr_lower}:
      (read_data_valid_reg[0] & read_data_reg_sop1_lower)? 2'd1:
      (read_data_valid_reg[1] & read_data_reg_sop0_upper)?
      {1'b1, read_data_reg_sop0_ptr_upper}:
      (read_data_valid_reg[1] & read_data_reg_sop1_upper)? 2'd3: 2'd0;
  assign  read_data_out_is_sop1_ptr[1:0] = (read_data_valid_reg[0] & read_data_reg_sop1_lower)? 4'd1:
      (read_data_valid_reg[0] & read_data_valid_reg[1] & read_data_reg_sop0_lower &
       read_data_reg_sop0_upper)? {1'b1, read_data_reg_sop0_ptr_upper}:
      (read_data_valid_reg[1] & read_data_reg_sop0_upper &
       read_data_reg_sop1_upper)? 2'd3: 2'd0;
    assign  read_data_out_is_sop2_ptr[1:0] = (read_data_valid_reg[0] & read_data_valid_reg[1] & 
                          read_data_reg_sop1_lower & read_data_reg_sop0_upper)? 
        {1'b1, read_data_reg_sop0_ptr_upper}:
        (read_data_valid_reg[0] & read_data_valid_reg[1] & 
         read_data_reg_sop0_lower & read_data_reg_sop1_upper)? 2'd3: 2'd0;
  assign    read_data_out_is_sop3_ptr[1:0] = (read_data_valid_reg[0] & read_data_valid_reg[1] & 
                          read_data_reg_sop1_lower & read_data_reg_sop1_upper)? 2'd3: 2'd0;

  assign  read_data_out_is_eop[0] = ((read_data_valid_reg[0] & (read_data_reg_eop0_lower | 
                                read_data_reg_eop1_lower))) |
      ((read_data_valid_reg[1] & (read_data_reg_eop0_upper | read_data_reg_eop1_upper)));

  assign  read_data_out_is_eop0_ptr[3:0] = (read_data_valid_reg[0] & read_data_reg_eop0_lower)?
       {1'b0, read_data_reg_eop0_ptr_lower[2:0]}:
      (read_data_valid_reg[0] & read_data_reg_eop1_lower)?
       {1'b0, read_data_reg_eop1_ptr_lower[2:0]}:
      (read_data_valid_reg[1] & read_data_reg_eop0_upper)?
       {1'b1, read_data_reg_eop0_ptr_upper[2:0]}:
      (read_data_valid_reg[1] & read_data_reg_eop1_upper)?
       {1'b1, read_data_reg_eop1_ptr_upper[2:0]}: 4'd0;
  
  assign  read_data_out_is_eop[1] = (read_data_valid_reg[0] & read_data_reg_eop1_lower) | 
      (read_data_valid_reg[1] & read_data_reg_eop1_upper) | 
      (read_data_valid_reg[0] & read_data_reg_eop0_lower & read_data_valid_reg[1] &
       read_data_reg_eop0_upper);
  assign  read_data_out_is_eop1_ptr[3:0] = (read_data_valid_reg[0] & read_data_reg_eop1_lower)?
       {1'b0, read_data_reg_eop1_ptr_lower[2:0]}:
      (read_data_valid_reg[0] & read_data_reg_eop0_lower & 
       read_data_valid_reg[1] & read_data_reg_eop0_upper)?
       {1'b1, read_data_reg_eop0_ptr_upper[2:0]}:
      (read_data_valid_reg[1] & read_data_reg_eop1_upper)?
      {1'b1, read_data_reg_eop1_ptr_upper[2:0]}: 4'd0;

  assign  read_data_out_is_eop[2] = read_data_valid_reg[0] & read_data_valid_reg[1] & 
      ((read_data_reg_eop1_lower & read_data_reg_eop0_upper) |
       (read_data_reg_eop0_lower & read_data_reg_eop1_upper));
  assign  read_data_out_is_eop2_ptr[3:0] = (read_data_valid_reg[0] & read_data_valid_reg[1] & 
                        read_data_reg_eop1_lower & read_data_reg_eop0_upper)?
       {1'b1, read_data_reg_eop0_ptr_upper[2:0]}:
      (read_data_valid_reg[0] & read_data_valid_reg[1] & 
       read_data_reg_eop0_lower & read_data_reg_eop1_upper)?
       {1'b1, read_data_reg_eop1_ptr_upper[2:0]}: 4'd0;
  assign  read_data_out_is_eop[3] = read_data_valid_reg[0] & read_data_valid_reg[1] & 
      read_data_reg_eop1_lower & read_data_reg_eop1_upper;
  assign  read_data_out_is_eop3_ptr[3:0] = (read_data_valid_reg[0] & read_data_valid_reg[1] & 
                        read_data_reg_eop1_lower & read_data_reg_eop1_upper)?
      {1'b1, read_data_reg_eop1_ptr_upper[2:0]}: 4'd0;

   assign read_data_out_discontinue = (read_data_valid_reg[0] & read_data_reg_discontinue_lower) |
      (read_data_valid_reg[1] & read_data_reg_discontinue_upper);      

   assign read_data_out_parity[31:0] = read_data_valid_reg[0]? read_data_reg_parity_lower: 32'd0;
   assign read_data_out_parity[63:32] = read_data_valid_reg[1]? read_data_reg_parity_upper: 32'd0;  

   assign read_data_out_tuser = {
                 read_data_out_parity[63:0],
                 read_data_out_discontinue,
                 read_data_out_is_eop3_ptr[3:0],
                 read_data_out_is_eop2_ptr[3:0],
                 read_data_out_is_eop1_ptr[3:0],
                 read_data_out_is_eop0_ptr[3:0],
                 read_data_out_is_eop[3:0],
                 read_data_out_is_sop3_ptr[1:0],
                 read_data_out_is_sop2_ptr[1:0],
                 read_data_out_is_sop1_ptr[1:0],
                 read_data_out_is_sop0_ptr[1:0],
                 read_data_out_is_sop[3:0],
                 read_data_out_byte_en[63:0]
                 };

   assign read_data_out_tdata[AXI4_USER_DATA_WIDTH/2-1:0] = read_data_valid_reg[0]? read_data_reg[AXI4_CORE_DATA_WIDTH-1:0]:
      {AXI4_USER_DATA_WIDTH/2{1'b0}};
   assign read_data_out_tdata[AXI4_USER_DATA_WIDTH-1:AXI4_USER_DATA_WIDTH/2] = read_data_valid_reg[1]?
      read_data_reg[FIFO_READ_DATA_UPPER_OFFSET+AXI4_CORE_DATA_WIDTH-1:FIFO_READ_DATA_UPPER_OFFSET]: {AXI4_USER_DATA_WIDTH/2{1'b0}};
   
  assign  read_data_out_tkeep[AXI4_USER_RC_TKEEP_WIDTH/2-1:0] = attr_straddle_en_i? {AXI4_USER_RC_TKEEP_WIDTH/2{1'b1}}:
      read_data_valid_reg[0]? 
      read_data_reg[AXI4_CORE_DATA_WIDTH+AXI4_CORE_RC_TKEEP_WIDTH-1:AXI4_CORE_DATA_WIDTH]: {AXI4_USER_RC_TKEEP_WIDTH/2{1'b0}};
   assign read_data_out_tkeep[AXI4_USER_RC_TKEEP_WIDTH-1:AXI4_USER_RC_TKEEP_WIDTH/2] = attr_straddle_en_i? {AXI4_USER_RC_TKEEP_WIDTH/2{1'b1}}:
      read_data_valid_reg[1]? 
      read_data_reg[FIFO_READ_TKEEP_UPPER_OFFSET+AXI4_CORE_RC_TKEEP_WIDTH-1:FIFO_READ_TKEEP_UPPER_OFFSET]:
      {AXI4_USER_RC_TKEEP_WIDTH/2{1'b0}};

   assign read_data_out_tlast = attr_straddle_en_i? 1'b0: 
      (read_data_valid_reg[0] & read_data_reg_tlast_lower) |
      (read_data_valid_reg[1] & read_data_reg_tlast_upper);

   assign output_mux_in_data = {
                read_data_out_tlast,
                read_data_out_tuser,
                read_data_out_tkeep,
                read_data_out_tdata
                };

   // Instance of output MUX
   pcie4_uscale_plus_0_512b_rc_output_mux #
     (
      .TCQ(TCQ),
      .IMPL_TARGET(IMPL_TARGET),
      .IN_DATA_WIDTH(OUTPUT_MUX_IN_DATA_WIDTH),
      .OUT_DATA_WIDTH(AXI4_USER_DATA_WIDTH),
      .TUSER_WIDTH(AXI4_USER_RC_TUSER_WIDTH),
      .TKEEP_WIDTH(AXI4_USER_RC_TKEEP_WIDTH)
      )
     pcie_4_0_512b_rc_output_mux_blk
       (
        .clk_i(user_clk_i),
        .reset_n_i(reset_n_user_clk_i),
        .link_down_reset_i(link_down_reset_i),
    .in_data_i(output_mux_in_data),
    .in_data_valid_i(read_data_valid_reg[0]),
        .attr_straddle_en_i(attr_straddle_en_i),

    .upstream_ready_o(output_mux_ready),
    .out_data_o(m_axis_rc_tdata_o),
        .out_data_valid_o(m_axis_rc_tvalid_o),
    .out_tuser_o(m_axis_rc_tuser_o),
    .out_tlast_o(m_axis_rc_tlast_o),
    .out_tkeep_o(m_axis_rc_tkeep_o),
    .downstream_ready_i(m_axis_rc_tready_i),

    // Completion delivered indications to AXI hard block
    .pcie_compl_delivered_o(pcie_compl_delivered_user_clk),
    .pcie_compl_delivered_tag0_o(pcie_compl_delivered_tag0_user_clk),
    .pcie_compl_delivered_tag1_o(pcie_compl_delivered_tag1_user_clk),
    .pcie_compl_delivered_tag2_o(pcie_compl_delivered_tag2_user_clk),
    .pcie_compl_delivered_tag3_o(pcie_compl_delivered_tag3_user_clk)
    );

  // Return tags of delivered Completions to the AXI hard block.
  always @(posedge user_clk2_i)
    if (~reset_n_user_clk2_i)
      begin
    compl_delivered_o <= #TCQ 2'b00;
    compl_delivered_tag0_o <= #TCQ 8'd0;
    compl_delivered_tag1_o <= #TCQ 8'd0;
      end
    else if (~user_clk_en_i)
      begin
    compl_delivered_o <= #TCQ pcie_compl_delivered_user_clk[1:0];
    compl_delivered_tag0_o <= #TCQ pcie_compl_delivered_tag0_user_clk;
    compl_delivered_tag1_o <= #TCQ pcie_compl_delivered_tag1_user_clk;
      end
    else
      begin
    compl_delivered_o <= #TCQ pcie_compl_delivered_user_clk[3:2];
    compl_delivered_tag0_o <= #TCQ pcie_compl_delivered_tag2_user_clk;
    compl_delivered_tag1_o <= #TCQ pcie_compl_delivered_tag3_user_clk;
      end // else: !if(~user_clk_en_i)

endmodule // pcie_4_0_512b_rc_intfc







   
