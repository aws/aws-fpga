//-----------------------------------------------------------------------------
//
// (c) Copyright 1995, 2007, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD, Inc. and is protected under U.S. and
// international copyright and other intellectual property
// laws.
//
// DISCLAIMER
// This disclaimer is not a license and does not grant any
// rights to the materials distributed herewith. Except as
// otherwise provided in a valid license issued to you by
// AMD, and to the maximum extent permitted by applicable
// law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// WITH ALL FAULTS, AND AMD HEREBY DISCLAIMS ALL WARRANTIES
// AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// (2) AMD shall not be liable (whether in contract or tort,
// including negligence, or under any other theory of
// liability) for any loss or damage of any kind or nature
// related to, arising under or in connection with these
// materials, including for any direct, or any indirect,
// special, incidental, or consequential loss or damage
// (including loss of data, profits, goodwill, or any type of
// loss or damage suffered as a result of any action brought
// by a third party) even if such damage or loss was
// reasonably foreseeable or AMD had been advised of the
// possibility of the same.
//
// CRITICAL APPLICATIONS
// AMD products are not designed or intended to be fail-
// safe, or for use in any application requiring fail-safe
// performance, such as life-support or safety devices or
// systems, Class III medical devices, nuclear facilities,
// applications related to the deployment of airbags, or any
// other applications that could lead to death, personal
// injury, or severe property or environmental damage
// (individually and collectively, "Critical
// Applications"). Customer assumes the sole risk and
// liability of any use of AMD products in Critical
// Applications, subject only to applicable laws and
// regulations governing limitations on product liability.
//
// THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// PART OF THIS FILE AT ALL TIMES.
//
//-----------------------------------------------------------------------------
//
// Project    : UltraScale+ FPGA PCI Express CCIX v4.0 Integrated Block
// File       : pcie_bridge_rc_pcie4c_ip_512b_cq_intfc.v
// Version    : 1.0 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------
`timescale 1ps/1ps
(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie_bridge_rc_pcie4c_ip_512b_cq_intfc #(
   parameter TCQ = 100,
   parameter IMPL_TARGET = "SOFT",
   parameter AXISTEN_IF_EXT_512_INTFC_RAM_STYLE = "SRL",
   parameter AXI4_USER_DATA_WIDTH = 512,
   parameter AXI4_CORE_DATA_WIDTH = 256,
   parameter AXI4_USER_CQ_TUSER_WIDTH = 183,
   parameter AXI4_CORE_CQ_TUSER_WIDTH = 88,
   parameter AXI4_USER_CQ_TKEEP_WIDTH = 16,
   parameter AXI4_CORE_CQ_TKEEP_WIDTH = 8,
   parameter AXI4_CORE_CQ_TREADY_WIDTH = 22,
   parameter PARITY_ENABLE = 0
   ) 
  (
    input  wire           user_clk2_i // 500 MHz clock for core-facing interfaces
   ,input  wire           user_clk_i // 250 MHz clock for client-facing interfaces
   ,input  wire           user_clk_en_i // User clock enable for clock domain crossing
   ,input  wire           reset_n_user_clk_i // Reset in the user clock domain
   ,input  wire           reset_n_user_clk2_i // Reset in the user clock2 domain
   ,input  wire           link_down_reset_i // Link went down
   ,input wire            conf_mcap_design_switch_i // FPGA configuration in progress
   // Attributes
   ,input  wire           attr_straddle_en_i // Enable straddle
   ,input wire [1:0]      attr_alignment_mode_i // Payload alignment mode
                                                // (00= Dword-aligned, 10 = 128b address-aligned)
   ,input wire            attr_mcap_input_gate_design_switch_i // MCAP input to enable grant of initial credit
                                                   // on NP_REQ interface
   //-----------------------------------------------------------------------------------------------
   // Client-side signals
   //-----------------------------------------------------------------------------------------------
   ,output wire [AXI4_USER_DATA_WIDTH-1:0]   m_axis_cq_tdata_o
   ,output wire           m_axis_cq_tvalid_o
   ,output wire [AXI4_USER_CQ_TUSER_WIDTH-1:0]   m_axis_cq_tuser_o
   ,output wire           m_axis_cq_tlast_o
   ,output wire [AXI4_USER_CQ_TKEEP_WIDTH-1:0]    m_axis_cq_tkeep_o
   ,input  wire           m_axis_cq_tready_i
   ,input  wire [1:0]     pcie_cq_np_req_i // Client request to deliver NP TLP
   ,output wire [5:0]     pcie_cq_np_req_count_o // Current value of interface credit count for NP TLPs
   //-----------------------------------------------------------------------------------------------
   // Core-side signals
   //-----------------------------------------------------------------------------------------------
   ,input  wire [AXI4_CORE_DATA_WIDTH-1:0] core_cq_tdata_i
   ,input  wire           core_cq_tvalid_i
   ,input  wire [AXI4_CORE_CQ_TUSER_WIDTH-1:0] core_cq_tuser_i
   ,input  wire           core_cq_tlast_i
   ,input  wire [AXI4_CORE_CQ_TKEEP_WIDTH-1:0] core_cq_tkeep_i
   ,output wire [AXI4_CORE_CQ_TREADY_WIDTH-1:0] core_cq_tready_o
   ,output reg            posted_req_delivered_o // Signals the delivery of a Posted Req on the CQ interface
   ,output reg            cq_pipeline_empty_o // Indicates that the entire CQ pipeline of the bridge is empty.
   ,output reg            cq_np_user_credit_rcvd_o // Indicates that the user issued one NP credit
   );

   localparam FIFO_WIDTH = PARITY_ENABLE? (AXI4_CORE_DATA_WIDTH + AXI4_CORE_CQ_TUSER_WIDTH + 
                       AXI4_CORE_CQ_TKEEP_WIDTH + 1)*2 +2 :
               (AXI4_CORE_DATA_WIDTH + AXI4_CORE_CQ_TUSER_WIDTH + 
                AXI4_CORE_CQ_TKEEP_WIDTH + 1)*2 +2 -64;

   localparam TUSER_LOWER_OFFSET = AXI4_CORE_DATA_WIDTH + AXI4_CORE_CQ_TKEEP_WIDTH;
   localparam TUSER_UPPER_OFFSET = PARITY_ENABLE? AXI4_CORE_DATA_WIDTH*2 + AXI4_CORE_CQ_TKEEP_WIDTH*2 +
                   AXI4_CORE_CQ_TUSER_WIDTH +2:
                   AXI4_CORE_DATA_WIDTH*2 + AXI4_CORE_CQ_TKEEP_WIDTH*2 +
                   AXI4_CORE_CQ_TUSER_WIDTH +2 -32;
   
  localparam FIFO_READ_DATA_UPPER_OFFSET = PARITY_ENABLE?
                   AXI4_CORE_DATA_WIDTH + AXI4_CORE_CQ_TKEEP_WIDTH + AXI4_CORE_CQ_TUSER_WIDTH +2:
                   AXI4_CORE_DATA_WIDTH + AXI4_CORE_CQ_TKEEP_WIDTH + AXI4_CORE_CQ_TUSER_WIDTH +2 -32;
  
  localparam FIFO_READ_TKEEP_UPPER_OFFSET = PARITY_ENABLE?
                    AXI4_CORE_DATA_WIDTH*2 + AXI4_CORE_CQ_TKEEP_WIDTH + AXI4_CORE_CQ_TUSER_WIDTH +2:
                                    AXI4_CORE_DATA_WIDTH*2 + AXI4_CORE_CQ_TKEEP_WIDTH + AXI4_CORE_CQ_TUSER_WIDTH +2 -32;

   localparam OUTPUT_MUX_IN_DATA_WIDTH = AXI4_USER_DATA_WIDTH +
                     AXI4_USER_CQ_TKEEP_WIDTH +
                     AXI4_USER_CQ_TUSER_WIDTH + 1;

   (* KEEP = "true" *) reg [AXI4_CORE_CQ_TREADY_WIDTH-1:0] core_cq_tready_reg;
   (* KEEP = "true" *) reg core_cq_tready_user_clk2;

   reg [AXI4_CORE_DATA_WIDTH-1:0] core_cq_tdata_reg_upper;
   reg [AXI4_CORE_DATA_WIDTH-1:0] core_cq_tdata_reg_lower;
   reg [AXI4_CORE_CQ_TUSER_WIDTH-1:0] core_cq_tuser_reg_upper;
   reg [AXI4_CORE_CQ_TUSER_WIDTH-1:0] core_cq_tuser_reg_lower;
   reg                       core_cq_tlast_reg_upper;
   reg                       core_cq_tlast_reg_lower;
   reg [AXI4_CORE_CQ_TKEEP_WIDTH-1:0] core_cq_tkeep_reg_upper;
   reg [AXI4_CORE_CQ_TKEEP_WIDTH-1:0] core_cq_tkeep_reg_lower;
   reg                       core_cq_tvalid_reg_upper;
   reg                       core_cq_tvalid_reg_lower;

   wire                   fifo_almost_full_user_clk;

   wire [FIFO_WIDTH-1:0]           fifo_in_data;
   reg [FIFO_WIDTH-1:0]           fifo_in_data_reg;
   reg                       fifo_in_data_valid_reg;
   reg                       fifo_read_en;
   wire                   fifo_read_data_valid;
   wire [FIFO_WIDTH-1:0]           fifo_read_data;

   wire [3:0]                   read_first_be_lower;
   wire [3:0]                   read_last_be_lower;
   wire [31:0]                   read_byte_en_lower;
   wire                   read_sop_lower;
   wire                   read_discontinue_lower;
   wire                   read_tph_present_lower;
   wire [1:0]                   read_tph_type_lower;
   wire [7:0]                   read_tph_st_tag_lower;
   wire [2:0]                   read_eop_ptr_lower;
   wire                   read_tlast_lower;
   wire                   read_tlast_upper;
   wire                   read_data_valid_lower;
   wire                   read_data_valid_upper;

   wire [3:0]                   read_first_be_upper;
   wire [3:0]                   read_last_be_upper;
   wire [31:0]                   read_byte_en_upper;
   wire                   read_sop_upper;
   wire                   read_discontinue_upper;
   wire                   read_tph_present_upper;
   wire [1:0]                   read_tph_type_upper;
   wire [7:0]                   read_tph_st_tag_upper;
   wire [2:0]                   read_eop_ptr_upper;

   reg [1:0]                   read_data_valid_reg;
   reg [FIFO_WIDTH-1:0]           read_data_reg;
   reg [FIFO_WIDTH/2-1:0]           saved_data_reg;
   reg                       saved_eop;
   reg                       saved_err;
   
   wire [3:0]                   read_data_reg_first_be_lower;
   wire [3:0]                   read_data_reg_last_be_lower;
   wire [31:0]                   read_data_reg_byte_en_lower;
   wire                    read_data_reg_sop_lower;
   wire                    read_data_reg_discontinue_lower;
   wire                    read_data_reg_tph_present_lower;
   wire [1:0]                   read_data_reg_tph_type_lower;
   wire [7:0]                   read_data_reg_tph_st_tag_lower;
   wire [31:0]                   read_data_reg_parity_lower;
   wire [2:0]                   read_data_reg_eop_ptr_lower;
   wire [3:0]                   read_data_reg_first_be_upper;
   wire [3:0]                   read_data_reg_last_be_upper;
   wire [31:0]                   read_data_reg_byte_en_upper;
   wire                    read_data_reg_sop_upper;
   wire                    read_data_reg_discontinue_upper;
   wire                    read_data_reg_tph_present_upper;
   wire [1:0]                   read_data_reg_tph_type_upper;
   wire [7:0]                   read_data_reg_tph_st_tag_upper;
   wire [31:0]                   read_data_reg_parity_upper;
   wire [2:0]                   read_data_reg_eop_ptr_upper;
  wire                       read_data_reg_tlast_lower;
  wire                       read_data_reg_tlast_upper;
   wire                   sop_in_lower_half;
   wire                   sop_in_upper_half;
   wire                   eop_in_lower_half;
   wire                   eop_in_upper_half;

   wire [7:0]                   read_data_out_first_be;
   wire [7:0]                   read_data_out_last_be;
   wire [63:0]                   read_data_out_byte_en;
   wire [1:0]                   read_data_out_is_sop;
   wire [1:0]                   read_data_out_is_sop0_ptr;
   wire [1:0]                   read_data_out_is_sop1_ptr;
   wire [1:0]                   read_data_out_is_eop;
   wire [3:0]                   read_data_out_is_eop0_ptr;
   wire [3:0]                   read_data_out_is_eop1_ptr;
   wire                   read_data_out_discontinue;
   wire [1:0]                   read_data_out_tph_present;
   wire [3:0]                   read_data_out_tph_type;
   wire [15:0]                   read_data_out_tph_st_tag;
   wire [63:0]                   read_data_out_parity;
   
   wire [ AXI4_USER_CQ_TUSER_WIDTH-1:0] read_data_out_tuser;
   wire [ AXI4_USER_DATA_WIDTH-1:0]     read_data_out_tdata;
   wire [ AXI4_USER_CQ_TKEEP_WIDTH-1:0] read_data_out_tkeep;
   wire                 read_data_out_tlast;
   
   wire [OUTPUT_MUX_IN_DATA_WIDTH-1:0]     output_mux_in_data;

   wire                 output_mux_ready;
   
   wire [1:0]                 cq_np_user_credit_rcvd_user_clk;
   wire [1:0]                 posted_req_delivered_user_clk;

   wire                 pipeline_empty_user_clk;
   wire                 out_mux_pipeline_empty;
   reg                     pipeline_empty_core_clk;
   reg [2:0]                 cq_pipeline_empty_reg;

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
      core_cq_tdata_reg_upper <= #TCQ {AXI4_CORE_DATA_WIDTH{1'b0}};
      core_cq_tdata_reg_lower <= #TCQ {AXI4_CORE_DATA_WIDTH{1'b0}};
      core_cq_tuser_reg_upper <= #TCQ {AXI4_CORE_CQ_TUSER_WIDTH{1'b0}};
      core_cq_tuser_reg_lower <= #TCQ {AXI4_CORE_CQ_TUSER_WIDTH{1'b0}};
      core_cq_tkeep_reg_upper <= #TCQ {AXI4_CORE_CQ_TKEEP_WIDTH{1'b0}};
      core_cq_tkeep_reg_lower <= #TCQ {AXI4_CORE_CQ_TKEEP_WIDTH{1'b0}};
      core_cq_tlast_reg_upper <= #TCQ 1'b0;
      core_cq_tlast_reg_lower <= #TCQ 1'b0;
       core_cq_tvalid_reg_upper <= #TCQ 1'b0;
      core_cq_tvalid_reg_lower <= #TCQ 1'b0;
       end // if (~reset_n_user_clk_i)
     else
       if (user_clk_en_i)
     begin
        core_cq_tdata_reg_lower <= #TCQ core_cq_tdata_i;
        core_cq_tuser_reg_lower <= #TCQ core_cq_tuser_i;
        core_cq_tkeep_reg_lower <= #TCQ core_cq_tkeep_i;
        core_cq_tlast_reg_lower <= #TCQ core_cq_tlast_i;
        core_cq_tvalid_reg_lower <= #TCQ core_cq_tvalid_i & core_cq_tready_user_clk2;
     end
       else
     begin
        core_cq_tdata_reg_upper <= #TCQ core_cq_tdata_i;
        core_cq_tuser_reg_upper <= #TCQ core_cq_tuser_i;
        core_cq_tkeep_reg_upper <= #TCQ core_cq_tkeep_i;
        core_cq_tlast_reg_upper <= #TCQ core_cq_tlast_i;
        core_cq_tvalid_reg_upper <= #TCQ core_cq_tvalid_i & core_cq_tready_user_clk2;
     end // else: !if(user_clk_en_i)

   // Write data into FIFO using 250 MHz user_clk

  generate
    if (PARITY_ENABLE)
      assign fifo_in_data =
          {
       core_cq_tvalid_reg_upper,
       core_cq_tlast_reg_upper,
       core_cq_tuser_reg_upper,
       core_cq_tkeep_reg_upper,
       core_cq_tdata_reg_upper,
       core_cq_tvalid_reg_lower,
       core_cq_tlast_reg_lower,
       core_cq_tuser_reg_lower,
       core_cq_tkeep_reg_lower,
       core_cq_tdata_reg_lower
       };
    else
      assign fifo_in_data =
          {
       core_cq_tvalid_reg_upper,
       core_cq_tlast_reg_upper,
       core_cq_tuser_reg_upper[87:85],
       core_cq_tuser_reg_upper[52:0],
       core_cq_tkeep_reg_upper,
       core_cq_tdata_reg_upper,
       core_cq_tvalid_reg_lower,
       core_cq_tlast_reg_lower,
       core_cq_tuser_reg_lower[87:85],
       core_cq_tuser_reg_lower[52:0],
       core_cq_tkeep_reg_lower,
       core_cq_tdata_reg_lower
       };
  endgenerate

   always @(posedge user_clk_i)
     if (~reset_n_user_clk_i)
       begin
      fifo_in_data_reg <= #TCQ {FIFO_WIDTH{1'b0}};      
      fifo_in_data_valid_reg <= #TCQ 1'b0;
       end
     else
       begin
      fifo_in_data_reg <= #TCQ fifo_in_data;
         fifo_in_data_valid_reg <= #TCQ (core_cq_tvalid_reg_lower |
                     core_cq_tvalid_reg_upper);
       end // else: !if(~reset_n_user_clk_i)

   // Generate ready to core in the user_clk2 domain
   always @(posedge user_clk2_i)
     if (~reset_n_user_clk2_i)
       begin
      core_cq_tready_user_clk2 <= #TCQ 1'b0;
      core_cq_tready_reg <= #TCQ {AXI4_CORE_CQ_TREADY_WIDTH{1'b0}};
       end
     else
       begin
             core_cq_tready_user_clk2 <= #TCQ ~fifo_almost_full_user_clk;
      core_cq_tready_reg <= #TCQ {AXI4_CORE_CQ_TREADY_WIDTH{~fifo_almost_full_user_clk}};
       end

   assign core_cq_tready_o = core_cq_tready_reg;
   
   // Main FIFO instance
   pcie_bridge_rc_pcie4c_ip_512b_sync_fifo #
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
    .write_data_i(fifo_in_data_reg),
    .write_en_i(fifo_in_data_valid_reg),
    .read_en_i(fifo_read_en),
    .read_data_o(fifo_read_data),
    .read_data_valid_o(fifo_read_data_valid),
    .fifo_almost_full(fifo_almost_full_user_clk)
    );
   
   // Read-side logic
   
   assign read_first_be_lower = fifo_read_data[TUSER_LOWER_OFFSET +3:
                           TUSER_LOWER_OFFSET];
   assign read_last_be_lower = fifo_read_data[TUSER_LOWER_OFFSET +7:
                          TUSER_LOWER_OFFSET +4];
   assign read_byte_en_lower = fifo_read_data[TUSER_LOWER_OFFSET +39:
                             TUSER_LOWER_OFFSET +8];
   assign read_sop_lower = fifo_read_data[TUSER_LOWER_OFFSET + 40];
   assign read_discontinue_lower = fifo_read_data[TUSER_LOWER_OFFSET + 41];
   assign read_tph_present_lower = fifo_read_data[TUSER_LOWER_OFFSET + 42];  
   assign read_tph_type_lower = fifo_read_data[TUSER_LOWER_OFFSET + 44:
                        TUSER_LOWER_OFFSET + 43];
   assign read_tph_st_tag_lower = fifo_read_data[TUSER_LOWER_OFFSET + 52:   
                            TUSER_LOWER_OFFSET + 45];
  generate
    if (PARITY_ENABLE)
      assign read_eop_ptr_lower = fifo_read_data[TUSER_LOWER_OFFSET + 87:
                         TUSER_LOWER_OFFSET + 85];
    else
      assign read_eop_ptr_lower = fifo_read_data[TUSER_LOWER_OFFSET + 55:
                         TUSER_LOWER_OFFSET + 53];
  endgenerate


  assign     read_first_be_upper = fifo_read_data[TUSER_UPPER_OFFSET +3:
                           TUSER_UPPER_OFFSET];
   assign read_last_be_upper = fifo_read_data[TUSER_UPPER_OFFSET +7:
                          TUSER_UPPER_OFFSET +4];
   assign read_byte_en_upper = fifo_read_data[TUSER_UPPER_OFFSET +39:
                             TUSER_UPPER_OFFSET +8];
   assign read_sop_upper = fifo_read_data[TUSER_UPPER_OFFSET + 40];
   assign read_discontinue_upper = fifo_read_data[TUSER_UPPER_OFFSET + 41];
   assign read_tph_present_upper = fifo_read_data[TUSER_UPPER_OFFSET + 42];  
   assign read_tph_type_upper = fifo_read_data[TUSER_UPPER_OFFSET + 44:
                        TUSER_UPPER_OFFSET + 43];
   assign read_tph_st_tag_upper = fifo_read_data[TUSER_UPPER_OFFSET + 52:   
                            TUSER_UPPER_OFFSET + 45];
  generate
    if (PARITY_ENABLE)
      assign read_eop_ptr_upper = fifo_read_data[TUSER_UPPER_OFFSET + 87:
                         TUSER_UPPER_OFFSET + 85];
    else
      assign read_eop_ptr_upper = fifo_read_data[TUSER_UPPER_OFFSET + 55:
                           TUSER_UPPER_OFFSET + 53];
  endgenerate

  generate
    if (PARITY_ENABLE)
      begin
    assign     read_tlast_lower = fifo_read_data[AXI4_CORE_DATA_WIDTH + AXI4_CORE_CQ_TKEEP_WIDTH +
                             AXI4_CORE_CQ_TUSER_WIDTH];
    assign     read_tlast_upper = fifo_read_data[AXI4_CORE_DATA_WIDTH*2 + AXI4_CORE_CQ_TKEEP_WIDTH*2 +
                             AXI4_CORE_CQ_TUSER_WIDTH*2 +2];
      end
    else
      begin
    assign     read_tlast_lower = fifo_read_data[AXI4_CORE_DATA_WIDTH + AXI4_CORE_CQ_TKEEP_WIDTH +
                             AXI4_CORE_CQ_TUSER_WIDTH -32];
    assign     read_tlast_upper = fifo_read_data[AXI4_CORE_DATA_WIDTH*2 + AXI4_CORE_CQ_TKEEP_WIDTH*2 +
                             AXI4_CORE_CQ_TUSER_WIDTH*2 +2 -64];
      end // else: !if(PARITY_ENABLE)
  endgenerate

    assign        read_data_valid_lower = fifo_read_data[FIFO_WIDTH/2-1] & fifo_read_data_valid;
    assign        read_data_valid_upper = fifo_read_data[FIFO_WIDTH-1] & fifo_read_data_valid;


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
                   if (read_tlast_upper)
                     read_state <= #TCQ IDLE;
                   else
                     read_state <= #TCQ EXPECT_NEW_WORD;
                end // else: !if(~attr_straddle_en_i & read_sop_upper)
               end // if (read_data_valid_upper)
             else
               begin
                  // New TLP started in the lower half, but there is no valid data in the upper half.
                  if (read_tlast_lower)
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
                end // else: !if(read_tlast_lower)
               end // else: !if(read_data_valid_upper)
              end // if (read_data_valid_lower)
            else
              if (read_data_valid_upper)
            begin
               // No valid data in the lower half of the incoming word, but there is a packet starting in the upper half.
               if (read_tlast_upper)
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
                 end // else: !if(read_tlast_upper)
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
                   if (read_tlast_upper)
                     read_state <= #TCQ IDLE;
                   else
                     read_state <= #TCQ EXPECT_NEW_WORD;
                end // else: !if(~attr_straddle_en_i & read_sop_upper)
               end // if (read_data_valid_upper)
             else
               begin
                  // Valid data in the lower half, but no valid data in the upper half.
                  if (read_tlast_lower)
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
                end // else: !if(read_tlast_lower)
               end // else: !if(read_data_valid_upper)
              end // if (read_data_valid_lower)
            else
              if (read_data_valid_upper)
            begin
               // No valid data in the lower half of the incoming word, but there is data in the upper half.
               if (read_tlast_upper)
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
                 end // else: !if(read_tlast_upper)
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
                if (read_tlast_lower)
                  read_state <= #TCQ IDLE;
                else
                  read_state <= #TCQ EXPECT_NEW_WORD;
                 end // else: !if(read_data_valid_upper)
            end // if (read_data_valid_lower)
              else
            if (read_data_valid_upper)
              begin
                 // No valid data in the lower half of the incoming word, but there is data in the upper half.
                 if (read_tlast_upper)
                   // We have a complete packet, send it in the upper half.
                   begin
                  read_data_valid_reg <= #TCQ 2'b11;
                  read_state <= #TCQ IDLE;
                   end
                 else
                   begin
                  read_data_valid_reg <= #TCQ 2'b11;
                  read_state <= #TCQ EXPECT_NEW_WORD;
                   end // else: !if(read_tlast_upper)
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
                 if (read_tlast_upper)
                   read_state <= #TCQ SEND_SAVED_HALF_WORD;
                 else
                   read_state <= #TCQ WAIT_FOR_UPPER_HALF;
               end
             else
               begin
                 if (read_tlast_lower)
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
               if (read_tlast_upper)
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
            saved_eop <= #TCQ read_tlast_upper;
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
            saved_eop <= #TCQ read_tlast_upper;
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
                  saved_eop <= #TCQ read_tlast_lower;
                  saved_err <= #TCQ read_discontinue_lower;
               end
             else
               begin
                  saved_data_reg <= #TCQ fifo_read_data[FIFO_WIDTH-1: FIFO_WIDTH/2];
                  saved_eop <= #TCQ read_tlast_upper;
                  saved_err <= #TCQ read_discontinue_upper;
               end
              end
            else
              begin
             saved_data_reg <= #TCQ fifo_read_data[FIFO_WIDTH-1: FIFO_WIDTH/2];
             saved_eop <= #TCQ read_tlast_upper;
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
           saved_eop <= #TCQ read_tlast_upper;
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
   

   assign read_data_reg_first_be_lower = read_data_reg[TUSER_LOWER_OFFSET +3:
                               TUSER_LOWER_OFFSET];
   assign read_data_reg_last_be_lower = read_data_reg[TUSER_LOWER_OFFSET +7:
                              TUSER_LOWER_OFFSET +4];
   assign read_data_reg_byte_en_lower = read_data_reg[TUSER_LOWER_OFFSET +39:
                                 TUSER_LOWER_OFFSET +8];
   assign read_data_reg_sop_lower = read_data_reg[TUSER_LOWER_OFFSET + 40];
   assign read_data_reg_discontinue_lower = read_data_reg[TUSER_LOWER_OFFSET + 41];
   assign read_data_reg_tph_present_lower = read_data_reg[TUSER_LOWER_OFFSET + 42];  
   assign read_data_reg_tph_type_lower = read_data_reg[TUSER_LOWER_OFFSET + 44:
                                  TUSER_LOWER_OFFSET + 43];
   assign read_data_reg_tph_st_tag_lower = read_data_reg[TUSER_LOWER_OFFSET + 52:   
                                  TUSER_LOWER_OFFSET + 45];
  generate
    if (PARITY_ENABLE)
      begin
    assign read_data_reg_parity_lower = read_data_reg[TUSER_LOWER_OFFSET + 84:   
                                   TUSER_LOWER_OFFSET + 53];
    assign read_data_reg_eop_ptr_lower = read_data_reg[TUSER_LOWER_OFFSET + 87:
                                    TUSER_LOWER_OFFSET + 85];
      end
    else
      begin
    assign read_data_reg_parity_lower = 32'd0;
    assign read_data_reg_eop_ptr_lower = read_data_reg[TUSER_LOWER_OFFSET + 55:
                                    TUSER_LOWER_OFFSET + 53];
      end // else: !if(PARITY_ENABLE)
  endgenerate
      
   assign read_data_reg_first_be_upper = read_data_reg[TUSER_UPPER_OFFSET +3:
                               TUSER_UPPER_OFFSET];
   assign read_data_reg_last_be_upper = read_data_reg[TUSER_UPPER_OFFSET +7:
                              TUSER_UPPER_OFFSET +4];
   assign read_data_reg_byte_en_upper = read_data_reg[TUSER_UPPER_OFFSET +39:
                                 TUSER_UPPER_OFFSET +8];
   assign read_data_reg_sop_upper = read_data_reg[TUSER_UPPER_OFFSET + 40];
   assign read_data_reg_discontinue_upper = read_data_reg[TUSER_UPPER_OFFSET + 41];
   assign read_data_reg_tph_present_upper = read_data_reg[TUSER_UPPER_OFFSET + 42];  
   assign read_data_reg_tph_type_upper = read_data_reg[TUSER_UPPER_OFFSET + 44:
                                  TUSER_UPPER_OFFSET + 43];
   assign read_data_reg_tph_st_tag_upper = read_data_reg[TUSER_UPPER_OFFSET + 52:   
                                  TUSER_UPPER_OFFSET + 45];
  generate
    if (PARITY_ENABLE)
      begin
    assign read_data_reg_parity_upper = read_data_reg[TUSER_UPPER_OFFSET + 84:   
                                   TUSER_UPPER_OFFSET + 53];
    assign read_data_reg_eop_ptr_upper = read_data_reg[TUSER_UPPER_OFFSET + 87:
                               TUSER_UPPER_OFFSET + 85];
      end
    else
      begin
    assign read_data_reg_parity_upper = 32'd0;

    assign read_data_reg_eop_ptr_upper = read_data_reg[TUSER_UPPER_OFFSET + 55:
                               TUSER_UPPER_OFFSET + 53];
      end
  endgenerate

  generate
    if (PARITY_ENABLE)
      begin
    assign  read_data_reg_tlast_lower = read_data_reg[AXI4_CORE_DATA_WIDTH + AXI4_CORE_CQ_TKEEP_WIDTH +
                              AXI4_CORE_CQ_TUSER_WIDTH];
    assign     read_data_reg_tlast_upper = read_data_reg[AXI4_CORE_DATA_WIDTH*2 + AXI4_CORE_CQ_TKEEP_WIDTH*2 +
                              AXI4_CORE_CQ_TUSER_WIDTH*2 +2];
      end
    else
      begin
    assign  read_data_reg_tlast_lower = read_data_reg[AXI4_CORE_DATA_WIDTH + AXI4_CORE_CQ_TKEEP_WIDTH +
                              AXI4_CORE_CQ_TUSER_WIDTH -32];
    assign     read_data_reg_tlast_upper = read_data_reg[AXI4_CORE_DATA_WIDTH*2 + AXI4_CORE_CQ_TKEEP_WIDTH*2 +
                              AXI4_CORE_CQ_TUSER_WIDTH*2 +2 -64];
      end // else: !if(PARITY_ENABLE)
  endgenerate

   assign sop_in_lower_half = read_data_valid_reg[0] & read_data_reg_sop_lower;
   assign sop_in_upper_half = attr_straddle_en_i & read_data_valid_reg[1] & read_data_reg_sop_upper;

   assign eop_in_lower_half = read_data_valid_reg[0] & read_data_reg_tlast_lower;
   assign eop_in_upper_half = read_data_valid_reg[1] & read_data_reg_tlast_upper;
   
   assign read_data_out_first_be[3:0] = sop_in_lower_half? read_data_reg_first_be_lower: 
      sop_in_upper_half? read_data_reg_first_be_upper: 4'd0;
   assign read_data_out_first_be[7:4] = (sop_in_lower_half & sop_in_upper_half)?
      read_data_reg_first_be_upper: 4'd0;
   assign read_data_out_last_be[3:0] = sop_in_lower_half? read_data_reg_last_be_lower: 
      sop_in_upper_half? read_data_reg_last_be_upper: 4'd0;
   assign read_data_out_last_be[7:4] = (sop_in_lower_half & sop_in_upper_half)?
      read_data_reg_last_be_upper: 4'd0;
   assign read_data_out_byte_en[31:0] = read_data_valid_reg[0]? read_data_reg_byte_en_lower: 32'd0;
   assign read_data_out_byte_en[63:32] = read_data_valid_reg[1]? read_data_reg_byte_en_upper: 32'd0;
   
   assign read_data_out_is_sop[0] = sop_in_lower_half | sop_in_upper_half;
   assign read_data_out_is_sop[1] = sop_in_lower_half & sop_in_upper_half;

   assign read_data_out_is_sop0_ptr[1] = ~sop_in_lower_half & sop_in_upper_half;
   assign read_data_out_is_sop0_ptr[0] = 1'b0;
   assign read_data_out_is_sop1_ptr[1] = read_data_out_is_sop[1];
   assign read_data_out_is_sop1_ptr[0] = 1'b0;
   assign read_data_out_is_eop[0] = eop_in_lower_half | eop_in_upper_half;
   assign read_data_out_is_eop[1] = attr_straddle_en_i & eop_in_lower_half & eop_in_upper_half;
   assign read_data_out_is_eop0_ptr[3:0] = eop_in_lower_half? {1'b0, read_data_reg_eop_ptr_lower}:
      eop_in_upper_half? {1'b1, read_data_reg_eop_ptr_upper}: 4'd0;
   assign read_data_out_is_eop1_ptr[3:0] = (attr_straddle_en_i & eop_in_lower_half & eop_in_upper_half)?
      {1'b1, read_data_reg_eop_ptr_upper}: 4'd0;
   assign read_data_out_discontinue = (read_data_valid_reg[0] & read_data_reg_discontinue_lower) |
      (read_data_valid_reg[1] & read_data_reg_discontinue_upper);      

   assign read_data_out_tph_present[0] = sop_in_lower_half? read_data_reg_tph_present_lower:
      sop_in_upper_half? read_data_reg_tph_present_upper: 1'b0;
   assign read_data_out_tph_present[1] = (sop_in_lower_half & sop_in_upper_half)? read_data_reg_tph_present_upper: 1'b0;

   assign read_data_out_tph_type[1:0] = sop_in_lower_half? read_data_reg_tph_type_lower[1:0]:
      sop_in_upper_half? read_data_reg_tph_type_upper[1:0]: 2'd0;
   assign read_data_out_tph_type[3:2] = (sop_in_lower_half & sop_in_upper_half)? read_data_reg_tph_type_upper[1:0]: 2'd0;

   assign read_data_out_tph_st_tag[7:0] = sop_in_lower_half? read_data_reg_tph_st_tag_lower[7:0]:
      sop_in_upper_half? read_data_reg_tph_st_tag_upper[7:0]: 8'd0;
   assign read_data_out_tph_st_tag[15:8] = (sop_in_lower_half & sop_in_upper_half)? read_data_reg_tph_st_tag_upper[7:0]: 8'd0;

   assign read_data_out_parity[31:0] = read_data_valid_reg[0]? read_data_reg_parity_lower: 32'd0;
   assign read_data_out_parity[63:32] = read_data_valid_reg[1]? read_data_reg_parity_upper: 32'd0;

   assign read_data_out_tuser = {
                 read_data_out_parity[63:0],
                 read_data_out_tph_st_tag[15:0],
                 read_data_out_tph_type[3:0],
                 read_data_out_tph_present[1:0],
                 read_data_out_discontinue,
                 read_data_out_is_eop1_ptr[3:0],
                 read_data_out_is_eop0_ptr[3:0],
                 read_data_out_is_eop[1:0],
                 read_data_out_is_sop1_ptr[1:0],
                 read_data_out_is_sop0_ptr[1:0],
                 read_data_out_is_sop[1:0],
                 read_data_out_byte_en[63:0],
                 read_data_out_last_be[7:0],
                 read_data_out_first_be[7:0]
                 };


   assign read_data_out_tdata[AXI4_USER_DATA_WIDTH/2-1:0] = read_data_valid_reg[0]? read_data_reg[AXI4_CORE_DATA_WIDTH-1:0]:
      {AXI4_USER_DATA_WIDTH/2{1'b0}};
   assign read_data_out_tdata[AXI4_USER_DATA_WIDTH-1:AXI4_USER_DATA_WIDTH/2] = read_data_valid_reg[1]?
      read_data_reg[FIFO_READ_DATA_UPPER_OFFSET+AXI4_CORE_DATA_WIDTH-1:FIFO_READ_DATA_UPPER_OFFSET]: {AXI4_USER_DATA_WIDTH/2{1'b0}};
   
  assign  read_data_out_tkeep[AXI4_USER_CQ_TKEEP_WIDTH/2-1:0] = attr_straddle_en_i? {AXI4_USER_CQ_TKEEP_WIDTH/2{1'b1}}:
      read_data_valid_reg[0]? 
      read_data_reg[AXI4_CORE_DATA_WIDTH+AXI4_CORE_CQ_TKEEP_WIDTH-1:AXI4_CORE_DATA_WIDTH]: {AXI4_USER_CQ_TKEEP_WIDTH/2{1'b0}};
   assign read_data_out_tkeep[AXI4_USER_CQ_TKEEP_WIDTH-1:AXI4_USER_CQ_TKEEP_WIDTH/2] = attr_straddle_en_i? {AXI4_USER_CQ_TKEEP_WIDTH/2{1'b1}}:
      read_data_valid_reg[1]? 
      read_data_reg[FIFO_READ_TKEEP_UPPER_OFFSET+AXI4_CORE_CQ_TKEEP_WIDTH-1:FIFO_READ_TKEEP_UPPER_OFFSET]:
      {AXI4_USER_CQ_TKEEP_WIDTH/2{1'b0}};

   assign read_data_out_tlast = attr_straddle_en_i? 1'b0: (eop_in_lower_half | eop_in_upper_half);

   assign output_mux_in_data = {
                read_data_out_tlast,
                read_data_out_tuser,
                read_data_out_tkeep,
                read_data_out_tdata
                };

   // Instance of output MUX
   pcie_bridge_rc_pcie4c_ip_512b_cq_output_mux #
     (
      .TCQ(TCQ),
      .IMPL_TARGET(IMPL_TARGET),
      .IN_DATA_WIDTH(OUTPUT_MUX_IN_DATA_WIDTH),
      .OUT_DATA_WIDTH(AXI4_USER_DATA_WIDTH),
      .TUSER_WIDTH(AXI4_USER_CQ_TUSER_WIDTH),
      .TKEEP_WIDTH(AXI4_USER_CQ_TKEEP_WIDTH)
      )
     pcie_4_0_512b_cq_output_mux_blk
       (
        .clk_i(user_clk_i),
        .reset_n_i(reset_n_user_clk_i),
        .link_down_reset_i(link_down_reset_i),
        .attr_mcap_input_gate_design_switch_i(attr_mcap_input_gate_design_switch_i),
        .conf_mcap_design_switch_i(conf_mcap_design_switch_i),
    .in_data_i(output_mux_in_data),
    .in_data_valid_i(read_data_valid_reg[0]),
        .attr_straddle_en_i(attr_straddle_en_i),

    .upstream_ready_o(output_mux_ready),
    .out_data_o(m_axis_cq_tdata_o),
        .out_data_valid_o(m_axis_cq_tvalid_o),
    .out_tuser_o(m_axis_cq_tuser_o),
    .out_tlast_o(m_axis_cq_tlast_o),
    .out_tkeep_o(m_axis_cq_tkeep_o),
    .downstream_ready_i(m_axis_cq_tready_i),
    
    .pcie_cq_np_req_i(pcie_cq_np_req_i),
    .pcie_cq_np_req_count_o(pcie_cq_np_req_count_o),
    .np_credit_received_o(cq_np_user_credit_rcvd_user_clk),
    .posted_req_delivered_o(posted_req_delivered_user_clk),
    .pipeline_empty_o(out_mux_pipeline_empty)
    );

   // Change clock domain for np_user_credit_rcvd signal
   always @(posedge user_clk2_i)
     if (~reset_n_user_clk2_i)
       cq_np_user_credit_rcvd_o <= #TCQ 1'b0;
     else
       if (user_clk_en_i)
     cq_np_user_credit_rcvd_o <= #TCQ cq_np_user_credit_rcvd_user_clk[0];
       else
     cq_np_user_credit_rcvd_o <= #TCQ cq_np_user_credit_rcvd_user_clk[1];

   // Change clock domain for posted_req_delivered signal
   always @(posedge user_clk2_i)
     if (~reset_n_user_clk2_i)
       posted_req_delivered_o <= #TCQ 1'b0;
     else
       if (user_clk_en_i)
     posted_req_delivered_o <= #TCQ posted_req_delivered_user_clk[0];
       else
     posted_req_delivered_o <= #TCQ posted_req_delivered_user_clk[1];

   assign pipeline_empty_user_clk = out_mux_pipeline_empty &&
      (read_data_valid_reg == 2'b00) &&
      ~fifo_read_data_valid &&
      ~fifo_in_data_valid_reg;

   always @(posedge user_clk2_i)
     if (~reset_n_user_clk2_i)
       pipeline_empty_core_clk <= #TCQ 1'b0;
     else
       pipeline_empty_core_clk <= #TCQ pipeline_empty_user_clk;

   always @(posedge user_clk2_i)
     if (~reset_n_user_clk2_i)
       cq_pipeline_empty_reg <= #TCQ 3'b111;
     else
       begin
      // Wait for pipeline empty signals to stay asserted for 3 cycles before signaling the output.
      cq_pipeline_empty_reg[0] <= #TCQ pipeline_empty_core_clk &
                      ~core_cq_tvalid_i &
                      ~core_cq_tvalid_reg_lower &
                      ~core_cq_tvalid_reg_upper;
         cq_pipeline_empty_reg[1] <= #TCQ cq_pipeline_empty_reg[0];
         cq_pipeline_empty_reg[2] <= #TCQ cq_pipeline_empty_reg[1];
      cq_pipeline_empty_o <= #TCQ &cq_pipeline_empty_reg;
       end // else: !if(~reset_n_user_clk2_i)
         

endmodule // pcie_4_0_512b_cq_intfc








   
