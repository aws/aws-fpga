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
// File       : pcie4_uscale_plus_0_512b_cc_intfc.v
// Version    : 1.1 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------
`timescale 1ps/1ps
(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie4_uscale_plus_0_512b_cc_intfc #(
   parameter TCQ = 100,
   parameter IMPL_TARGET = "SOFT",
   parameter AXI4_USER_DATA_WIDTH = 512,
   parameter AXI4_CORE_DATA_WIDTH = 256,
   parameter AXI4_USER_CC_TUSER_WIDTH = 81,
   parameter AXI4_CORE_CC_TUSER_WIDTH = 33,
   parameter AXI4_USER_CC_TKEEP_WIDTH = 16,
   parameter AXI4_CORE_CC_TKEEP_WIDTH = 8,
   parameter AXI4_CORE_CC_TREADY_WIDTH = 4,
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
   ,input wire [1:0]      attr_alignment_mode_i // Payload alignment mode
                                                // (00= Dword-aligned, 10 = 128b address-aligned)
   ,input wire            attr_axisten_if_rq_cc_registered_tready_i // 0 = registered_tready enabled, 1 = registered_tready disabled
   //-----------------------------------------------------------------------------------------------
   // Client-side signals
   //-----------------------------------------------------------------------------------------------
   ,input wire [AXI4_USER_DATA_WIDTH-1:0]    s_axis_cc_tdata_i
   ,input wire            s_axis_cc_tvalid_i
   ,input wire [AXI4_USER_CC_TUSER_WIDTH-1:0]     s_axis_cc_tuser_i
   ,input wire            s_axis_cc_tlast_i
   ,input wire [AXI4_USER_CC_TKEEP_WIDTH-1:0]     s_axis_cc_tkeep_i
   ,output reg            s_axis_cc_tready_o   
   //-----------------------------------------------------------------------------------------------
   // Core-side signals
   //-----------------------------------------------------------------------------------------------
   ,output wire [AXI4_CORE_DATA_WIDTH-1:0]    core_cc_tdata_o
   ,output wire            core_cc_tvalid_o
   ,output wire [AXI4_CORE_CC_TUSER_WIDTH-1:0]   core_cc_tuser_o
   ,output wire            core_cc_tlast_o
   ,output wire [AXI4_CORE_CC_TKEEP_WIDTH-1:0]   core_cc_tkeep_o
   ,input wire [AXI4_CORE_CC_TREADY_WIDTH-1:0] core_cc_tready_i
   );

   localparam FIFO_IN_DATA_WIDTH = AXI4_USER_DATA_WIDTH + AXI4_USER_CC_TKEEP_WIDTH + AXI4_CORE_CC_TUSER_WIDTH*2 +
                   2;
   localparam FIFO_OUT_DATA_WIDTH = FIFO_IN_DATA_WIDTH/2;

   localparam OUTPUT_MUX_IN_DATA_WIDTH = AXI4_CORE_DATA_WIDTH + AXI4_CORE_CC_TKEEP_WIDTH + AXI4_CORE_CC_TUSER_WIDTH + 1;

   reg [AXI4_USER_DATA_WIDTH-1:0] s_axis_cc_tdata_reg;
   reg                   s_axis_cc_tvalid_reg_lower;
   reg                   s_axis_cc_tvalid_reg_upper;
   reg [AXI4_USER_CC_TKEEP_WIDTH-1:0] s_axis_cc_tkeep_reg;
   reg                       s_axis_cc_tlast_reg_lower;
   reg                       s_axis_cc_tlast_reg_upper;
   reg [AXI4_USER_CC_TUSER_WIDTH-1:0] s_axis_cc_tuser_reg;

   wire [1:0]                   s_axis_cc_sop;
   wire [1:0]                   s_axis_cc_eop;
   wire [1:0]                   s_axis_cc_sop0_ptr;
   wire [3:0]                   s_axis_cc_eop0_ptr;
   wire [3:0]                   s_axis_cc_eop1_ptr;
   wire [63:0]                   s_axis_cc_parity;

   wire [AXI4_CORE_CC_TUSER_WIDTH*2-1:0] fifo_in_data_tuser;
   wire [1:0]                  fifo_in_data_tlast;

  wire [FIFO_IN_DATA_WIDTH-1:0]      fifo_in_data;
   wire [1:0]                 fifo_in_data_valid;
   wire                  fifo_almost_full_user_clk;

   reg                      s_axis_cc_tuser_discontinue_reg_lower;
   reg                      s_axis_cc_tuser_discontinue_reg_upper;

  wire [FIFO_OUT_DATA_WIDTH-1:0]      fifo_read_data;
   wire                  fifo_read_data_valid;
   wire                  output_mux_ready;

  reg [AXI4_CORE_CC_TREADY_WIDTH-1:0]      core_cc_tready_reg;
  wire [AXI4_CORE_CC_TREADY_WIDTH-1:0]      core_cc_tready_int;

   // Register input data

  assign                  s_axis_cc_sop[1:0] =  s_axis_cc_tuser_i[1:0];
  assign                  s_axis_cc_sop0_ptr[1:0] =  s_axis_cc_tuser_i[3:2];
  assign                  s_axis_cc_eop[1:0] =  s_axis_cc_tuser_i[7:6];
  assign                  s_axis_cc_eop0_ptr[3:0] =  s_axis_cc_tuser_i[11:8];
  assign                  s_axis_cc_eop1_ptr[3:0] =  s_axis_cc_tuser_i[15:12];

   always @(posedge user_clk_i)
     if (~reset_n_user_clk_i)
       begin
      s_axis_cc_tdata_reg <= {AXI4_USER_DATA_WIDTH{1'b0}};
      s_axis_cc_tvalid_reg_lower <= 1'b0;
      s_axis_cc_tvalid_reg_upper <= 1'b0;
      s_axis_cc_tkeep_reg <= {AXI4_USER_CC_TKEEP_WIDTH{1'b0}};
      s_axis_cc_tuser_reg <= {AXI4_USER_CC_TUSER_WIDTH{1'b0}};
     s_axis_cc_tuser_discontinue_reg_lower <= 1'b0;
     s_axis_cc_tuser_discontinue_reg_upper <= 1'b0;
     s_axis_cc_tlast_reg_lower <= 1'b0;
     s_axis_cc_tlast_reg_upper <= 1'b0;
       end
     else
       begin
      s_axis_cc_tdata_reg <= s_axis_cc_tdata_i;
      s_axis_cc_tvalid_reg_lower <= s_axis_cc_tvalid_i & s_axis_cc_tready_o;
      s_axis_cc_tvalid_reg_upper <= attr_straddle_en_i? s_axis_cc_tvalid_i & s_axis_cc_tready_o &
                    (~s_axis_cc_eop[0] | s_axis_cc_eop0_ptr[3] |
                     (s_axis_cc_sop[0] & s_axis_cc_sop0_ptr[1]) |
                     s_axis_cc_sop[1]):
                    s_axis_cc_tvalid_i & s_axis_cc_tready_o &
                    (~s_axis_cc_tlast_i | s_axis_cc_tkeep_i[8]);
     // Generate tkeep settings for core side
     if (~attr_straddle_en_i)
       s_axis_cc_tkeep_reg[7:0] <= s_axis_cc_tkeep_i[7:0];
     else if (s_axis_cc_tvalid_i & s_axis_cc_tready_o)
       begin
         if (~s_axis_cc_eop[0] | s_axis_cc_eop0_ptr[3])
           s_axis_cc_tkeep_reg[7:0] <= 8'hff;
         else
           case(s_axis_cc_eop0_ptr[2:0])
         3'd0: s_axis_cc_tkeep_reg[7:0] <= 8'h01;
         3'd1: s_axis_cc_tkeep_reg[7:0] <= 8'h03;
         3'd2: s_axis_cc_tkeep_reg[7:0] <= 8'h07;
         3'd3: s_axis_cc_tkeep_reg[7:0] <= 8'h0f;
         3'd4: s_axis_cc_tkeep_reg[7:0] <= 8'h1f;
         3'd5: s_axis_cc_tkeep_reg[7:0] <= 8'h3f;
         3'd6: s_axis_cc_tkeep_reg[7:0] <= 8'h7f;
         default: s_axis_cc_tkeep_reg[7:0] <= 8'hff;
           endcase // case(s_axis_cc_eop0_ptr[2:0])
       end // if (s_axis_cc_tvalid_i & s_axis_cc_tready_o)
     else
       s_axis_cc_tkeep_reg[7:0] <= 8'd0;
         
     if (~attr_straddle_en_i)
       s_axis_cc_tkeep_reg[15:8] <= s_axis_cc_tkeep_i[15:8];
     else if (s_axis_cc_tvalid_i & s_axis_cc_tready_o)
       begin
         if (~s_axis_cc_eop[0])
           s_axis_cc_tkeep_reg[15:8] <= 8'hff;
         else if (s_axis_cc_eop0_ptr[3])
           case(s_axis_cc_eop0_ptr[2:0])
         3'd0: s_axis_cc_tkeep_reg[15:8] <= 8'h01;
         3'd1: s_axis_cc_tkeep_reg[15:8] <= 8'h03;
         3'd2: s_axis_cc_tkeep_reg[15:8] <= 8'h07;
         3'd3: s_axis_cc_tkeep_reg[15:8] <= 8'h0f;
         3'd4: s_axis_cc_tkeep_reg[15:8] <= 8'h1f;
         3'd5: s_axis_cc_tkeep_reg[15:8] <= 8'h3f;
         3'd6: s_axis_cc_tkeep_reg[15:8] <= 8'h7f;
         default: s_axis_cc_tkeep_reg[15:8] <= 8'hff;
           endcase // case(s_axis_cc_eop0_ptr[2:0])
         else if ((s_axis_cc_sop[0] && (s_axis_cc_sop0_ptr[1]))||
              s_axis_cc_sop[1])
           // Packet starting in second half
           begin
         if (~s_axis_cc_eop[1])
           s_axis_cc_tkeep_reg[15:8] <= 8'hff;
         else
           case(s_axis_cc_eop1_ptr[2:0])
             3'd2: s_axis_cc_tkeep_reg[15:8] <= 8'h07;
             3'd3: s_axis_cc_tkeep_reg[15:8] <= 8'h0f;
             3'd4: s_axis_cc_tkeep_reg[15:8] <= 8'h1f;
             3'd5: s_axis_cc_tkeep_reg[15:8] <= 8'h3f;
             3'd6: s_axis_cc_tkeep_reg[15:8] <= 8'h7f;
             default: s_axis_cc_tkeep_reg[15:8] <= 8'hff;
           endcase // case(s_axis_cc_eop1_ptr[2:0])
           end // if ((s_axis_cc_sop[0] && (s_axis_cc_sop0_ptr[1]))||...
         else
           s_axis_cc_tkeep_reg[15:8] <= 8'd0;
       end // if (s_axis_cc_tvalid_i & s_axis_cc_tready_o)
     else
       s_axis_cc_tkeep_reg[15:8] <= 8'd0;

      s_axis_cc_tuser_reg <= s_axis_cc_tuser_i;
     // Generate discontinue for lower and upper halves
     if (~attr_straddle_en_i) 
       begin
         s_axis_cc_tuser_discontinue_reg_lower <= s_axis_cc_tuser_i[16] &
                              (~s_axis_cc_tlast_i |
                               ~s_axis_cc_tkeep_i[8]);
         s_axis_cc_tuser_discontinue_reg_upper <= s_axis_cc_tuser_i[16] &
                              (~s_axis_cc_tlast_i |
                               s_axis_cc_tkeep_i[8]);
       end // if (~attr_straddle_en_i)
     else
       begin
         s_axis_cc_tuser_discontinue_reg_lower <= s_axis_cc_tuser_i[16] &
                              (~s_axis_cc_eop[0] |
                               ~s_axis_cc_eop0_ptr[3]);
         s_axis_cc_tuser_discontinue_reg_upper <= s_axis_cc_tuser_i[16] &
                              (~s_axis_cc_eop[0] |
                               s_axis_cc_eop0_ptr[3]);
       end // else: !if(~attr_straddle_en_i)

     // Generate tlast for lower and upper halves
     s_axis_cc_tlast_reg_lower <= attr_straddle_en_i? (s_axis_cc_eop[0] & ~s_axis_cc_eop0_ptr[3]):
                      s_axis_cc_tlast_i & ~s_axis_cc_tkeep_i[8];
     s_axis_cc_tlast_reg_upper <= attr_straddle_en_i? (s_axis_cc_eop[0] & s_axis_cc_eop0_ptr[3]) |
                      s_axis_cc_eop[1]:
                      s_axis_cc_tlast_i & s_axis_cc_tkeep_i[8];
       end // else: !if(~reset_n_user_clk_i)

  assign  s_axis_cc_parity[63:0] =  PARITY_ENABLE? s_axis_cc_tuser_reg[80:17] : 64'd0;

   // Generate the tuser signals for the core side
   // discontinue
  assign  fifo_in_data_tuser[0] = s_axis_cc_tuser_discontinue_reg_lower;
  assign  fifo_in_data_tuser[AXI4_CORE_CC_TUSER_WIDTH+0] = s_axis_cc_tuser_discontinue_reg_upper;
   // parity
   assign fifo_in_data_tuser[32:1] = s_axis_cc_parity[31:0];
   assign fifo_in_data_tuser[AXI4_CORE_CC_TUSER_WIDTH+32:AXI4_CORE_CC_TUSER_WIDTH+1] = s_axis_cc_parity[63:32];
   
   // Generate tlast for lower and upper halves
  assign fifo_in_data_tlast[0] = s_axis_cc_tlast_reg_lower;
  assign fifo_in_data_tlast[1] = s_axis_cc_tlast_reg_upper;
   
   // Generate valid for upper half
  assign fifo_in_data_valid[0] = s_axis_cc_tvalid_reg_lower;
  assign fifo_in_data_valid[1] = s_axis_cc_tvalid_reg_upper;

   assign fifo_in_data[AXI4_CORE_DATA_WIDTH-1:0] = s_axis_cc_tdata_reg[AXI4_CORE_DATA_WIDTH-1:0];
   assign fifo_in_data[FIFO_IN_DATA_WIDTH/2+AXI4_CORE_DATA_WIDTH-1:FIFO_IN_DATA_WIDTH/2] =
      s_axis_cc_tdata_reg[AXI4_CORE_DATA_WIDTH*2-1:AXI4_CORE_DATA_WIDTH];

   assign fifo_in_data[AXI4_CORE_DATA_WIDTH + AXI4_CORE_CC_TKEEP_WIDTH-1: AXI4_CORE_DATA_WIDTH] =
      s_axis_cc_tkeep_reg[AXI4_CORE_CC_TKEEP_WIDTH-1:0];
  assign  fifo_in_data[FIFO_IN_DATA_WIDTH/2 + AXI4_CORE_DATA_WIDTH + AXI4_CORE_CC_TKEEP_WIDTH-1:
               FIFO_IN_DATA_WIDTH/2 + AXI4_CORE_DATA_WIDTH] =
      s_axis_cc_tkeep_reg[AXI4_CORE_CC_TKEEP_WIDTH*2-1:AXI4_CORE_CC_TKEEP_WIDTH];

   assign fifo_in_data[AXI4_CORE_DATA_WIDTH + AXI4_CORE_CC_TKEEP_WIDTH +  AXI4_CORE_CC_TUSER_WIDTH-1:
               AXI4_CORE_DATA_WIDTH + AXI4_CORE_CC_TKEEP_WIDTH] = 
      fifo_in_data_tuser[AXI4_CORE_CC_TUSER_WIDTH-1:0];
   assign fifo_in_data[FIFO_IN_DATA_WIDTH/2 + AXI4_CORE_DATA_WIDTH + AXI4_CORE_CC_TKEEP_WIDTH +  AXI4_CORE_CC_TUSER_WIDTH-1:
               FIFO_IN_DATA_WIDTH/2 + AXI4_CORE_DATA_WIDTH + AXI4_CORE_CC_TKEEP_WIDTH] = 
      fifo_in_data_tuser[AXI4_CORE_CC_TUSER_WIDTH*2-1:AXI4_CORE_CC_TUSER_WIDTH];

   assign fifo_in_data[AXI4_CORE_DATA_WIDTH + AXI4_CORE_CC_TKEEP_WIDTH +  AXI4_CORE_CC_TUSER_WIDTH] =
      fifo_in_data_tlast[0];
   assign fifo_in_data[FIFO_IN_DATA_WIDTH/2 + AXI4_CORE_DATA_WIDTH + AXI4_CORE_CC_TKEEP_WIDTH +  AXI4_CORE_CC_TUSER_WIDTH] =
      fifo_in_data_tlast[1];

   // De-assert ready when FIFO is almost full
   always @(posedge user_clk_i)
     if (~reset_n_user_clk_i)
       s_axis_cc_tready_o <= 1'b0;
     else
       s_axis_cc_tready_o <= #(TCQ) ~fifo_almost_full_user_clk;

  // Register tready from hard block
   always @(posedge user_clk2_i)
     if (~reset_n_user_clk2_i)
       core_cc_tready_reg <= {AXI4_CORE_CC_TREADY_WIDTH{1'b0}};
     else
       core_cc_tready_reg <= core_cc_tready_i;

  assign  core_cc_tready_int = attr_axisten_if_rq_cc_registered_tready_i?
      core_cc_tready_reg : core_cc_tready_i;

   // Async FIFO
   pcie4_uscale_plus_0_512b_async_fifo #
     (
      .TCQ(TCQ),
      .IMPL_TARGET(IMPL_TARGET),
      .IN_DATA_WIDTH(FIFO_IN_DATA_WIDTH),
      .FIFO_WIDTH(FIFO_OUT_DATA_WIDTH),
      .FIFO_DEPTH(16),
      .FIFO_ALMOST_FULL_THRESHOLD(7)
      )
     pcie_4_0_512b_async_fifo_blk
       (
    // Write side
    .clk_i(user_clk2_i),
    .clk_en_i(user_clk_en_i),
        .reset_n_i(reset_n_user_clk2_i),
        .link_down_reset_i(link_down_reset_i),
    .write_data_i(fifo_in_data),
    .write_en_i(fifo_in_data_valid),
    .fifo_almost_full_o(fifo_almost_full_user_clk),
    // Read side
    .read_en_i(output_mux_ready),
    .read_data_o(fifo_read_data),
    .read_data_valid_o(fifo_read_data_valid)
    );

   // Instance of output MUX
   pcie4_uscale_plus_0_512b_cc_output_mux #
     (
      .TCQ(TCQ),
      .IMPL_TARGET(IMPL_TARGET),
      .IN_DATA_WIDTH(OUTPUT_MUX_IN_DATA_WIDTH),
      .OUT_DATA_WIDTH(AXI4_CORE_DATA_WIDTH),
      .TUSER_WIDTH(AXI4_CORE_CC_TUSER_WIDTH),
      .TKEEP_WIDTH(AXI4_CORE_CC_TKEEP_WIDTH),
      .TREADY_WIDTH(AXI4_CORE_CC_TREADY_WIDTH)
      )
     pcie_4_0_512b_cc_output_mux_blk
       (
        .clk_i(user_clk2_i),
        .reset_n_i(reset_n_user_clk2_i),
        .link_down_reset_i(link_down_reset_i),
    .in_data_i(fifo_read_data),
    .in_data_valid_i(fifo_read_data_valid),
    .upstream_ready_o(output_mux_ready),

    .out_data_o(core_cc_tdata_o),
        .out_data_valid_o(core_cc_tvalid_o),
    .out_tuser_o(core_cc_tuser_o),
    .out_tlast_o(core_cc_tlast_o),
    .out_tkeep_o(core_cc_tkeep_o),
    .downstream_ready_i(core_cc_tready_int)
    );


endmodule // pcie4_0_512b_cc_intfc







   
