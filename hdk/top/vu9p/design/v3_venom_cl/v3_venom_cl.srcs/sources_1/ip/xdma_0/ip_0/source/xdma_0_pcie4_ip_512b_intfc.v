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
// File       : xdma_0_pcie4_ip_512b_intfc.v
// Version    : 1.1 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------
`timescale 1ps/1ps
(* DowngradeIPIdentifiedWarnings = "yes" *)
module xdma_0_pcie4_ip_512b_intfc #(
     parameter           TCQ = 100
   , parameter           IMPL_TARGET = "SOFT"
   , parameter           AXISTEN_IF_EXT_512_INTFC_RAM_STYLE = "BRAM"
   , parameter           AXISTEN_IF_RQ_CC_REGISTERED_TREADY = "TRUE"
   , parameter           AXI4_USER_DATA_WIDTH = 512
   , parameter           AXI4_CORE_DATA_WIDTH = 256
   , parameter           AXI4_USER_CQ_TUSER_WIDTH = 183
   , parameter           AXI4_USER_CC_TUSER_WIDTH = 81
   , parameter           AXI4_USER_RQ_TUSER_WIDTH = 137
   , parameter           AXI4_USER_RC_TUSER_WIDTH = 161
   , parameter           AXI4_CORE_CQ_TUSER_WIDTH = 88
   , parameter           AXI4_CORE_CC_TUSER_WIDTH = 33
   , parameter           AXI4_CORE_RQ_TUSER_WIDTH = 62
   , parameter           AXI4_CORE_RC_TUSER_WIDTH = 75
   , parameter           AXI4_USER_CQ_TKEEP_WIDTH = 16
   , parameter           AXI4_USER_CC_TKEEP_WIDTH = 16
   , parameter           AXI4_USER_RQ_TKEEP_WIDTH = 16
   , parameter           AXI4_USER_RC_TKEEP_WIDTH = 16
   , parameter           AXI4_CORE_CQ_TKEEP_WIDTH = 8
   , parameter           AXI4_CORE_CC_TKEEP_WIDTH = 8
   , parameter           AXI4_CORE_RQ_TKEEP_WIDTH = 8
   , parameter           AXI4_CORE_RC_TKEEP_WIDTH = 8
   , parameter           AXI4_CORE_CQ_TREADY_WIDTH = 22  
   , parameter           AXI4_CORE_RC_TREADY_WIDTH = 22  
   , parameter           AXISTEN_IF_EXT_512_CQ_STRADDLE="FALSE"
   , parameter           AXISTEN_IF_EXT_512_CC_STRADDLE="FALSE"
   , parameter           AXISTEN_IF_EXT_512_RQ_STRADDLE="FALSE"
   , parameter           AXISTEN_IF_EXT_512_RC_STRADDLE="FALSE"
   , parameter           AXISTEN_IF_EXT_512_RC_4TLP_STRADDLE="TRUE"
   , parameter [1:0]     AXISTEN_IF_CQ_ALIGNMENT_MODE=2'b00
   , parameter [1:0]     AXISTEN_IF_CC_ALIGNMENT_MODE=2'b00
   , parameter [1:0]     AXISTEN_IF_RQ_ALIGNMENT_MODE=2'b00
   , parameter [1:0]     AXISTEN_IF_RC_ALIGNMENT_MODE=2'b00
   , parameter           AXISTEN_IF_RX_PARITY_EN="TRUE"
   , parameter           AXISTEN_IF_TX_PARITY_EN="TRUE"
   ) 
  (
    input  wire           user_clk2_i // 500 MHz clock for core-facing interfaces
   ,input  wire           user_clk_i // 250 MHz clock for client-facing interfaces
   ,input  wire           user_clk_en_i // User clock enable for clock domain crossing
   ,input  wire           reset_n_user_clk_i // Reset in the user clock domain
   ,input  wire           reset_n_user_clk2_i // Reset in the user clock2 domain
   ,input  wire           link_down_reset_i // Link went down
   //-----------------------------------------------------------------------------------------------
   // Client-side interfaces
   //-----------------------------------------------------------------------------------------------
   // CQ Interface
   ,output wire [511:0]   m_axis_cq_tdata_o
   ,output wire           m_axis_cq_tvalid_o
   ,output wire [182:0]   m_axis_cq_tuser_o
   ,output wire           m_axis_cq_tlast_o
   ,output wire [15:0]    m_axis_cq_tkeep_o
   ,input  wire           m_axis_cq_tready_i
   ,input  wire [1:0]     pcie_cq_np_req_i // Client request to deliver NP TLP
   ,output wire [5:0]      pcie_cq_np_req_count_o // Current value of interface credit count for NP TLPs
   // CC Interface
   ,input wire [511:0]    s_axis_cc_tdata_i
   ,input wire            s_axis_cc_tvalid_i
   ,input wire [80:0]     s_axis_cc_tuser_i
   ,input wire            s_axis_cc_tlast_i
   ,input wire [15:0]     s_axis_cc_tkeep_i
   ,output wire            s_axis_cc_tready_o   
   // RQ Interface
   ,input wire [511:0]    s_axis_rq_tdata_i
   ,input wire            s_axis_rq_tvalid_i
   ,input wire [136:0]    s_axis_rq_tuser_i
   ,input wire            s_axis_rq_tlast_i
   ,input wire [15:0]     s_axis_rq_tkeep_i
   ,output wire            s_axis_rq_tready_o   
   // RC Interface
   ,output wire [511:0]   m_axis_rc_tdata_o
   ,output wire           m_axis_rc_tvalid_o
   ,output wire [160:0]   m_axis_rc_tuser_o
   ,output wire           m_axis_rc_tlast_o
   ,output wire [15:0]    m_axis_rc_tkeep_o
   ,input  wire           m_axis_rc_tready_i
   //-----------------------------------------------------------------------------------------------
   // Core-side interfaces
   //-----------------------------------------------------------------------------------------------
   // CQ Interface
   ,input  wire [255:0]   core_cq_tdata_i
   ,input  wire           core_cq_tvalid_i
   ,input  wire [87:0]    core_cq_tuser_i
   ,input  wire           core_cq_tlast_i
   ,input  wire [7:0]     core_cq_tkeep_i
   ,output wire [21:0]     core_cq_tready_o
   ,output wire            posted_req_delivered_o // Signals the delivery of a Posted Req on the CQ interface
   ,output wire            cq_pipeline_empty_o // Indicates that the entire CQ pipeline of the bridge is empty.
   ,output wire            cq_np_user_credit_rcvd_o // Indicates that the user issued one NP credit
   // CC Interface
   ,output wire [255:0]    core_cc_tdata_o
   ,output wire            core_cc_tvalid_o
   ,output wire [32:0]     core_cc_tuser_o
   ,output wire            core_cc_tlast_o
   ,output wire [7:0]      core_cc_tkeep_o
   ,input wire [3:0]      core_cc_tready_i
   // RQ Interface
   ,output wire [255:0]    core_rq_tdata_o
   ,output wire            core_rq_tvalid_o
   ,output wire [61:0]     core_rq_tuser_o
   ,output wire            core_rq_tlast_o
   ,output wire [7:0]      core_rq_tkeep_o
   ,input wire [3:0]      core_rq_tready_i
   // RC Interface
   ,input  wire [255:0]   core_rc_tdata_i
   ,input  wire           core_rc_tvalid_i
   ,input  wire [74:0]    core_rc_tuser_i
   ,input  wire           core_rc_tlast_i
   ,input  wire [7:0]     core_rc_tkeep_i
   ,output wire [21:0]     core_rc_tready_o
   // Completion delivered indications
   ,output wire [1:0]      compl_delivered_o // Completions delivered to user
                                            // 00 = No Compl, 01 = 1 Compl, 11 = 2 Completions
   ,output wire [7:0]      compl_delivered_tag0_o// Tag associated with first delivered Completion
   ,output wire [7:0]      compl_delivered_tag1_o// Tag associated with second delivered Completion
   );

  wire        attr_axisten_if_ext_512_cq_straddle;
  wire        attr_axisten_if_ext_512_cc_straddle;
  wire        attr_axisten_if_ext_512_rq_straddle;
  wire        attr_axisten_if_ext_512_rc_straddle;
  wire        attr_axisten_if_ext_512_rc_4tlp_straddle;
  wire [1:0] attr_axisten_if_cq_alignment_mode;
  wire [1:0] attr_axisten_if_cc_alignment_mode;
  wire [1:0] attr_axisten_if_rq_alignment_mode;
  wire [1:0] attr_axisten_if_rc_alignment_mode;
  wire     attr_axisten_if_rq_cc_registered_tready;
  wire        spare_bit0;
  
  generate
    if (AXISTEN_IF_EXT_512_CQ_STRADDLE == "TRUE")
      assign attr_axisten_if_ext_512_cq_straddle = 1'b1;
    else
      assign attr_axisten_if_ext_512_cq_straddle = 1'b0;
  endgenerate
  
  generate
    if (AXISTEN_IF_EXT_512_CC_STRADDLE == "TRUE")
      assign attr_axisten_if_ext_512_cc_straddle = 1'b1;
    else
      assign attr_axisten_if_ext_512_cc_straddle = 1'b0;
  endgenerate

  generate
    if (AXISTEN_IF_EXT_512_RQ_STRADDLE == "TRUE")
      assign attr_axisten_if_ext_512_rq_straddle = 1'b1;
    else
      assign attr_axisten_if_ext_512_rq_straddle = 1'b0;
  endgenerate

  generate
    if (AXISTEN_IF_EXT_512_RC_STRADDLE == "TRUE")
      assign attr_axisten_if_ext_512_rc_straddle = 1'b1;
    else
      assign attr_axisten_if_ext_512_rc_straddle = 1'b0;
  endgenerate

  generate
    if (AXISTEN_IF_EXT_512_RC_4TLP_STRADDLE == "TRUE")
      assign attr_axisten_if_ext_512_rc_4tlp_straddle = 1'b1;
    else
      assign attr_axisten_if_ext_512_rc_4tlp_straddle = 1'b0;
  endgenerate

  generate
    if (AXISTEN_IF_RQ_CC_REGISTERED_TREADY == "TRUE")
      assign spare_bit0 = 1'b1; 
    else
      assign spare_bit0 = 1'b0; 
  endgenerate
  assign     attr_axisten_if_rq_cc_registered_tready = spare_bit0;

  assign     attr_axisten_if_cq_alignment_mode = AXISTEN_IF_CQ_ALIGNMENT_MODE;
  assign     attr_axisten_if_cc_alignment_mode = AXISTEN_IF_CC_ALIGNMENT_MODE;
  assign     attr_axisten_if_rq_alignment_mode = AXISTEN_IF_RQ_ALIGNMENT_MODE;
  assign     attr_axisten_if_rc_alignment_mode = AXISTEN_IF_RC_ALIGNMENT_MODE;

  xdma_0_pcie4_ip_512b_intfc_int #
    (
     .TCQ(TCQ),
     .IMPL_TARGET(IMPL_TARGET),
     .AXISTEN_IF_EXT_512_INTFC_RAM_STYLE("SRL"),
     .AXI4_USER_DATA_WIDTH(AXI4_USER_DATA_WIDTH),
     .AXI4_CORE_DATA_WIDTH(AXI4_CORE_DATA_WIDTH),
     .AXI4_USER_CQ_TUSER_WIDTH(AXI4_USER_CQ_TUSER_WIDTH),
     .AXI4_USER_CC_TUSER_WIDTH(AXI4_USER_CC_TUSER_WIDTH),
     .AXI4_USER_RQ_TUSER_WIDTH(AXI4_USER_RQ_TUSER_WIDTH),
     .AXI4_USER_RC_TUSER_WIDTH(AXI4_USER_RC_TUSER_WIDTH),
     .AXI4_CORE_CQ_TUSER_WIDTH(AXI4_CORE_CQ_TUSER_WIDTH),
     .AXI4_CORE_CC_TUSER_WIDTH(AXI4_CORE_CC_TUSER_WIDTH),
     .AXI4_CORE_RQ_TUSER_WIDTH(AXI4_CORE_RQ_TUSER_WIDTH),
     .AXI4_CORE_RC_TUSER_WIDTH(AXI4_CORE_RC_TUSER_WIDTH),
     .AXI4_USER_CQ_TKEEP_WIDTH(AXI4_USER_CQ_TKEEP_WIDTH),
     .AXI4_USER_CC_TKEEP_WIDTH(AXI4_USER_CC_TKEEP_WIDTH),
     .AXI4_USER_RQ_TKEEP_WIDTH(AXI4_USER_RQ_TKEEP_WIDTH),
     .AXI4_USER_RC_TKEEP_WIDTH(AXI4_USER_RC_TKEEP_WIDTH),
     .AXI4_CORE_CQ_TKEEP_WIDTH(AXI4_CORE_CQ_TKEEP_WIDTH),
     .AXI4_CORE_CC_TKEEP_WIDTH(AXI4_CORE_CC_TKEEP_WIDTH),
     .AXI4_CORE_RQ_TKEEP_WIDTH(AXI4_CORE_RQ_TKEEP_WIDTH),
     .AXI4_CORE_RC_TKEEP_WIDTH(AXI4_CORE_RC_TKEEP_WIDTH),
     .AXI4_CORE_CQ_TREADY_WIDTH(AXI4_CORE_CQ_TREADY_WIDTH),
     .AXI4_CORE_RC_TREADY_WIDTH(AXI4_CORE_RC_TREADY_WIDTH),
     .AXISTEN_IF_RX_PARITY_EN(AXISTEN_IF_RX_PARITY_EN),
     .AXISTEN_IF_TX_PARITY_EN(AXISTEN_IF_TX_PARITY_EN)
     )
    pcie_4_0_512b_intfc_int_mod
  (
   .user_clk_i         (user_clk_i),
   .user_clk2_i        (user_clk2_i),
   .user_clk_en_i      (user_clk_en_i),
   .reset_n_user_clk_i (reset_n_user_clk_i),
   .reset_n_user_clk2_i(reset_n_user_clk2_i),
   .link_down_reset_i  (link_down_reset_i),
   // Attributes
   .attr_axisten_if_ext_512_cq_straddle_i(attr_axisten_if_ext_512_cq_straddle),
   .attr_axisten_if_ext_512_cc_straddle_i(attr_axisten_if_ext_512_cc_straddle),
   .attr_axisten_if_ext_512_rq_straddle_i(attr_axisten_if_ext_512_rq_straddle),
   .attr_axisten_if_ext_512_rc_straddle_i(attr_axisten_if_ext_512_rc_straddle),
   .attr_axisten_if_ext_512_rc_4tlp_straddle_i(attr_axisten_if_ext_512_rc_4tlp_straddle),
   .attr_axisten_if_cq_alignment_mode_i(attr_axisten_if_cq_alignment_mode),
   .attr_axisten_if_cc_alignment_mode_i(attr_axisten_if_cc_alignment_mode),
   .attr_axisten_if_rq_alignment_mode_i(attr_axisten_if_rq_alignment_mode),
   .attr_axisten_if_rc_alignment_mode_i(attr_axisten_if_rc_alignment_mode),
   .attr_axisten_if_rq_cc_registered_tready_i(attr_axisten_if_rq_cc_registered_tready),
   //-----------------------------------
   // Client-side signals
   //-----------------------------------
   // CQ Interface
   .m_axis_cq_tdata_o  (m_axis_cq_tdata_o),
   .m_axis_cq_tvalid_o (m_axis_cq_tvalid_o),
   .m_axis_cq_tuser_o  (m_axis_cq_tuser_o),
   .m_axis_cq_tlast_o  (m_axis_cq_tlast_o),
   .m_axis_cq_tkeep_o  (m_axis_cq_tkeep_o),
   .m_axis_cq_tready_i (m_axis_cq_tready_i),
   .pcie_cq_np_req_i   (pcie_cq_np_req_i),
   .pcie_cq_np_req_count_o(pcie_cq_np_req_count_o),
   // CC Interface
   .s_axis_cc_tdata_i  (s_axis_cc_tdata_i),
   .s_axis_cc_tvalid_i (s_axis_cc_tvalid_i),
   .s_axis_cc_tuser_i  (s_axis_cc_tuser_i),
   .s_axis_cc_tlast_i  (s_axis_cc_tlast_i),
   .s_axis_cc_tkeep_i  (s_axis_cc_tkeep_i),
   .s_axis_cc_tready_o (s_axis_cc_tready_o),
   // RQ Interface
   .s_axis_rq_tdata_i  (s_axis_rq_tdata_i),
   .s_axis_rq_tvalid_i (s_axis_rq_tvalid_i),
   .s_axis_rq_tuser_i  (s_axis_rq_tuser_i),
   .s_axis_rq_tlast_i  (s_axis_rq_tlast_i),
   .s_axis_rq_tkeep_i  (s_axis_rq_tkeep_i),
   .s_axis_rq_tready_o (s_axis_rq_tready_o),
   // RC Interface
   .m_axis_rc_tdata_o  (m_axis_rc_tdata_o),
   .m_axis_rc_tvalid_o (m_axis_rc_tvalid_o),
   .m_axis_rc_tuser_o  (m_axis_rc_tuser_o),
   .m_axis_rc_tlast_o  (m_axis_rc_tlast_o),
   .m_axis_rc_tkeep_o  (m_axis_rc_tkeep_o),
   .m_axis_rc_tready_i (m_axis_rc_tready_i),
   //-----------------------------------
   // Core-side signals
   //-----------------------------------
   // CQ Interface
   .core_cq_tdata_i    (core_cq_tdata_i),
   .core_cq_tvalid_i   (core_cq_tvalid_i),
   .core_cq_tuser_i    (core_cq_tuser_i),
   .core_cq_tlast_i    (core_cq_tlast_i),
   .core_cq_tkeep_i    (core_cq_tkeep_i),
   .core_cq_tready_o   (core_cq_tready_o),
   .posted_req_delivered_o(posted_req_delivered_o),
   .cq_pipeline_empty_o(cq_pipeline_empty_o),
   .cq_np_user_credit_rcvd_o(cq_np_user_credit_rcvd_o),
   // CC Interface
   .core_cc_tdata_o    (core_cc_tdata_o),
   .core_cc_tvalid_o   (core_cc_tvalid_o),
   .core_cc_tuser_o    (core_cc_tuser_o),
   .core_cc_tlast_o    (core_cc_tlast_o),
   .core_cc_tkeep_o    (core_cc_tkeep_o),
   .core_cc_tready_i   (core_cc_tready_i),
   // RQ Interface
   .core_rq_tdata_o    (core_rq_tdata_o),
   .core_rq_tvalid_o   (core_rq_tvalid_o),
   .core_rq_tuser_o    (core_rq_tuser_o),
   .core_rq_tlast_o    (core_rq_tlast_o),
   .core_rq_tkeep_o    (core_rq_tkeep_o),
   .core_rq_tready_i   (core_rq_tready_i),
   // RC Interface
   .core_rc_tdata_i    (core_rc_tdata_i),
   .core_rc_tvalid_i   (core_rc_tvalid_i),
   .core_rc_tuser_i    (core_rc_tuser_i),
   .core_rc_tlast_i    (core_rc_tlast_i),
   .core_rc_tkeep_i    (core_rc_tkeep_i),
   .core_rc_tready_o   (core_rc_tready_o),
   .compl_delivered_o  (compl_delivered_o),
   .compl_delivered_tag0_o(compl_delivered_tag0_o),
   .compl_delivered_tag1_o(compl_delivered_tag1_o)
   );
endmodule // pcie_4_0_512b_intfc
