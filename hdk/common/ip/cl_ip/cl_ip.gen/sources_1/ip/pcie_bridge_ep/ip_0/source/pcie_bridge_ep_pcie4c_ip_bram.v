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
// File       : pcie_bridge_ep_pcie4c_ip_bram.v
// Version    : 1.0 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------
`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie_bridge_ep_pcie4c_ip_bram #(
  parameter           TCQ = 100
, parameter           ECC_PIPELINE="FALSE"
, parameter           AXISTEN_IF_MSIX_TO_RAM_PIPELINE="FALSE"
, parameter           AXISTEN_IF_MSIX_FROM_RAM_PIPELINE="FALSE"
, parameter           TPH_TO_RAM_PIPELINE="FALSE"
, parameter           TPH_FROM_RAM_PIPELINE="FALSE"
, parameter [1:0]     TL_COMPLETION_RAM_SIZE=2'b01
, parameter           TL_RX_COMPLETION_TO_RAM_WRITE_PIPELINE="FALSE"
, parameter           TL_RX_COMPLETION_TO_RAM_READ_PIPELINE="FALSE"
, parameter           TL_RX_COMPLETION_FROM_RAM_READ_PIPELINE="FALSE"
, parameter           TL_RX_POSTED_TO_RAM_WRITE_PIPELINE="FALSE"
, parameter           TL_RX_POSTED_TO_RAM_READ_PIPELINE="FALSE"
, parameter           TL_RX_POSTED_FROM_RAM_READ_PIPELINE="FALSE"
, parameter           LL_REPLAY_TO_RAM_PIPELINE="FALSE"
, parameter           LL_REPLAY_FROM_RAM_PIPELINE="FALSE"
, parameter [1:0]     TL_PF_ENABLE_REG=2'h0
, parameter [3:0]     SRIOV_CAP_ENABLE=4'h0
, parameter [15:0]    PF0_SRIOV_CAP_TOTAL_VF=16'h0
, parameter [15:0]    PF1_SRIOV_CAP_TOTAL_VF=16'h0
, parameter [15:0]    PF2_SRIOV_CAP_TOTAL_VF=16'h0
, parameter [15:0]    PF3_SRIOV_CAP_TOTAL_VF=16'h0
, parameter           PF0_TPHR_CAP_ENABLE="FALSE"
, parameter           MSIX_CAP_TABLE_SIZE=11'h0
, parameter           MSIX_TABLE_RAM_ENABLE="FALSE"

  ) (
  input  wire         core_clk_i,
  input  wire         user_clk_i,
  input  wire         reset_i,
  input  wire         core_reset_i,

  input  wire   [8:0] mi_rep_addr_i,
  input  wire [255:0] mi_rep_wdata_i,
  input  wire         mi_rep_wen_i,
  output wire [255:0] mi_rep_rdata_o,
  input  wire         mi_rep_rden_i,

  output wire   [3:0] mi_rep_err_cor_o,
  output wire   [3:0] mi_rep_err_uncor_o,

  input  wire   [8:0] mi_req_waddr0_i,
  input  wire [143:0] mi_req_wdata0_i,
  input  wire         mi_req_wen0_i,
  input  wire   [8:0] mi_req_waddr1_i,
  input  wire [143:0] mi_req_wdata1_i,
  input  wire         mi_req_wen1_i,

  input  wire   [8:0] mi_req_raddr0_i,
  input  wire         mi_req_ren0_i,
  output wire [143:0] mi_req_rdata0_o,
  input  wire   [8:0] mi_req_raddr1_i,
  input  wire         mi_req_ren1_i,
  output wire [143:0] mi_req_rdata1_o,

  output wire   [5:0] mi_req_err_cor_o,
  output wire   [5:0] mi_req_err_uncor_o,

  input  wire   [8:0] mi_cpl_waddr0_i,
  input  wire [143:0] mi_cpl_wdata0_i,
  input  wire   [1:0] mi_cpl_wen0_i,
  input  wire   [8:0] mi_cpl_waddr1_i,
  input  wire [143:0] mi_cpl_wdata1_i,
  input  wire   [1:0] mi_cpl_wen1_i,

  input  wire   [8:0] mi_cpl_raddr0_i,
  input  wire   [1:0] mi_cpl_ren0_i,
  output wire [143:0] mi_cpl_rdata0_o,
  input  wire   [8:0] mi_cpl_raddr1_i,
  input  wire   [1:0] mi_cpl_ren1_i,
  output wire [143:0] mi_cpl_rdata1_o,

  output wire  [11:0] mi_cpl_err_cor_o,
  output wire  [11:0] mi_cpl_err_uncor_o,

  input  wire  [12:0] cfg_msix_waddr_i,
  input  wire  [31:0] cfg_msix_wdata_i,
  input  wire   [3:0] cfg_msix_wdip_i,
  input  wire   [3:0] cfg_msix_wen_i,
  output wire  [31:0] cfg_msix_rdata_o,
  output wire   [3:0] cfg_msix_rdop_o,
  input  wire         cfg_msix_ren_i,

  input  wire   [7:0] user_tph_stt_func_num_i,
  input  wire   [5:0] user_tph_stt_index_i,
  input  wire         user_tph_stt_rd_en_i,
  output wire   [7:0] user_tph_stt_rd_data_o,

  input  wire  [11:0] cfg_tph_waddr_i,
  input  wire  [31:0] cfg_tph_wdata_i,
  input  wire   [3:0] cfg_tph_wdip_i,
  input  wire   [3:0] cfg_tph_wen_i,
  output wire  [31:0] cfg_tph_rdata_o,
  output wire   [3:0] cfg_tph_rdop_o,
  input  wire         cfg_tph_ren_i

  );

  pcie_bridge_ep_pcie4c_ip_bram_rep #(

    .TCQ (TCQ),
    .TO_RAM_PIPELINE(LL_REPLAY_TO_RAM_PIPELINE),
    .FROM_RAM_PIPELINE(LL_REPLAY_FROM_RAM_PIPELINE),
    .ECC_PIPELINE(ECC_PIPELINE)

  )
  bram_repl_inst (

    .clk_i (core_clk_i),
    .reset_i (core_reset_i),

    .addr_i(mi_rep_addr_i[8:0]),
    .wdata_i(mi_rep_wdata_i[255:0]),
    .wen_i(mi_rep_wen_i),
    .rdata_o(mi_rep_rdata_o[255:0]),
    .ren_i(mi_rep_rden_i),
    .err_cor_o(mi_rep_err_cor_o[3:0]),
    .err_uncor_o(mi_rep_err_uncor_o[3:0])

  );

  pcie_bridge_ep_pcie4c_ip_bram_16k #(

    .TCQ (TCQ),
    .TO_RAM_WRITE_PIPELINE(TL_RX_POSTED_TO_RAM_WRITE_PIPELINE),
    .TO_RAM_READ_PIPELINE(TL_RX_POSTED_TO_RAM_READ_PIPELINE),
    .FROM_RAM_READ_PIPELINE(TL_RX_POSTED_FROM_RAM_READ_PIPELINE),
    .ECC_PIPELINE(ECC_PIPELINE)

  )
  bram_post_inst (

    .clk_i (core_clk_i),
    .reset_i (core_reset_i),

    .waddr0_i(mi_req_waddr0_i[8:0]),
    .wdata0_i(mi_req_wdata0_i[143:0]),
    .wen0_i(mi_req_wen0_i),
    .waddr1_i(mi_req_waddr1_i[8:0]),
    .wdata1_i(mi_req_wdata1_i[143:0]),
    .wen1_i(mi_req_wen1_i),
    .raddr0_i(mi_req_raddr0_i[8:0]),
    .rdata0_o(mi_req_rdata0_o[143:0]),
    .ren0_i(mi_req_ren0_i),
    .raddr1_i(mi_req_raddr1_i[8:0]),
    .rdata1_o(mi_req_rdata1_o[143:0]),
    .ren1_i(mi_req_ren1_i),
    .err_cor_o(mi_req_err_cor_o[5:0]),
    .err_uncor_o(mi_req_err_uncor_o[5:0])

  );

  generate 

  if (TL_COMPLETION_RAM_SIZE == 2'b10) begin : RAM32K

    pcie_bridge_ep_pcie4c_ip_bram_32k #(

      .TCQ (TCQ),
      .TO_RAM_WRITE_PIPELINE(TL_RX_COMPLETION_TO_RAM_WRITE_PIPELINE),
      .TO_RAM_READ_PIPELINE(TL_RX_COMPLETION_TO_RAM_READ_PIPELINE),
      .FROM_RAM_READ_PIPELINE(TL_RX_COMPLETION_FROM_RAM_READ_PIPELINE),
      .ECC_PIPELINE(ECC_PIPELINE)

    )
    bram_comp_inst (

      .clk_i (core_clk_i),
      .reset_i (core_reset_i),
  
      .waddr0_i(mi_cpl_waddr0_i[8:0]),
      .wdata0_i(mi_cpl_wdata0_i[143:0]),
      .wen0_i(mi_cpl_wen0_i[1:0]),
      .waddr1_i(mi_cpl_waddr1_i[8:0]),
      .wdata1_i(mi_cpl_wdata1_i[143:0]),
      .wen1_i(mi_cpl_wen1_i[1:0]),
      .raddr0_i(mi_cpl_raddr0_i[8:0]),
      .rdata0_o(mi_cpl_rdata0_o[143:0]),
      .ren0_i(mi_cpl_ren0_i[1:0]),
      .raddr1_i(mi_cpl_raddr1_i[8:0]),
      .rdata1_o(mi_cpl_rdata1_o[143:0]),
      .ren1_i(mi_cpl_ren1_i[1:0]),
      .err_cor_o(mi_cpl_err_cor_o[11:0]),
      .err_uncor_o(mi_cpl_err_uncor_o[11:0])

    );

  end else begin : RAM16K

    pcie_bridge_ep_pcie4c_ip_bram_16k #(

      .TCQ (TCQ),
      .TO_RAM_WRITE_PIPELINE(TL_RX_COMPLETION_TO_RAM_WRITE_PIPELINE),
      .TO_RAM_READ_PIPELINE(TL_RX_COMPLETION_TO_RAM_READ_PIPELINE),
      .FROM_RAM_READ_PIPELINE(TL_RX_COMPLETION_FROM_RAM_READ_PIPELINE),
      .ECC_PIPELINE(ECC_PIPELINE)

    )
    bram_comp_inst (

      .clk_i (core_clk_i),
      .reset_i (core_reset_i),
  
      .waddr0_i(mi_cpl_waddr0_i[8:0]),
      .wdata0_i(mi_cpl_wdata0_i[143:0]),
      .wen0_i(mi_cpl_wen0_i[0]),
      .waddr1_i(mi_cpl_waddr1_i[8:0]),
      .wdata1_i(mi_cpl_wdata1_i[143:0]),
      .wen1_i(mi_cpl_wen1_i[0]),
      .raddr0_i(mi_cpl_raddr0_i[8:0]),
      .rdata0_o(mi_cpl_rdata0_o[143:0]),
      .ren0_i(mi_cpl_ren0_i[0]),
      .raddr1_i(mi_cpl_raddr1_i[8:0]),
      .rdata1_o(mi_cpl_rdata1_o[143:0]),
      .ren1_i(mi_cpl_ren1_i[0]),
      .err_cor_o(mi_cpl_err_cor_o[5:0]),
      .err_uncor_o(mi_cpl_err_uncor_o[5:0])

    );

    assign mi_cpl_err_cor_o[11:6] = 6'b0;
    assign mi_cpl_err_uncor_o[11:6] = 6'b0;

  end

  endgenerate 


  pcie_bridge_ep_pcie4c_ip_bram_msix #(

    .TCQ (TCQ),
    .TO_RAM_PIPELINE(AXISTEN_IF_MSIX_TO_RAM_PIPELINE),
    .FROM_RAM_PIPELINE(AXISTEN_IF_MSIX_FROM_RAM_PIPELINE),
    .MSIX_CAP_TABLE_SIZE(MSIX_CAP_TABLE_SIZE),
    .MSIX_TABLE_RAM_ENABLE(MSIX_TABLE_RAM_ENABLE)

  )
  bram_msix_inst (

    .clk_i(user_clk_i),
    .reset_i(reset_i),

    .addr_i(cfg_msix_waddr_i[12:0]),
    .wdata_i(cfg_msix_wdata_i[31:0]),
    .wdip_i(cfg_msix_wdip_i[3:0]),
    .wen_i(cfg_msix_wen_i[3:0]),
    .rdata_o(cfg_msix_rdata_o[31:0]),
    .rdop_o(cfg_msix_rdop_o[3:0])

  );

  pcie_bridge_ep_pcie4c_ip_bram_tph #(

    .TCQ (TCQ),
    .TO_RAM_PIPELINE(TPH_TO_RAM_PIPELINE),
    .FROM_RAM_PIPELINE(TPH_FROM_RAM_PIPELINE),
    .TL_PF_ENABLE_REG(TL_PF_ENABLE_REG),
    .SRIOV_CAP_ENABLE(SRIOV_CAP_ENABLE),
    .PF0_SRIOV_CAP_TOTAL_VF(PF0_SRIOV_CAP_TOTAL_VF),
    .PF1_SRIOV_CAP_TOTAL_VF(PF1_SRIOV_CAP_TOTAL_VF),
    .PF2_SRIOV_CAP_TOTAL_VF(PF2_SRIOV_CAP_TOTAL_VF),
    .PF3_SRIOV_CAP_TOTAL_VF(PF3_SRIOV_CAP_TOTAL_VF),
    .PF0_TPHR_CAP_ENABLE(PF0_TPHR_CAP_ENABLE)

  )
  bram_tph_inst (

    .clk_i(user_clk_i),
    .reset_i(reset_i),

    .user_tph_stt_func_num_i(user_tph_stt_func_num_i[7:0]),
    .user_tph_stt_index_i(user_tph_stt_index_i[5:0]),
    .user_tph_stt_rd_en_i(user_tph_stt_rd_en_i),
    .user_tph_stt_rd_data_o(user_tph_stt_rd_data_o[7:0]),

    .addr_i(cfg_tph_waddr_i[11:0]),
    .wdata_i(cfg_tph_wdata_i[31:0]),
    .wdip_i(cfg_tph_wdip_i[3:0]),
    .wen_i(cfg_tph_wen_i[3:0]),
    .rdata_o(cfg_tph_rdata_o[31:0]),
    .rdop_o(cfg_tph_rdop_o[3:0])

  );


endmodule
