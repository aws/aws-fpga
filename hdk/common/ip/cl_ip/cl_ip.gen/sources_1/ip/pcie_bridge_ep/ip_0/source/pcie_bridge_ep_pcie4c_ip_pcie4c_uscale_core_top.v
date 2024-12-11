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
// File       : pcie_bridge_ep_pcie4c_ip_pcie4c_uscale_core_top.v
// Version    : 1.0 
//-----------------------------------------------------------------------------
/////////////////////////////////////////////////////////////////////////////
`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie_bridge_ep_pcie4c_ip_pcie4c_uscale_core_top
#(
  parameter           TCQ = 100,
  parameter           KESTREL_512_HLF = "FALSE",
  parameter           IMPL_TARGET = "HARD",
  parameter           AXISTEN_IF_EXT_512_INTFC_RAM_STYLE = "BRAM",
  parameter           FPGA_FAMILY = "USM",
  parameter           FPGA_XCVR = "Y",
  parameter integer   PIPE_PIPELINE_STAGES = 1,
  parameter integer   PHY_REFCLK_FREQ  = 0,
  parameter           CRM_CORE_CLK_FREQ_500="TRUE",
  parameter [1:0]     CRM_USER_CLK_FREQ=2'b11,
  parameter           CRM_MCAP_CLK_FREQ=1'b0,
  parameter           AXI4_DATA_WIDTH = 512,
  parameter           AXI4_TKEEP_WIDTH = 16,
  parameter [1:0]     AXISTEN_IF_WIDTH = (AXI4_DATA_WIDTH == 64) ? 2'b00 : (AXI4_DATA_WIDTH == 128) ? 2'b01 : 2'b10,
  parameter           AXISTEN_IF_EXT_512= (AXI4_DATA_WIDTH == 512) ? "TRUE" : "FALSE",
  parameter           AXISTEN_IF_EXT_512_CQ_STRADDLE="FALSE",
  parameter           AXISTEN_IF_EXT_512_CC_STRADDLE="FALSE",
  parameter           AXISTEN_IF_EXT_512_RQ_STRADDLE="FALSE",
  parameter           AXISTEN_IF_EXT_512_RC_STRADDLE="FALSE",
  parameter           AXISTEN_IF_EXT_512_RC_4TLP_STRADDLE="TRUE",
  parameter [1:0]     AXISTEN_IF_CQ_ALIGNMENT_MODE=2'b00,
  parameter [1:0]     AXISTEN_IF_CC_ALIGNMENT_MODE=2'b00,
  parameter [1:0]     AXISTEN_IF_RQ_ALIGNMENT_MODE=2'b00,
  parameter [1:0]     AXISTEN_IF_RC_ALIGNMENT_MODE=2'b00,
  parameter           AXISTEN_IF_RC_STRADDLE="FALSE",

  parameter           AXIS_CCIX_RX_TDATA_WIDTH = 256,
  parameter           AXIS_CCIX_TX_TDATA_WIDTH = 256,
  parameter           AXIS_CCIX_RX_TUSER_WIDTH = 46,
  parameter           AXIS_CCIX_TX_TUSER_WIDTH = 46,

  parameter           AXI4_CQ_TUSER_WIDTH = 183,
  parameter           AXI4_CQ_TREADY_WIDTH = 22,
  parameter           AXI4_CC_TUSER_WIDTH = 81,
  parameter           AXI4_CC_TREADY_WIDTH = 4,
  parameter           AXI4_RQ_TUSER_WIDTH = 137,
  parameter           AXI4_RQ_TREADY_WIDTH = 4,
  parameter           AXI4_RC_TUSER_WIDTH = 161,
  parameter           AXI4_RC_TREADY_WIDTH = 22,


  parameter           AXISTEN_IF_ENABLE_RX_MSG_INTFC="FALSE",
  parameter [17:0]    AXISTEN_IF_ENABLE_MSG_ROUTE=18'h0,
  parameter           AXISTEN_IF_RX_PARITY_EN="FALSE",
  parameter           AXISTEN_IF_TX_PARITY_EN="FALSE",
  parameter           AXISTEN_IF_ENABLE_CLIENT_TAG="FALSE",
  parameter           AXISTEN_IF_ENABLE_256_TAGS="TRUE",
  parameter [23:0]    AXISTEN_IF_COMPL_TIMEOUT_REG0=24'hBEBC20,
  parameter [27:0]    AXISTEN_IF_COMPL_TIMEOUT_REG1=28'h2FAF080,
  parameter           AXISTEN_IF_LEGACY_MODE_ENABLE="FALSE",
  parameter           AXISTEN_IF_ENABLE_MESSAGE_RID_CHECK="TRUE",
  parameter           AXISTEN_IF_MSIX_TO_RAM_PIPELINE="TRUE",
  parameter           AXISTEN_IF_MSIX_FROM_RAM_PIPELINE="TRUE",
  parameter           AXISTEN_IF_MSIX_RX_PARITY_EN="TRUE",
  parameter           AXISTEN_IF_ENABLE_INTERNAL_MSIX_TABLE="FALSE",
  parameter           AXISTEN_IF_SIM_SHORT_CPL_TIMEOUT="FALSE",
  parameter           AXISTEN_IF_CQ_EN_POISONED_MEM_WR="FALSE",
  parameter           AXISTEN_IF_RQ_CC_REGISTERED_TREADY="TRUE",
  parameter [15:0]    PM_ASPML0S_TIMEOUT=16'h1500,
  parameter [31:0]    PM_L1_REENTRY_DELAY= (CRM_CORE_CLK_FREQ_500 == "TRUE") ? 32'hC350 :  32'h61A8,
  parameter [19:0]    PM_ASPML1_ENTRY_DELAY=(CRM_CORE_CLK_FREQ_500 == "TRUE") ? 20'h7D0 : 20'h3E8,
  parameter           PM_ENABLE_SLOT_POWER_CAPTURE="TRUE",
  parameter [19:0]    PM_PME_SERVICE_TIMEOUT_DELAY=20'h0,
  parameter [15:0]    PM_PME_TURNOFF_ACK_DELAY=16'h100,
  parameter           PL_UPSTREAM_FACING="TRUE",
  parameter [4:0]     PL_LINK_CAP_MAX_LINK_WIDTH=5'b01000,
  parameter [3:0]     PL_LINK_CAP_MAX_LINK_SPEED=4'b0100,
  parameter           PL_DISABLE_DC_BALANCE="FALSE",
  parameter           PL_DISABLE_EI_INFER_IN_L0="FALSE",
  parameter integer   PL_N_FTS=255,
  parameter           PL_DISABLE_UPCONFIG_CAPABLE="FALSE",
  parameter           PL_DISABLE_RETRAIN_ON_FRAMING_ERROR="FALSE",
  parameter           PL_DISABLE_RETRAIN_ON_EB_ERROR="FALSE",
  parameter [15:0]    PL_DISABLE_RETRAIN_ON_SPECIFIC_FRAMING_ERROR=16'b0000000000000000,
  parameter [7:0]     PL_REPORT_ALL_PHY_ERRORS=8'b00000000,
  parameter [1:0]     PL_DISABLE_LFSR_UPDATE_ON_SKP=2'b00,
  parameter [31:0]    PL_LANE0_EQ_CONTROL = PL_UPSTREAM_FACING == "TRUE" ? 32'h3F00 : 32'h3505,
  parameter [31:0]    PL_LANE1_EQ_CONTROL = PL_UPSTREAM_FACING == "TRUE" ? 32'h3F00 : 32'h3505,
  parameter [31:0]    PL_LANE2_EQ_CONTROL = PL_UPSTREAM_FACING == "TRUE" ? 32'h3F00 : 32'h3505,
  parameter [31:0]    PL_LANE3_EQ_CONTROL = PL_UPSTREAM_FACING == "TRUE" ? 32'h3F00 : 32'h3505,
  parameter [31:0]    PL_LANE4_EQ_CONTROL = PL_UPSTREAM_FACING == "TRUE" ? 32'h3F00 : 32'h3505,
  parameter [31:0]    PL_LANE5_EQ_CONTROL = PL_UPSTREAM_FACING == "TRUE" ? 32'h3F00 : 32'h3505,
  parameter [31:0]    PL_LANE6_EQ_CONTROL = PL_UPSTREAM_FACING == "TRUE" ? 32'h3F00 : 32'h3505,
  parameter [31:0]    PL_LANE7_EQ_CONTROL = PL_UPSTREAM_FACING == "TRUE" ? 32'h3F00 : 32'h3505,
  parameter [31:0]    PL_LANE8_EQ_CONTROL = PL_UPSTREAM_FACING == "TRUE" ? 32'h3F00 : 32'h3505,
  parameter [31:0]    PL_LANE9_EQ_CONTROL = PL_UPSTREAM_FACING == "TRUE" ? 32'h3F00 : 32'h3505,
  parameter [31:0]    PL_LANE10_EQ_CONTROL= PL_UPSTREAM_FACING == "TRUE" ? 32'h3F00 : 32'h3505,
  parameter [31:0]    PL_LANE11_EQ_CONTROL= PL_UPSTREAM_FACING == "TRUE" ? 32'h3F00 : 32'h3505,
  parameter [31:0]    PL_LANE12_EQ_CONTROL= PL_UPSTREAM_FACING == "TRUE" ? 32'h3F00 : 32'h3505,
  parameter [31:0]    PL_LANE13_EQ_CONTROL= PL_UPSTREAM_FACING == "TRUE" ? 32'h3F00 : 32'h3505,
  parameter [31:0]    PL_LANE14_EQ_CONTROL= PL_UPSTREAM_FACING == "TRUE" ? 32'h3F00 : 32'h3505,
  parameter [31:0]    PL_LANE15_EQ_CONTROL= PL_UPSTREAM_FACING == "TRUE" ? 32'h3F00 : 32'h3505,
    //pragma translate_off
  parameter [1:0]     PL_EQ_BYPASS_PHASE23=2'b01,
    //pragma translate_on
  parameter [4:0]     PL_EQ_ADAPT_ITER_COUNT=5'h2,
  parameter [1:0]     PL_EQ_ADAPT_REJECT_RETRY_COUNT=2'h1,
  parameter           PL_EQ_SHORT_ADAPT_PHASE="FALSE",
  parameter [1:0]     PL_EQ_ADAPT_DISABLE_COEFF_CHECK=2'b0,
  parameter [1:0]     PL_EQ_ADAPT_DISABLE_PRESET_CHECK=2'b0,
  parameter [7:0]     PL_EQ_DEFAULT_TX_PRESET=8'h44,
  parameter [5:0]     PL_EQ_DEFAULT_RX_PRESET_HINT=6'h33,
  parameter [1:0]     PL_EQ_RX_ADAPT_EQ_PHASE0=2'b00,
  parameter [1:0]     PL_EQ_RX_ADAPT_EQ_PHASE1=2'b00,
  parameter           PL_EQ_DISABLE_MISMATCH_CHECK ="TRUE",
  parameter [1:0]     PL_RX_L0S_EXIT_TO_RECOVERY=2'b00,
  parameter           PL_EQ_TX_8G_EQ_TS2_ENABLE="FALSE",
  parameter           PL_DISABLE_AUTO_EQ_SPEED_CHANGE_TO_GEN4="FALSE",
  parameter           PL_DISABLE_AUTO_EQ_SPEED_CHANGE_TO_GEN3="FALSE",
  parameter           PL_DISABLE_AUTO_SPEED_CHANGE_TO_GEN2="FALSE",
  parameter           PL_DESKEW_ON_SKIP_IN_GEN12="FALSE",
  parameter           PL_INFER_EI_DISABLE_REC_RC="FALSE",
  parameter           PL_INFER_EI_DISABLE_REC_SPD="FALSE",
  parameter           PL_INFER_EI_DISABLE_LPBK_ACTIVE="FALSE",
  parameter [3:0]     PL_RX_ADAPT_TIMER_RRL_GEN3=4'h6,
  parameter [1:0]     PL_RX_ADAPT_TIMER_RRL_CLOBBER_TX_TS=2'b00,
  parameter [3:0]     PL_RX_ADAPT_TIMER_RRL_GEN4=4'h0,
  parameter [3:0]     PL_RX_ADAPT_TIMER_CLWS_GEN3=4'h0,
  parameter [1:0]     PL_RX_ADAPT_TIMER_CLWS_CLOBBER_TX_TS=2'b00,
  parameter [3:0]     PL_RX_ADAPT_TIMER_CLWS_GEN4=4'h0,
  parameter           PL_DISABLE_LANE_REVERSAL="FALSE",
  parameter           PL_CFG_STATE_ROBUSTNESS_ENABLE="TRUE",
  parameter           PL_REDO_EQ_SOURCE_SELECT="TRUE"                                              ,
  parameter           PL_DEEMPH_SOURCE_SELECT="FALSE",
  parameter           PL_EXIT_LOOPBACK_ON_EI_ENTRY="TRUE",
  parameter           PL_QUIESCE_GUARANTEE_DISABLE="FALSE",
  parameter           PL_SRIS_ENABLE="FALSE",
  parameter [6:0]     PL_SRIS_SKPOS_GEN_SPD_VEC=7'h0,
  parameter [6:0]     PL_SRIS_SKPOS_REC_SPD_VEC=7'h0,
  parameter [1:0]     PL_SIM_FAST_LINK_TRAINING=2'h3,
  parameter [15:0]    PL_USER_SPARE=16'h13,
  parameter           LL_ACK_TIMEOUT_EN="FALSE",
  parameter [8:0]     LL_ACK_TIMEOUT=9'h0,
  parameter integer   LL_ACK_TIMEOUT_FUNC=0,
  parameter           LL_REPLAY_TIMEOUT_EN="FALSE",
  parameter [8:0]     LL_REPLAY_TIMEOUT=9'h0,
  parameter integer   LL_REPLAY_TIMEOUT_FUNC=0,
  parameter           LL_REPLAY_TO_RAM_PIPELINE="TRUE",
  parameter           LL_REPLAY_FROM_RAM_PIPELINE="TRUE",
  parameter           LL_DISABLE_SCHED_TX_NAK="FALSE",
  parameter           LL_TX_TLP_PARITY_CHK="FALSE",
  parameter           LL_RX_TLP_PARITY_GEN="FALSE",
  parameter [15:0]    LL_USER_SPARE=16'h18,
  parameter           IS_SWITCH_PORT="FALSE",
  parameter           CFG_BYPASS_MODE_ENABLE="FALSE",
  parameter [1:0]     TL_PF_ENABLE_REG=2'h0,
  parameter [11:0]    TL_CREDITS_CD=12'h1C0,
  parameter [7:0]     TL_CREDITS_CH=8'h20,
  parameter [1:0]     TL_COMPLETION_RAM_SIZE=2'b01,
  parameter [1:0]     TL_COMPLETION_RAM_NUM_TLPS=2'b10,
  parameter [11:0]    TL_CREDITS_NPD=12'h4,
  parameter [7:0]     TL_CREDITS_NPH=8'h20,
  parameter [11:0]    TL_CREDITS_PD=12'he0,
  parameter [7:0]     TL_CREDITS_PH=8'h20,
  parameter           TL_POSTED_RAM_SIZE=1'b1,
  parameter           TL_RX_COMPLETION_TO_RAM_WRITE_PIPELINE="TRUE",
  parameter           TL_RX_COMPLETION_TO_RAM_READ_PIPELINE="TRUE",
  parameter           TL_RX_COMPLETION_FROM_RAM_READ_PIPELINE="TRUE",
  parameter           TL_RX_POSTED_TO_RAM_WRITE_PIPELINE="TRUE",
  parameter           TL_RX_POSTED_TO_RAM_READ_PIPELINE="TRUE",
  parameter           TL_RX_POSTED_FROM_RAM_READ_PIPELINE="TRUE",
  parameter           TL_TX_MUX_STRICT_PRIORITY="FALSE",
  parameter           TL_TX_TLP_STRADDLE_ENABLE="FALSE",
  parameter           TL_TX_TLP_TERMINATE_PARITY="FALSE",
  parameter [4:0]     TL_FC_UPDATE_MIN_INTERVAL_TLP_COUNT=5'h8,
  parameter [4:0]     TL_FC_UPDATE_MIN_INTERVAL_TIME=5'h2,
  parameter [15:0]    TL_USER_SPARE=16'h0,
  parameter [23:0]    PF0_CLASS_CODE=24'h000000,
  parameter [23:0]    PF1_CLASS_CODE=24'h000000,
  parameter [23:0]    PF2_CLASS_CODE=24'h000000,
  parameter [23:0]    PF3_CLASS_CODE=24'h000000,
  parameter [2:0]     PF0_INTERRUPT_PIN=3'h1,
  parameter [2:0]     PF1_INTERRUPT_PIN=3'h1,
  parameter [2:0]     PF2_INTERRUPT_PIN=3'h1,
  parameter [2:0]     PF3_INTERRUPT_PIN=3'h1,
  parameter [7:0]     PF0_CAPABILITY_POINTER=8'h80,
  parameter [7:0]     PF1_CAPABILITY_POINTER=8'h80,
  parameter [7:0]     PF2_CAPABILITY_POINTER=8'h80,
  parameter [7:0]     PF3_CAPABILITY_POINTER=8'h80,
  parameter [7:0]     VF0_CAPABILITY_POINTER=8'h80,
  parameter           LEGACY_CFG_EXTEND_INTERFACE_ENABLE="FALSE",
  parameter           EXTENDED_CFG_EXTEND_INTERFACE_ENABLE="FALSE",
  parameter           EXT_XVC_VSEC_ENABLE="FALSE",
  parameter           ACS_EXT_CAP_ENABLE="FALSE",
  parameter           ACS_CAP_NEXTPTR=12'h000,
  parameter [11:0]    RBAR_CAP_NEXTPTR=12'h000,
  parameter [2:0]     PF0_RBAR_NUM_BAR =3'h1,
  parameter [2:0]     PF1_RBAR_NUM_BAR =3'h1,
  parameter [2:0]     PF2_RBAR_NUM_BAR =3'h1,
  parameter [2:0]     PF3_RBAR_NUM_BAR =3'h1,
  parameter [2:0]     PF0_RBAR_BAR_INDEX_0 =3'h0,
  parameter [2:0]     PF0_RBAR_BAR_INDEX_1 =3'h0,
  parameter [2:0]     PF0_RBAR_BAR_INDEX_2 =3'h0,
  parameter [2:0]     PF0_RBAR_BAR_INDEX_3 =3'h0,
  parameter [2:0]     PF0_RBAR_BAR_INDEX_4 =3'h0,
  parameter [2:0]     PF0_RBAR_BAR_INDEX_5 =3'h0,
  parameter [2:0]     PF1_RBAR_BAR_INDEX_0 =3'h0,
  parameter [2:0]     PF1_RBAR_BAR_INDEX_1 =3'h0,
  parameter [2:0]     PF1_RBAR_BAR_INDEX_2 =3'h0,
  parameter [2:0]     PF1_RBAR_BAR_INDEX_3 =3'h0,
  parameter [2:0]     PF1_RBAR_BAR_INDEX_4 =3'h0,
  parameter [2:0]     PF1_RBAR_BAR_INDEX_5 =3'h0,
  parameter [2:0]     PF2_RBAR_BAR_INDEX_0 =3'h0,
  parameter [2:0]     PF2_RBAR_BAR_INDEX_1 =3'h0,
  parameter [2:0]     PF2_RBAR_BAR_INDEX_2 =3'h0,
  parameter [2:0]     PF2_RBAR_BAR_INDEX_3 =3'h0,
  parameter [2:0]     PF2_RBAR_BAR_INDEX_4 =3'h0,
  parameter [2:0]     PF2_RBAR_BAR_INDEX_5 =3'h0,
  parameter [2:0]     PF3_RBAR_BAR_INDEX_0 =3'h0,
  parameter [2:0]     PF3_RBAR_BAR_INDEX_1 =3'h0,
  parameter [2:0]     PF3_RBAR_BAR_INDEX_2 =3'h0,
  parameter [2:0]     PF3_RBAR_BAR_INDEX_3 =3'h0,
  parameter [2:0]     PF3_RBAR_BAR_INDEX_4 =3'h0,
  parameter [2:0]     PF3_RBAR_BAR_INDEX_5 =3'h0,
  parameter [15:0]    PF0_RBAR_CAP_BAR0_UPPER=16'h0,
  parameter [15:0]    PF0_RBAR_CAP_BAR1_UPPER=16'h0,
  parameter [15:0]    PF0_RBAR_CAP_BAR2_UPPER=16'h0,
  parameter [15:0]    PF0_RBAR_CAP_BAR3_UPPER=16'h0,
  parameter [15:0]    PF0_RBAR_CAP_BAR4_UPPER=16'h0,
  parameter [15:0]    PF0_RBAR_CAP_BAR5_UPPER=16'h0,
  parameter [15:0]    PF1_RBAR_CAP_BAR0_UPPER=16'h0,
  parameter [15:0]    PF1_RBAR_CAP_BAR1_UPPER=16'h0,
  parameter [15:0]    PF1_RBAR_CAP_BAR2_UPPER=16'h0,
  parameter [15:0]    PF1_RBAR_CAP_BAR3_UPPER=16'h0,
  parameter [15:0]    PF1_RBAR_CAP_BAR4_UPPER=16'h0,
  parameter [15:0]    PF1_RBAR_CAP_BAR5_UPPER=16'h0,
  parameter [15:0]    PF2_RBAR_CAP_BAR0_UPPER=16'h0,
  parameter [15:0]    PF2_RBAR_CAP_BAR1_UPPER=16'h0,
  parameter [15:0]    PF2_RBAR_CAP_BAR2_UPPER=16'h0,
  parameter [15:0]    PF2_RBAR_CAP_BAR3_UPPER=16'h0,
  parameter [15:0]    PF2_RBAR_CAP_BAR4_UPPER=16'h0,
  parameter [15:0]    PF2_RBAR_CAP_BAR5_UPPER=16'h0,
  parameter [15:0]    PF3_RBAR_CAP_BAR0_UPPER=16'h0,
  parameter [15:0]    PF3_RBAR_CAP_BAR1_UPPER=16'h0,
  parameter [15:0]    PF3_RBAR_CAP_BAR2_UPPER=16'h0,
  parameter [15:0]    PF3_RBAR_CAP_BAR3_UPPER=16'h0,
  parameter [15:0]    PF3_RBAR_CAP_BAR4_UPPER=16'h0,
  parameter [15:0]    PF3_RBAR_CAP_BAR5_UPPER=16'h0,
  parameter [31:0]    PF0_RBAR_CAP_BAR0_LOWER=32'h0,
  parameter [31:0]    PF0_RBAR_CAP_BAR1_LOWER=32'h0,
  parameter [31:0]    PF0_RBAR_CAP_BAR2_LOWER=32'h0,
  parameter [31:0]    PF0_RBAR_CAP_BAR3_LOWER=32'h0,
  parameter [31:0]    PF0_RBAR_CAP_BAR4_LOWER=32'h0,
  parameter [31:0]    PF0_RBAR_CAP_BAR5_LOWER=32'h0,
  parameter [31:0]    PF1_RBAR_CAP_BAR0_LOWER=32'h0,
  parameter [31:0]    PF1_RBAR_CAP_BAR1_LOWER=32'h0,
  parameter [31:0]    PF1_RBAR_CAP_BAR2_LOWER=32'h0,
  parameter [31:0]    PF1_RBAR_CAP_BAR3_LOWER=32'h0,
  parameter [31:0]    PF1_RBAR_CAP_BAR4_LOWER=32'h0,
  parameter [31:0]    PF1_RBAR_CAP_BAR5_LOWER=32'h0,
  parameter [31:0]    PF2_RBAR_CAP_BAR0_LOWER=32'h0,
  parameter [31:0]    PF2_RBAR_CAP_BAR1_LOWER=32'h0,
  parameter [31:0]    PF2_RBAR_CAP_BAR2_LOWER=32'h0,
  parameter [31:0]    PF2_RBAR_CAP_BAR3_LOWER=32'h0,
  parameter [31:0]    PF2_RBAR_CAP_BAR4_LOWER=32'h0,
  parameter [31:0]    PF2_RBAR_CAP_BAR5_LOWER=32'h0,
  parameter [31:0]    PF3_RBAR_CAP_BAR0_LOWER=32'h0,
  parameter [31:0]    PF3_RBAR_CAP_BAR1_LOWER=32'h0,
  parameter [31:0]    PF3_RBAR_CAP_BAR2_LOWER=32'h0,
  parameter [31:0]    PF3_RBAR_CAP_BAR3_LOWER=32'h0,
  parameter [31:0]    PF3_RBAR_CAP_BAR4_LOWER=32'h0,
  parameter [31:0]    PF3_RBAR_CAP_BAR5_LOWER=32'h0,
  parameter [47:0]    PF0_RBAR_CAP_BAR0= {PF0_RBAR_CAP_BAR0_UPPER,PF0_RBAR_CAP_BAR0_LOWER},
  parameter [47:0]    PF0_RBAR_CAP_BAR1= {PF0_RBAR_CAP_BAR1_UPPER,PF0_RBAR_CAP_BAR1_LOWER},
  parameter [47:0]    PF0_RBAR_CAP_BAR2= {PF0_RBAR_CAP_BAR2_UPPER,PF0_RBAR_CAP_BAR2_LOWER},
  parameter [47:0]    PF0_RBAR_CAP_BAR3= {PF0_RBAR_CAP_BAR3_UPPER,PF0_RBAR_CAP_BAR3_LOWER},
  parameter [47:0]    PF0_RBAR_CAP_BAR4= {PF0_RBAR_CAP_BAR4_UPPER,PF0_RBAR_CAP_BAR4_LOWER},
  parameter [47:0]    PF0_RBAR_CAP_BAR5= {PF0_RBAR_CAP_BAR5_UPPER,PF0_RBAR_CAP_BAR5_LOWER},
  parameter [47:0]    PF1_RBAR_CAP_BAR0= {PF1_RBAR_CAP_BAR0_UPPER,PF1_RBAR_CAP_BAR0_LOWER},
  parameter [47:0]    PF1_RBAR_CAP_BAR1= {PF1_RBAR_CAP_BAR1_UPPER,PF1_RBAR_CAP_BAR1_LOWER},
  parameter [47:0]    PF1_RBAR_CAP_BAR2= {PF1_RBAR_CAP_BAR2_UPPER,PF1_RBAR_CAP_BAR2_LOWER},
  parameter [47:0]    PF1_RBAR_CAP_BAR3= {PF1_RBAR_CAP_BAR3_UPPER,PF1_RBAR_CAP_BAR3_LOWER},
  parameter [47:0]    PF1_RBAR_CAP_BAR4= {PF1_RBAR_CAP_BAR4_UPPER,PF1_RBAR_CAP_BAR4_LOWER},
  parameter [47:0]    PF1_RBAR_CAP_BAR5= {PF1_RBAR_CAP_BAR5_UPPER,PF1_RBAR_CAP_BAR5_LOWER},
  parameter [47:0]    PF2_RBAR_CAP_BAR0= {PF2_RBAR_CAP_BAR0_UPPER,PF2_RBAR_CAP_BAR0_LOWER},
  parameter [47:0]    PF2_RBAR_CAP_BAR1= {PF2_RBAR_CAP_BAR1_UPPER,PF2_RBAR_CAP_BAR1_LOWER},
  parameter [47:0]    PF2_RBAR_CAP_BAR2= {PF2_RBAR_CAP_BAR2_UPPER,PF2_RBAR_CAP_BAR2_LOWER},
  parameter [47:0]    PF2_RBAR_CAP_BAR3= {PF2_RBAR_CAP_BAR3_UPPER,PF2_RBAR_CAP_BAR3_LOWER},
  parameter [47:0]    PF2_RBAR_CAP_BAR4= {PF2_RBAR_CAP_BAR4_UPPER,PF2_RBAR_CAP_BAR4_LOWER},
  parameter [47:0]    PF2_RBAR_CAP_BAR5= {PF2_RBAR_CAP_BAR5_UPPER,PF2_RBAR_CAP_BAR5_LOWER},
  parameter [47:0]    PF3_RBAR_CAP_BAR0= {PF3_RBAR_CAP_BAR0_UPPER,PF3_RBAR_CAP_BAR0_LOWER},
  parameter [47:0]    PF3_RBAR_CAP_BAR1= {PF3_RBAR_CAP_BAR1_UPPER,PF3_RBAR_CAP_BAR1_LOWER},
  parameter [47:0]    PF3_RBAR_CAP_BAR2= {PF3_RBAR_CAP_BAR2_UPPER,PF3_RBAR_CAP_BAR2_LOWER},
  parameter [47:0]    PF3_RBAR_CAP_BAR3= {PF3_RBAR_CAP_BAR3_UPPER,PF3_RBAR_CAP_BAR3_LOWER},
  parameter [47:0]    PF3_RBAR_CAP_BAR4= {PF3_RBAR_CAP_BAR4_UPPER,PF3_RBAR_CAP_BAR4_LOWER},
  parameter [47:0]    PF3_RBAR_CAP_BAR5= {PF3_RBAR_CAP_BAR5_UPPER,PF3_RBAR_CAP_BAR5_LOWER},
  parameter           RBAR_ENABLE ="FALSE",
  parameter           PDVSEC_NEXTPTR=12'h000,
  parameter           TL2CFG_IF_PARITY_CHK="FALSE",
  parameter           HEADER_TYPE_OVERRIDE="FALSE",
  parameter [2:0]     PF0_BAR0_CONTROL=3'b100,
  parameter [2:0]     PF1_BAR0_CONTROL=3'b100,
  parameter [2:0]     PF2_BAR0_CONTROL=3'b100,
  parameter [2:0]     PF3_BAR0_CONTROL=3'b100,
  parameter [5:0]     PF0_BAR0_APERTURE_SIZE=6'b000011,
  parameter [5:0]     PF1_BAR0_APERTURE_SIZE=6'b000011,
  parameter [5:0]     PF2_BAR0_APERTURE_SIZE=6'b000011,
  parameter [5:0]     PF3_BAR0_APERTURE_SIZE=6'b000011,
  parameter [2:0]     PF0_BAR1_CONTROL=3'h4,
  parameter [2:0]     PF1_BAR1_CONTROL=3'b0,
  parameter [2:0]     PF2_BAR1_CONTROL=3'b0,
  parameter [2:0]     PF3_BAR1_CONTROL=3'b0,
  parameter [4:0]     PF0_BAR1_APERTURE_SIZE=5'b0,
  parameter [4:0]     PF1_BAR1_APERTURE_SIZE=5'b0,
  parameter [4:0]     PF2_BAR1_APERTURE_SIZE=5'b0,
  parameter [4:0]     PF3_BAR1_APERTURE_SIZE=5'b0,
  parameter [2:0]     PF0_BAR2_CONTROL=3'b100,
  parameter [2:0]     PF1_BAR2_CONTROL=3'b100,
  parameter [2:0]     PF2_BAR2_CONTROL=3'b100,
  parameter [2:0]     PF3_BAR2_CONTROL=3'b100,
  parameter [5:0]     PF0_BAR2_APERTURE_SIZE=6'b00011,
  parameter [5:0]     PF1_BAR2_APERTURE_SIZE=6'b00011,
  parameter [5:0]     PF2_BAR2_APERTURE_SIZE=6'b00011,
  parameter [5:0]     PF3_BAR2_APERTURE_SIZE=6'b00011,
  parameter [2:0]     PF0_BAR3_CONTROL=3'b0,
  parameter [2:0]     PF1_BAR3_CONTROL=3'b0,
  parameter [2:0]     PF2_BAR3_CONTROL=3'b0,
  parameter [2:0]     PF3_BAR3_CONTROL=3'b0,
  parameter [4:0]     PF0_BAR3_APERTURE_SIZE=5'b00011,
  parameter [4:0]     PF1_BAR3_APERTURE_SIZE=5'b00011,
  parameter [4:0]     PF2_BAR3_APERTURE_SIZE=5'b00011,
  parameter [4:0]     PF3_BAR3_APERTURE_SIZE=5'b00011,
  parameter [2:0]     PF0_BAR4_CONTROL=3'b100,
  parameter [2:0]     PF1_BAR4_CONTROL=3'b100,
  parameter [2:0]     PF2_BAR4_CONTROL=3'b100,
  parameter [2:0]     PF3_BAR4_CONTROL=3'b100,
  parameter [5:0]     PF0_BAR4_APERTURE_SIZE=6'b00011,
  parameter [5:0]     PF1_BAR4_APERTURE_SIZE=6'b00011,
  parameter [5:0]     PF2_BAR4_APERTURE_SIZE=6'b00011,
  parameter [5:0]     PF3_BAR4_APERTURE_SIZE=6'b00011,
  parameter [2:0]     PF0_BAR5_CONTROL=3'b0,
  parameter [2:0]     PF1_BAR5_CONTROL=3'b0,
  parameter [2:0]     PF2_BAR5_CONTROL=3'b0,
  parameter [2:0]     PF3_BAR5_CONTROL=3'b0,
  parameter [4:0]     PF0_BAR5_APERTURE_SIZE=5'b00011,
  parameter [4:0]     PF1_BAR5_APERTURE_SIZE=5'b00011,
  parameter [4:0]     PF2_BAR5_APERTURE_SIZE=5'b00011,
  parameter [4:0]     PF3_BAR5_APERTURE_SIZE=5'b00011,
  parameter           PF0_EXPANSION_ROM_ENABLE="FALSE",
  parameter           PF1_EXPANSION_ROM_ENABLE="FALSE",
  parameter           PF2_EXPANSION_ROM_ENABLE="FALSE",
  parameter           PF3_EXPANSION_ROM_ENABLE="FALSE",
  parameter [4:0]     PF0_EXPANSION_ROM_APERTURE_SIZE=5'b00011,
  parameter [4:0]     PF1_EXPANSION_ROM_APERTURE_SIZE=5'b00011,
  parameter [4:0]     PF2_EXPANSION_ROM_APERTURE_SIZE=5'b00011,
  parameter [4:0]     PF3_EXPANSION_ROM_APERTURE_SIZE=5'b00011,
  parameter [11:0]     VF0_EXT_PCIE_CFG_SPACE_ENABLED_NEXTPTR = 'h00,
  parameter [11:0]     VF1_EXT_PCIE_CFG_SPACE_ENABLED_NEXTPTR = 'h00,
  parameter [11:0]     VF2_EXT_PCIE_CFG_SPACE_ENABLED_NEXTPTR = 'h00,
  parameter [11:0]     VF3_EXT_PCIE_CFG_SPACE_ENABLED_NEXTPTR = 'h00,
  parameter [7:0]     PF0_PCIE_CAP_NEXTPTR=8'h0,
  parameter [7:0]     PF1_PCIE_CAP_NEXTPTR=8'h0,
  parameter [7:0]     PF2_PCIE_CAP_NEXTPTR=8'h0,
  parameter [7:0]     PF3_PCIE_CAP_NEXTPTR=8'h0 ,
  parameter [7:0]     VFG0_PCIE_CAP_NEXTPTR=8'h0,
  parameter [7:0]     VFG1_PCIE_CAP_NEXTPTR=8'h0,
  parameter [7:0]     VFG2_PCIE_CAP_NEXTPTR=8'h0,
  parameter [7:0]     VFG3_PCIE_CAP_NEXTPTR=8'h0,
  parameter [2:0]     PF0_DEV_CAP_MAX_PAYLOAD_SIZE=3'b011,
  parameter [2:0]     PF1_DEV_CAP_MAX_PAYLOAD_SIZE=3'b011,
  parameter [2:0]     PF2_DEV_CAP_MAX_PAYLOAD_SIZE=3'b011,
  parameter [2:0]     PF3_DEV_CAP_MAX_PAYLOAD_SIZE=3'b011,
  parameter           PF0_DEV_CAP_EXT_TAG_SUPPORTED="TRUE",
  parameter integer   PF0_DEV_CAP_ENDPOINT_L0S_LATENCY=0,
  parameter integer   PF0_DEV_CAP_ENDPOINT_L1_LATENCY=0,
  parameter           PF0_DEV_CAP_FUNCTION_LEVEL_RESET_CAPABLE="TRUE",
  parameter integer   PF0_LINK_CAP_ASPM_SUPPORT=0,
  parameter [0:0]     PF0_LINK_CONTROL_RCB=1'b0,
  parameter           PF0_LINK_STATUS_SLOT_CLOCK_CONFIG="TRUE",
  parameter integer   PF0_LINK_CAP_L0S_EXIT_LATENCY_COMCLK_GEN1=7,
  parameter integer   PF0_LINK_CAP_L0S_EXIT_LATENCY_COMCLK_GEN2=7,
  parameter integer   PF0_LINK_CAP_L0S_EXIT_LATENCY_COMCLK_GEN3=7,
  parameter integer   PF0_LINK_CAP_L0S_EXIT_LATENCY_COMCLK_GEN4=7,
  parameter integer   PF0_LINK_CAP_L0S_EXIT_LATENCY_GEN1=7,
  parameter integer   PF0_LINK_CAP_L0S_EXIT_LATENCY_GEN2=7,
  parameter integer   PF0_LINK_CAP_L0S_EXIT_LATENCY_GEN3=7,
  parameter integer   PF0_LINK_CAP_L0S_EXIT_LATENCY_GEN4=7,
  parameter integer   PF0_LINK_CAP_L1_EXIT_LATENCY_COMCLK_GEN1=7,
  parameter integer   PF0_LINK_CAP_L1_EXIT_LATENCY_COMCLK_GEN2=7,
  parameter integer   PF0_LINK_CAP_L1_EXIT_LATENCY_COMCLK_GEN3=7,
  parameter integer   PF0_LINK_CAP_L1_EXIT_LATENCY_COMCLK_GEN4=7,
  parameter integer   PF0_LINK_CAP_L1_EXIT_LATENCY_GEN1=7,
  parameter integer   PF0_LINK_CAP_L1_EXIT_LATENCY_GEN2=7,
  parameter integer   PF0_LINK_CAP_L1_EXIT_LATENCY_GEN3=7,
  parameter integer   PF0_LINK_CAP_L1_EXIT_LATENCY_GEN4=7,
  parameter           PF0_DEV_CAP2_CPL_TIMEOUT_DISABLE="TRUE",
  parameter           PF0_DEV_CAP2_32B_ATOMIC_COMPLETER_SUPPORT="TRUE",
  parameter           PF0_DEV_CAP2_64B_ATOMIC_COMPLETER_SUPPORT="TRUE",
  parameter           PF0_DEV_CAP2_128B_CAS_ATOMIC_COMPLETER_SUPPORT="TRUE",
  parameter           PF0_DEV_CAP2_LTR_SUPPORT="FALSE",
  parameter           PF0_DEV_CAP2_TPH_COMPLETER_SUPPORT="FALSE",
  parameter [1:0]     PF0_DEV_CAP2_OBFF_SUPPORT=2'b00,
  parameter           PF0_DEV_CAP2_ARI_FORWARD_ENABLE="FALSE",
  parameter [7:0]     PF0_MSI_CAP_NEXTPTR=8'h0,
  parameter [7:0]     PF1_MSI_CAP_NEXTPTR=8'h0,
  parameter [7:0]     PF2_MSI_CAP_NEXTPTR=8'h0,
  parameter [7:0]     PF3_MSI_CAP_NEXTPTR=8'h0,
  parameter           PF0_MSI_CAP_PERVECMASKCAP="FALSE",
  parameter           PF1_MSI_CAP_PERVECMASKCAP="FALSE",
  parameter           PF2_MSI_CAP_PERVECMASKCAP="FALSE",
  parameter           PF3_MSI_CAP_PERVECMASKCAP="FALSE",
  parameter integer   PF0_MSI_CAP_MULTIMSGCAP=0,
  parameter integer   PF1_MSI_CAP_MULTIMSGCAP=0,
  parameter integer   PF2_MSI_CAP_MULTIMSGCAP=0,
  parameter integer   PF3_MSI_CAP_MULTIMSGCAP=0,
  parameter [7:0]     PF0_MSIX_CAP_NEXTPTR=8'h0,
  parameter [7:0]     PF1_MSIX_CAP_NEXTPTR=8'h0,
  parameter [7:0]     PF2_MSIX_CAP_NEXTPTR=8'h0,
  parameter [7:0]     PF3_MSIX_CAP_NEXTPTR=8'h0,
  parameter [7:0]     VFG0_MSIX_CAP_NEXTPTR=PF0_MSIX_CAP_NEXTPTR,
  parameter [7:0]     VFG1_MSIX_CAP_NEXTPTR=PF1_MSIX_CAP_NEXTPTR,
  parameter [7:0]     VFG2_MSIX_CAP_NEXTPTR=PF2_MSIX_CAP_NEXTPTR,
  parameter [7:0]     VFG3_MSIX_CAP_NEXTPTR=PF3_MSIX_CAP_NEXTPTR,
  parameter integer   PF0_MSIX_CAP_PBA_BIR=0,
  parameter integer   PF1_MSIX_CAP_PBA_BIR=0,
  parameter integer   PF2_MSIX_CAP_PBA_BIR=0,
  parameter integer   PF3_MSIX_CAP_PBA_BIR=0,
  parameter integer   VFG0_MSIX_CAP_PBA_BIR=PF0_MSIX_CAP_PBA_BIR,
  parameter integer   VFG1_MSIX_CAP_PBA_BIR=PF1_MSIX_CAP_PBA_BIR,
  parameter integer   VFG2_MSIX_CAP_PBA_BIR=PF2_MSIX_CAP_PBA_BIR,
  parameter integer   VFG3_MSIX_CAP_PBA_BIR=PF3_MSIX_CAP_PBA_BIR,
  parameter [28:0]    PF0_MSIX_CAP_PBA_OFFSET=29'h50,
  parameter [28:0]    PF1_MSIX_CAP_PBA_OFFSET=29'h50,
  parameter [28:0]    PF2_MSIX_CAP_PBA_OFFSET=29'h50,
  parameter [28:0]    PF3_MSIX_CAP_PBA_OFFSET=29'h50,
  parameter [28:0]    VFG0_MSIX_CAP_PBA_OFFSET=PF0_MSIX_CAP_PBA_OFFSET,
  parameter [28:0]    VFG1_MSIX_CAP_PBA_OFFSET=PF1_MSIX_CAP_PBA_OFFSET,
  parameter [28:0]    VFG2_MSIX_CAP_PBA_OFFSET=PF2_MSIX_CAP_PBA_OFFSET,
  parameter [28:0]    VFG3_MSIX_CAP_PBA_OFFSET=PF3_MSIX_CAP_PBA_OFFSET,
  parameter integer   PF0_MSIX_CAP_TABLE_BIR=0,
  parameter integer   PF1_MSIX_CAP_TABLE_BIR=0,
  parameter integer   PF2_MSIX_CAP_TABLE_BIR=0,
  parameter integer   PF3_MSIX_CAP_TABLE_BIR=0,
  parameter integer   VFG0_MSIX_CAP_TABLE_BIR=PF0_MSIX_CAP_TABLE_BIR,
  parameter integer   VFG1_MSIX_CAP_TABLE_BIR=PF1_MSIX_CAP_TABLE_BIR,
  parameter integer   VFG2_MSIX_CAP_TABLE_BIR=PF2_MSIX_CAP_TABLE_BIR,
  parameter integer   VFG3_MSIX_CAP_TABLE_BIR=PF3_MSIX_CAP_TABLE_BIR,
  parameter [28:0]    PF0_MSIX_CAP_TABLE_OFFSET=29'h40,
  parameter [28:0]    PF1_MSIX_CAP_TABLE_OFFSET=29'h40,
  parameter [28:0]    PF2_MSIX_CAP_TABLE_OFFSET=29'h40,
  parameter [28:0]    PF3_MSIX_CAP_TABLE_OFFSET=29'h40,
  parameter [28:0]    VFG0_MSIX_CAP_TABLE_OFFSET=PF0_MSIX_CAP_TABLE_OFFSET,
  parameter [28:0]    VFG1_MSIX_CAP_TABLE_OFFSET=PF1_MSIX_CAP_TABLE_OFFSET,
  parameter [28:0]    VFG2_MSIX_CAP_TABLE_OFFSET=PF2_MSIX_CAP_TABLE_OFFSET,
  parameter [28:0]    VFG3_MSIX_CAP_TABLE_OFFSET=PF3_MSIX_CAP_TABLE_OFFSET,
  parameter [10:0]    PF0_MSIX_CAP_TABLE_SIZE=11'h0,
  parameter [10:0]    PF1_MSIX_CAP_TABLE_SIZE=11'h0,
  parameter [10:0]    PF2_MSIX_CAP_TABLE_SIZE=11'h0,
  parameter [10:0]    PF3_MSIX_CAP_TABLE_SIZE=11'h0,
  parameter [10:0]    VFG0_MSIX_CAP_TABLE_SIZE=PF0_MSIX_CAP_TABLE_SIZE,
  parameter [10:0]    VFG1_MSIX_CAP_TABLE_SIZE=PF1_MSIX_CAP_TABLE_SIZE,
  parameter [10:0]    VFG2_MSIX_CAP_TABLE_SIZE=PF2_MSIX_CAP_TABLE_SIZE,
  parameter [10:0]    VFG3_MSIX_CAP_TABLE_SIZE=PF3_MSIX_CAP_TABLE_SIZE,
  parameter [5:0]     PF0_MSIX_VECTOR_COUNT=6'h4,
  parameter [7:0]     PF0_PM_CAP_ID=8'h1,
  parameter [7:0]     PF0_PM_CAP_NEXTPTR=8'h0,
  parameter [7:0]     PF1_PM_CAP_NEXTPTR=8'h0,
  parameter [7:0]     PF2_PM_CAP_NEXTPTR=8'h0,
  parameter [7:0]     PF3_PM_CAP_NEXTPTR=8'h0,
  parameter           PF0_PM_CAP_PMESUPPORT_D3HOT="TRUE",
  parameter           PF0_PM_CAP_PMESUPPORT_D1="TRUE",
  parameter           PF0_PM_CAP_PMESUPPORT_D0="TRUE",
  parameter           PF0_PM_CAP_SUPP_D1_STATE="TRUE",
  parameter [2:0]     PF0_PM_CAP_VER_ID=3'h3,
  parameter           PF0_PM_CSR_NOSOFTRESET="TRUE",
  parameter [7:0]     DNSTREAM_LINK_NUM=8'h0,
  parameter           AUTO_FLR_RESPONSE="FALSE",
  parameter [11:0]    PF0_DSN_CAP_NEXTPTR=12'h10C,
  parameter [11:0]    PF1_DSN_CAP_NEXTPTR=12'h10C,
  parameter [11:0]    PF2_DSN_CAP_NEXTPTR=12'h10C,
  parameter [11:0]    PF3_DSN_CAP_NEXTPTR=12'h10C,
  parameter           DSN_CAP_ENABLE="FALSE",
  parameter [3:0]     PF0_VC_CAP_VER=4'h1,
  parameter [11:0]    PF0_VC_CAP_NEXTPTR=12'h0,
  parameter           PF0_VC_CAP_ENABLE="FALSE",
  parameter [11:0]    PF0_SECONDARY_PCIE_CAP_NEXTPTR=12'h0,
  parameter [11:0]    PF0_AER_CAP_NEXTPTR=12'h0,
  parameter [11:0]    PF1_AER_CAP_NEXTPTR=12'h0,
  parameter [11:0]    PF2_AER_CAP_NEXTPTR=12'h0,
  parameter [11:0]    PF3_AER_CAP_NEXTPTR=12'h0,
  parameter           PF0_AER_CAP_ECRC_GEN_AND_CHECK_CAPABLE="FALSE",
  parameter           ARI_CAP_ENABLE="FALSE",
  parameter [11:0]    PF0_ARI_CAP_NEXTPTR=12'h0,
  parameter [11:0]    PF1_ARI_CAP_NEXTPTR=12'h0,
  parameter [11:0]    PF2_ARI_CAP_NEXTPTR=12'h0,
  parameter [11:0]    PF3_ARI_CAP_NEXTPTR=12'h0,
  parameter [11:0]    VFG0_ARI_CAP_NEXTPTR=VF0_EXT_PCIE_CFG_SPACE_ENABLED_NEXTPTR, //12'h0
  parameter [11:0]    VFG1_ARI_CAP_NEXTPTR=VF1_EXT_PCIE_CFG_SPACE_ENABLED_NEXTPTR, //12'h0
  parameter [11:0]    VFG2_ARI_CAP_NEXTPTR=VF2_EXT_PCIE_CFG_SPACE_ENABLED_NEXTPTR, //12'h0
  parameter [11:0]    VFG3_ARI_CAP_NEXTPTR=VF3_EXT_PCIE_CFG_SPACE_ENABLED_NEXTPTR, //12'h0
  parameter [3:0]     PF0_ARI_CAP_VER=4'h1,
  parameter [7:0]     PF0_ARI_CAP_NEXT_FUNC=8'h0,
  parameter [7:0]     PF1_ARI_CAP_NEXT_FUNC=8'h0,
  parameter [7:0]     PF2_ARI_CAP_NEXT_FUNC=8'h0,
  parameter [7:0]     PF3_ARI_CAP_NEXT_FUNC=8'h0,
  parameter [11:0]    PF0_LTR_CAP_NEXTPTR=12'h0,
  parameter [3:0]     PF0_LTR_CAP_VER=4'h1,
  parameter [9:0]     PF0_LTR_CAP_MAX_SNOOP_LAT=10'h0,
  parameter [9:0]     PF0_LTR_CAP_MAX_NOSNOOP_LAT=10'h0,
  parameter           LTR_TX_MESSAGE_ON_LTR_ENABLE="FALSE",
  parameter           LTR_TX_MESSAGE_ON_FUNC_POWER_STATE_CHANGE="FALSE",
  parameter [9:0]     LTR_TX_MESSAGE_MINIMUM_INTERVAL=10'h250,
  parameter [3:0]     SRIOV_CAP_ENABLE=4'h0,
  parameter [11:0]    PF0_SRIOV_CAP_NEXTPTR=12'h0,
  parameter [11:0]    PF1_SRIOV_CAP_NEXTPTR=12'h0,
  parameter [11:0]    PF2_SRIOV_CAP_NEXTPTR=12'h0,
  parameter [11:0]    PF3_SRIOV_CAP_NEXTPTR=12'h0,
  parameter [3:0]     PF0_SRIOV_CAP_VER=4'h1,
  parameter [3:0]     PF1_SRIOV_CAP_VER=4'h1,
  parameter [3:0]     PF2_SRIOV_CAP_VER=4'h1,
  parameter [3:0]     PF3_SRIOV_CAP_VER=4'h1,
  parameter           PF0_SRIOV_ARI_CAPBL_HIER_PRESERVED="FALSE",
  parameter           PF1_SRIOV_ARI_CAPBL_HIER_PRESERVED="FALSE",
  parameter           PF2_SRIOV_ARI_CAPBL_HIER_PRESERVED="FALSE",
  parameter           PF3_SRIOV_ARI_CAPBL_HIER_PRESERVED="FALSE",
  parameter [15:0]    PF0_SRIOV_CAP_INITIAL_VF=16'h0,
  parameter [15:0]    PF1_SRIOV_CAP_INITIAL_VF=16'h0,
  parameter [15:0]    PF2_SRIOV_CAP_INITIAL_VF=16'h0,
  parameter [15:0]    PF3_SRIOV_CAP_INITIAL_VF=16'h0,
  parameter [15:0]    PF0_SRIOV_CAP_TOTAL_VF=16'h0,
  parameter [15:0]    PF1_SRIOV_CAP_TOTAL_VF=16'h0,
  parameter [15:0]    PF2_SRIOV_CAP_TOTAL_VF=16'h0,
  parameter [15:0]    PF3_SRIOV_CAP_TOTAL_VF=16'h0,
  parameter [15:0]    PF0_SRIOV_FUNC_DEP_LINK=16'h0,
  parameter [15:0]    PF1_SRIOV_FUNC_DEP_LINK=16'h0,
  parameter [15:0]    PF2_SRIOV_FUNC_DEP_LINK=16'h0,
  parameter [15:0]    PF3_SRIOV_FUNC_DEP_LINK=16'h0,
  parameter [15:0]    PF0_SRIOV_FIRST_VF_OFFSET=16'h0,
  parameter [15:0]    PF1_SRIOV_FIRST_VF_OFFSET=16'h0,
  parameter [15:0]    PF2_SRIOV_FIRST_VF_OFFSET=16'h0,
  parameter [15:0]    PF3_SRIOV_FIRST_VF_OFFSET=16'h0,
  parameter [15:0]    PF0_SRIOV_VF_DEVICE_ID=16'h0,
  parameter [15:0]    PF1_SRIOV_VF_DEVICE_ID=16'h0,
  parameter [15:0]    PF2_SRIOV_VF_DEVICE_ID=16'h0,
  parameter [15:0]    PF3_SRIOV_VF_DEVICE_ID=16'h0,
  parameter [31:0]    PF0_SRIOV_SUPPORTED_PAGE_SIZE=32'h0,
  parameter [31:0]    PF1_SRIOV_SUPPORTED_PAGE_SIZE=32'h0,
  parameter [31:0]    PF2_SRIOV_SUPPORTED_PAGE_SIZE=32'h0,
  parameter [31:0]    PF3_SRIOV_SUPPORTED_PAGE_SIZE=32'h0,
  parameter [2:0]     PF0_SRIOV_BAR0_CONTROL=3'b100,
  parameter [2:0]     PF1_SRIOV_BAR0_CONTROL=3'b100,
  parameter [2:0]     PF2_SRIOV_BAR0_CONTROL=3'b100,
  parameter [2:0]     PF3_SRIOV_BAR0_CONTROL=3'b100,
  parameter [5:0]     PF0_SRIOV_BAR0_APERTURE_SIZE=6'b000011,
  parameter [5:0]     PF1_SRIOV_BAR0_APERTURE_SIZE=6'b000011,
  parameter [5:0]     PF2_SRIOV_BAR0_APERTURE_SIZE=6'b000011,
  parameter [5:0]     PF3_SRIOV_BAR0_APERTURE_SIZE=6'b000011,
  parameter [2:0]     PF0_SRIOV_BAR1_CONTROL=3'b0,
  parameter [2:0]     PF1_SRIOV_BAR1_CONTROL=3'b0,
  parameter [2:0]     PF2_SRIOV_BAR1_CONTROL=3'b0,
  parameter [2:0]     PF3_SRIOV_BAR1_CONTROL=3'b0,
  parameter [4:0]     PF0_SRIOV_BAR1_APERTURE_SIZE=5'b0,
  parameter [4:0]     PF1_SRIOV_BAR1_APERTURE_SIZE=5'b0,
  parameter [4:0]     PF2_SRIOV_BAR1_APERTURE_SIZE=5'b0,
  parameter [4:0]     PF3_SRIOV_BAR1_APERTURE_SIZE=5'b0,
  parameter [2:0]     PF0_SRIOV_BAR2_CONTROL=3'b100,
  parameter [2:0]     PF1_SRIOV_BAR2_CONTROL=3'b100,
  parameter [2:0]     PF2_SRIOV_BAR2_CONTROL=3'b100,
  parameter [2:0]     PF3_SRIOV_BAR2_CONTROL=3'b100,
  parameter [5:0]     PF0_SRIOV_BAR2_APERTURE_SIZE=6'b000011,
  parameter [5:0]     PF1_SRIOV_BAR2_APERTURE_SIZE=6'b000011,
  parameter [5:0]     PF2_SRIOV_BAR2_APERTURE_SIZE=6'b000011,
  parameter [5:0]     PF3_SRIOV_BAR2_APERTURE_SIZE=6'b000011,
  parameter [2:0]     PF0_SRIOV_BAR3_CONTROL=3'b0,
  parameter [2:0]     PF1_SRIOV_BAR3_CONTROL=3'b0,
  parameter [2:0]     PF2_SRIOV_BAR3_CONTROL=3'b0,
  parameter [2:0]     PF3_SRIOV_BAR3_CONTROL=3'b0,
  parameter [4:0]     PF0_SRIOV_BAR3_APERTURE_SIZE=5'b00011,
  parameter [4:0]     PF1_SRIOV_BAR3_APERTURE_SIZE=5'b00011,
  parameter [4:0]     PF2_SRIOV_BAR3_APERTURE_SIZE=5'b00011,
  parameter [4:0]     PF3_SRIOV_BAR3_APERTURE_SIZE=5'b00011,
  parameter [2:0]     PF0_SRIOV_BAR4_CONTROL=3'b100,
  parameter [2:0]     PF1_SRIOV_BAR4_CONTROL=3'b100,
  parameter [2:0]     PF2_SRIOV_BAR4_CONTROL=3'b100,
  parameter [2:0]     PF3_SRIOV_BAR4_CONTROL=3'b100,
  parameter [5:0]     PF0_SRIOV_BAR4_APERTURE_SIZE=6'b000011,
  parameter [5:0]     PF1_SRIOV_BAR4_APERTURE_SIZE=6'b000011,
  parameter [5:0]     PF2_SRIOV_BAR4_APERTURE_SIZE=6'b000011,
  parameter [5:0]     PF3_SRIOV_BAR4_APERTURE_SIZE=6'b000011,
  parameter [2:0]     PF0_SRIOV_BAR5_CONTROL=3'b0,
  parameter [2:0]     PF1_SRIOV_BAR5_CONTROL=3'b0,
  parameter [2:0]     PF2_SRIOV_BAR5_CONTROL=3'b0,
  parameter [2:0]     PF3_SRIOV_BAR5_CONTROL=3'b0,
  parameter [4:0]     PF0_SRIOV_BAR5_APERTURE_SIZE=5'b00011,
  parameter [4:0]     PF1_SRIOV_BAR5_APERTURE_SIZE=5'b00011,
  parameter [4:0]     PF2_SRIOV_BAR5_APERTURE_SIZE=5'b00011,
  parameter [4:0]     PF3_SRIOV_BAR5_APERTURE_SIZE=5'b00011,
  parameter [11:0]    PF0_TPHR_CAP_NEXTPTR=12'h0,
  parameter [11:0]    PF1_TPHR_CAP_NEXTPTR=12'h0,
  parameter [11:0]    PF2_TPHR_CAP_NEXTPTR=12'h0,
  parameter [11:0]    PF3_TPHR_CAP_NEXTPTR=12'h0,
  parameter [11:0]    VFG0_TPHR_CAP_NEXTPTR=12'h0,
  parameter [11:0]    VFG1_TPHR_CAP_NEXTPTR=12'h0,
  parameter [11:0]    VFG2_TPHR_CAP_NEXTPTR=12'h0,
  parameter [11:0]    VFG3_TPHR_CAP_NEXTPTR=12'h0,
  parameter [3:0]     PF0_TPHR_CAP_VER=4'h1,
  parameter           PF0_TPHR_CAP_INT_VEC_MODE="TRUE",
  parameter           PF0_TPHR_CAP_DEV_SPECIFIC_MODE="TRUE",
  parameter [1:0]     PF0_TPHR_CAP_ST_TABLE_LOC=2'h0,
  parameter [10:0]    PF0_TPHR_CAP_ST_TABLE_SIZE=11'h0,
  parameter [2:0]     PF0_TPHR_CAP_ST_MODE_SEL=3'h0,
  parameter [2:0]     PF1_TPHR_CAP_ST_MODE_SEL=3'h0,
  parameter [2:0]     PF2_TPHR_CAP_ST_MODE_SEL=3'h0,
  parameter [2:0]     PF3_TPHR_CAP_ST_MODE_SEL=3'h0,
  parameter [2:0]     VFG0_TPHR_CAP_ST_MODE_SEL=3'h0,
  parameter [2:0]     VFG1_TPHR_CAP_ST_MODE_SEL=3'h0,
  parameter [2:0]     VFG2_TPHR_CAP_ST_MODE_SEL=3'h0,
  parameter [2:0]     VFG3_TPHR_CAP_ST_MODE_SEL=3'h0,
  parameter           PF0_TPHR_CAP_ENABLE="FALSE",
  parameter           TPH_TO_RAM_PIPELINE="TRUE",
  parameter           TPH_FROM_RAM_PIPELINE="TRUE",
  parameter           MCAP_ENABLE="FALSE",
  parameter           MCAP_INTERRUPT_ON_MCAP_ERROR="FALSE",
  parameter           ECC_PIPELINE="FALSE",
  parameter           MCAP_INTERRUPT_ON_MCAP_EOS="FALSE",
  parameter           MCAP_CONFIGURE_OVERRIDE="FALSE",
  parameter [15:0]    MCAP_VSEC_ID=16'h0001,
  parameter [3:0]     MCAP_VSEC_REV=4'h1,
  parameter [11:0]    MCAP_VSEC_LEN=12'h2C,
  parameter [31:0]    MCAP_FPGA_BITSTREAM_VERSION=32'h00300000,
  parameter           MCAP_INPUT_GATE_DESIGN_SWITCH="FALSE",
  parameter           MCAP_GATE_MEM_ENABLE_DESIGN_SWITCH="FALSE",
  parameter           MCAP_GATE_IO_ENABLE_DESIGN_SWITCH="FALSE",
  parameter           MCAP_EOS_DESIGN_SWITCH="FALSE",
  parameter [11:0]    MCAP_CAP_NEXTPTR=12'h0,
  parameter [31:0]    SIM_JTAG_IDCODE=32'h0,
  parameter [7:0]     DEBUG_AXIST_DISABLE_FEATURE_BIT=8'h0,
  parameter           DEBUG_TL_DISABLE_RX_TLP_ORDER_CHECKS="FALSE",
  parameter           DEBUG_TL_DISABLE_FC_TIMEOUT="FALSE",
  parameter           DEBUG_PL_DISABLE_SCRAMBLING="FALSE",
  parameter           DEBUG_PL_DISABLE_REC_ENTRY_ON_DYNAMIC_DSKEW_FAIL ="FALSE",
  parameter           DEBUG_PL_DISABLE_REC_ENTRY_ON_RX_BUFFER_UNDER_OVER_FLOW ="FALSE",
  parameter           DEBUG_PL_DISABLE_LES_UPDATE_ON_SKP_ERROR="FALSE",
  parameter           DEBUG_PL_DISABLE_LES_UPDATE_ON_SKP_PARITY_ERROR="FALSE",
  parameter           DEBUG_PL_DISABLE_LES_UPDATE_ON_DEFRAMER_ERROR="FALSE",
  parameter           DEBUG_PL_SIM_RESET_LFSR="FALSE",
  parameter [15:0]    DEBUG_PL_SPARE=16'h0,
  parameter [15:0]    DEBUG_LL_SPARE=16'h0,
  parameter [15:0]    DEBUG_TL_SPARE=16'h0,
  parameter [15:0]    DEBUG_AXI4ST_SPARE=16'h0,
  parameter [15:0]    DEBUG_CFG_SPARE=16'h0,
  parameter [3:0]     DEBUG_CAR_SPARE=4'h0,
  parameter           TEST_MODE_PIN_CHAR="FALSE",
  parameter           SPARE_BIT0="FALSE",
  parameter           SPARE_BIT1=1'b0,
  parameter           SPARE_BIT2=1'b0,
  parameter           SPARE_BIT3="FALSE",
  parameter           SPARE_BIT4=1'b0,
  parameter           SPARE_BIT5=1'b0,
  parameter           SPARE_BIT6=1'b0,
  parameter           SPARE_BIT7=1'b0,
  parameter           SPARE_BIT8=1'b0,
  parameter [7:0]     SPARE_BYTE0=8'h0,
  parameter [7:0]     SPARE_BYTE1=8'h0,
  parameter [7:0]     SPARE_BYTE2=8'h0,
  parameter [7:0]     SPARE_BYTE3=8'h0,
  parameter [31:0]    SPARE_WORD0=32'h0,
  parameter [31:0]    SPARE_WORD1=32'h0,
  parameter [31:0]    SPARE_WORD2=32'h0,
  parameter [31:0]    SPARE_WORD3=32'h0,

  parameter [7:0]     AXISTEN_IF_CCIX_RX_CREDIT_LIMIT	= 8'h08,
  parameter [7:0]     AXISTEN_IF_CCIX_TX_CREDIT_LIMIT	= 8'h08,
  parameter           AXISTEN_IF_CCIX_TX_REGISTERED_TREADY	= "FALSE",
  parameter           CCIX_DIRECT_ATTACH_MODE	= "FALSE",
  parameter           CCIX_ENABLE	= "FALSE",
  parameter           CCIX_DVSEC	= "FALSE",
  parameter [15:0]    CCIX_VENDOR_ID	= 16'h0000,

  parameter [3:0]     PF0_VC_ARB_CAPABILITY	= 4'h0,
  parameter [7:0]     PF0_VC_ARB_TBL_OFFSET	= 8'h00,
  parameter           PF0_VC_EXTENDED_COUNT	= "FALSE",
  parameter           PF0_VC_LOW_PRIORITY_EXTENDED_COUNT	= "FALSE",

  parameter           PASID_CAP_ON	= "FALSE",

  parameter [4:0]     PF0_ATS_CAP_INV_QUEUE_DEPTH	= 5'h00,
  parameter [11:0]    PF0_ATS_CAP_NEXTPTR	= 12'h000,
  parameter           PF0_ATS_CAP_ON	= "FALSE",
  parameter [11:0]    PF0_PRI_CAP_NEXTPTR	= 12'h000,
  parameter           PF0_PRI_CAP_ON	= "FALSE",
  parameter [31:0]    PF0_PRI_OST_PR_CAPACITY	= 32'h00000000,
  parameter [4:0]     PF1_ATS_CAP_INV_QUEUE_DEPTH	= 5'h00,
  parameter [11:0]    PF1_ATS_CAP_NEXTPTR	= 12'h000,
  parameter           PF1_ATS_CAP_ON	= "FALSE",
  parameter [11:0]    PF1_PRI_CAP_NEXTPTR	= 12'h000,
  parameter           PF1_PRI_CAP_ON	= "FALSE",
  parameter [31:0]    PF1_PRI_OST_PR_CAPACITY	= 32'h00000000,
  parameter [4:0]     PF2_ATS_CAP_INV_QUEUE_DEPTH	= 5'h00,
  parameter [11:0]    PF2_ATS_CAP_NEXTPTR	= 12'h000,
  parameter           PF2_ATS_CAP_ON	= "FALSE",
  parameter [11:0]    PF2_PRI_CAP_NEXTPTR	= 12'h000,
  parameter           PF2_PRI_CAP_ON	= "FALSE",
  parameter [31:0]    PF2_PRI_OST_PR_CAPACITY	= 32'h00000000,
  parameter [4:0]     PF3_ATS_CAP_INV_QUEUE_DEPTH	= 5'h00,
  parameter [11:0]    PF3_ATS_CAP_NEXTPTR	= 12'h000,
  parameter           PF3_ATS_CAP_ON	= "FALSE",
  parameter [11:0]    PF3_PRI_CAP_NEXTPTR	= 12'h000,
  parameter           PF3_PRI_CAP_ON	= "FALSE",
  parameter [31:0]    PF3_PRI_OST_PR_CAPACITY	= 32'h00000000,

  parameter           PL_CTRL_SKP_GEN_ENABLE	= "TRUE",
  parameter           PL_CTRL_SKP_PARITY_AND_CRC_CHECK_DISABLE	= "TRUE",
  parameter [15:0]    PL_USER_SPARE2	= 16'h0000,

  parameter [11:0]    TL_CREDITS_CD_VC1	= 12'h000,
  parameter [7:0]     TL_CREDITS_CH_VC1	= 8'h00,
  parameter [11:0]    TL_CREDITS_NPD_VC1	= 12'h000,
  parameter [7:0]     TL_CREDITS_NPH_VC1	= 8'h01,
  parameter [11:0]    TL_CREDITS_PD_VC1	= 12'h3e0,
  parameter [7:0]     TL_CREDITS_PH_VC1	= 8'h20,

  parameter [4:0]     TL_FC_UPDATE_MIN_INTERVAL_TIME_VC1	= 5'h02,
  parameter [4:0]     TL_FC_UPDATE_MIN_INTERVAL_TLP_COUNT_VC1	= 5'h08,
  parameter           TL_FEATURE_ENABLE_FC_SCALING	= "FALSE",

  parameter [4:0]     VFG0_ATS_CAP_INV_QUEUE_DEPTH	= PF0_ATS_CAP_INV_QUEUE_DEPTH,
  parameter [11:0]    VFG0_ATS_CAP_NEXTPTR	= PF0_ATS_CAP_NEXTPTR,
  parameter           VFG0_ATS_CAP_ON	= PF0_ATS_CAP_ON,
  parameter [4:0]     VFG1_ATS_CAP_INV_QUEUE_DEPTH	= PF1_ATS_CAP_INV_QUEUE_DEPTH,
  parameter [11:0]    VFG1_ATS_CAP_NEXTPTR	= PF1_ATS_CAP_NEXTPTR,
  parameter           VFG1_ATS_CAP_ON	= PF1_ATS_CAP_ON,
  parameter [4:0]     VFG2_ATS_CAP_INV_QUEUE_DEPTH	= PF2_ATS_CAP_INV_QUEUE_DEPTH,
  parameter [11:0]    VFG2_ATS_CAP_NEXTPTR	= PF2_ATS_CAP_NEXTPTR,
  parameter           VFG2_ATS_CAP_ON	= PF2_ATS_CAP_ON,
  parameter [4:0]     VFG3_ATS_CAP_INV_QUEUE_DEPTH	= PF3_ATS_CAP_INV_QUEUE_DEPTH,
  parameter [11:0]    VFG3_ATS_CAP_NEXTPTR	= PF3_ATS_CAP_NEXTPTR,
  parameter           VFG3_ATS_CAP_ON	= PF3_ATS_CAP_ON,

// ----------------------------------------------
//   DVSEC
// ----------------------------------------------
  parameter         TDVSEC_OPT_TLP_SUPPORT      = "TRUE",
  parameter [11:0]  CCIX_DVSEC_PCSR_START_ADDR  = 12'h680,
  parameter [11:0]  CCIX_DVSEC_PCSR_SIZE        = 12'h50,
  parameter [11:0]  CCIX_DVSEC_PCR_START_ADDR   = 12'h800,
  parameter [11:0]  CCIX_DVSEC_PCR_SIZE         = 12'h3C,
  parameter [11:0]  CCIX_DVSEC_SAM_TABLE_START_ADDR   = 12'hA00,
  parameter [11:0]  CCIX_DVSEC_SAM_TABLE_SIZE         = 12'h80,
  parameter [11:0]  CCIX_DVSEC_IDM_TABLE_START_ADDR   = 12'hC00,
  parameter [11:0]  CCIX_DVSEC_IDM_TABLE_SIZE         = 12'h40,
  parameter [9:0]   CCIX_TDVSEC_OFFSET      = 10'h180 , //- Transport DVSEC offset
  parameter [16:0]  CCIX_PDVSEC_CPL_TIMEOUT = 17'd1250, // - unit of 4ns
// ----------------------------------------------
  parameter PF0_VENDOR_ID='H10EE,
  parameter PF0_SUBSYSTEM_VENDOR_ID='H10EE,
  parameter PF0_DEVICE_ID='H903F,
  parameter PF1_DEVICE_ID='H903F,
  parameter PF2_DEVICE_ID='H903F,
  parameter PF3_DEVICE_ID='H903F,
  parameter PF0_REVISION_ID='H00,
  parameter PF1_REVISION_ID='H00,
  parameter PF2_REVISION_ID='H00,
  parameter PF3_REVISION_ID='H00,
  parameter PF0_SUBSYSTEM_ID='H0007,
  parameter PF1_SUBSYSTEM_ID='H0007,
  parameter PF2_SUBSYSTEM_ID='H0007,
  parameter PF3_SUBSYSTEM_ID='H0007,

/// ----------------------------------------------
  parameter TL_LEGACY_MODE_ENABLE="FALSE",
  parameter DEDICATE_PERST="TRUE",
  parameter SYS_RESET_POLARITY=0,
  parameter DIS_GT_WIZARD="TRUE",
  parameter BMD_PIO_MODE="FALSE",
  parameter DBG_CHECKER="FALSE",
  parameter ENABLE_IBERT="FALSE",
  parameter GEN4_EIEOS_0S7="FALSE",
  parameter ENABLE_JTAG_DBG="FALSE",
  parameter ENABLE_LTSSM_DBG="FALSE",
  parameter WARM_REBOOT_SBR_FIX="FALSE",
  parameter DBG_DESCRAMBLE_EN = "TRUE",
  parameter PIPE_DEBUG_EN = "FALSE",
  parameter MSI_INT = 32,
  parameter COMPLETER_MODEL="FALSE",
  parameter SRIOV_EXD_MODE="FALSE",
  parameter THREE_PORT_SWITCH="FALSE",
  parameter TWO_PORT_SWITCH="FALSE",
  parameter TWO_PORT_CONFIG="X8G3",
  parameter silicon_revision="ES1",
  parameter DEV_PORT_TYPE= 0,
  parameter pcie_blk_locn=0,
  parameter gen_x0y0_xdc=0,
  parameter gen_x0y1_xdc=0,
  parameter gen_x0y2_xdc=0,
  parameter gen_x0y3_xdc=0,
  parameter gen_x0y4_xdc=0,
  parameter gen_x0y5_xdc=0,
  parameter gen_x0y6_xdc=0,
  parameter gen_x0y7_xdc=0,
  parameter gen_x1y0_xdc=1,
  parameter gen_x1y1_xdc=0,
  parameter gen_x1y2_xdc=0,
  parameter gen_x1y3_xdc=0,
  parameter gen_x1y4_xdc=0,
  parameter gen_x1y5_xdc=0,
  parameter xlnx_ref_board="None",
  parameter PIPE_SIM="FALSE",
  parameter EXT_PIPE_SIM="FALSE",
  parameter PCIE_FAST_CONFIG="NONE",
  parameter EXT_STARTUP_PRIMITIVE="FALSE",
  parameter PL_INTERFACE="FALSE",
  parameter PCIE_CONFIGURATION="FALSE",
  parameter CFG_STATUS_IF="TRUE",
  parameter TX_FC_IF="TRUE",
  parameter CFG_EXT_IF="TRUE",
  parameter CFG_FC_IF="TRUE",
  parameter PER_FUNC_STATUS_IF="TRUE",
  parameter CFG_MGMT_IF="TRUE",
  parameter CFG_PM_IF="TRUE",
  parameter RCV_MSG_IF="TRUE",
  parameter CFG_TX_MSG_IF="TRUE",
  parameter CFG_CTL_IF="TRUE",
  parameter PCIE_ID_IF="FALSE",
  parameter MSI_EN="TRUE",
  parameter MSIX_EN="FALSE",
  parameter PCIE4_DRP="FALSE",
  parameter TRANSCEIVER_CTRL_STATUS_PORTS="FALSE",
  parameter SHARED_LOGIC=1,
  parameter GTWIZ_IN_CORE=1,
  parameter GTCOM_IN_CORE=1,
  parameter MCAP_ENABLEMENT="NONE",
  parameter EXT_CH_GT_DRP="FALSE",
  parameter EN_GT_SELECTION="FALSE",
  parameter PLL_TYPE = 0,
  parameter EN_PARITY = "FALSE",
  parameter INS_LOSS_PROFILE = "TRUE",
  parameter MSI_X_OPTIONS="MSI-X_Ext",
  parameter SELECT_QUAD="GTY_Quad_124",
  parameter VU9P_BOARD = "FALSE",
  parameter integer PHY_LP_TXPRESET = 4,
  parameter IS_BOARD_PROJECT = 0,
  parameter integer GT_DRP_CLK_SRC = 1,
  parameter integer FREE_RUN_FREQ = 1,
  parameter PM_ENABLE_L23_ENTRY = "FALSE",
  parameter integer AWS_MODE_VALUE = 0,
  parameter GT_TYPE = "GTY",
  parameter TX_RX_MASTER_CHANNEL = "X0Y19",
  parameter X1_CH_EN = "X0Y19",
  parameter X2_CH_EN = "X0Y19",
  parameter X4_CH_EN = "X0Y19",
  parameter X8_CH_EN = "X0Y19",
  parameter XS_CH_EN = "X0Y19",
  parameter EXT_SYS_CLK_BUFG = "FALSE",
  parameter ENABLE_MORE = "FALSE",
  parameter ENABLE_AUTO_RXEQ="FALSE",
  parameter DISABLE_BRAM_PIPELINE        ="FALSE",
  parameter ENABLE_MULTIPF_AER="FALSE",
  parameter DISABLE_EQ_SYNCHRONIZER      ="FALSE",
  parameter DMA_2RP      ="FALSE",
  parameter QDMA_TPH_MSIX_BRAMS_DIS = "FALSE",
  parameter USE_STANDARD_INTERFACES="FALSE",
  parameter MASTER_GT_QUAD_INX=99,
  parameter MASTER_GT_CONTAINER=99,
  parameter SRIOV_ACTIVE_VFS=252,
  parameter EN_SLOT_CAP_REG="FALSE",
  parameter  [31:0]  SLOT_CAP_REG=32'h00000060,
  parameter ENABLE_MSIX_32VEC="FALSE",
  parameter TANDEM_RFSOC = "FALSE"
  /// ----------------------------------------------

) (

  input        pl_gen2_upstream_prefer_deemph,
  output       pl_eq_in_progress,
  output [1:0] pl_eq_phase,
  input        pl_redo_eq,
  input        pl_redo_eq_speed,
  output       pl_eq_mismatch,
  output       pl_redo_eq_pending,

  output [AXI4_DATA_WIDTH-1:0] m_axis_cq_tdata,
  input  [AXI4_DATA_WIDTH-1:0] s_axis_cc_tdata,
  input  [AXI4_DATA_WIDTH-1:0] s_axis_rq_tdata,
  output [AXI4_DATA_WIDTH-1:0] m_axis_rc_tdata,
  output [AXI4_CQ_TUSER_WIDTH-1:0] m_axis_cq_tuser,
  input  [AXI4_CC_TUSER_WIDTH-1:0] s_axis_cc_tuser,
  output           m_axis_cq_tlast,
  input            s_axis_rq_tlast,
  output           m_axis_rc_tlast,
  input            s_axis_cc_tlast,
  input  [1:0]     pcie_cq_np_req,
  output [5:0]     pcie_cq_np_req_count,
  input  [AXI4_RQ_TUSER_WIDTH-1:0] s_axis_rq_tuser,
  output [AXI4_RC_TUSER_WIDTH-1:0] m_axis_rc_tuser,
  output [AXI4_TKEEP_WIDTH-1:0] m_axis_cq_tkeep,
  input  [AXI4_TKEEP_WIDTH-1:0] s_axis_cc_tkeep,
  input  [AXI4_TKEEP_WIDTH-1:0] s_axis_rq_tkeep,
  output [AXI4_TKEEP_WIDTH-1:0] m_axis_rc_tkeep,
  output           m_axis_cq_tvalid,
  input            s_axis_cc_tvalid,
  input            s_axis_rq_tvalid,
  output           m_axis_rc_tvalid,
  input            m_axis_cq_tready,
  output [AXI4_CC_TREADY_WIDTH-1:0] s_axis_cc_tready,
  output [AXI4_RQ_TREADY_WIDTH-1:0] s_axis_rq_tready,
  input            m_axis_rc_tready,

  output [5:0]     pcie_rq_seq_num0,
  output           pcie_rq_seq_num_vld0,
  output [5:0]     pcie_rq_seq_num1,
  output           pcie_rq_seq_num_vld1,
  output [7:0]     pcie_rq_tag0,
  output           pcie_rq_tag_vld0,
  output [7:0]     pcie_rq_tag1,
  output           pcie_rq_tag_vld1,
  output [3:0]     pcie_tfc_nph_av,
  output [3:0]     pcie_tfc_npd_av,
  output [3:0]     pcie_rq_tag_av,
  input  [9:0]     cfg_mgmt_addr,
  input  [7:0]     cfg_mgmt_function_number,
  input            cfg_mgmt_write,
  input  [31:0]    cfg_mgmt_write_data,
  input  [3:0]     cfg_mgmt_byte_enable,
  input            cfg_mgmt_read,
  output [31:0]    cfg_mgmt_read_data,
  output           cfg_mgmt_read_write_done,
  input            cfg_mgmt_debug_access,
  output           cfg_phy_link_down,
  output [1:0]     cfg_phy_link_status,
  output [2:0]     cfg_negotiated_width,
  output [1:0]     cfg_current_speed,
  output [1:0]     cfg_max_payload,
  output [2:0]     cfg_max_read_req,
  output [15:0]    cfg_function_status,
  output [11:0]    cfg_function_power_state,
  output [1:0]     cfg_link_power_state,
  output           cfg_err_cor_out,
  output           cfg_err_nonfatal_out,
  output           cfg_err_fatal_out,
  output           cfg_local_error_valid,
  output [4:0]     cfg_local_error_out,
  output [5:0]     cfg_ltssm_state,
  output [1:0]     cfg_rx_pm_state,
  output [1:0]     cfg_tx_pm_state,
  output [3:0]     cfg_rcb_status,
  output [1:0]     cfg_obff_enable,
  output           cfg_pl_status_change,
  output [3:0]     cfg_tph_requester_enable,
  output [11:0]    cfg_tph_st_mode,
  output           cfg_msg_received,
  output [7:0]     cfg_msg_received_data,
  output [4:0]     cfg_msg_received_type,
  input            cfg_msg_transmit,
  input  [2:0]     cfg_msg_transmit_type,
  input  [31:0]    cfg_msg_transmit_data,
  output           cfg_msg_transmit_done,
  output [7:0]     cfg_fc_ph,
  output [11:0]    cfg_fc_pd,
  output [7:0]     cfg_fc_nph,
  output [11:0]    cfg_fc_npd,
  output [7:0]     cfg_fc_cplh,
  output [11:0]    cfg_fc_cpld,
  input  [2:0]     cfg_fc_sel,
  input            cfg_fc_vc_sel,
  input            cfg_hot_reset_in,
  output           cfg_hot_reset_out,
  input            cfg_config_space_enable,
  input  [63:0]    cfg_dsn,
  input  [15:0]    cfg_dev_id_pf0,
  input  [15:0]    cfg_dev_id_pf1,
  input  [15:0]    cfg_dev_id_pf2,
  input  [15:0]    cfg_dev_id_pf3,
  input  [15:0]    cfg_vend_id,
  input  [7:0]     cfg_rev_id_pf0,
  input  [7:0]     cfg_rev_id_pf1,
  input  [7:0]     cfg_rev_id_pf2,
  input  [7:0]     cfg_rev_id_pf3,
  input  [15:0]    cfg_subsys_id_pf0,
  input  [15:0]    cfg_subsys_id_pf1,
  input  [15:0]    cfg_subsys_id_pf2,
  input  [15:0]    cfg_subsys_id_pf3,
  input  [15:0]    cfg_subsys_vend_id,
  input  [7:0]     cfg_ds_port_number,
  input  [7:0]     cfg_ds_bus_number,
  input  [4:0]     cfg_ds_device_number,
  input  [2:0]     cfg_ds_function_number,
  output [7:0]     cfg_bus_number,
  input            cfg_power_state_change_ack,
  output           cfg_power_state_change_interrupt,
  input            cfg_err_cor_in,
  input            cfg_err_uncor_in,
  input  [3:0]     cfg_flr_done,
  output [3:0]     cfg_flr_in_process,
  input            cfg_req_pm_transition_l23_ready,
  input            cfg_link_training_enable,
  input  [3:0]     cfg_interrupt_int,
  output           cfg_interrupt_sent,
  input  [3:0]     cfg_interrupt_pending,
  output [3:0]     cfg_interrupt_msi_enable,
  input  [MSI_INT-1:0]    cfg_interrupt_msi_int,
  output           cfg_interrupt_msi_sent,
  output           cfg_interrupt_msi_fail,
  output [11:0]    cfg_interrupt_msi_mmenable,
  input  [31:0]    cfg_interrupt_msi_pending_status,
  input  [1:0]     cfg_interrupt_msi_pending_status_function_num,
  input            cfg_interrupt_msi_pending_status_data_enable,
  output           cfg_interrupt_msi_mask_update,
  input  [1:0]     cfg_interrupt_msi_select,
  output [31:0]    cfg_interrupt_msi_data,
  output [3:0]     cfg_interrupt_msix_enable,
  output [3:0]     cfg_interrupt_msix_mask,
  input  [63:0]    cfg_interrupt_msix_address,
  input  [31:0]    cfg_interrupt_msix_data,
  input            cfg_interrupt_msix_int,
  input  [1:0]     cfg_interrupt_msix_vec_pending,
  output           cfg_interrupt_msix_vec_pending_status,
  input  [2:0]     cfg_interrupt_msi_attr,
  input            cfg_interrupt_msi_tph_present,
  input  [1:0]     cfg_interrupt_msi_tph_type,
  input  [7:0]     cfg_interrupt_msi_tph_st_tag,
  input  [7:0]     cfg_interrupt_msi_function_number,
  output           cfg_ext_read_received,
  output           cfg_ext_write_received,
  output [9:0]     cfg_ext_register_number,
  output [7:0]     cfg_ext_function_number,
  output [31:0]    cfg_ext_write_data,
  output [3:0]     cfg_ext_write_byte_enable,
  input  [31:0]    cfg_ext_read_data,
  input            cfg_ext_read_data_valid,
  output [5:0]     rbar_bar_size,
  output [7:0]     rbar_function_number,
  output           rbar_write_enable_bar0,
  output           rbar_write_enable_bar1,
  output           rbar_write_enable_bar2,
  output           rbar_write_enable_bar3,
  output           rbar_write_enable_bar4,
  output           rbar_write_enable_bar5,
  output [251:0]   cfg_vf_flr_in_process,
  input  [7:0]     cfg_vf_flr_func_num,
  input            cfg_vf_flr_done,
  output [503:0]   cfg_vf_status,
  output [755:0]   cfg_vf_power_state,
  output [251:0]   cfg_vf_tph_requester_enable,
  output [755:0]   cfg_vf_tph_st_mode,
  output [251:0]   cfg_interrupt_msix_vf_enable,
  output [251:0]   cfg_interrupt_msix_vf_mask,
  output [2*4-1:0] cfg_pri_control,             // 2 bits per PF
  output [4-1:0]   cfg_ats_control_enable,      // 1 bit (E) per PF
  output [251:0]   cfg_vf_ats_control_enable,   // 1 bit (E) per VF
  output [3*4-1:0] cfg_pasid_control,           // 3 bits per PF
  output [5*4-1:0] cfg_max_pasid_width_control, // 5 bits per PF
  input            cfg_pm_aspm_l1_entry_reject,
  input            cfg_pm_aspm_tx_l0s_entry_disable,
  input  [1:0]     conf_req_type,
  input  [3:0]     conf_req_reg_num,
  input  [31:0]    conf_req_data,
  input            conf_req_valid,
  output           conf_req_ready,
  output [31:0]    conf_resp_rdata,
  output           conf_resp_valid,
  output           cap_req,
  input            cap_gnt,
  input            cap_rel,
  output           mcap_design_switch,
  output           user_clk,
  output           core_clk,
  output           mcap_clk,
  output           gt_drp_clk,
(* keep = "true" *)  output reg       user_reset,
(* keep = "true" *)  output reg       user_lnk_up,
  input            sys_clk,
  output           sys_clk_ce_out,
  input            sys_clk_gt,
  input            sys_reset,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]     pci_exp_rxp,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]     pci_exp_rxn,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]     pci_exp_txp,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]     pci_exp_txn,

  // CXS interface,
  input                                                                cxs0_active_req_tx,
  output                                                               cxs0_active_ack_tx,
  output                                                               cxs0_deact_hint_tx,
  input                                                                cxs0_valid_tx,
  output                                                               cxs0_crdgnt_tx,
  input                                                                cxs0_crdrtn_tx,
  input  [AXIS_CCIX_TX_TUSER_WIDTH-(AXIS_CCIX_TX_TDATA_WIDTH/8)-2:0]   cxs0_cntl_tx,
  input  [AXIS_CCIX_TX_TDATA_WIDTH-1:0]                                cxs0_data_tx,
  input                                                                cxs0_valid_chk_tx,
  output                                                               cxs0_crdgnt_chk_tx,
  input                                                                cxs0_crdrtn_chk_tx,
  input                                                                cxs0_cntl_chk_tx,
  input  [AXIS_CCIX_TX_TDATA_WIDTH/8-1:0]                              cxs0_data_chk_tx,
  output                                                               cxs0_active_req_rx,
  input                                                                cxs0_active_ack_rx,
  input                                                                cxs0_deact_hint_rx,
  output                                                               cxs0_valid_rx,
  input                                                                cxs0_crdgnt_rx,
  output                                                               cxs0_crdrtn_rx,
  output [AXIS_CCIX_RX_TUSER_WIDTH-(AXIS_CCIX_RX_TDATA_WIDTH/8)-2:0]   cxs0_cntl_rx,
  output [AXIS_CCIX_RX_TDATA_WIDTH-1:0]                                cxs0_data_rx,
  output                                                               cxs0_valid_chk_rx,
  input                                                                cxs0_crdgnt_chk_rx,
  output                                                               cxs0_crdrtn_chk_rx,
  output                                                               cxs0_cntl_chk_rx,
  output [AXIS_CCIX_RX_TDATA_WIDTH/8-1:0]                              cxs0_data_chk_rx,
  output [7:0]    ccix_rx_credit_av,
  output          cfg_vc1_enable,
  output          cfg_vc1_negotiation_pending,
  output          ccix_optimized_tlp_tx_and_rx_enable,
  input           ccix_optimized_tlp_tx_and_rx_enable_rp,

  //- Interrupt line to processor,
  output  rd_interrupt,
  output  wr_interrupt,

  input   s_aclk,
  input   s_aresetn,

  input   [13:0]  s_axi_araddr,
  input   [1:0]   s_axi_arburst,
  input   [3:0]   s_axi_arcache,
  input   [15:0]  s_axi_arid,
  input   [7:0]   s_axi_arlen,
  input   [0:0]   s_axi_arlock,
  input   [2:0]   s_axi_arprot,
  input   [3:0]   s_axi_arqos,
  output          s_axi_arready,
  input   [2:0]   s_axi_arsize,
  input   [15:0]  s_axi_aruser,
  input           s_axi_arvalid,
  input   [13:0]  s_axi_awaddr,
  input   [1:0]   s_axi_awburst,
  input   [3:0]   s_axi_awcache,
  input   [15:0]  s_axi_awid,
  input   [7:0]   s_axi_awlen,
  input   [0:0]   s_axi_awlock,
  input   [2:0]   s_axi_awprot,
  input   [3:0]   s_axi_awqos,
  output          s_axi_awready,
  input   [2:0]   s_axi_awsize,
  input   [15:0]  s_axi_awuser,
  input           s_axi_awvalid,
  output   [15:0] s_axi_bid,
  input           s_axi_bready,
  output   [1:0]  s_axi_bresp,
  output          s_axi_bvalid,
  output   [31:0] s_axi_rdata,
  output   [15:0] s_axi_rid,
  output          s_axi_rlast,
  input           s_axi_rready,
  output   [1:0]  s_axi_rresp,
  output          s_axi_rvalid,
  input   [31:0]  s_axi_wdata,
  input           s_axi_wlast,
  output          s_axi_wready,
  input   [3:0]   s_axi_wstrb,
  input           s_axi_wvalid,

  //--------------------------------------------------------------------------
  // GT Channel DRP Port
  //--------------------------------------------------------------------------
  output                                           ext_ch_gt_drpclk,
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH * 10)-1):0] ext_ch_gt_drpaddr,
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH *  1)-1):0] ext_ch_gt_drpen,
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH *  1)-1):0] ext_ch_gt_drpwe,
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH * 16)-1):0] ext_ch_gt_drpdi,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH *  1)-1):0] ext_ch_gt_drprdy,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH * 16)-1):0] ext_ch_gt_drpdo,
  //--------------------------------------------------------------------------
  // PCIe DRP Port
  //--------------------------------------------------------------------------
  output         drp_rdy,
  output  [15:0] drp_do,
  input          drp_clk,
  input          drp_en,
  input          drp_we,
  input    [9:0] drp_addr,
  input   [15:0] drp_di,
 //--------------------------------------------------------------------------
 //  Transceiver Debug And Status Ports,
 //--------------------------------------------------------------------------
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_pcieuserratedone,
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH*3)-1):0] gt_loopback,
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_txprbsforceerr,
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_txinhibit,
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH*4)-1):0] gt_txprbssel,
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH*4)-1):0] gt_rxprbssel,
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_rxprbscntreset,

  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_txelecidle,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_txresetdone,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_rxresetdone,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_rxpmaresetdone,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_txphaligndone,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_txphinitdone,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_txdlysresetdone,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_rxphaligndone,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_rxdlysresetdone,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_rxsyncdone,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_eyescandataerror,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_rxprbserr,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*16)-1):0] gt_dmonitorout,
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_dmonfiforeset,
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_dmonitorclk,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_rxcommadet,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_phystatus,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_rxvalid,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_rxcdrlock,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_pcierateidle,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_pcieuserratestart,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_gtpowergood,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_cplllock,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_rxoutclk,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_rxrecclkout,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] gt_qpll0lock,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] gt_qpll1lock,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*3)-1):0] gt_rxstatus,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*3)-1):0] gt_rxbufstatus,
  output [8:0]                                  gt_bufgtdiv,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*2)-1):0] phy_txeq_ctrl,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*4)-1):0] phy_txeq_preset,
  output [3:0]                                  phy_rst_fsm,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*3)-1):0] phy_txeq_fsm,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*3)-1):0] phy_rxeq_fsm,
  output                                        phy_rst_idle,
  output                                        phy_rrst_n,
  output                                        phy_prst_n,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       gt_gen34_eios_det,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       gt_txoutclk,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       gt_txoutclkfabric,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       gt_rxoutclkfabric,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       gt_txoutclkpcs,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       gt_rxoutclkpcs,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       gt_txpmareset,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       gt_rxpmareset,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       gt_txpcsreset,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       gt_rxpcsreset,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       gt_rxbufreset,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       gt_rxcdrreset,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       gt_rxdfelpmreset,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       gt_txprogdivresetdone,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       gt_txpmaresetdone,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       gt_txsyncdone,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       gt_rxprbslocked,
  input                                         free_run_clock,
  //--------------------------------------------------------------------------
  // PIPE INTERFACE
  //--------------------------------------------------------------------------
  input  [25:0]  common_commands_in,
  input  [83:0]  pipe_rx_0_sigs,
  input  [83:0]  pipe_rx_1_sigs,
  input  [83:0]  pipe_rx_2_sigs,
  input  [83:0]  pipe_rx_3_sigs,
  input  [83:0]  pipe_rx_4_sigs,
  input  [83:0]  pipe_rx_5_sigs,
  input  [83:0]  pipe_rx_6_sigs,
  input  [83:0]  pipe_rx_7_sigs,
  input  [83:0]  pipe_rx_8_sigs,
  input  [83:0]  pipe_rx_9_sigs,
  input  [83:0]  pipe_rx_10_sigs,
  input  [83:0]  pipe_rx_11_sigs,
  input  [83:0]  pipe_rx_12_sigs,
  input  [83:0]  pipe_rx_13_sigs,
  input  [83:0]  pipe_rx_14_sigs,
  input  [83:0]  pipe_rx_15_sigs,

  output [25:0]  common_commands_out,
  output [83:0]  pipe_tx_0_sigs,
  output [83:0]  pipe_tx_1_sigs,
  output [83:0]  pipe_tx_2_sigs,
  output [83:0]  pipe_tx_3_sigs,
  output [83:0]  pipe_tx_4_sigs,
  output [83:0]  pipe_tx_5_sigs,
  output [83:0]  pipe_tx_6_sigs,
  output [83:0]  pipe_tx_7_sigs,
  output [83:0]  pipe_tx_8_sigs,
  output [83:0]  pipe_tx_9_sigs,
  output [83:0]  pipe_tx_10_sigs,
  output [83:0]  pipe_tx_11_sigs,
  output [83:0]  pipe_tx_12_sigs,
  output [83:0]  pipe_tx_13_sigs,
  output [83:0]  pipe_tx_14_sigs,
  output [83:0]  pipe_tx_15_sigs,

  //---------- Internal GT COMMON Ports ----------------------
  output [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] int_qpll0lock_out,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] int_qpll0outrefclk_out,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] int_qpll0outclk_out,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] int_qpll1lock_out,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] int_qpll1outrefclk_out,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] int_qpll1outclk_out,

  //---------- External GT COMMON Ports ----------------------
  output [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_qpllxrefclk,
  output [((((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2)+1)*3)-1:0] ext_qpllxrate,
  output                                                   ext_qpllxrcalenb,

  output [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_qpll0pd,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_qpll0reset,
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_qpll0lock_out,
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_qpll0outclk_out,
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_qpll0outrefclk_out,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_qpll1pd,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_qpll1reset,
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_qpll1lock_out,
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_qpll1outclk_out,
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_qpll1outrefclk_out,

  //--------------------------------------------------------------------------
  //  GT WIZARD IP is not in the PCIe core
  //--------------------------------------------------------------------------
  output [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2:0] gtrefclk01_in,
  output [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2:0] gtrefclk00_in,
  
  output [((((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2)+1)*3)-1:0] pcierateqpll0_in,
  output [((((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2)+1)*3)-1:0] pcierateqpll1_in,
  
  output [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2 : 0]  qpll0pd_in,
  output [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2 : 0]  qpll0reset_in,
  output [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2 : 0]  qpll1pd_in,
  output [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2 : 0]  qpll1reset_in,
  input  [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2:0]    qpll0lock_out,
  input  [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2:0]    qpll0outclk_out,
  input  [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2:0]    qpll0outrefclk_out,
  input  [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2:0]    qpll1lock_out,
  input  [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2:0]    qpll1outclk_out,
  input  [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2:0]    qpll1outrefclk_out,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         qpll0freqlock_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         qpll1freqlock_in,
  input  [(PL_LINK_CAP_MAX_LINK_WIDTH*2)-1:0]     pcierateqpllpd_out,
  input  [(PL_LINK_CAP_MAX_LINK_WIDTH*2)-1:0]     pcierateqpllreset_out,

  output [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2 : 0]  rcalenb_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txpisopd_in,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         bufgtce_out,
  input  [(PL_LINK_CAP_MAX_LINK_WIDTH* 3)-1:0]    bufgtcemask_out,
  input  [(PL_LINK_CAP_MAX_LINK_WIDTH* 9)-1:0]    bufgtdiv_out,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         bufgtreset_out,
  input  [(PL_LINK_CAP_MAX_LINK_WIDTH* 3)-1:0]    bufgtrstmask_out,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         cpllfreqlock_in,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         cplllock_out,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         cpllpd_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         cpllreset_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         dmonfiforeset_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         dmonitorclk_in,
  input  [(PL_LINK_CAP_MAX_LINK_WIDTH*16)-1:0]    dmonitorout_out,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         eyescanreset_in,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         gtpowergood_out,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         gtrefclk0_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         gtrxreset_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         gttxreset_in,
  
  output gtwiz_reset_rx_done_in,
  output gtwiz_reset_tx_done_in,
  output gtwiz_userclk_rx_active_in,
  output gtwiz_userclk_tx_active_in,

  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 3)-1:0]    loopback_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         pcieeqrxeqadaptdone_in,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         pcierategen3_out,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         pcierateidle_out,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         pcierstidle_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         pciersttxsyncstart_in,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         pciesynctxsyncdone_out,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         pcieusergen3rdy_out,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         pcieuserphystatusrst_out,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         pcieuserratedone_in,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         pcieuserratestart_out,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         phystatus_out,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         resetovrd_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rx8b10ben_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxbufreset_in,
  input  [(PL_LINK_CAP_MAX_LINK_WIDTH*3)-1:0]     rxbufstatus_out,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxbyteisaligned_out,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxbyterealign_out,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxcdrfreqreset_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxcdrhold_in,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxcdrlock_out,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxcdrreset_in,
  input  [(PL_LINK_CAP_MAX_LINK_WIDTH * 2)-1 : 0] rxclkcorcnt_out,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxcommadet_out,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxcommadeten_in,
  input  [(PL_LINK_CAP_MAX_LINK_WIDTH*16)-1:0]    rxctrl0_out,
  input  [(PL_LINK_CAP_MAX_LINK_WIDTH*16)-1:0]    rxctrl1_out,
  input  [(PL_LINK_CAP_MAX_LINK_WIDTH*8)-1:0]     rxctrl2_out,
  input  [(PL_LINK_CAP_MAX_LINK_WIDTH*8)-1:0]     rxctrl3_out,
  input  [(PL_LINK_CAP_MAX_LINK_WIDTH*128)-1:0]   rxdata_out,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfeagchold_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfecfokhold_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfekhhold_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfelfhold_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxdfelpmreset_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfetap10hold_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfetap11hold_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfetap12hold_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfetap13hold_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfetap14hold_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfetap15hold_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfetap2hold_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfetap3hold_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfetap4hold_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfetap5hold_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfetap6hold_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfetap7hold_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfetap8hold_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfetap9hold_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfeuthold_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfevphold_in,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxdlysresetdone_out,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxelecidle_out,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxlpmen_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxlpmgchold_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxlpmhfhold_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxlpmlfhold_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxlpmoshold_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxmcommaalignen_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxoshold_in,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxoutclk_out,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxoutclkfabric_out,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxoutclkpcs_out,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxpcommaalignen_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxpcsreset_in,
  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 2)-1:0]    rxpd_in,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxphaligndone_out,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxpmareset_in,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxpmaresetdone_out,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxpolarity_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxprbscntreset_in,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxprbserr_out,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxprbslocked_out,
  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 4)-1:0]    rxprbssel_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxprogdivreset_in,
  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 3)-1:0]    rxrate_in,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxratedone_out,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxrecclkout_out,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxresetdone_out,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxslide_in,
  input  [(PL_LINK_CAP_MAX_LINK_WIDTH* 3)-1:0]    rxstatus_out,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxsyncdone_out,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxtermination_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxuserrdy_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxusrclk2_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxusrclk_in,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxvalid_out,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       tx8b10ben_in,
  output [(PL_LINK_CAP_MAX_LINK_WIDTH*16)-1:0]  txctrl0_in,
  output [(PL_LINK_CAP_MAX_LINK_WIDTH*16)-1:0]  txctrl1_in,
  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 8)-1:0]  txctrl2_in,
  output [(PL_LINK_CAP_MAX_LINK_WIDTH*128)-1:0] txdata_in,
  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 2)-1:0]  txdeemph_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txdetectrx_in,
  output [(PL_LINK_CAP_MAX_LINK_WIDTH*5)-1:0]   txdiffctrl_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txdlybypass_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txdlyen_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txdlyhold_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txdlyovrden_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txdlysreset_in,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txdlysresetdone_out,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txdlyupdown_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txelecidle_in,
  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 7)-1:0]  txmaincursor_in,
  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 3)-1:0]  txmargin_in,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txoutclk_out,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txoutclkfabric_out,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txoutclkpcs_out,
  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 3)-1:0]  txoutclksel_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txpcsreset_in,
  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 2)-1:0]  txpd_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txphalign_in,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txphaligndone_out,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txphalignen_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txphdlypd_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txphdlyreset_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txphdlytstclk_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txphinit_in,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txphinitdone_out,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txphovrden_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       rxratemode_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txpmareset_in,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]     txpmaresetdone_out,
  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 5)-1:0]  txpostcursor_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txprbsforceerr_in,
  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 4)-1:0]  txprbssel_in,
  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 5)-1:0]  txprecursor_in,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txprgdivresetdone_out,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txprogdivreset_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txpdelecidlemode_in,
  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 3)-1:0]  txrate_in,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txresetdone_out,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txswing_in,
  output [(PL_LINK_CAP_MAX_LINK_WIDTH-1) : 0]   txsyncallin_in,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]     txsyncdone_out,
  output [(PL_LINK_CAP_MAX_LINK_WIDTH-1) : 0]   txsyncin_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txsyncmode_in,
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txsyncout_out,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txuserrdy_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txusrclk2_in,
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txusrclk_in,
  
  output                                           drpclk_in,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH * 10)-1):0] drpaddr_in,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH *  1)-1):0] drpen_in,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH *  1)-1):0] drprst_in,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH *  1)-1):0] drpwe_in,
  output [((PL_LINK_CAP_MAX_LINK_WIDTH * 16)-1):0] drpdi_in,
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH *  1)-1):0] drprdy_out,
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH * 16)-1):0] drpdo_out,
  input        ext_phy_clk_pclk2_gt,
  input        ext_phy_clk_int_clock,
  input        ext_phy_clk_pclk,
  input        ext_phy_clk_phy_pclk2,
  input        ext_phy_clk_phy_coreclk,
  input        ext_phy_clk_phy_userclk,
  input        ext_phy_clk_phy_mcapclk,

  output       ext_phy_clk_bufg_gt_ce,
  output       ext_phy_clk_bufg_gt_reset,
  output       ext_phy_clk_rst_idle,
  output       ext_phy_clk_txoutclk,
  output       ext_phy_clk_bufgtcemask,
  output       ext_phy_clk_gt_bufgtrstmask,
  output [8:0] ext_phy_clk_bufgtdiv,
  output  phy_rdy_out,
  output  ats_pri_en,
 //--------------------------------------------------------------------------
 //  
 //--------------------------------------------------------------------------
  // These inputs and outputs may be use when the startup block is generated internal to the PCI Express Core.
  output wire         startup_cfgclk,     // 1-bit output: Configuration main clock output
  output wire         startup_cfgmclk,    // 1-bit output: Configuration internal oscillator clock output
  output wire   [3:0] startup_di,
  output wire         startup_eos,        // 1-bit output: Active high output signal indicating the End Of Startup
  output wire         startup_preq,       // 1-bit output: PROGRAM request to fabric output
  input  wire   [3:0] startup_do,
  input  wire   [3:0] startup_dts,
  input  wire         startup_fcsbo,
  input  wire         startup_fcsbts,
  input  wire         startup_gsr,        // 1-bit input: Global Set/Reset input (GSR cannot be used for the port name)
  input  wire         startup_gts,        // 1-bit input: Global 3-state input (GTS cannot be used for the port name)
  input  wire         startup_keyclearb,  // 1-bit input: Clear AES Decrypter Key input from Battery-Backed RAM (BBRAM)
  input  wire         startup_pack,       // 1-bit input: PROGRAM acknowledge input
  input  wire         startup_usrcclko,   // 1-bit input: User CCLK input
  input  wire         startup_usrcclkts,  // 1-bit input: User CCLK 3-state enable input
  input  wire         startup_usrdoneo,   // 1-bit input: User DONE pin output control
  input  wire         startup_usrdonets,  // 1-bit input: User DONE 3-state enable output
  //--------------------------------------------------------------------------
  //  PIPE DEBUG MODULE in the PCIe core
  //--------------------------------------------------------------------------
  input   [31:0]	  pipe_debug_ctl_in_tx0,
  input	  [31:0]	  pipe_debug_ctl_in_tx1,
  input	  [31:0]	  pipe_debug_ctl_in_rx0,
  input   [31:0]	  pipe_debug_ctl_in_rx1,
  input					    pipe_debug_ltssm_rec_spd_1,
  input					    pipe_debug_ltssm_pol_act,
  input   [3:0] 	  pipe_debug_ctl_vec4,
  input   [31:0] 	  pipe_debug_mux_ctl,
  output  [127:0]	  pipe_debug_debug_out_128_0,
  output  [15:0]	  pipe_debug_debug_out_ext_16_0,
  output  [127:0]	  pipe_debug_debug_out_128_1,
  output  [15:0]	  pipe_debug_debug_out_ext_16_1,
  output  [127:0]	  pipe_debug_debug_out_128_2,
  output  [15:0]	  pipe_debug_debug_out_ext_16_2,
  output  [127:0]	  pipe_debug_debug_out_128_3,
  output  [15:0]	  pipe_debug_debug_out_ext_16_3,
  output  [7:0] 	  pipe_debug_inject_tx_status,
  output  [7:0] 	  pipe_debug_inject_rx_status

);

  localparam EXT_PIPESIM =
  // synthesis translate_off
  (PIPE_SIM == "TRUE") ? "TRUE" : 
  // synthesis translate_on
  "FALSE";

   wire           mcap_rst_b;
   wire           pcie_perst0_b;
   wire           pcie_perst1_b;
   wire           mgmt_reset_n;
   wire           phy_rdy ;
   wire           phy_rdy_phystatus;
   wire [1:0]     pipe_rx00_char_is_k;
   wire [1:0]     pipe_rx01_char_is_k;
   wire [1:0]     pipe_rx02_char_is_k;
   wire [1:0]     pipe_rx03_char_is_k;
   wire [1:0]     pipe_rx04_char_is_k;
   wire [1:0]     pipe_rx05_char_is_k;
   wire [1:0]     pipe_rx06_char_is_k;
   wire [1:0]     pipe_rx07_char_is_k;
   wire [1:0]     pipe_rx08_char_is_k;
   wire [1:0]     pipe_rx09_char_is_k;
   wire [1:0]     pipe_rx10_char_is_k;
   wire [1:0]     pipe_rx11_char_is_k;
   wire [1:0]     pipe_rx12_char_is_k;
   wire [1:0]     pipe_rx13_char_is_k;
   wire [1:0]     pipe_rx14_char_is_k;
   wire [1:0]     pipe_rx15_char_is_k;
   wire           pipe_rx00_valid;
   wire           pipe_rx01_valid;
   wire           pipe_rx02_valid;
   wire           pipe_rx03_valid;
   wire           pipe_rx04_valid;
   wire           pipe_rx05_valid;
   wire           pipe_rx06_valid;
   wire           pipe_rx07_valid;
   wire           pipe_rx08_valid;
   wire           pipe_rx09_valid;
   wire           pipe_rx10_valid;
   wire           pipe_rx11_valid;
   wire           pipe_rx12_valid;
   wire           pipe_rx13_valid;
   wire           pipe_rx14_valid;
   wire           pipe_rx15_valid;
   wire [63:0]    pipe_rx00_data;
   wire [63:0]    pipe_rx01_data;
   wire [63:0]    pipe_rx02_data;
   wire [63:0]    pipe_rx03_data;
   wire [63:0]    pipe_rx04_data;
   wire [63:0]    pipe_rx05_data;
   wire [63:0]    pipe_rx06_data;
   wire [63:0]    pipe_rx07_data;
   wire [63:0]    pipe_rx08_data;
   wire [63:0]    pipe_rx09_data;
   wire [63:0]    pipe_rx10_data;
   wire [63:0]    pipe_rx11_data;
   wire [63:0]    pipe_rx12_data;
   wire [63:0]    pipe_rx13_data;
   wire [63:0]    pipe_rx14_data;
   wire [63:0]    pipe_rx15_data;
   wire           pipe_rx00_polarity;
   wire           pipe_rx01_polarity;
   wire           pipe_rx02_polarity;
   wire           pipe_rx03_polarity;
   wire           pipe_rx04_polarity;
   wire           pipe_rx05_polarity;
   wire           pipe_rx06_polarity;
   wire           pipe_rx07_polarity;
   wire           pipe_rx08_polarity;
   wire           pipe_rx09_polarity;
   wire           pipe_rx10_polarity;
   wire           pipe_rx11_polarity;
   wire           pipe_rx12_polarity;
   wire           pipe_rx13_polarity;
   wire           pipe_rx14_polarity;
   wire           pipe_rx15_polarity;
   wire [2:0]     pipe_rx00_status;
   wire [2:0]     pipe_rx01_status;
   wire [2:0]     pipe_rx02_status;
   wire [2:0]     pipe_rx03_status;
   wire [2:0]     pipe_rx04_status;
   wire [2:0]     pipe_rx05_status;
   wire [2:0]     pipe_rx06_status;
   wire [2:0]     pipe_rx07_status;
   wire [2:0]     pipe_rx08_status;
   wire [2:0]     pipe_rx09_status;
   wire [2:0]     pipe_rx10_status;
   wire [2:0]     pipe_rx11_status;
   wire [2:0]     pipe_rx12_status;
   wire [2:0]     pipe_rx13_status;
   wire [2:0]     pipe_rx14_status;
   wire [2:0]     pipe_rx15_status;
   wire           pipe_rx00_phy_status;
   wire           pipe_rx01_phy_status;
   wire           pipe_rx02_phy_status;
   wire           pipe_rx03_phy_status;
   wire           pipe_rx04_phy_status;
   wire           pipe_rx05_phy_status;
   wire           pipe_rx06_phy_status;
   wire           pipe_rx07_phy_status;
   wire           pipe_rx08_phy_status;
   wire           pipe_rx09_phy_status;
   wire           pipe_rx10_phy_status;
   wire           pipe_rx11_phy_status;
   wire           pipe_rx12_phy_status;
   wire           pipe_rx13_phy_status;
   wire           pipe_rx14_phy_status;
   wire           pipe_rx15_phy_status;
   wire           pipe_rx00_elec_idle;
   wire           pipe_rx01_elec_idle;
   wire           pipe_rx02_elec_idle;
   wire           pipe_rx03_elec_idle;
   wire           pipe_rx04_elec_idle;
   wire           pipe_rx05_elec_idle;
   wire           pipe_rx06_elec_idle;
   wire           pipe_rx07_elec_idle;
   wire           pipe_rx08_elec_idle;
   wire           pipe_rx09_elec_idle;
   wire           pipe_rx10_elec_idle;
   wire           pipe_rx11_elec_idle;
   wire           pipe_rx12_elec_idle;
   wire           pipe_rx13_elec_idle;
   wire           pipe_rx14_elec_idle;
   wire           pipe_rx15_elec_idle;
   wire           pipe_rx00_data_valid;
   wire           pipe_rx01_data_valid;
   wire           pipe_rx02_data_valid;
   wire           pipe_rx03_data_valid;
   wire           pipe_rx04_data_valid;
   wire           pipe_rx05_data_valid;
   wire           pipe_rx06_data_valid;
   wire           pipe_rx07_data_valid;
   wire           pipe_rx08_data_valid;
   wire           pipe_rx09_data_valid;
   wire           pipe_rx10_data_valid;
   wire           pipe_rx11_data_valid;
   wire           pipe_rx12_data_valid;
   wire           pipe_rx13_data_valid;
   wire           pipe_rx14_data_valid;
   wire           pipe_rx15_data_valid;
   wire [1:0]     pipe_rx00_start_block;
   wire [1:0]     pipe_rx01_start_block;
   wire [1:0]     pipe_rx02_start_block;
   wire [1:0]     pipe_rx03_start_block;
   wire [1:0]     pipe_rx04_start_block;
   wire [1:0]     pipe_rx05_start_block;
   wire [1:0]     pipe_rx06_start_block;
   wire [1:0]     pipe_rx07_start_block;
   wire [1:0]     pipe_rx08_start_block;
   wire [1:0]     pipe_rx09_start_block;
   wire [1:0]     pipe_rx10_start_block;
   wire [1:0]     pipe_rx11_start_block;
   wire [1:0]     pipe_rx12_start_block;
   wire [1:0]     pipe_rx13_start_block;
   wire [1:0]     pipe_rx14_start_block;
   wire [1:0]     pipe_rx15_start_block;
   wire [1:0]     pipe_rx00_sync_header;
   wire [1:0]     pipe_rx01_sync_header;
   wire [1:0]     pipe_rx02_sync_header;
   wire [1:0]     pipe_rx03_sync_header;
   wire [1:0]     pipe_rx04_sync_header;
   wire [1:0]     pipe_rx05_sync_header;
   wire [1:0]     pipe_rx06_sync_header;
   wire [1:0]     pipe_rx07_sync_header;
   wire [1:0]     pipe_rx08_sync_header;
   wire [1:0]     pipe_rx09_sync_header;
   wire [1:0]     pipe_rx10_sync_header;
   wire [1:0]     pipe_rx11_sync_header;
   wire [1:0]     pipe_rx12_sync_header;
   wire [1:0]     pipe_rx13_sync_header;
   wire [1:0]     pipe_rx14_sync_header;
   wire [1:0]     pipe_rx15_sync_header;
   wire           pipe_tx00_compliance;
   wire           pipe_tx01_compliance;
   wire           pipe_tx02_compliance;
   wire           pipe_tx03_compliance;
   wire           pipe_tx04_compliance;
   wire           pipe_tx05_compliance;
   wire           pipe_tx06_compliance;
   wire           pipe_tx07_compliance;
   wire           pipe_tx08_compliance;
   wire           pipe_tx09_compliance;
   wire           pipe_tx10_compliance;
   wire           pipe_tx11_compliance;
   wire           pipe_tx12_compliance;
   wire           pipe_tx13_compliance;
   wire           pipe_tx14_compliance;
   wire           pipe_tx15_compliance;
   wire [1:0]     pipe_tx00_char_is_k;
   wire [1:0]     pipe_tx01_char_is_k;
   wire [1:0]     pipe_tx02_char_is_k;
   wire [1:0]     pipe_tx03_char_is_k;
   wire [1:0]     pipe_tx04_char_is_k;
   wire [1:0]     pipe_tx05_char_is_k;
   wire [1:0]     pipe_tx06_char_is_k;
   wire [1:0]     pipe_tx07_char_is_k;
   wire [1:0]     pipe_tx08_char_is_k;
   wire [1:0]     pipe_tx09_char_is_k;
   wire [1:0]     pipe_tx10_char_is_k;
   wire [1:0]     pipe_tx11_char_is_k;
   wire [1:0]     pipe_tx12_char_is_k;
   wire [1:0]     pipe_tx13_char_is_k;
   wire [1:0]     pipe_tx14_char_is_k;
   wire [1:0]     pipe_tx15_char_is_k;
   wire [31:0]    pipe_tx00_data;
   wire [31:0]    pipe_tx01_data;
   wire [31:0]    pipe_tx02_data;
   wire [31:0]    pipe_tx03_data;
   wire [31:0]    pipe_tx04_data;
   wire [31:0]    pipe_tx05_data;
   wire [31:0]    pipe_tx06_data;
   wire [31:0]    pipe_tx07_data;
   wire [31:0]    pipe_tx08_data;
   wire [31:0]    pipe_tx09_data;
   wire [31:0]    pipe_tx10_data;
   wire [31:0]    pipe_tx11_data;
   wire [31:0]    pipe_tx12_data;
   wire [31:0]    pipe_tx13_data;
   wire [31:0]    pipe_tx14_data;
   wire [31:0]    pipe_tx15_data;
   wire           pipe_tx00_elec_idle;
   wire           pipe_tx01_elec_idle;
   wire           pipe_tx02_elec_idle;
   wire           pipe_tx03_elec_idle;
   wire           pipe_tx04_elec_idle;
   wire           pipe_tx05_elec_idle;
   wire           pipe_tx06_elec_idle;
   wire           pipe_tx07_elec_idle;
   wire           pipe_tx08_elec_idle;
   wire           pipe_tx09_elec_idle;
   wire           pipe_tx10_elec_idle;
   wire           pipe_tx11_elec_idle;
   wire           pipe_tx12_elec_idle;
   wire           pipe_tx13_elec_idle;
   wire           pipe_tx14_elec_idle;
   wire           pipe_tx15_elec_idle;
   wire [1:0]     pipe_tx00_powerdown;
   wire [1:0]     pipe_tx01_powerdown;
   wire [1:0]     pipe_tx02_powerdown;
   wire [1:0]     pipe_tx03_powerdown;
   wire [1:0]     pipe_tx04_powerdown;
   wire [1:0]     pipe_tx05_powerdown;
   wire [1:0]     pipe_tx06_powerdown;
   wire [1:0]     pipe_tx07_powerdown;
   wire [1:0]     pipe_tx08_powerdown;
   wire [1:0]     pipe_tx09_powerdown;
   wire [1:0]     pipe_tx10_powerdown;
   wire [1:0]     pipe_tx11_powerdown;
   wire [1:0]     pipe_tx12_powerdown;
   wire [1:0]     pipe_tx13_powerdown;
   wire [1:0]     pipe_tx14_powerdown;
   wire [1:0]     pipe_tx15_powerdown;
   wire           pipe_tx00_data_valid;
   wire           pipe_tx01_data_valid;
   wire           pipe_tx02_data_valid;
   wire           pipe_tx03_data_valid;
   wire           pipe_tx04_data_valid;
   wire           pipe_tx05_data_valid;
   wire           pipe_tx06_data_valid;
   wire           pipe_tx07_data_valid;
   wire           pipe_tx08_data_valid;
   wire           pipe_tx09_data_valid;
   wire           pipe_tx10_data_valid;
   wire           pipe_tx11_data_valid;
   wire           pipe_tx12_data_valid;
   wire           pipe_tx13_data_valid;
   wire           pipe_tx14_data_valid;
   wire           pipe_tx15_data_valid;
   wire           pipe_tx00_start_block;
   wire           pipe_tx01_start_block;
   wire           pipe_tx02_start_block;
   wire           pipe_tx03_start_block;
   wire           pipe_tx04_start_block;
   wire           pipe_tx05_start_block;
   wire           pipe_tx06_start_block;
   wire           pipe_tx07_start_block;
   wire           pipe_tx08_start_block;
   wire           pipe_tx09_start_block;
   wire           pipe_tx10_start_block;
   wire           pipe_tx11_start_block;
   wire           pipe_tx12_start_block;
   wire           pipe_tx13_start_block;
   wire           pipe_tx14_start_block;
   wire           pipe_tx15_start_block;
   wire [1:0]     pipe_tx00_sync_header;
   wire [1:0]     pipe_tx01_sync_header;
   wire [1:0]     pipe_tx02_sync_header;
   wire [1:0]     pipe_tx03_sync_header;
   wire [1:0]     pipe_tx04_sync_header;
   wire [1:0]     pipe_tx05_sync_header;
   wire [1:0]     pipe_tx06_sync_header;
   wire [1:0]     pipe_tx07_sync_header;
   wire [1:0]     pipe_tx08_sync_header;
   wire [1:0]     pipe_tx09_sync_header;
   wire [1:0]     pipe_tx10_sync_header;
   wire [1:0]     pipe_tx11_sync_header;
   wire [1:0]     pipe_tx12_sync_header;
   wire [1:0]     pipe_tx13_sync_header;
   wire [1:0]     pipe_tx14_sync_header;
   wire [1:0]     pipe_tx15_sync_header;
   wire [1:0]     pipe_rx00_eq_control;
   wire [1:0]     pipe_rx01_eq_control;
   wire [1:0]     pipe_rx02_eq_control;
   wire [1:0]     pipe_rx03_eq_control;
   wire [1:0]     pipe_rx04_eq_control;
   wire [1:0]     pipe_rx05_eq_control;
   wire [1:0]     pipe_rx06_eq_control;
   wire [1:0]     pipe_rx07_eq_control;
   wire [1:0]     pipe_rx08_eq_control;
   wire [1:0]     pipe_rx09_eq_control;
   wire [1:0]     pipe_rx10_eq_control;
   wire [1:0]     pipe_rx11_eq_control;
   wire [1:0]     pipe_rx12_eq_control;
   wire [1:0]     pipe_rx13_eq_control;
   wire [1:0]     pipe_rx14_eq_control;
   wire [1:0]     pipe_rx15_eq_control;
   wire           pipe_rx00_eq_lp_lf_fs_sel;
   wire           pipe_rx01_eq_lp_lf_fs_sel;
   wire           pipe_rx02_eq_lp_lf_fs_sel;
   wire           pipe_rx03_eq_lp_lf_fs_sel;
   wire           pipe_rx04_eq_lp_lf_fs_sel;
   wire           pipe_rx05_eq_lp_lf_fs_sel;
   wire           pipe_rx06_eq_lp_lf_fs_sel;
   wire           pipe_rx07_eq_lp_lf_fs_sel;
   wire           pipe_rx08_eq_lp_lf_fs_sel;
   wire           pipe_rx09_eq_lp_lf_fs_sel;
   wire           pipe_rx10_eq_lp_lf_fs_sel;
   wire           pipe_rx11_eq_lp_lf_fs_sel;
   wire           pipe_rx12_eq_lp_lf_fs_sel;
   wire           pipe_rx13_eq_lp_lf_fs_sel;
   wire           pipe_rx14_eq_lp_lf_fs_sel;
   wire           pipe_rx15_eq_lp_lf_fs_sel;
   wire [17:0]    pipe_rx00_eq_lp_new_tx_coeff_or_preset;
   wire [17:0]    pipe_rx01_eq_lp_new_tx_coeff_or_preset;
   wire [17:0]    pipe_rx02_eq_lp_new_tx_coeff_or_preset;
   wire [17:0]    pipe_rx03_eq_lp_new_tx_coeff_or_preset;
   wire [17:0]    pipe_rx04_eq_lp_new_tx_coeff_or_preset;
   wire [17:0]    pipe_rx05_eq_lp_new_tx_coeff_or_preset;
   wire [17:0]    pipe_rx06_eq_lp_new_tx_coeff_or_preset;
   wire [17:0]    pipe_rx07_eq_lp_new_tx_coeff_or_preset;
   wire [17:0]    pipe_rx08_eq_lp_new_tx_coeff_or_preset;
   wire [17:0]    pipe_rx09_eq_lp_new_tx_coeff_or_preset;
   wire [17:0]    pipe_rx10_eq_lp_new_tx_coeff_or_preset;
   wire [17:0]    pipe_rx11_eq_lp_new_tx_coeff_or_preset;
   wire [17:0]    pipe_rx12_eq_lp_new_tx_coeff_or_preset;
   wire [17:0]    pipe_rx13_eq_lp_new_tx_coeff_or_preset;
   wire [17:0]    pipe_rx14_eq_lp_new_tx_coeff_or_preset;
   wire [17:0]    pipe_rx15_eq_lp_new_tx_coeff_or_preset;
   wire           pipe_rx00_eq_lp_adapt_done;
   wire           pipe_rx01_eq_lp_adapt_done;
   wire           pipe_rx02_eq_lp_adapt_done;
   wire           pipe_rx03_eq_lp_adapt_done;
   wire           pipe_rx04_eq_lp_adapt_done;
   wire           pipe_rx05_eq_lp_adapt_done;
   wire           pipe_rx06_eq_lp_adapt_done;
   wire           pipe_rx07_eq_lp_adapt_done;
   wire           pipe_rx08_eq_lp_adapt_done;
   wire           pipe_rx09_eq_lp_adapt_done;
   wire           pipe_rx10_eq_lp_adapt_done;
   wire           pipe_rx11_eq_lp_adapt_done;
   wire           pipe_rx12_eq_lp_adapt_done;
   wire           pipe_rx13_eq_lp_adapt_done;
   wire           pipe_rx14_eq_lp_adapt_done;
   wire           pipe_rx15_eq_lp_adapt_done;
   wire           pipe_rx00_eq_done;
   wire           pipe_rx01_eq_done;
   wire           pipe_rx02_eq_done;
   wire           pipe_rx03_eq_done;
   wire           pipe_rx04_eq_done;
   wire           pipe_rx05_eq_done;
   wire           pipe_rx06_eq_done;
   wire           pipe_rx07_eq_done;
   wire           pipe_rx08_eq_done;
   wire           pipe_rx09_eq_done;
   wire           pipe_rx10_eq_done;
   wire           pipe_rx11_eq_done;
   wire           pipe_rx12_eq_done;
   wire           pipe_rx13_eq_done;
   wire           pipe_rx14_eq_done;
   wire           pipe_rx15_eq_done;
   wire [1:0]     pipe_tx00_eq_control;
   wire [1:0]     pipe_tx01_eq_control;
   wire [1:0]     pipe_tx02_eq_control;
   wire [1:0]     pipe_tx03_eq_control;
   wire [1:0]     pipe_tx04_eq_control;
   wire [1:0]     pipe_tx05_eq_control;
   wire [1:0]     pipe_tx06_eq_control;
   wire [1:0]     pipe_tx07_eq_control;
   wire [1:0]     pipe_tx08_eq_control;
   wire [1:0]     pipe_tx09_eq_control;
   wire [1:0]     pipe_tx10_eq_control;
   wire [1:0]     pipe_tx11_eq_control;
   wire [1:0]     pipe_tx12_eq_control;
   wire [1:0]     pipe_tx13_eq_control;
   wire [1:0]     pipe_tx14_eq_control;
   wire [1:0]     pipe_tx15_eq_control;
   wire [5:0]     pipe_tx00_eq_deemph;
   wire [5:0]     pipe_tx01_eq_deemph;
   wire [5:0]     pipe_tx02_eq_deemph;
   wire [5:0]     pipe_tx03_eq_deemph;
   wire [5:0]     pipe_tx04_eq_deemph;
   wire [5:0]     pipe_tx05_eq_deemph;
   wire [5:0]     pipe_tx06_eq_deemph;
   wire [5:0]     pipe_tx07_eq_deemph;
   wire [5:0]     pipe_tx08_eq_deemph;
   wire [5:0]     pipe_tx09_eq_deemph;
   wire [5:0]     pipe_tx10_eq_deemph;
   wire [5:0]     pipe_tx11_eq_deemph;
   wire [5:0]     pipe_tx12_eq_deemph;
   wire [5:0]     pipe_tx13_eq_deemph;
   wire [5:0]     pipe_tx14_eq_deemph;
   wire [5:0]     pipe_tx15_eq_deemph;
   wire [17:0]    pipe_tx00_eq_coeff;
   wire [17:0]    pipe_tx01_eq_coeff;
   wire [17:0]    pipe_tx02_eq_coeff;
   wire [17:0]    pipe_tx03_eq_coeff;
   wire [17:0]    pipe_tx04_eq_coeff;
   wire [17:0]    pipe_tx05_eq_coeff;
   wire [17:0]    pipe_tx06_eq_coeff;
   wire [17:0]    pipe_tx07_eq_coeff;
   wire [17:0]    pipe_tx08_eq_coeff;
   wire [17:0]    pipe_tx09_eq_coeff;
   wire [17:0]    pipe_tx10_eq_coeff;
   wire [17:0]    pipe_tx11_eq_coeff;
   wire [17:0]    pipe_tx12_eq_coeff;
   wire [17:0]    pipe_tx13_eq_coeff;
   wire [17:0]    pipe_tx14_eq_coeff;
   wire [17:0]    pipe_tx15_eq_coeff;
   wire           pipe_tx00_eq_done;
   wire           pipe_tx01_eq_done;
   wire           pipe_tx02_eq_done;
   wire           pipe_tx03_eq_done;
   wire           pipe_tx04_eq_done;
   wire           pipe_tx05_eq_done;
   wire           pipe_tx06_eq_done;
   wire           pipe_tx07_eq_done;
   wire           pipe_tx08_eq_done;
   wire           pipe_tx09_eq_done;
   wire           pipe_tx10_eq_done;
   wire           pipe_tx11_eq_done;
   wire           pipe_tx12_eq_done;
   wire           pipe_tx13_eq_done;
   wire           pipe_tx14_eq_done;
   wire           pipe_tx15_eq_done;

   wire [3:0]     pipe_rx_eq_lp_tx_preset;
   wire [5:0]     pipe_rx_eq_lp_lf_fs;
   wire           pipe_tx_rcvr_det;
   reg  [1:0]     pipe_tx_rate_ff;
   wire [1:0]     pipe_tx_rate_i;
   reg            speed_change_in_progress;
   wire           pipe_tx_deemph;
   wire [2:0]     pipe_tx_margin;
   wire           pipe_tx_swing;
   wire           pipe_tx_reset;
   wire [5:0]     pipe_eq_fs;
   wire [5:0]     pipe_eq_lf;

   wire [2:0]     pipe_rx_eq_preset = 3'b0;

   wire           user_clk_en;
   wire           sys_reset_in_n;      // Convert incoming sys_reset to always active low reset.
   wire           sys_reset_in_n_sync; // Sync to sys_clk. Always active low reset.
   wire           sys_rst_n;
   wire           sys_or_hot_rst_int;
   wire           sys_or_hot_rst_pclk;
   wire           sys_or_hot_rst_uclk;
   wire           user_lnk_up_int;
   wire           user_lnk_up_cdc_o;
   wire           user_clk2 = (AXISTEN_IF_EXT_512 == "TRUE") ? core_clk : user_clk;
   wire           mcap_clk_int;
   wire           conf_req_ready_wire;
   wire           conf_mcap_design_switch_o;
  wire                conf_mcap_design_switch;
  reg [5:0] np_req_wait;
   wire mcap_pcie_request;
   wire mcap_external_request;
   wire design_switch;
   reg [7:0] flr_cntr;
   reg [5:0] ds_srl;
   wire ds_pulse;

  // Critical signal muxing.
   wire mcap_external_request_int;
   wire [1:0] pcie_cq_np_req_int;
   wire m_axis_cq_tvalid_int;
   wire s_axis_cc_tvalid_int;
   wire s_axis_rq_tvalid_int;
   wire m_axis_rc_tvalid_int;
   wire m_axis_cq_tready_int;
   wire [AXI4_CC_TREADY_WIDTH-1:0] s_axis_cc_tready_int;
   wire [AXI4_RQ_TREADY_WIDTH-1:0] s_axis_rq_tready_int;
   wire m_axis_rc_tready_int;
   wire cfg_mgmt_write_int;
   wire cfg_mgmt_read_int;
   wire cfg_msg_transmit_wire;
   wire cfg_hot_reset_in_int;
   wire cfg_config_space_enable_int;
   wire [63:0] cfg_dsn_int;
   wire cfg_power_state_change_ack_int;
   wire cfg_err_cor_in_int;
   wire cfg_err_uncor_in_int;
   wire [3:0] cfg_flr_done_int;
   wire cfg_req_pm_transition_l23_ready_int;
   wire cfg_link_training_enable_int;
   wire [3:0] cfg_interrupt_int_int;
   wire [3:0] cfg_interrupt_pending_int;
   wire [31:0] cfg_interrupt_msi_int_int;
   wire cfg_interrupt_msi_pending_status_data_enable_int;
   wire cfg_interrupt_msix_int_int;
   wire [1:0] cfg_interrupt_msix_vec_pending_int;
   wire [7:0] cfg_vf_flr_func_num_int;
   wire cfg_vf_flr_done_int;
   wire cfg_pm_aspm_l1_entry_reject_int;
   wire cfg_pm_aspm_tx_l0s_entry_disable_int;
   wire conf_req_valid_int;
   wire conf_req_ready_int;
   wire [((PL_LINK_CAP_MAX_LINK_WIDTH *  1)-1):0] ext_ch_gt_drpen_int;
   wire                                        drp_en_local;
   wire [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_pcieuserratedone_int;
   wire [((PL_LINK_CAP_MAX_LINK_WIDTH*3)-1):0] gt_loopback_int;
   wire [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_txprbsforceerr_int;
   wire [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_txinhibit_int;
   wire [((PL_LINK_CAP_MAX_LINK_WIDTH*4)-1):0] gt_txprbssel_int;
   wire [((PL_LINK_CAP_MAX_LINK_WIDTH*4)-1):0] gt_rxprbssel_int;
   wire [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_rxprbscntreset_int;
   wire [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_dmonfiforeset_int;
   wire [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0] gt_dmonitorclk_int;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0] gt_txpmareset_int;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0] gt_rxpmareset_int;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0] gt_txpcsreset_int;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0] gt_rxpcsreset_int;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0] gt_rxbufreset_int;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0] gt_rxcdrreset_int;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0] gt_rxdfelpmreset_int;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_rxlpmen;


  wire [(PL_LINK_CAP_MAX_LINK_WIDTH*5)-1:0]  txeq_precursor_o;
  wire [(PL_LINK_CAP_MAX_LINK_WIDTH*5)-1:0]  txeq_postcursor_o;
  wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]      gt_pcierategen3_o;
  wire [1:0]                                 pipe_tx_rate_o;
  wire                                       pipe_tx0_rcvr_det;
  wire [1:0]                                 pipe_tx0_powerdown;

  wire                                        pipe_clk;
  wire                                        sys_clk_bufg;



   wire [(PL_LINK_CAP_MAX_LINK_WIDTH*64)-1:0]     PHY_RXDATA;
   wire [(PL_LINK_CAP_MAX_LINK_WIDTH* 2)-1:0]     PHY_RXDATAK;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]          PHY_RXDATA_VALID;
   wire [(PL_LINK_CAP_MAX_LINK_WIDTH* 2)-1:0]     PHY_RXSTART_BLOCK;
   reg [(PL_LINK_CAP_MAX_LINK_WIDTH* 2)-1:0]     PHY_RXSYNC_HEADER;

   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]          PHY_RXVALID;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]          PHY_PHYSTATUS;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]          phy_status_fix;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]          PHY_RXELECIDLE;
   wire [(PL_LINK_CAP_MAX_LINK_WIDTH*3)-1:0]      PHY_RXSTATUS;

   wire [(PL_LINK_CAP_MAX_LINK_WIDTH*18)-1:0]     PHY_TXEQ_NEW_COEFF;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]          PHY_TXEQ_DONE;

   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]          PHY_RXEQ_LFFS_SEL;
   wire [(PL_LINK_CAP_MAX_LINK_WIDTH*18)-1:0]     PHY_RXEQ_NEW_TXCOEFF;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]          PHY_RXEQ_ADAPT_DONE;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]          PHY_RXEQ_DONE;

   wire [PL_LINK_CAP_MAX_LINK_WIDTH*64-1:0]       PHY_TXDATA;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH*2-1:0]        PHY_TXDATAK;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]          PHY_TXDATA_VALID;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]          PHY_TXSTART_BLOCK;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH*2-1:0]        PHY_TXSYNC_HEADER;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]          PHY_TXELECIDLE;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]          PHY_TXCOMPLIANCE;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]          PHY_RXPOLARITY;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH*2-1:0]        PHY_TXEQ_CTRL;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH*4-1:0]        PHY_TXEQ_PRESET;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH*6-1:0]        PHY_TXEQ_COEFF;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH*2-1:0]        PHY_RXEQ_CTRL;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]          PHY_RXPOLARITY_TEMP;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH*2-1:0]        PHY_RXEQ_CTRL_TEMP;
   wire [3:0]     pipe_rx_eq_lp_tx_preset_temp;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH*4-1:0]        PHY_TXEQ_PRESET_TEMP;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH*6-1:0]        PHY_TXEQ_COEFF_TEMP;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH*2-1:0]        PHY_TXSYNC_HEADER_TEMP;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]          PHY_TXSTART_BLOCK_TEMP;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]          PHY_TXDATA_VALID_TEMP;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]          PHY_TXELECIDLE_TEMP;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]          PHY_TXCOMPLIANCE_TEMP;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH*64-1:0]       PHY_TXDATA_TEMP;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH*2-1:0]        PHY_TXDATAK_TEMP;
   wire           pipe_tx_rcvr_det_temp;
   wire [1:0]     pipe_tx00_powerdown_temp;
   wire [1:0]     pipe_tx_rate_i_temp;
   wire           pipe_tx_deemph_temp;
   wire [2:0]     pipe_tx_margin_temp;
   wire           pipe_tx_swing_temp;
   wire [5:0]     pipe_eq_fs_temp;
   wire [5:0]     pipe_eq_lf_temp;
   wire [(PL_LINK_CAP_MAX_LINK_WIDTH*18)-1:0]     PHY_TXEQ_NEW_COEFF_TEMP;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]          PHY_TXEQ_DONE_TEMP;
   wire [(PL_LINK_CAP_MAX_LINK_WIDTH* 2)-1:0]     rxsync_header_nogate_temp;
   wire [(PL_LINK_CAP_MAX_LINK_WIDTH* 2)-1:0]     PHY_RXSTART_BLOCK_TEMP;
   wire [(PL_LINK_CAP_MAX_LINK_WIDTH*18)-1:0]     PHY_RXEQ_NEW_TXCOEFF_TEMP;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]          PHY_RXEQ_LFFS_SEL_TEMP;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]          PHY_RXEQ_ADAPT_DONE_TEMP;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]          PHY_RXEQ_DONE_TEMP;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]          PHY_RXELECIDLE_TEMP;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]          PHY_PHYSTATUS_TEMP;
   wire [(PL_LINK_CAP_MAX_LINK_WIDTH*3)-1:0]      PHY_RXSTATUS_TEMP;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]          PHY_RXDATA_VALID_TEMP;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]          PHY_RXVALID_TEMP;
   wire [(PL_LINK_CAP_MAX_LINK_WIDTH* 2)-1:0]     PHY_RXDATAK_TEMP;
   wire [(PL_LINK_CAP_MAX_LINK_WIDTH*64)-1:0]     PHY_RXDATA_TEMP;
   wire [PL_LINK_CAP_MAX_LINK_WIDTH*2-1:0]        PHY_TXEQ_CTRL_TEMP;
   wire user_reset_int;
   wire user_reset_cdc_o;

//////////////////////////
// WORKAROUND RX Singals
   reg [(PL_LINK_CAP_MAX_LINK_WIDTH*64)-1:0]      PHY_RXDATA_REG;
   reg [(PL_LINK_CAP_MAX_LINK_WIDTH* 2)-1:0]      PHY_RXDATAK_REG;
   reg [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]           PHY_RXDATA_VALID_REG;
   reg [(PL_LINK_CAP_MAX_LINK_WIDTH* 2)-1:0]      PHY_RXSTART_BLOCK_REG;
   reg [(PL_LINK_CAP_MAX_LINK_WIDTH* 2)-1:0]      rxsync_header_nogate_reg;

   reg [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]           PHY_RXVALID_REG;
   reg [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]           PHY_PHYSTATUS_REG;
   reg [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]           PHY_RXELECIDLE_REG;
   reg [(PL_LINK_CAP_MAX_LINK_WIDTH*3)-1:0]       PHY_RXSTATUS_REG;
//////////////////////////

   reg   as_cdr_hold_req_user;
   reg   as_cdr_hold_req_ff;
   reg   as_cdr_hold_req_ff1;
   reg   as_mac_in_detect_user;
   reg   as_mac_in_detect_ff;
   reg   as_mac_in_detect_ff1;
   wire [31:0] acs_cfg_ext_read_data;
   wire        acs_cfg_ext_read_data_valid;
   wire [31:0] cfg_ext_read_data_int;
   wire        cfg_ext_read_data_valid_int;
   wire  [31:0] rbar_cfg_ext_read_data;
   wire         rbar_cfg_ext_read_data_valid;
  //--------------------------------------------------------------------------
  // PCIe DRP Port internal signals
  //--------------------------------------------------------------------------
   wire         drp_rdy_int;
   wire  [15:0] drp_do_int;
   wire         drp_clk_int;
   wire         drp_en_int;
   wire         drp_we_int;
   wire   [9:0] drp_addr_int;
   wire  [15:0] drp_di_int;
// Gate rxsync_header with rxstart_block
wire [(PL_LINK_CAP_MAX_LINK_WIDTH* 2)-1:0]     rxsync_header_nogate;
integer ii;
always @*
  for (ii=0;ii<(PL_LINK_CAP_MAX_LINK_WIDTH*2);ii=ii+2)
    PHY_RXSYNC_HEADER[ii+:2] = rxsync_header_nogate_temp[ii+:2] & {2{^PHY_RXSTART_BLOCK_TEMP[ii+:2]}};


// Workaround for the double-triggering on cfg_msg_transmit
wire cfg_msg_transmit_int = cfg_msg_transmit_wire & ~cfg_msg_transmit_done;
//-------------------------------------------------------------------------------------------
   wire         cfg_ext_read_received_i;
   wire         cfg_ext_write_received_i;
   wire [9:0]   cfg_ext_register_number_i;
   wire [7:0]   cfg_ext_function_number_i;
   wire [31:0]  cfg_ext_write_data_i;
   wire [3:0]   cfg_ext_write_byte_enable_i;
   wire [31:0]  cfg_ext_read_data_i;
   wire         cfg_ext_read_data_valid_i;
  //-----------------------------------------------------------------------
  // CCIX Interface
  //-----------------------------------------------------------------------
   wire [AXIS_CCIX_TX_TDATA_WIDTH-1:0]   s_axis_ccix_tx_tdata;   // 256-bit data
   wire                                  s_axis_ccix_tx_tvalid;  // Valid
   wire [AXIS_CCIX_TX_TUSER_WIDTH-1:0]   s_axis_ccix_tx_tuser;   // tuser bus
   wire                                  ccix_tx_credit_gnt;     // Flow control credits from CCIX protocol processing block
   wire                                  ccix_tx_credit_rtn;     // Used to return unused credits to CCIX protocol processing block
   wire                                  ccix_tx_active_req;     // Asserted by TL to request a transition from STOP to ACTIVATE
   wire                                  ccix_tx_active_ack;     // Grant from CCIX block
   wire                                  ccix_tx_deact_hint;

   wire [AXIS_CCIX_RX_TDATA_WIDTH-1:0]   m_axis_ccix_rx_tdata;   // 256-bit data
   wire                                  m_axis_ccix_rx_tvalid;  // Valid
   wire [AXIS_CCIX_RX_TUSER_WIDTH-1:0]   m_axis_ccix_rx_tuser;   // tuser bus
   wire                                  ccix_rx_credit_grant;   // Flow control credits from CCIX protocol processing block
   wire                                  ccix_rx_credit_return;  // Used to return unused credits to CCIX protocol processing block
  //wire[7:0]                             ccix_rx_credit_av;      // Current value of available credit maintained by the bridge
   wire                                  ccix_rx_active_req;     // Asserted by TL to request a transition from STOP to ACTIVATE
   wire                                  ccix_rx_active_ack;     // Grant from CCIX block
   wire                                  ccix_rx_deact_hint;

   wire [31:0]  dvsec_cfg_ext_read_data;
   wire         dvsec_cfg_ext_read_data_valid;
 assign  cfg_ext_read_received  = cfg_ext_read_received_i;
 assign  cfg_ext_write_received = cfg_ext_write_received_i;
 assign  cfg_ext_register_number = cfg_ext_register_number_i;
 assign  cfg_ext_function_number = cfg_ext_function_number_i;
 assign  cfg_ext_write_data = cfg_ext_write_data_i;
 assign  cfg_ext_write_byte_enable = cfg_ext_write_byte_enable_i;

 //assign  cfg_ext_read_data_i = cfg_ext_read_data;
 //assign  cfg_ext_read_data_valid_i = cfg_ext_read_data_valid;
 assign  dvsec_cfg_ext_read_data = 'd0;
 assign  dvsec_cfg_ext_read_data_valid = 'd0;
 assign  ccix_optimized_tlp_tx_and_rx_enable_i = ccix_optimized_tlp_tx_and_rx_enable_rp;
 assign  ats_pri_en = 1'b0;

wire [31:0] cfg_mgmt_read_data_sig;
generate if (EN_SLOT_CAP_REG == "TRUE" && PL_UPSTREAM_FACING == "FALSE")
begin
 assign cfg_mgmt_read_data = (cfg_mgmt_addr == 10'h21 && cfg_mgmt_read == 1'b1) ? SLOT_CAP_REG : cfg_mgmt_read_data_sig;
end else begin
 assign cfg_mgmt_read_data = cfg_mgmt_read_data_sig;
end
endgenerate

//-------------------------------------------------------------------------------------------
generate if (EXT_PIPESIM == "TRUE")
begin
  /////////////// phy_rdy, rcvr det , seepd_change & gt_powerdown /////////////////////////////

  reg [31:0] phy_rdy_reg = 32'b0;
  reg [31:0] rcvr_det_reg     = 32'b0;
  reg  [7:0] pipe_rate_reg    = 8'b0;
  reg  [7:0] gt_powerdown_reg = {4{2'b10}};

  wire      rcvr_det;
  wire      speed_change;
  wire      gt_powerdown;

  always @ (posedge pipe_clk)
  begin
   phy_rdy_reg      <= {phy_rdy_reg[30:0], sys_rst_n};
   rcvr_det_reg     <= {rcvr_det_reg[30:0], pipe_tx0_rcvr_det};
   pipe_rate_reg    <= {pipe_rate_reg[5:0], common_commands_out[2:1]};
   gt_powerdown_reg <= {gt_powerdown_reg[5:0],pipe_tx_0_sigs[41:40]};
  end

  assign phy_rdy      =  phy_rdy_reg[31];
  assign rcvr_det     = ~rcvr_det_reg[30] && rcvr_det_reg[29];
  assign speed_change = (pipe_rate_reg[7:6] != pipe_rate_reg[5:4])? 1'b1 : 1'b0;
  assign gt_powerdown = (gt_powerdown_reg[7:6] == 2'b10 && gt_powerdown_reg[5:4] == 2'b0)? 1'b1 : 1'b0;



  //////// generate Rx status and Phy status //////////////

  wire [2:0] rx_status;
  wire       phy_status;

  assign  rx_status  = (pipe_tx0_rcvr_det && rcvr_det) ? 3'b011 : 3'b0;
  assign  phy_status = (pipe_tx0_rcvr_det && rcvr_det) || speed_change || gt_powerdown ;


  //////// generate clocks for pipe mode //////////////

  wire clk_500;
  wire clk_250;
  wire clk_125;
  wire clk_62_5;

  pcie_bridge_ep_pcie4c_ip_sys_clk_gen_ps 	#(.offset(7000),.halfcycle(1000)) clk_gen_500  (.sys_clk(clk_500));
  pcie_bridge_ep_pcie4c_ip_sys_clk_gen_ps 	#(.offset(6000),.halfcycle(2000)) clk_gen_250  (.sys_clk(clk_250));
  pcie_bridge_ep_pcie4c_ip_sys_clk_gen_ps 	#(.offset(4000),.halfcycle(4000)) clk_gen_125  (.sys_clk(clk_125));
  pcie_bridge_ep_pcie4c_ip_sys_clk_gen_ps 	#(.offset(0000),.halfcycle(8000)) clk_gen_62_5 (.sys_clk(clk_62_5));

  assign mcap_clk_int = (CRM_USER_CLK_FREQ == 2'b10 || CRM_USER_CLK_FREQ == 2'b11) ? clk_125 : user_clk;
  assign pipe_clk     = (common_commands_out[2:1] == 2'b0)? clk_125 : clk_250;
  assign core_clk     = (CRM_CORE_CLK_FREQ_500 == "TRUE") ? clk_500 : clk_250 ;
  assign user_clk     = (CRM_USER_CLK_FREQ == 2'b10 || CRM_USER_CLK_FREQ == 2'b11) ? clk_250: ((CRM_USER_CLK_FREQ == 01) ? clk_125 : clk_62_5);
  assign sys_clk_bufg = sys_clk;

  // PCIE_4_C Instance
  pcie_bridge_ep_pcie4c_ip_pipe
  #(

    .TCQ(TCQ)
   ,.IMPL_TARGET(IMPL_TARGET)
   ,.AXISTEN_IF_EXT_512_INTFC_RAM_STYLE(AXISTEN_IF_EXT_512_INTFC_RAM_STYLE)
   ,.CRM_CORE_CLK_FREQ_500(CRM_CORE_CLK_FREQ_500)
   ,.CRM_USER_CLK_FREQ(CRM_USER_CLK_FREQ)
   ,.AXISTEN_IF_WIDTH(AXISTEN_IF_WIDTH)
   ,.AXISTEN_IF_EXT_512_CQ_STRADDLE(AXISTEN_IF_EXT_512_CQ_STRADDLE)
   ,.AXISTEN_IF_EXT_512_CC_STRADDLE(AXISTEN_IF_EXT_512_CC_STRADDLE)
   ,.AXISTEN_IF_EXT_512_RQ_STRADDLE(AXISTEN_IF_EXT_512_RQ_STRADDLE)
   ,.AXISTEN_IF_EXT_512_RC_STRADDLE(AXISTEN_IF_EXT_512_RC_STRADDLE)
   ,.AXISTEN_IF_EXT_512_RC_4TLP_STRADDLE(AXISTEN_IF_EXT_512_RC_4TLP_STRADDLE)
   ,.AXISTEN_IF_EXT_512(AXISTEN_IF_EXT_512)
   ,.AXISTEN_IF_CQ_ALIGNMENT_MODE(AXISTEN_IF_CQ_ALIGNMENT_MODE)
   ,.AXISTEN_IF_CC_ALIGNMENT_MODE(AXISTEN_IF_CC_ALIGNMENT_MODE)
   ,.AXISTEN_IF_RQ_ALIGNMENT_MODE(AXISTEN_IF_RQ_ALIGNMENT_MODE)
   ,.AXISTEN_IF_RC_ALIGNMENT_MODE(AXISTEN_IF_RC_ALIGNMENT_MODE)
   ,.AXISTEN_IF_RC_STRADDLE(AXISTEN_IF_RC_STRADDLE)
   ,.AXI4_DATA_WIDTH(AXI4_DATA_WIDTH)
   ,.AXI4_TKEEP_WIDTH(AXI4_TKEEP_WIDTH)
   ,.AXI4_CQ_TUSER_WIDTH(AXI4_CQ_TUSER_WIDTH)
   ,.AXI4_CC_TUSER_WIDTH(AXI4_CC_TUSER_WIDTH)
   ,.AXI4_RQ_TUSER_WIDTH(AXI4_RQ_TUSER_WIDTH)
   ,.AXI4_RC_TUSER_WIDTH(AXI4_RC_TUSER_WIDTH)
   ,.AXI4_CQ_TREADY_WIDTH(AXI4_CQ_TREADY_WIDTH)
   ,.AXI4_CC_TREADY_WIDTH(AXI4_CC_TREADY_WIDTH)
   ,.AXI4_RQ_TREADY_WIDTH(AXI4_RQ_TREADY_WIDTH)
   ,.AXI4_RC_TREADY_WIDTH(AXI4_RC_TREADY_WIDTH)
   ,.AXIS_CCIX_TX_TDATA_WIDTH(AXIS_CCIX_TX_TDATA_WIDTH)
   ,.AXIS_CCIX_RX_TDATA_WIDTH(AXIS_CCIX_RX_TDATA_WIDTH)
   ,.AXIS_CCIX_TX_TUSER_WIDTH(AXIS_CCIX_TX_TUSER_WIDTH)
   ,.AXIS_CCIX_RX_TUSER_WIDTH(AXIS_CCIX_RX_TUSER_WIDTH)
   ,.AXISTEN_IF_ENABLE_RX_MSG_INTFC(AXISTEN_IF_ENABLE_RX_MSG_INTFC)
   ,.AXISTEN_IF_ENABLE_MSG_ROUTE(AXISTEN_IF_ENABLE_MSG_ROUTE)
   ,.AXISTEN_IF_RX_PARITY_EN(AXISTEN_IF_RX_PARITY_EN)
   ,.AXISTEN_IF_TX_PARITY_EN(AXISTEN_IF_TX_PARITY_EN)
   ,.AXISTEN_IF_ENABLE_CLIENT_TAG(AXISTEN_IF_ENABLE_CLIENT_TAG)
   ,.AXISTEN_IF_ENABLE_256_TAGS(AXISTEN_IF_ENABLE_256_TAGS)
   ,.AXISTEN_IF_COMPL_TIMEOUT_REG0(AXISTEN_IF_COMPL_TIMEOUT_REG0)
   ,.AXISTEN_IF_COMPL_TIMEOUT_REG1(AXISTEN_IF_COMPL_TIMEOUT_REG1)
   ,.AXISTEN_IF_LEGACY_MODE_ENABLE(AXISTEN_IF_LEGACY_MODE_ENABLE)
   ,.AXISTEN_IF_ENABLE_MESSAGE_RID_CHECK(AXISTEN_IF_ENABLE_MESSAGE_RID_CHECK)
   ,.AXISTEN_IF_MSIX_TO_RAM_PIPELINE(AXISTEN_IF_MSIX_TO_RAM_PIPELINE)
   ,.AXISTEN_IF_MSIX_FROM_RAM_PIPELINE(AXISTEN_IF_MSIX_FROM_RAM_PIPELINE)
   ,.AXISTEN_IF_MSIX_RX_PARITY_EN(AXISTEN_IF_MSIX_RX_PARITY_EN)
   ,.AXISTEN_IF_ENABLE_INTERNAL_MSIX_TABLE(AXISTEN_IF_ENABLE_INTERNAL_MSIX_TABLE)
   ,.AXISTEN_IF_SIM_SHORT_CPL_TIMEOUT(AXISTEN_IF_SIM_SHORT_CPL_TIMEOUT)
   ,.AXISTEN_IF_CQ_EN_POISONED_MEM_WR(AXISTEN_IF_CQ_EN_POISONED_MEM_WR)
   ,.AXISTEN_IF_RQ_CC_REGISTERED_TREADY(AXISTEN_IF_RQ_CC_REGISTERED_TREADY)
   ,.PM_ASPML0S_TIMEOUT(PM_ASPML0S_TIMEOUT)
   ,.PM_L1_REENTRY_DELAY(PM_L1_REENTRY_DELAY)
   ,.PM_ASPML1_ENTRY_DELAY(PM_ASPML1_ENTRY_DELAY)
   ,.PM_ENABLE_SLOT_POWER_CAPTURE(PM_ENABLE_SLOT_POWER_CAPTURE)
   ,.PM_PME_SERVICE_TIMEOUT_DELAY(PM_PME_SERVICE_TIMEOUT_DELAY)
   ,.PM_PME_TURNOFF_ACK_DELAY(PM_PME_TURNOFF_ACK_DELAY)
   ,.PL_UPSTREAM_FACING(PL_UPSTREAM_FACING)
   ,.PL_LINK_CAP_MAX_LINK_WIDTH(PL_LINK_CAP_MAX_LINK_WIDTH)
   ,.PL_LINK_CAP_MAX_LINK_SPEED(PL_LINK_CAP_MAX_LINK_SPEED)
   ,.PL_DISABLE_DC_BALANCE(PL_DISABLE_DC_BALANCE)
   ,.PL_DISABLE_EI_INFER_IN_L0(PL_DISABLE_EI_INFER_IN_L0)
   ,.PL_N_FTS(PL_N_FTS)
   ,.PL_DISABLE_UPCONFIG_CAPABLE(PL_DISABLE_UPCONFIG_CAPABLE)
   ,.PL_DISABLE_RETRAIN_ON_FRAMING_ERROR(PL_DISABLE_RETRAIN_ON_FRAMING_ERROR)
   ,.PL_DISABLE_RETRAIN_ON_EB_ERROR(PL_DISABLE_RETRAIN_ON_EB_ERROR)
   ,.PL_DISABLE_RETRAIN_ON_SPECIFIC_FRAMING_ERROR(PL_DISABLE_RETRAIN_ON_SPECIFIC_FRAMING_ERROR)
   ,.PL_REPORT_ALL_PHY_ERRORS(PL_REPORT_ALL_PHY_ERRORS)
   ,.PL_DISABLE_LFSR_UPDATE_ON_SKP(PL_DISABLE_LFSR_UPDATE_ON_SKP)
   ,.PL_LANE0_EQ_CONTROL(PL_LANE0_EQ_CONTROL)
   ,.PL_LANE1_EQ_CONTROL(PL_LANE1_EQ_CONTROL)
   ,.PL_LANE2_EQ_CONTROL(PL_LANE2_EQ_CONTROL)
   ,.PL_LANE3_EQ_CONTROL(PL_LANE3_EQ_CONTROL)
   ,.PL_LANE4_EQ_CONTROL(PL_LANE4_EQ_CONTROL)
   ,.PL_LANE5_EQ_CONTROL(PL_LANE5_EQ_CONTROL)
   ,.PL_LANE6_EQ_CONTROL(PL_LANE6_EQ_CONTROL)
   ,.PL_LANE7_EQ_CONTROL(PL_LANE7_EQ_CONTROL)
   ,.PL_LANE8_EQ_CONTROL(PL_LANE8_EQ_CONTROL)
   ,.PL_LANE9_EQ_CONTROL(PL_LANE9_EQ_CONTROL)
   ,.PL_LANE10_EQ_CONTROL(PL_LANE10_EQ_CONTROL)
   ,.PL_LANE11_EQ_CONTROL(PL_LANE11_EQ_CONTROL)
   ,.PL_LANE12_EQ_CONTROL(PL_LANE12_EQ_CONTROL)
   ,.PL_LANE13_EQ_CONTROL(PL_LANE13_EQ_CONTROL)
   ,.PL_LANE14_EQ_CONTROL(PL_LANE14_EQ_CONTROL)
   ,.PL_LANE15_EQ_CONTROL(PL_LANE15_EQ_CONTROL)
    //pragma translate_off
   ,.PL_EQ_BYPASS_PHASE23(PL_EQ_BYPASS_PHASE23)
    //pragma translate_on
   ,.PL_EQ_ADAPT_ITER_COUNT(PL_EQ_ADAPT_ITER_COUNT)
   ,.PL_EQ_ADAPT_REJECT_RETRY_COUNT(PL_EQ_ADAPT_REJECT_RETRY_COUNT)
   ,.PL_EQ_SHORT_ADAPT_PHASE(PL_EQ_SHORT_ADAPT_PHASE)
   ,.PL_EQ_ADAPT_DISABLE_COEFF_CHECK(PL_EQ_ADAPT_DISABLE_COEFF_CHECK)
   ,.PL_EQ_ADAPT_DISABLE_PRESET_CHECK(PL_EQ_ADAPT_DISABLE_PRESET_CHECK)
   ,.PL_EQ_DEFAULT_TX_PRESET(PL_EQ_DEFAULT_TX_PRESET)
   ,.PL_EQ_DEFAULT_RX_PRESET_HINT(PL_EQ_DEFAULT_RX_PRESET_HINT)
   ,.PL_EQ_RX_ADAPT_EQ_PHASE0(PL_EQ_RX_ADAPT_EQ_PHASE0)
   ,.PL_EQ_RX_ADAPT_EQ_PHASE1(PL_EQ_RX_ADAPT_EQ_PHASE1)
   ,.PL_EQ_DISABLE_MISMATCH_CHECK(PL_EQ_DISABLE_MISMATCH_CHECK)
   ,.PL_RX_L0S_EXIT_TO_RECOVERY(PL_RX_L0S_EXIT_TO_RECOVERY)
   ,.PL_EQ_TX_8G_EQ_TS2_ENABLE(PL_EQ_TX_8G_EQ_TS2_ENABLE)
   ,.PL_DISABLE_AUTO_EQ_SPEED_CHANGE_TO_GEN4(PL_DISABLE_AUTO_EQ_SPEED_CHANGE_TO_GEN4)
   ,.PL_DISABLE_AUTO_EQ_SPEED_CHANGE_TO_GEN3(PL_DISABLE_AUTO_EQ_SPEED_CHANGE_TO_GEN3)
   ,.PL_DISABLE_AUTO_SPEED_CHANGE_TO_GEN2(PL_DISABLE_AUTO_SPEED_CHANGE_TO_GEN2)
   ,.PL_DESKEW_ON_SKIP_IN_GEN12(PL_DESKEW_ON_SKIP_IN_GEN12)
   ,.PL_INFER_EI_DISABLE_REC_RC(PL_INFER_EI_DISABLE_REC_RC)
   ,.PL_INFER_EI_DISABLE_REC_SPD(PL_INFER_EI_DISABLE_REC_SPD)
   ,.PL_INFER_EI_DISABLE_LPBK_ACTIVE(PL_INFER_EI_DISABLE_LPBK_ACTIVE)
   ,.PL_RX_ADAPT_TIMER_RRL_GEN3(PL_RX_ADAPT_TIMER_RRL_GEN3)
   ,.PL_RX_ADAPT_TIMER_RRL_CLOBBER_TX_TS(PL_RX_ADAPT_TIMER_RRL_CLOBBER_TX_TS)
   ,.PL_RX_ADAPT_TIMER_RRL_GEN4(PL_RX_ADAPT_TIMER_RRL_GEN4)
   ,.PL_RX_ADAPT_TIMER_CLWS_GEN3(PL_RX_ADAPT_TIMER_CLWS_GEN3)
   ,.PL_RX_ADAPT_TIMER_CLWS_CLOBBER_TX_TS(PL_RX_ADAPT_TIMER_CLWS_CLOBBER_TX_TS)
   ,.PL_RX_ADAPT_TIMER_CLWS_GEN4(PL_RX_ADAPT_TIMER_CLWS_GEN4)
   ,.PL_DISABLE_LANE_REVERSAL(PL_DISABLE_LANE_REVERSAL)
   ,.PL_CFG_STATE_ROBUSTNESS_ENABLE(PL_CFG_STATE_ROBUSTNESS_ENABLE)
   ,.PL_REDO_EQ_SOURCE_SELECT(PL_REDO_EQ_SOURCE_SELECT)
   ,.PL_DEEMPH_SOURCE_SELECT(PL_DEEMPH_SOURCE_SELECT)
   ,.PL_EXIT_LOOPBACK_ON_EI_ENTRY(PL_EXIT_LOOPBACK_ON_EI_ENTRY)
   ,.PL_QUIESCE_GUARANTEE_DISABLE(PL_QUIESCE_GUARANTEE_DISABLE)
   ,.PL_SRIS_ENABLE(PL_SRIS_ENABLE)
   ,.PL_SRIS_SKPOS_GEN_SPD_VEC(PL_SRIS_SKPOS_GEN_SPD_VEC)
   ,.PL_SRIS_SKPOS_REC_SPD_VEC(PL_SRIS_SKPOS_REC_SPD_VEC)
  // synthesis translate_off
   ,.PL_SIM_FAST_LINK_TRAINING(PL_SIM_FAST_LINK_TRAINING)
  // synthesis translate_on
   ,.PL_USER_SPARE(PL_USER_SPARE)
   ,.LL_ACK_TIMEOUT_EN(LL_ACK_TIMEOUT_EN)
   ,.LL_ACK_TIMEOUT(LL_ACK_TIMEOUT)
   ,.LL_ACK_TIMEOUT_FUNC(LL_ACK_TIMEOUT_FUNC)
   ,.LL_REPLAY_TIMEOUT_EN(LL_REPLAY_TIMEOUT_EN)
   ,.LL_REPLAY_TIMEOUT(LL_REPLAY_TIMEOUT)
   ,.LL_REPLAY_TIMEOUT_FUNC(LL_REPLAY_TIMEOUT_FUNC)
   ,.LL_REPLAY_TO_RAM_PIPELINE(LL_REPLAY_TO_RAM_PIPELINE)
   ,.LL_REPLAY_FROM_RAM_PIPELINE(LL_REPLAY_FROM_RAM_PIPELINE)
   ,.LL_DISABLE_SCHED_TX_NAK(LL_DISABLE_SCHED_TX_NAK)
   ,.LL_TX_TLP_PARITY_CHK(LL_TX_TLP_PARITY_CHK)
   ,.LL_RX_TLP_PARITY_GEN(LL_RX_TLP_PARITY_GEN)
   ,.LL_USER_SPARE(LL_USER_SPARE)
   ,.IS_SWITCH_PORT(IS_SWITCH_PORT)
   ,.CFG_BYPASS_MODE_ENABLE(CFG_BYPASS_MODE_ENABLE)
   ,.TL_PF_ENABLE_REG(TL_PF_ENABLE_REG)
   ,.TL_CREDITS_CD(TL_CREDITS_CD)
   ,.TL_CREDITS_CH(TL_CREDITS_CH)
   ,.TL_COMPLETION_RAM_SIZE(TL_COMPLETION_RAM_SIZE)
   ,.TL_COMPLETION_RAM_NUM_TLPS(TL_COMPLETION_RAM_NUM_TLPS)
   ,.TL_CREDITS_NPD(TL_CREDITS_NPD)
   ,.TL_CREDITS_NPH(TL_CREDITS_NPH)
   ,.TL_CREDITS_PD(TL_CREDITS_PD)
   ,.TL_CREDITS_PH(TL_CREDITS_PH)
   ,.TL_RX_COMPLETION_TO_RAM_WRITE_PIPELINE(TL_RX_COMPLETION_TO_RAM_WRITE_PIPELINE)
   ,.TL_RX_COMPLETION_TO_RAM_READ_PIPELINE(TL_RX_COMPLETION_TO_RAM_READ_PIPELINE)
   ,.TL_RX_COMPLETION_FROM_RAM_READ_PIPELINE(TL_RX_COMPLETION_FROM_RAM_READ_PIPELINE)
   ,.TL_POSTED_RAM_SIZE(TL_POSTED_RAM_SIZE)
   ,.TL_RX_POSTED_TO_RAM_WRITE_PIPELINE(TL_RX_POSTED_TO_RAM_WRITE_PIPELINE)
   ,.TL_RX_POSTED_TO_RAM_READ_PIPELINE(TL_RX_POSTED_TO_RAM_READ_PIPELINE)
   ,.TL_RX_POSTED_FROM_RAM_READ_PIPELINE(TL_RX_POSTED_FROM_RAM_READ_PIPELINE)
   ,.TL_TX_MUX_STRICT_PRIORITY(TL_TX_MUX_STRICT_PRIORITY)
   ,.TL_TX_TLP_STRADDLE_ENABLE(TL_TX_TLP_STRADDLE_ENABLE)
   ,.TL_TX_TLP_TERMINATE_PARITY(TL_TX_TLP_TERMINATE_PARITY)
   ,.TL_FC_UPDATE_MIN_INTERVAL_TLP_COUNT(TL_FC_UPDATE_MIN_INTERVAL_TLP_COUNT)
   ,.TL_FC_UPDATE_MIN_INTERVAL_TIME(TL_FC_UPDATE_MIN_INTERVAL_TIME)
   ,.TL_USER_SPARE(TL_USER_SPARE)
   ,.PF0_CLASS_CODE(PF0_CLASS_CODE)
   ,.PF1_CLASS_CODE(PF1_CLASS_CODE)
   ,.PF2_CLASS_CODE(PF2_CLASS_CODE)
   ,.PF3_CLASS_CODE(PF3_CLASS_CODE)
   ,.PF0_INTERRUPT_PIN(PF0_INTERRUPT_PIN)
   ,.PF1_INTERRUPT_PIN(PF1_INTERRUPT_PIN)
   ,.PF2_INTERRUPT_PIN(PF2_INTERRUPT_PIN)
   ,.PF3_INTERRUPT_PIN(PF3_INTERRUPT_PIN)
   ,.PF0_CAPABILITY_POINTER(PF0_CAPABILITY_POINTER)
   ,.PF1_CAPABILITY_POINTER(PF1_CAPABILITY_POINTER)
   ,.PF2_CAPABILITY_POINTER(PF2_CAPABILITY_POINTER)
   ,.PF3_CAPABILITY_POINTER(PF3_CAPABILITY_POINTER)
   ,.VF0_CAPABILITY_POINTER(VF0_CAPABILITY_POINTER)
   ,.LEGACY_CFG_EXTEND_INTERFACE_ENABLE(LEGACY_CFG_EXTEND_INTERFACE_ENABLE)
   ,.EXTENDED_CFG_EXTEND_INTERFACE_ENABLE(EXTENDED_CFG_EXTEND_INTERFACE_ENABLE)
   ,.TL2CFG_IF_PARITY_CHK(TL2CFG_IF_PARITY_CHK)
   ,.HEADER_TYPE_OVERRIDE(HEADER_TYPE_OVERRIDE)
   ,.PF0_BAR0_CONTROL(PF0_BAR0_CONTROL)
   ,.PF1_BAR0_CONTROL(PF1_BAR0_CONTROL)
   ,.PF2_BAR0_CONTROL(PF2_BAR0_CONTROL)
   ,.PF3_BAR0_CONTROL(PF3_BAR0_CONTROL)
   ,.PF0_BAR0_APERTURE_SIZE(PF0_BAR0_APERTURE_SIZE)
   ,.PF1_BAR0_APERTURE_SIZE(PF1_BAR0_APERTURE_SIZE)
   ,.PF2_BAR0_APERTURE_SIZE(PF2_BAR0_APERTURE_SIZE)
   ,.PF3_BAR0_APERTURE_SIZE(PF3_BAR0_APERTURE_SIZE)
   ,.PF0_BAR1_CONTROL(PF0_BAR1_CONTROL)
   ,.PF1_BAR1_CONTROL(PF1_BAR1_CONTROL)
   ,.PF2_BAR1_CONTROL(PF2_BAR1_CONTROL)
   ,.PF3_BAR1_CONTROL(PF3_BAR1_CONTROL)
   ,.PF0_BAR1_APERTURE_SIZE(PF0_BAR1_APERTURE_SIZE)
   ,.PF1_BAR1_APERTURE_SIZE(PF1_BAR1_APERTURE_SIZE)
   ,.PF2_BAR1_APERTURE_SIZE(PF2_BAR1_APERTURE_SIZE)
   ,.PF3_BAR1_APERTURE_SIZE(PF3_BAR1_APERTURE_SIZE)
   ,.PF0_BAR2_CONTROL(PF0_BAR2_CONTROL)
   ,.PF1_BAR2_CONTROL(PF1_BAR2_CONTROL)
   ,.PF2_BAR2_CONTROL(PF2_BAR2_CONTROL)
   ,.PF3_BAR2_CONTROL(PF3_BAR2_CONTROL)
   ,.PF0_BAR2_APERTURE_SIZE(PF0_BAR2_APERTURE_SIZE)
   ,.PF1_BAR2_APERTURE_SIZE(PF1_BAR2_APERTURE_SIZE)
   ,.PF2_BAR2_APERTURE_SIZE(PF2_BAR2_APERTURE_SIZE)
   ,.PF3_BAR2_APERTURE_SIZE(PF3_BAR2_APERTURE_SIZE)
   ,.PF0_BAR3_CONTROL(PF0_BAR3_CONTROL)
   ,.PF1_BAR3_CONTROL(PF1_BAR3_CONTROL)
   ,.PF2_BAR3_CONTROL(PF2_BAR3_CONTROL)
   ,.PF3_BAR3_CONTROL(PF3_BAR3_CONTROL)
   ,.PF0_BAR3_APERTURE_SIZE(PF0_BAR3_APERTURE_SIZE)
   ,.PF1_BAR3_APERTURE_SIZE(PF1_BAR3_APERTURE_SIZE)
   ,.PF2_BAR3_APERTURE_SIZE(PF2_BAR3_APERTURE_SIZE)
   ,.PF3_BAR3_APERTURE_SIZE(PF3_BAR3_APERTURE_SIZE)
   ,.PF0_BAR4_CONTROL(PF0_BAR4_CONTROL)
   ,.PF1_BAR4_CONTROL(PF1_BAR4_CONTROL)
   ,.PF2_BAR4_CONTROL(PF2_BAR4_CONTROL)
   ,.PF3_BAR4_CONTROL(PF3_BAR4_CONTROL)
   ,.PF0_BAR4_APERTURE_SIZE(PF0_BAR4_APERTURE_SIZE)
   ,.PF1_BAR4_APERTURE_SIZE(PF1_BAR4_APERTURE_SIZE)
   ,.PF2_BAR4_APERTURE_SIZE(PF2_BAR4_APERTURE_SIZE)
   ,.PF3_BAR4_APERTURE_SIZE(PF3_BAR4_APERTURE_SIZE)
   ,.PF0_BAR5_CONTROL(PF0_BAR5_CONTROL)
   ,.PF1_BAR5_CONTROL(PF1_BAR5_CONTROL)
   ,.PF2_BAR5_CONTROL(PF2_BAR5_CONTROL)
   ,.PF3_BAR5_CONTROL(PF3_BAR5_CONTROL)
   ,.PF0_BAR5_APERTURE_SIZE(PF0_BAR5_APERTURE_SIZE)
   ,.PF1_BAR5_APERTURE_SIZE(PF1_BAR5_APERTURE_SIZE)
   ,.PF2_BAR5_APERTURE_SIZE(PF2_BAR5_APERTURE_SIZE)
   ,.PF3_BAR5_APERTURE_SIZE(PF3_BAR5_APERTURE_SIZE)
   ,.PF0_EXPANSION_ROM_ENABLE(PF0_EXPANSION_ROM_ENABLE)
   ,.PF1_EXPANSION_ROM_ENABLE(PF1_EXPANSION_ROM_ENABLE)
   ,.PF2_EXPANSION_ROM_ENABLE(PF2_EXPANSION_ROM_ENABLE)
   ,.PF3_EXPANSION_ROM_ENABLE(PF3_EXPANSION_ROM_ENABLE)
   ,.PF0_EXPANSION_ROM_APERTURE_SIZE(PF0_EXPANSION_ROM_APERTURE_SIZE)
   ,.PF1_EXPANSION_ROM_APERTURE_SIZE(PF1_EXPANSION_ROM_APERTURE_SIZE)
   ,.PF2_EXPANSION_ROM_APERTURE_SIZE(PF2_EXPANSION_ROM_APERTURE_SIZE)
   ,.PF3_EXPANSION_ROM_APERTURE_SIZE(PF3_EXPANSION_ROM_APERTURE_SIZE)
   ,.PF0_PCIE_CAP_NEXTPTR(PF0_PCIE_CAP_NEXTPTR)
   ,.PF1_PCIE_CAP_NEXTPTR(PF1_PCIE_CAP_NEXTPTR)
   ,.PF2_PCIE_CAP_NEXTPTR(PF2_PCIE_CAP_NEXTPTR)
   ,.PF3_PCIE_CAP_NEXTPTR(PF3_PCIE_CAP_NEXTPTR)
   ,.VFG0_PCIE_CAP_NEXTPTR(VFG0_PCIE_CAP_NEXTPTR)
   ,.VFG1_PCIE_CAP_NEXTPTR(VFG1_PCIE_CAP_NEXTPTR)
   ,.VFG2_PCIE_CAP_NEXTPTR(VFG2_PCIE_CAP_NEXTPTR)
   ,.VFG3_PCIE_CAP_NEXTPTR(VFG3_PCIE_CAP_NEXTPTR)
   ,.PF0_DEV_CAP_MAX_PAYLOAD_SIZE(PF0_DEV_CAP_MAX_PAYLOAD_SIZE)
   ,.PF1_DEV_CAP_MAX_PAYLOAD_SIZE(PF1_DEV_CAP_MAX_PAYLOAD_SIZE)
   ,.PF2_DEV_CAP_MAX_PAYLOAD_SIZE(PF2_DEV_CAP_MAX_PAYLOAD_SIZE)
   ,.PF3_DEV_CAP_MAX_PAYLOAD_SIZE(PF3_DEV_CAP_MAX_PAYLOAD_SIZE)
   ,.PF0_DEV_CAP_EXT_TAG_SUPPORTED(PF0_DEV_CAP_EXT_TAG_SUPPORTED)
   ,.PF0_DEV_CAP_ENDPOINT_L0S_LATENCY(PF0_DEV_CAP_ENDPOINT_L0S_LATENCY)
   ,.PF0_DEV_CAP_ENDPOINT_L1_LATENCY(PF0_DEV_CAP_ENDPOINT_L1_LATENCY)
   ,.PF0_DEV_CAP_FUNCTION_LEVEL_RESET_CAPABLE(PF0_DEV_CAP_FUNCTION_LEVEL_RESET_CAPABLE)
   ,.PF0_LINK_CAP_ASPM_SUPPORT(PF0_LINK_CAP_ASPM_SUPPORT)
   ,.PF0_LINK_CONTROL_RCB(PF0_LINK_CONTROL_RCB)
   ,.PF0_LINK_STATUS_SLOT_CLOCK_CONFIG(PF0_LINK_STATUS_SLOT_CLOCK_CONFIG)
   ,.PF0_LINK_CAP_L0S_EXIT_LATENCY_COMCLK_GEN1(PF0_LINK_CAP_L0S_EXIT_LATENCY_COMCLK_GEN1)
   ,.PF0_LINK_CAP_L0S_EXIT_LATENCY_COMCLK_GEN2(PF0_LINK_CAP_L0S_EXIT_LATENCY_COMCLK_GEN2)
   ,.PF0_LINK_CAP_L0S_EXIT_LATENCY_COMCLK_GEN3(PF0_LINK_CAP_L0S_EXIT_LATENCY_COMCLK_GEN3)
   ,.PF0_LINK_CAP_L0S_EXIT_LATENCY_COMCLK_GEN4(PF0_LINK_CAP_L0S_EXIT_LATENCY_COMCLK_GEN4)
   ,.PF0_LINK_CAP_L0S_EXIT_LATENCY_GEN1(PF0_LINK_CAP_L0S_EXIT_LATENCY_GEN1)
   ,.PF0_LINK_CAP_L0S_EXIT_LATENCY_GEN2(PF0_LINK_CAP_L0S_EXIT_LATENCY_GEN2)
   ,.PF0_LINK_CAP_L0S_EXIT_LATENCY_GEN3(PF0_LINK_CAP_L0S_EXIT_LATENCY_GEN3)
   ,.PF0_LINK_CAP_L0S_EXIT_LATENCY_GEN4(PF0_LINK_CAP_L0S_EXIT_LATENCY_GEN4)
   ,.PF0_LINK_CAP_L1_EXIT_LATENCY_COMCLK_GEN1(PF0_LINK_CAP_L1_EXIT_LATENCY_COMCLK_GEN1)
   ,.PF0_LINK_CAP_L1_EXIT_LATENCY_COMCLK_GEN2(PF0_LINK_CAP_L1_EXIT_LATENCY_COMCLK_GEN2)
   ,.PF0_LINK_CAP_L1_EXIT_LATENCY_COMCLK_GEN3(PF0_LINK_CAP_L1_EXIT_LATENCY_COMCLK_GEN3)
   ,.PF0_LINK_CAP_L1_EXIT_LATENCY_COMCLK_GEN4(PF0_LINK_CAP_L1_EXIT_LATENCY_COMCLK_GEN4)
   ,.PF0_LINK_CAP_L1_EXIT_LATENCY_GEN1(PF0_LINK_CAP_L1_EXIT_LATENCY_GEN1)
   ,.PF0_LINK_CAP_L1_EXIT_LATENCY_GEN2(PF0_LINK_CAP_L1_EXIT_LATENCY_GEN2)
   ,.PF0_LINK_CAP_L1_EXIT_LATENCY_GEN3(PF0_LINK_CAP_L1_EXIT_LATENCY_GEN3)
   ,.PF0_LINK_CAP_L1_EXIT_LATENCY_GEN4(PF0_LINK_CAP_L1_EXIT_LATENCY_GEN4)
   ,.PF0_DEV_CAP2_CPL_TIMEOUT_DISABLE(PF0_DEV_CAP2_CPL_TIMEOUT_DISABLE)
   ,.PF0_DEV_CAP2_32B_ATOMIC_COMPLETER_SUPPORT(PF0_DEV_CAP2_32B_ATOMIC_COMPLETER_SUPPORT)
   ,.PF0_DEV_CAP2_64B_ATOMIC_COMPLETER_SUPPORT(PF0_DEV_CAP2_64B_ATOMIC_COMPLETER_SUPPORT)
   ,.PF0_DEV_CAP2_128B_CAS_ATOMIC_COMPLETER_SUPPORT(PF0_DEV_CAP2_128B_CAS_ATOMIC_COMPLETER_SUPPORT)
   ,.PF0_DEV_CAP2_LTR_SUPPORT(PF0_DEV_CAP2_LTR_SUPPORT)
   ,.PF0_DEV_CAP2_TPH_COMPLETER_SUPPORT(PF0_DEV_CAP2_TPH_COMPLETER_SUPPORT)
   ,.PF0_DEV_CAP2_OBFF_SUPPORT(PF0_DEV_CAP2_OBFF_SUPPORT)
   ,.PF0_DEV_CAP2_ARI_FORWARD_ENABLE(PF0_DEV_CAP2_ARI_FORWARD_ENABLE)
   ,.PF0_MSI_CAP_NEXTPTR(PF0_MSI_CAP_NEXTPTR)
   ,.PF1_MSI_CAP_NEXTPTR(PF1_MSI_CAP_NEXTPTR)
   ,.PF2_MSI_CAP_NEXTPTR(PF2_MSI_CAP_NEXTPTR)
   ,.PF3_MSI_CAP_NEXTPTR(PF3_MSI_CAP_NEXTPTR)
   ,.PF0_MSI_CAP_PERVECMASKCAP(PF0_MSI_CAP_PERVECMASKCAP)
   ,.PF1_MSI_CAP_PERVECMASKCAP(PF1_MSI_CAP_PERVECMASKCAP)
   ,.PF2_MSI_CAP_PERVECMASKCAP(PF2_MSI_CAP_PERVECMASKCAP)
   ,.PF3_MSI_CAP_PERVECMASKCAP(PF3_MSI_CAP_PERVECMASKCAP)
   ,.PF0_MSI_CAP_MULTIMSGCAP(PF0_MSI_CAP_MULTIMSGCAP)
   ,.PF1_MSI_CAP_MULTIMSGCAP(PF1_MSI_CAP_MULTIMSGCAP)
   ,.PF2_MSI_CAP_MULTIMSGCAP(PF2_MSI_CAP_MULTIMSGCAP)
   ,.PF3_MSI_CAP_MULTIMSGCAP(PF3_MSI_CAP_MULTIMSGCAP)
   ,.PF0_MSIX_CAP_NEXTPTR(PF0_MSIX_CAP_NEXTPTR)
   ,.PF1_MSIX_CAP_NEXTPTR(PF1_MSIX_CAP_NEXTPTR)
   ,.PF2_MSIX_CAP_NEXTPTR(PF2_MSIX_CAP_NEXTPTR)
   ,.PF3_MSIX_CAP_NEXTPTR(PF3_MSIX_CAP_NEXTPTR)
   ,.VFG0_MSIX_CAP_NEXTPTR(VFG0_MSIX_CAP_NEXTPTR)
   ,.VFG1_MSIX_CAP_NEXTPTR(VFG1_MSIX_CAP_NEXTPTR)
   ,.VFG2_MSIX_CAP_NEXTPTR(VFG2_MSIX_CAP_NEXTPTR)
   ,.VFG3_MSIX_CAP_NEXTPTR(VFG3_MSIX_CAP_NEXTPTR)
   ,.PF0_MSIX_CAP_PBA_BIR(PF0_MSIX_CAP_PBA_BIR)
   ,.PF1_MSIX_CAP_PBA_BIR(PF1_MSIX_CAP_PBA_BIR)
   ,.PF2_MSIX_CAP_PBA_BIR(PF2_MSIX_CAP_PBA_BIR)
   ,.PF3_MSIX_CAP_PBA_BIR(PF3_MSIX_CAP_PBA_BIR)
   ,.VFG0_MSIX_CAP_PBA_BIR(VFG0_MSIX_CAP_PBA_BIR)
   ,.VFG1_MSIX_CAP_PBA_BIR(VFG1_MSIX_CAP_PBA_BIR)
   ,.VFG2_MSIX_CAP_PBA_BIR(VFG2_MSIX_CAP_PBA_BIR)
   ,.VFG3_MSIX_CAP_PBA_BIR(VFG3_MSIX_CAP_PBA_BIR)
   ,.PF0_MSIX_CAP_PBA_OFFSET ({3'b000,PF0_MSIX_CAP_PBA_OFFSET[28:3]})
   ,.PF1_MSIX_CAP_PBA_OFFSET ({3'b000,PF1_MSIX_CAP_PBA_OFFSET[28:3]})
   ,.PF2_MSIX_CAP_PBA_OFFSET ({3'b000,PF2_MSIX_CAP_PBA_OFFSET[28:3]})
   ,.PF3_MSIX_CAP_PBA_OFFSET ({3'b000,PF3_MSIX_CAP_PBA_OFFSET[28:3]})
   ,.VFG0_MSIX_CAP_PBA_OFFSET({3'b000,VFG0_MSIX_CAP_PBA_OFFSET[28:3]})
   ,.VFG1_MSIX_CAP_PBA_OFFSET({3'b000,VFG1_MSIX_CAP_PBA_OFFSET[28:3]})
   ,.VFG2_MSIX_CAP_PBA_OFFSET({3'b000,VFG2_MSIX_CAP_PBA_OFFSET[28:3]})
   ,.VFG3_MSIX_CAP_PBA_OFFSET({3'b000,VFG3_MSIX_CAP_PBA_OFFSET[28:3]})
   ,.PF0_MSIX_CAP_TABLE_BIR(PF0_MSIX_CAP_TABLE_BIR)
   ,.PF1_MSIX_CAP_TABLE_BIR(PF1_MSIX_CAP_TABLE_BIR)
   ,.PF2_MSIX_CAP_TABLE_BIR(PF2_MSIX_CAP_TABLE_BIR)
   ,.PF3_MSIX_CAP_TABLE_BIR(PF3_MSIX_CAP_TABLE_BIR)
   ,.VFG0_MSIX_CAP_TABLE_BIR(VFG0_MSIX_CAP_TABLE_BIR)
   ,.VFG1_MSIX_CAP_TABLE_BIR(VFG1_MSIX_CAP_TABLE_BIR)
   ,.VFG2_MSIX_CAP_TABLE_BIR(VFG2_MSIX_CAP_TABLE_BIR)
   ,.VFG3_MSIX_CAP_TABLE_BIR(VFG3_MSIX_CAP_TABLE_BIR)
   ,.PF0_MSIX_CAP_TABLE_OFFSET ({3'b000,PF0_MSIX_CAP_TABLE_OFFSET[28:3]})
   ,.PF1_MSIX_CAP_TABLE_OFFSET ({3'b000,PF1_MSIX_CAP_TABLE_OFFSET[28:3]})
   ,.PF2_MSIX_CAP_TABLE_OFFSET ({3'b000,PF2_MSIX_CAP_TABLE_OFFSET[28:3]})
   ,.PF3_MSIX_CAP_TABLE_OFFSET ({3'b000,PF3_MSIX_CAP_TABLE_OFFSET[28:3]})
   ,.VFG0_MSIX_CAP_TABLE_OFFSET({3'b000,VFG0_MSIX_CAP_TABLE_OFFSET[28:3]})
   ,.VFG1_MSIX_CAP_TABLE_OFFSET({3'b000,VFG1_MSIX_CAP_TABLE_OFFSET[28:3]})
   ,.VFG2_MSIX_CAP_TABLE_OFFSET({3'b000,VFG2_MSIX_CAP_TABLE_OFFSET[28:3]})
   ,.VFG3_MSIX_CAP_TABLE_OFFSET({3'b000,VFG3_MSIX_CAP_TABLE_OFFSET[28:3]})
   ,.PF0_MSIX_CAP_TABLE_SIZE(PF0_MSIX_CAP_TABLE_SIZE)
   ,.PF1_MSIX_CAP_TABLE_SIZE(PF1_MSIX_CAP_TABLE_SIZE)
   ,.PF2_MSIX_CAP_TABLE_SIZE(PF2_MSIX_CAP_TABLE_SIZE)
   ,.PF3_MSIX_CAP_TABLE_SIZE(PF3_MSIX_CAP_TABLE_SIZE)
   ,.VFG0_MSIX_CAP_TABLE_SIZE(VFG0_MSIX_CAP_TABLE_SIZE)
   ,.VFG1_MSIX_CAP_TABLE_SIZE(VFG1_MSIX_CAP_TABLE_SIZE)
   ,.VFG2_MSIX_CAP_TABLE_SIZE(VFG2_MSIX_CAP_TABLE_SIZE)
   ,.VFG3_MSIX_CAP_TABLE_SIZE(VFG3_MSIX_CAP_TABLE_SIZE)
   ,.PF0_MSIX_VECTOR_COUNT(PF0_MSIX_VECTOR_COUNT)
   ,.PF0_PM_CAP_ID(PF0_PM_CAP_ID)
   ,.PF0_PM_CAP_NEXTPTR(PF0_PM_CAP_NEXTPTR)
   ,.PF1_PM_CAP_NEXTPTR(PF1_PM_CAP_NEXTPTR)
   ,.PF2_PM_CAP_NEXTPTR(PF2_PM_CAP_NEXTPTR)
   ,.PF3_PM_CAP_NEXTPTR(PF3_PM_CAP_NEXTPTR)
   ,.PF0_PM_CAP_PMESUPPORT_D3HOT(PF0_PM_CAP_PMESUPPORT_D3HOT)
   ,.PF0_PM_CAP_PMESUPPORT_D1(PF0_PM_CAP_PMESUPPORT_D1)
   ,.PF0_PM_CAP_PMESUPPORT_D0(PF0_PM_CAP_PMESUPPORT_D0)
   ,.PF0_PM_CAP_SUPP_D1_STATE(PF0_PM_CAP_SUPP_D1_STATE)
   ,.PF0_PM_CAP_VER_ID(PF0_PM_CAP_VER_ID)
   ,.PF0_PM_CSR_NOSOFTRESET(PF0_PM_CSR_NOSOFTRESET)
   ,.PM_ENABLE_L23_ENTRY(PM_ENABLE_L23_ENTRY)
   ,.DNSTREAM_LINK_NUM(DNSTREAM_LINK_NUM)
   ,.AUTO_FLR_RESPONSE(AUTO_FLR_RESPONSE)
   ,.PF0_DSN_CAP_NEXTPTR(PF0_DSN_CAP_NEXTPTR)
   ,.PF1_DSN_CAP_NEXTPTR(PF1_DSN_CAP_NEXTPTR)
   ,.PF2_DSN_CAP_NEXTPTR(PF2_DSN_CAP_NEXTPTR)
   ,.PF3_DSN_CAP_NEXTPTR(PF3_DSN_CAP_NEXTPTR)
   ,.DSN_CAP_ENABLE(DSN_CAP_ENABLE)
   ,.PF0_VC_CAP_VER(PF0_VC_CAP_VER)
   ,.PF0_VC_CAP_NEXTPTR(PF0_VC_CAP_NEXTPTR)
   ,.PF0_VC_CAP_ENABLE(PF0_VC_CAP_ENABLE)
   ,.PF0_SECONDARY_PCIE_CAP_NEXTPTR(PF0_SECONDARY_PCIE_CAP_NEXTPTR)
   ,.PF0_AER_CAP_NEXTPTR(PF0_AER_CAP_NEXTPTR)
   ,.PF1_AER_CAP_NEXTPTR(PF1_AER_CAP_NEXTPTR)
   ,.PF2_AER_CAP_NEXTPTR(PF2_AER_CAP_NEXTPTR)
   ,.PF3_AER_CAP_NEXTPTR(PF3_AER_CAP_NEXTPTR)
   ,.PF0_AER_CAP_ECRC_GEN_AND_CHECK_CAPABLE(PF0_AER_CAP_ECRC_GEN_AND_CHECK_CAPABLE)
   ,.ARI_CAP_ENABLE(ARI_CAP_ENABLE)
   ,.PF0_ARI_CAP_NEXTPTR(PF0_ARI_CAP_NEXTPTR)
   ,.PF1_ARI_CAP_NEXTPTR(PF1_ARI_CAP_NEXTPTR)
   ,.PF2_ARI_CAP_NEXTPTR(PF2_ARI_CAP_NEXTPTR)
   ,.PF3_ARI_CAP_NEXTPTR(PF3_ARI_CAP_NEXTPTR)
   ,.VFG0_ARI_CAP_NEXTPTR(VFG0_ARI_CAP_NEXTPTR)
   ,.VFG1_ARI_CAP_NEXTPTR(VFG1_ARI_CAP_NEXTPTR)
   ,.VFG2_ARI_CAP_NEXTPTR(VFG2_ARI_CAP_NEXTPTR)
   ,.VFG3_ARI_CAP_NEXTPTR(VFG3_ARI_CAP_NEXTPTR)
   ,.PF0_ARI_CAP_VER(PF0_ARI_CAP_VER)
   ,.PF0_ARI_CAP_NEXT_FUNC(PF0_ARI_CAP_NEXT_FUNC)
   ,.PF1_ARI_CAP_NEXT_FUNC(PF1_ARI_CAP_NEXT_FUNC)
   ,.PF2_ARI_CAP_NEXT_FUNC(PF2_ARI_CAP_NEXT_FUNC)
   ,.PF3_ARI_CAP_NEXT_FUNC(PF3_ARI_CAP_NEXT_FUNC)
   ,.PF0_LTR_CAP_NEXTPTR(PF0_LTR_CAP_NEXTPTR)
   ,.PF0_LTR_CAP_VER(PF0_LTR_CAP_VER)
   ,.PF0_LTR_CAP_MAX_SNOOP_LAT(PF0_LTR_CAP_MAX_SNOOP_LAT)
   ,.PF0_LTR_CAP_MAX_NOSNOOP_LAT(PF0_LTR_CAP_MAX_NOSNOOP_LAT)
   ,.LTR_TX_MESSAGE_ON_LTR_ENABLE(LTR_TX_MESSAGE_ON_LTR_ENABLE)
   ,.LTR_TX_MESSAGE_ON_FUNC_POWER_STATE_CHANGE(LTR_TX_MESSAGE_ON_FUNC_POWER_STATE_CHANGE)
   ,.LTR_TX_MESSAGE_MINIMUM_INTERVAL(LTR_TX_MESSAGE_MINIMUM_INTERVAL)
   ,.SRIOV_CAP_ENABLE(SRIOV_CAP_ENABLE)
   ,.PF0_SRIOV_CAP_NEXTPTR(PF0_SRIOV_CAP_NEXTPTR)
   ,.PF1_SRIOV_CAP_NEXTPTR(PF1_SRIOV_CAP_NEXTPTR)
   ,.PF2_SRIOV_CAP_NEXTPTR(PF2_SRIOV_CAP_NEXTPTR)
   ,.PF3_SRIOV_CAP_NEXTPTR(PF3_SRIOV_CAP_NEXTPTR)
   ,.PF0_SRIOV_CAP_VER(PF0_SRIOV_CAP_VER)
   ,.PF1_SRIOV_CAP_VER(PF1_SRIOV_CAP_VER)
   ,.PF2_SRIOV_CAP_VER(PF2_SRIOV_CAP_VER)
   ,.PF3_SRIOV_CAP_VER(PF3_SRIOV_CAP_VER)
   ,.PF0_SRIOV_ARI_CAPBL_HIER_PRESERVED(PF0_SRIOV_ARI_CAPBL_HIER_PRESERVED)
   ,.PF1_SRIOV_ARI_CAPBL_HIER_PRESERVED(PF1_SRIOV_ARI_CAPBL_HIER_PRESERVED)
   ,.PF2_SRIOV_ARI_CAPBL_HIER_PRESERVED(PF2_SRIOV_ARI_CAPBL_HIER_PRESERVED)
   ,.PF3_SRIOV_ARI_CAPBL_HIER_PRESERVED(PF3_SRIOV_ARI_CAPBL_HIER_PRESERVED)
   ,.PF0_SRIOV_CAP_INITIAL_VF(PF0_SRIOV_CAP_INITIAL_VF)
   ,.PF1_SRIOV_CAP_INITIAL_VF(PF1_SRIOV_CAP_INITIAL_VF)
   ,.PF2_SRIOV_CAP_INITIAL_VF(PF2_SRIOV_CAP_INITIAL_VF)
   ,.PF3_SRIOV_CAP_INITIAL_VF(PF3_SRIOV_CAP_INITIAL_VF)
   ,.PF0_SRIOV_CAP_TOTAL_VF(PF0_SRIOV_CAP_TOTAL_VF)
   ,.PF1_SRIOV_CAP_TOTAL_VF(PF1_SRIOV_CAP_TOTAL_VF)
   ,.PF2_SRIOV_CAP_TOTAL_VF(PF2_SRIOV_CAP_TOTAL_VF)
   ,.PF3_SRIOV_CAP_TOTAL_VF(PF3_SRIOV_CAP_TOTAL_VF)
   ,.PF0_SRIOV_FUNC_DEP_LINK(PF0_SRIOV_FUNC_DEP_LINK)
   ,.PF1_SRIOV_FUNC_DEP_LINK(PF1_SRIOV_FUNC_DEP_LINK)
   ,.PF2_SRIOV_FUNC_DEP_LINK(PF2_SRIOV_FUNC_DEP_LINK)
   ,.PF3_SRIOV_FUNC_DEP_LINK(PF3_SRIOV_FUNC_DEP_LINK)
   ,.PF0_SRIOV_FIRST_VF_OFFSET(PF0_SRIOV_FIRST_VF_OFFSET)
   ,.PF1_SRIOV_FIRST_VF_OFFSET(PF1_SRIOV_FIRST_VF_OFFSET)
   ,.PF2_SRIOV_FIRST_VF_OFFSET(PF2_SRIOV_FIRST_VF_OFFSET)
   ,.PF3_SRIOV_FIRST_VF_OFFSET(PF3_SRIOV_FIRST_VF_OFFSET)
   ,.PF0_SRIOV_VF_DEVICE_ID(PF0_SRIOV_VF_DEVICE_ID)
   ,.PF1_SRIOV_VF_DEVICE_ID(PF1_SRIOV_VF_DEVICE_ID)
   ,.PF2_SRIOV_VF_DEVICE_ID(PF2_SRIOV_VF_DEVICE_ID)
   ,.PF3_SRIOV_VF_DEVICE_ID(PF3_SRIOV_VF_DEVICE_ID)
   ,.PF0_SRIOV_SUPPORTED_PAGE_SIZE(PF0_SRIOV_SUPPORTED_PAGE_SIZE)
   ,.PF1_SRIOV_SUPPORTED_PAGE_SIZE(PF1_SRIOV_SUPPORTED_PAGE_SIZE)
   ,.PF2_SRIOV_SUPPORTED_PAGE_SIZE(PF2_SRIOV_SUPPORTED_PAGE_SIZE)
   ,.PF3_SRIOV_SUPPORTED_PAGE_SIZE(PF3_SRIOV_SUPPORTED_PAGE_SIZE)
   ,.PF0_SRIOV_BAR0_CONTROL(PF0_SRIOV_BAR0_CONTROL)
   ,.PF1_SRIOV_BAR0_CONTROL(PF1_SRIOV_BAR0_CONTROL)
   ,.PF2_SRIOV_BAR0_CONTROL(PF2_SRIOV_BAR0_CONTROL)
   ,.PF3_SRIOV_BAR0_CONTROL(PF3_SRIOV_BAR0_CONTROL)
   ,.PF0_SRIOV_BAR0_APERTURE_SIZE(PF0_SRIOV_BAR0_APERTURE_SIZE)
   ,.PF1_SRIOV_BAR0_APERTURE_SIZE(PF1_SRIOV_BAR0_APERTURE_SIZE)
   ,.PF2_SRIOV_BAR0_APERTURE_SIZE(PF2_SRIOV_BAR0_APERTURE_SIZE)
   ,.PF3_SRIOV_BAR0_APERTURE_SIZE(PF3_SRIOV_BAR0_APERTURE_SIZE)
   ,.PF0_SRIOV_BAR1_CONTROL(PF0_SRIOV_BAR1_CONTROL)
   ,.PF1_SRIOV_BAR1_CONTROL(PF1_SRIOV_BAR1_CONTROL)
   ,.PF2_SRIOV_BAR1_CONTROL(PF2_SRIOV_BAR1_CONTROL)
   ,.PF3_SRIOV_BAR1_CONTROL(PF3_SRIOV_BAR1_CONTROL)
   ,.PF0_SRIOV_BAR1_APERTURE_SIZE(PF0_SRIOV_BAR1_APERTURE_SIZE)
   ,.PF1_SRIOV_BAR1_APERTURE_SIZE(PF1_SRIOV_BAR1_APERTURE_SIZE)
   ,.PF2_SRIOV_BAR1_APERTURE_SIZE(PF2_SRIOV_BAR1_APERTURE_SIZE)
   ,.PF3_SRIOV_BAR1_APERTURE_SIZE(PF3_SRIOV_BAR1_APERTURE_SIZE)
   ,.PF0_SRIOV_BAR2_CONTROL(PF0_SRIOV_BAR2_CONTROL)
   ,.PF1_SRIOV_BAR2_CONTROL(PF1_SRIOV_BAR2_CONTROL)
   ,.PF2_SRIOV_BAR2_CONTROL(PF2_SRIOV_BAR2_CONTROL)
   ,.PF3_SRIOV_BAR2_CONTROL(PF3_SRIOV_BAR2_CONTROL)
   ,.PF0_SRIOV_BAR2_APERTURE_SIZE(PF0_SRIOV_BAR2_APERTURE_SIZE)
   ,.PF1_SRIOV_BAR2_APERTURE_SIZE(PF1_SRIOV_BAR2_APERTURE_SIZE)
   ,.PF2_SRIOV_BAR2_APERTURE_SIZE(PF2_SRIOV_BAR2_APERTURE_SIZE)
   ,.PF3_SRIOV_BAR2_APERTURE_SIZE(PF3_SRIOV_BAR2_APERTURE_SIZE)
   ,.PF0_SRIOV_BAR3_CONTROL(PF0_SRIOV_BAR3_CONTROL)
   ,.PF1_SRIOV_BAR3_CONTROL(PF1_SRIOV_BAR3_CONTROL)
   ,.PF2_SRIOV_BAR3_CONTROL(PF2_SRIOV_BAR3_CONTROL)
   ,.PF3_SRIOV_BAR3_CONTROL(PF3_SRIOV_BAR3_CONTROL)
   ,.PF0_SRIOV_BAR3_APERTURE_SIZE(PF0_SRIOV_BAR3_APERTURE_SIZE)
   ,.PF1_SRIOV_BAR3_APERTURE_SIZE(PF1_SRIOV_BAR3_APERTURE_SIZE)
   ,.PF2_SRIOV_BAR3_APERTURE_SIZE(PF2_SRIOV_BAR3_APERTURE_SIZE)
   ,.PF3_SRIOV_BAR3_APERTURE_SIZE(PF3_SRIOV_BAR3_APERTURE_SIZE)
   ,.PF0_SRIOV_BAR4_CONTROL(PF0_SRIOV_BAR4_CONTROL)
   ,.PF1_SRIOV_BAR4_CONTROL(PF1_SRIOV_BAR4_CONTROL)
   ,.PF2_SRIOV_BAR4_CONTROL(PF2_SRIOV_BAR4_CONTROL)
   ,.PF3_SRIOV_BAR4_CONTROL(PF3_SRIOV_BAR4_CONTROL)
   ,.PF0_SRIOV_BAR4_APERTURE_SIZE(PF0_SRIOV_BAR4_APERTURE_SIZE)
   ,.PF1_SRIOV_BAR4_APERTURE_SIZE(PF1_SRIOV_BAR4_APERTURE_SIZE)
   ,.PF2_SRIOV_BAR4_APERTURE_SIZE(PF2_SRIOV_BAR4_APERTURE_SIZE)
   ,.PF3_SRIOV_BAR4_APERTURE_SIZE(PF3_SRIOV_BAR4_APERTURE_SIZE)
   ,.PF0_SRIOV_BAR5_CONTROL(PF0_SRIOV_BAR5_CONTROL)
   ,.PF1_SRIOV_BAR5_CONTROL(PF1_SRIOV_BAR5_CONTROL)
   ,.PF2_SRIOV_BAR5_CONTROL(PF2_SRIOV_BAR5_CONTROL)
   ,.PF3_SRIOV_BAR5_CONTROL(PF3_SRIOV_BAR5_CONTROL)
   ,.PF0_SRIOV_BAR5_APERTURE_SIZE(PF0_SRIOV_BAR5_APERTURE_SIZE)
   ,.PF1_SRIOV_BAR5_APERTURE_SIZE(PF1_SRIOV_BAR5_APERTURE_SIZE)
   ,.PF2_SRIOV_BAR5_APERTURE_SIZE(PF2_SRIOV_BAR5_APERTURE_SIZE)
   ,.PF3_SRIOV_BAR5_APERTURE_SIZE(PF3_SRIOV_BAR5_APERTURE_SIZE)
   ,.PF0_TPHR_CAP_NEXTPTR(PF0_TPHR_CAP_NEXTPTR)
   ,.PF1_TPHR_CAP_NEXTPTR(PF1_TPHR_CAP_NEXTPTR)
   ,.PF2_TPHR_CAP_NEXTPTR(PF2_TPHR_CAP_NEXTPTR)
   ,.PF3_TPHR_CAP_NEXTPTR(PF3_TPHR_CAP_NEXTPTR)
   ,.VFG0_TPHR_CAP_NEXTPTR(VFG0_TPHR_CAP_NEXTPTR)
   ,.VFG1_TPHR_CAP_NEXTPTR(VFG1_TPHR_CAP_NEXTPTR)
   ,.VFG2_TPHR_CAP_NEXTPTR(VFG2_TPHR_CAP_NEXTPTR)
   ,.VFG3_TPHR_CAP_NEXTPTR(VFG3_TPHR_CAP_NEXTPTR)
   ,.PF0_TPHR_CAP_VER(PF0_TPHR_CAP_VER)
   ,.PF0_TPHR_CAP_INT_VEC_MODE(PF0_TPHR_CAP_INT_VEC_MODE)
   ,.PF0_TPHR_CAP_DEV_SPECIFIC_MODE(PF0_TPHR_CAP_DEV_SPECIFIC_MODE)
   ,.PF0_TPHR_CAP_ST_TABLE_LOC(PF0_TPHR_CAP_ST_TABLE_LOC)
   ,.PF0_TPHR_CAP_ST_TABLE_SIZE(PF0_TPHR_CAP_ST_TABLE_SIZE)
   ,.PF0_TPHR_CAP_ST_MODE_SEL(PF0_TPHR_CAP_ST_MODE_SEL)
   ,.PF1_TPHR_CAP_ST_MODE_SEL(PF1_TPHR_CAP_ST_MODE_SEL)
   ,.PF2_TPHR_CAP_ST_MODE_SEL(PF2_TPHR_CAP_ST_MODE_SEL)
   ,.PF3_TPHR_CAP_ST_MODE_SEL(PF3_TPHR_CAP_ST_MODE_SEL)
   ,.VFG0_TPHR_CAP_ST_MODE_SEL(VFG0_TPHR_CAP_ST_MODE_SEL)
   ,.VFG1_TPHR_CAP_ST_MODE_SEL(VFG1_TPHR_CAP_ST_MODE_SEL)
   ,.VFG2_TPHR_CAP_ST_MODE_SEL(VFG2_TPHR_CAP_ST_MODE_SEL)
   ,.VFG3_TPHR_CAP_ST_MODE_SEL(VFG3_TPHR_CAP_ST_MODE_SEL)
   ,.PF0_TPHR_CAP_ENABLE(PF0_TPHR_CAP_ENABLE)
   ,.TPH_TO_RAM_PIPELINE(TPH_TO_RAM_PIPELINE)
   ,.TPH_FROM_RAM_PIPELINE(TPH_FROM_RAM_PIPELINE)
   ,.MCAP_ENABLE(MCAP_ENABLE)
   ,.ECC_PIPELINE(ECC_PIPELINE)
   ,.MCAP_CONFIGURE_OVERRIDE(MCAP_CONFIGURE_OVERRIDE)
   ,.MCAP_CAP_NEXTPTR(MCAP_CAP_NEXTPTR)
   ,.MCAP_VSEC_ID(MCAP_VSEC_ID)
   ,.MCAP_VSEC_REV(MCAP_VSEC_REV)
   ,.MCAP_VSEC_LEN(MCAP_VSEC_LEN)
   ,.MCAP_FPGA_BITSTREAM_VERSION(MCAP_FPGA_BITSTREAM_VERSION)
   ,.MCAP_INTERRUPT_ON_MCAP_EOS(MCAP_INTERRUPT_ON_MCAP_EOS)
   ,.MCAP_INTERRUPT_ON_MCAP_ERROR(MCAP_INTERRUPT_ON_MCAP_ERROR)
   ,.MCAP_INPUT_GATE_DESIGN_SWITCH(MCAP_INPUT_GATE_DESIGN_SWITCH)
   ,.MCAP_EOS_DESIGN_SWITCH(MCAP_EOS_DESIGN_SWITCH)
   ,.MCAP_GATE_MEM_ENABLE_DESIGN_SWITCH(MCAP_GATE_MEM_ENABLE_DESIGN_SWITCH)
   ,.MCAP_GATE_IO_ENABLE_DESIGN_SWITCH(MCAP_GATE_IO_ENABLE_DESIGN_SWITCH)
   ,.SIM_JTAG_IDCODE(SIM_JTAG_IDCODE)
   ,.DEBUG_AXIST_DISABLE_FEATURE_BIT(DEBUG_AXIST_DISABLE_FEATURE_BIT)
   ,.DEBUG_TL_DISABLE_RX_TLP_ORDER_CHECKS(DEBUG_TL_DISABLE_RX_TLP_ORDER_CHECKS)
   ,.DEBUG_TL_DISABLE_FC_TIMEOUT(DEBUG_TL_DISABLE_FC_TIMEOUT)
   ,.DEBUG_PL_DISABLE_SCRAMBLING(DEBUG_PL_DISABLE_SCRAMBLING)
   ,.DEBUG_PL_DISABLE_REC_ENTRY_ON_DYNAMIC_DSKEW_FAIL (DEBUG_PL_DISABLE_REC_ENTRY_ON_DYNAMIC_DSKEW_FAIL )
   ,.DEBUG_PL_DISABLE_REC_ENTRY_ON_RX_BUFFER_UNDER_OVER_FLOW (DEBUG_PL_DISABLE_REC_ENTRY_ON_RX_BUFFER_UNDER_OVER_FLOW )
   ,.DEBUG_PL_DISABLE_LES_UPDATE_ON_SKP_ERROR(DEBUG_PL_DISABLE_LES_UPDATE_ON_SKP_ERROR)
   ,.DEBUG_PL_DISABLE_LES_UPDATE_ON_SKP_PARITY_ERROR(DEBUG_PL_DISABLE_LES_UPDATE_ON_SKP_PARITY_ERROR)
   ,.DEBUG_PL_DISABLE_LES_UPDATE_ON_DEFRAMER_ERROR(DEBUG_PL_DISABLE_LES_UPDATE_ON_DEFRAMER_ERROR)
   ,.DEBUG_PL_SIM_RESET_LFSR(DEBUG_PL_SIM_RESET_LFSR)
   ,.DEBUG_PL_SPARE(DEBUG_PL_SPARE)
   ,.DEBUG_LL_SPARE(DEBUG_LL_SPARE)
   ,.DEBUG_TL_SPARE(DEBUG_TL_SPARE)
   ,.DEBUG_AXI4ST_SPARE(DEBUG_AXI4ST_SPARE)
   ,.DEBUG_CFG_SPARE(DEBUG_CFG_SPARE)
   ,.DEBUG_CAR_SPARE(DEBUG_CAR_SPARE)
   ,.TEST_MODE_PIN_CHAR(TEST_MODE_PIN_CHAR)
   ,.SPARE_BIT0(SPARE_BIT0)
   ,.SPARE_BIT1(SPARE_BIT1)
   ,.SPARE_BIT2(SPARE_BIT2)
   ,.SPARE_BIT3(SPARE_BIT3)
   ,.SPARE_BIT4(SPARE_BIT4)
   ,.SPARE_BIT5(SPARE_BIT5)
   ,.SPARE_BIT6(SPARE_BIT6)
   ,.SPARE_BIT7(SPARE_BIT7)
   ,.SPARE_BIT8(SPARE_BIT8)
   ,.SPARE_BYTE0(SPARE_BYTE0)
   ,.SPARE_BYTE1(SPARE_BYTE1)
   ,.SPARE_BYTE2(SPARE_BYTE2)
   ,.SPARE_BYTE3(SPARE_BYTE3)
   ,.SPARE_WORD0(SPARE_WORD0)
   ,.SPARE_WORD1(SPARE_WORD1)
   ,.SPARE_WORD2(SPARE_WORD2)
   ,.SPARE_WORD3(SPARE_WORD3)

   ,.AXISTEN_IF_CCIX_RX_CREDIT_LIMIT(AXISTEN_IF_CCIX_RX_CREDIT_LIMIT)
   ,.AXISTEN_IF_CCIX_TX_CREDIT_LIMIT(AXISTEN_IF_CCIX_TX_CREDIT_LIMIT)
   ,.AXISTEN_IF_CCIX_TX_REGISTERED_TREADY(AXISTEN_IF_CCIX_TX_REGISTERED_TREADY)
   ,.CCIX_DIRECT_ATTACH_MODE(CCIX_DIRECT_ATTACH_MODE)
   ,.CCIX_ENABLE(CCIX_ENABLE)
   ,.CCIX_VENDOR_ID(CCIX_VENDOR_ID)
   ,.PF0_ATS_CAP_INV_QUEUE_DEPTH(PF0_ATS_CAP_INV_QUEUE_DEPTH)
   ,.PF0_ATS_CAP_NEXTPTR(PF0_ATS_CAP_NEXTPTR)
   ,.PF0_ATS_CAP_ON(PF0_ATS_CAP_ON)
   ,.PF0_PRI_CAP_NEXTPTR(PF0_PRI_CAP_NEXTPTR)
   ,.PF0_PRI_CAP_ON(PF0_PRI_CAP_ON)
   ,.PF0_PRI_OST_PR_CAPACITY(PF0_PRI_OST_PR_CAPACITY)
   ,.PF0_VC_ARB_CAPABILITY(PF0_VC_ARB_CAPABILITY)
   ,.PF0_VC_ARB_TBL_OFFSET(PF0_VC_ARB_TBL_OFFSET)
   ,.PF0_VC_EXTENDED_COUNT(PF0_VC_EXTENDED_COUNT)
   ,.PF0_VC_LOW_PRIORITY_EXTENDED_COUNT(PF0_VC_LOW_PRIORITY_EXTENDED_COUNT)
   ,.PF1_ATS_CAP_INV_QUEUE_DEPTH(PF1_ATS_CAP_INV_QUEUE_DEPTH)
   ,.PF1_ATS_CAP_NEXTPTR(PF1_ATS_CAP_NEXTPTR)
   ,.PF1_ATS_CAP_ON(PF1_ATS_CAP_ON)
   ,.PF1_PRI_CAP_NEXTPTR(PF1_PRI_CAP_NEXTPTR)
   ,.PF1_PRI_CAP_ON(PF1_PRI_CAP_ON)
   ,.PF1_PRI_OST_PR_CAPACITY(PF1_PRI_OST_PR_CAPACITY)
   ,.PF2_ATS_CAP_INV_QUEUE_DEPTH(PF2_ATS_CAP_INV_QUEUE_DEPTH)
   ,.PF2_ATS_CAP_NEXTPTR(PF2_ATS_CAP_NEXTPTR)
   ,.PF2_ATS_CAP_ON(PF2_ATS_CAP_ON)
   ,.PF2_PRI_CAP_NEXTPTR(PF2_PRI_CAP_NEXTPTR)
   ,.PF2_PRI_CAP_ON(PF2_PRI_CAP_ON)
   ,.PF2_PRI_OST_PR_CAPACITY(PF2_PRI_OST_PR_CAPACITY)
   ,.PF3_ATS_CAP_INV_QUEUE_DEPTH(PF3_ATS_CAP_INV_QUEUE_DEPTH)
   ,.PF3_ATS_CAP_NEXTPTR(PF3_ATS_CAP_NEXTPTR)
   ,.PF3_ATS_CAP_ON(PF3_ATS_CAP_ON)
   ,.PF3_PRI_CAP_NEXTPTR(PF3_PRI_CAP_NEXTPTR)
   ,.PF3_PRI_CAP_ON(PF3_PRI_CAP_ON)
   ,.PF3_PRI_OST_PR_CAPACITY(PF3_PRI_OST_PR_CAPACITY)
   ,.PL_CTRL_SKP_GEN_ENABLE(PL_CTRL_SKP_GEN_ENABLE)
   ,.PL_CTRL_SKP_PARITY_AND_CRC_CHECK_DISABLE(PL_CTRL_SKP_PARITY_AND_CRC_CHECK_DISABLE)
   ,.PL_USER_SPARE2(PL_USER_SPARE2)
   ,.TL_CREDITS_CD_VC1(TL_CREDITS_CD_VC1)
   ,.TL_CREDITS_CH_VC1(TL_CREDITS_CH_VC1)
   ,.TL_CREDITS_NPD_VC1(TL_CREDITS_NPD_VC1)
   ,.TL_CREDITS_NPH_VC1(TL_CREDITS_NPH_VC1)
   ,.TL_CREDITS_PD_VC1(TL_CREDITS_PD_VC1)
   ,.TL_CREDITS_PH_VC1(TL_CREDITS_PH_VC1)
   ,.TL_FC_UPDATE_MIN_INTERVAL_TIME_VC1(TL_FC_UPDATE_MIN_INTERVAL_TIME_VC1)
   ,.TL_FC_UPDATE_MIN_INTERVAL_TLP_COUNT_VC1(TL_FC_UPDATE_MIN_INTERVAL_TLP_COUNT_VC1)
   ,.TL_FEATURE_ENABLE_FC_SCALING(TL_FEATURE_ENABLE_FC_SCALING)
   ,.VFG0_ATS_CAP_INV_QUEUE_DEPTH(VFG0_ATS_CAP_INV_QUEUE_DEPTH)
   ,.VFG0_ATS_CAP_NEXTPTR(VFG0_ATS_CAP_NEXTPTR)
   ,.VFG0_ATS_CAP_ON(VFG0_ATS_CAP_ON)
   ,.VFG1_ATS_CAP_INV_QUEUE_DEPTH(VFG1_ATS_CAP_INV_QUEUE_DEPTH)
   ,.VFG1_ATS_CAP_NEXTPTR(VFG1_ATS_CAP_NEXTPTR)
   ,.VFG1_ATS_CAP_ON(VFG1_ATS_CAP_ON)
   ,.VFG2_ATS_CAP_INV_QUEUE_DEPTH(VFG2_ATS_CAP_INV_QUEUE_DEPTH)
   ,.VFG2_ATS_CAP_NEXTPTR(VFG2_ATS_CAP_NEXTPTR)
   ,.VFG2_ATS_CAP_ON(VFG2_ATS_CAP_ON)
   ,.VFG3_ATS_CAP_INV_QUEUE_DEPTH(VFG3_ATS_CAP_INV_QUEUE_DEPTH)
   ,.VFG3_ATS_CAP_NEXTPTR(VFG3_ATS_CAP_NEXTPTR)
   ,.VFG3_ATS_CAP_ON(VFG3_ATS_CAP_ON)
   ,.ENABLE_MSIX_32VEC(ENABLE_MSIX_32VEC)
  ) pcie_4_0_pipe_inst (

////////   PIPE Controls ////////////
   .pipe_tx_rcvr_det                   ( pipe_tx0_rcvr_det     ),//(pipe_tx_rcvr_det)
   .pipe_tx_rate                       ( common_commands_out[2:1]   ),//(pipe_tx_rate[1:0])
   .pipe_tx_deemph                     ( common_commands_out[9]     ),//(pipe_tx_deemph)
   .pipe_tx_margin                     ( common_commands_out[6:4]   ),//(pipe_tx_margin[2:0])
   .pipe_tx_swing                      ( common_commands_out[7]     ),//(pipe_tx_swing)
   .pipe_tx_reset                      ( common_commands_out[8]     ),//(pipe_tx_reset)
   .pipe_eq_fs                         ( 6'd40 ),//(pipe_eq_fs[5:0])
   .pipe_eq_lf                         ( 6'd12 ),//(pipe_eq_lf[5:0])

   .pipe_rx_eq_lp_tx_preset (pipe_rx_eq_lp_tx_preset[3:0]),
   .pipe_rx_eq_lp_lf_fs     (pipe_rx_eq_lp_lf_fs[5:0]),
  //-----------------------------
  // PIPE TX BUS Signals[69:0]
  //-----------------------------
  // pipe_tx_0_sigs[69:0]
   .pipe_tx00_data                       ( pipe_tx_0_sigs[31: 0] ),//(pipe_tx00_data[31:0])
   .pipe_tx00_char_is_k                  ( pipe_tx_0_sigs[33:32] ),//(pipe_tx00_char_is_k[1:0])
   .pipe_tx00_elec_idle                  ( pipe_tx_0_sigs[34]    ),//(pipe_tx00_elec_idle)
   .pipe_tx00_data_valid                 ( pipe_tx_0_sigs[35]    ),//(pipe_tx00_data_valid)
   .pipe_tx00_start_block                ( pipe_tx_0_sigs[36]    ),//(pipe_tx00_start_block)
   .pipe_tx00_sync_header                ( pipe_tx_0_sigs[38:37] ),//(pipe_tx00_sync_header[1:0])
   .pipe_rx00_polarity                   ( pipe_tx_0_sigs[39]    ),//(pipe_rx00_polarity)
   .pipe_tx00_powerdown                  ( pipe_tx_0_sigs[41:40] ),//(pipe_tx00_powerdown[1:0])
   .pipe_tx00_eq_control                 ( pipe_tx00_eq_control ),//(pipe_tx00_eq_control[1:0])
                                       //( pipe_tx_0_sigs[47:44] ),//
   .pipe_tx00_eq_deemph                  ( ),//(pipe_tx00_eq_deemph[5:0])
   .pipe_rx00_eq_control                 ( pipe_rx00_eq_control ),//(pipe_rx00_eq_control[1:0])
                                       //( pipe_tx_0_sigs[58:56] ),//
                                       //( pipe_tx_0_sigs[64:59] ),//
                                       //( pipe_tx_0_sigs[68:65] ),//
   .pipe_tx00_compliance                 ( ),//(pipe_tx00_compliance)
  //-----------------------------
  // pipe_tx_1_sigs[69:0]
   .pipe_tx01_data                       ( pipe_tx_1_sigs[31: 0] ),//(pipe_tx00_data[31:0])
   .pipe_tx01_char_is_k                  ( pipe_tx_1_sigs[33:32] ),//(pipe_tx00_char_is_k[1:0])
   .pipe_tx01_elec_idle                  ( pipe_tx_1_sigs[34]    ),//(pipe_tx00_elec_idle)
   .pipe_tx01_data_valid                 ( pipe_tx_1_sigs[35]    ),//(pipe_tx00_data_valid)
   .pipe_tx01_start_block                ( pipe_tx_1_sigs[36]    ),//(pipe_tx00_start_block)
   .pipe_tx01_sync_header                ( pipe_tx_1_sigs[38:37] ),//(pipe_tx00_sync_header[1:0])
   .pipe_rx01_polarity                   ( pipe_tx_1_sigs[39]    ),//(pipe_rx00_polarity)
   .pipe_tx01_powerdown                  ( pipe_tx_1_sigs[41:40] ),//(pipe_tx00_powerdown[1:0])
   .pipe_tx01_eq_control                 ( pipe_tx01_eq_control ),//(pipe_tx00_eq_control[1:0])
                                       //( pipe_tx_1_sigs[47:44] ),//
   .pipe_tx01_eq_deemph                  (  ),//(pipe_tx00_eq_deemph[5:0])
   .pipe_rx01_eq_control                 ( pipe_rx01_eq_control ),//(pipe_rx00_eq_control[1:0])
                                       //( pipe_tx_1_sigs[58:56] ),//
                                       //( pipe_tx_1_sigs[64:59] ),//
                                       //( pipe_tx_1_sigs[68:65] ),//
   .pipe_tx01_compliance                 ( ),//(pipe_tx00_compliance)
  //-----------------------------
  // pipe_tx_2_sigs[69:0]
   .pipe_tx02_data                       ( pipe_tx_2_sigs[31: 0] ),//(pipe_tx00_data[31:0])
   .pipe_tx02_char_is_k                  ( pipe_tx_2_sigs[33:32] ),//(pipe_tx00_char_is_k[1:0])
   .pipe_tx02_elec_idle                  ( pipe_tx_2_sigs[34]    ),//(pipe_tx00_elec_idle)
   .pipe_tx02_data_valid                 ( pipe_tx_2_sigs[35]    ),//(pipe_tx00_data_valid)
   .pipe_tx02_start_block                ( pipe_tx_2_sigs[36]    ),//(pipe_tx00_start_block)
   .pipe_tx02_sync_header                ( pipe_tx_2_sigs[38:37] ),//(pipe_tx00_sync_header[1:0])
   .pipe_rx02_polarity                   ( pipe_tx_2_sigs[39]    ),//(pipe_rx00_polarity)
   .pipe_tx02_powerdown                  ( pipe_tx_2_sigs[41:40] ),//(pipe_tx00_powerdown[1:0])
   .pipe_tx02_eq_control                 ( pipe_tx02_eq_control ),//(pipe_tx00_eq_control[1:0])
                                       //( pipe_tx_2_sigs[47:44] ),//
   .pipe_tx02_eq_deemph                  ( ),//(pipe_tx00_eq_deemph[5:0])
   .pipe_rx02_eq_control                 ( pipe_rx02_eq_control ),//(pipe_rx00_eq_control[1:0])
                                       //( pipe_tx_2_sigs[58:56] ),//
                                       //( pipe_tx_2_sigs[64:59] ),//
                                       //( pipe_tx_2_sigs[68:65] ),//
   .pipe_tx02_compliance                 ( ),//(pipe_tx00_compliance)
  //-----------------------------
  // pipe_tx_3_sigs[69:0]
   .pipe_tx03_data                       ( pipe_tx_3_sigs[31: 0] ),//(pipe_tx00_data[31:0])
   .pipe_tx03_char_is_k                  ( pipe_tx_3_sigs[33:32] ),//(pipe_tx00_char_is_k[1:0])
   .pipe_tx03_elec_idle                  ( pipe_tx_3_sigs[34]    ),//(pipe_tx00_elec_idle)
   .pipe_tx03_data_valid                 ( pipe_tx_3_sigs[35]    ),//(pipe_tx00_data_valid)
   .pipe_tx03_start_block                ( pipe_tx_3_sigs[36]    ),//(pipe_tx00_start_block)
   .pipe_tx03_sync_header                ( pipe_tx_3_sigs[38:37] ),//(pipe_tx00_sync_header[1:0])
   .pipe_rx03_polarity                   ( pipe_tx_3_sigs[39]    ),//(pipe_rx00_polarity)
   .pipe_tx03_powerdown                  ( pipe_tx_3_sigs[41:40] ),//(pipe_tx00_powerdown[1:0])
   .pipe_tx03_eq_control                 ( pipe_tx03_eq_control ),//(pipe_tx00_eq_control[1:0])
                                       //( pipe_tx_3_sigs[47:44] ),//
   .pipe_tx03_eq_deemph                  ( ),//(pipe_tx00_eq_deemph[5:0])
   .pipe_rx03_eq_control                 ( pipe_rx03_eq_control ),//(pipe_rx00_eq_control[1:0])
                                       //( pipe_tx_3_sigs[58:56] ),//
                                       //( pipe_tx_3_sigs[64:59] ),//
                                       //( pipe_tx_3_sigs[68:65] ),//
   .pipe_tx03_compliance                 ( ),//(pipe_tx00_compliance)
  //-----------------------------
  // pipe_tx_4_sigs[69:0]
   .pipe_tx04_data                       ( pipe_tx_4_sigs[31: 0] ),//(pipe_tx00_data[31:0])
   .pipe_tx04_char_is_k                  ( pipe_tx_4_sigs[33:32] ),//(pipe_tx00_char_is_k[1:0])
   .pipe_tx04_elec_idle                  ( pipe_tx_4_sigs[34]    ),//(pipe_tx00_elec_idle)
   .pipe_tx04_data_valid                 ( pipe_tx_4_sigs[35]    ),//(pipe_tx00_data_valid)
   .pipe_tx04_start_block                ( pipe_tx_4_sigs[36]    ),//(pipe_tx00_start_block)
   .pipe_tx04_sync_header                ( pipe_tx_4_sigs[38:37] ),//(pipe_tx00_sync_header[1:0])
   .pipe_rx04_polarity                   ( pipe_tx_4_sigs[39]    ),//(pipe_rx00_polarity)
   .pipe_tx04_powerdown                  ( pipe_tx_4_sigs[41:40] ),//(pipe_tx00_powerdown[1:0])
   .pipe_tx04_eq_control                 ( pipe_tx04_eq_control ),//(pipe_tx00_eq_control[1:0])
                                       //( pipe_tx_4_sigs[47:44] ),//
   .pipe_tx04_eq_deemph                  ( ),//(pipe_tx00_eq_deemph[5:0])
   .pipe_rx04_eq_control                 ( pipe_rx04_eq_control ),//(pipe_rx00_eq_control[1:0])
                                       //( pipe_tx_4_sigs[58:56] ),//
                                       //( pipe_tx_4_sigs[64:59] ),//
                                       //( pipe_tx_4_sigs[68:65] ),//
   .pipe_tx04_compliance                 ( ),//(pipe_tx00_compliance)
  //-----------------------------
  // pipe_tx_5_sigs[69:0]
   .pipe_tx05_data                       ( pipe_tx_5_sigs[31: 0] ),//(pipe_tx00_data[31:0])
   .pipe_tx05_char_is_k                  ( pipe_tx_5_sigs[33:32] ),//(pipe_tx00_char_is_k[1:0])
   .pipe_tx05_elec_idle                  ( pipe_tx_5_sigs[34]    ),//(pipe_tx00_elec_idle)
   .pipe_tx05_data_valid                 ( pipe_tx_5_sigs[35]    ),//(pipe_tx00_data_valid)
   .pipe_tx05_start_block                ( pipe_tx_5_sigs[36]    ),//(pipe_tx00_start_block)
   .pipe_tx05_sync_header                ( pipe_tx_5_sigs[38:37] ),//(pipe_tx00_sync_header[1:0])
   .pipe_rx05_polarity                   ( pipe_tx_5_sigs[39]    ),//(pipe_rx00_polarity)
   .pipe_tx05_powerdown                  ( pipe_tx_5_sigs[41:40] ),//(pipe_tx00_powerdown[1:0])
   .pipe_tx05_eq_control                 ( pipe_tx05_eq_control ),//(pipe_tx00_eq_control[1:0])
                                       //( pipe_tx_5_sigs[47:44] ),//
   .pipe_tx05_eq_deemph                  ( ),//(pipe_tx00_eq_deemph[5:0])
   .pipe_rx05_eq_control                 ( pipe_rx05_eq_control ),//(pipe_rx00_eq_control[1:0])
                                       //( pipe_tx_5_sigs[58:56] ),//
                                       //( pipe_tx_5_sigs[64:59] ),//
                                       //( pipe_tx_5_sigs[68:65] ),//
   .pipe_tx05_compliance                 ( ),//(pipe_tx00_compliance)
  //-----------------------------
  // pipe_tx_6_sigs[69:0]
   .pipe_tx06_data                       ( pipe_tx_6_sigs[31: 0] ),//(pipe_tx00_data[31:0])
   .pipe_tx06_char_is_k                  ( pipe_tx_6_sigs[33:32] ),//(pipe_tx00_char_is_k[1:0])
   .pipe_tx06_elec_idle                  ( pipe_tx_6_sigs[34]    ),//(pipe_tx00_elec_idle)
   .pipe_tx06_data_valid                 ( pipe_tx_6_sigs[35]    ),//(pipe_tx00_data_valid)
   .pipe_tx06_start_block                ( pipe_tx_6_sigs[36]    ),//(pipe_tx00_start_block)
   .pipe_tx06_sync_header                ( pipe_tx_6_sigs[38:37] ),//(pipe_tx00_sync_header[1:0])
   .pipe_rx06_polarity                   ( pipe_tx_6_sigs[39]    ),//(pipe_rx00_polarity)
   .pipe_tx06_powerdown                  ( pipe_tx_6_sigs[41:40] ),//(pipe_tx00_powerdown[1:0])
   .pipe_tx06_eq_control                 ( pipe_tx06_eq_control ),//(pipe_tx00_eq_control[1:0])
                                       //( pipe_tx_6_sigs[47:44] ),//
   .pipe_tx06_eq_deemph                  ( ),//(pipe_tx00_eq_deemph[5:0])
   .pipe_rx06_eq_control                 ( pipe_rx06_eq_control ),//(pipe_rx00_eq_control[1:0])
                                       //( pipe_tx_6_sigs[58:56] ),//
                                       //( pipe_tx_6_sigs[64:59] ),//
                                       //( pipe_tx_6_sigs[68:65] ),//
   .pipe_tx06_compliance                 ( ),//(pipe_tx00_compliance)
  //-----------------------------
  // pipe_tx_7_sigs[69:0]
   .pipe_tx07_data                       ( pipe_tx_7_sigs[31: 0] ),//(pipe_tx00_data[31:0])
   .pipe_tx07_char_is_k                  ( pipe_tx_7_sigs[33:32] ),//(pipe_tx00_char_is_k[1:0])
   .pipe_tx07_elec_idle                  ( pipe_tx_7_sigs[34]    ),//(pipe_tx00_elec_idle)
   .pipe_tx07_data_valid                 ( pipe_tx_7_sigs[35]    ),//(pipe_tx00_data_valid)
   .pipe_tx07_start_block                ( pipe_tx_7_sigs[36]    ),//(pipe_tx00_start_block)
   .pipe_tx07_sync_header                ( pipe_tx_7_sigs[38:37] ),//(pipe_tx00_sync_header[1:0])
   .pipe_rx07_polarity                   ( pipe_tx_7_sigs[39]    ),//(pipe_rx00_polarity)
   .pipe_tx07_powerdown                  ( pipe_tx_7_sigs[41:40] ),//(pipe_tx00_powerdown[1:0])
   .pipe_tx07_eq_control                 ( pipe_tx07_eq_control ),//(pipe_tx00_eq_control[1:0])
                                       //( pipe_tx_7_sigs[47:44] ),//
   .pipe_tx07_eq_deemph                  ( ),//(pipe_tx00_eq_deemph[5:0])
   .pipe_rx07_eq_control                 ( pipe_rx07_eq_control ),//(pipe_rx00_eq_control[1:0])
                                       //( pipe_tx_7_sigs[58:56] ),//
                                       //( pipe_tx_7_sigs[64:59] ),//
                                       //( pipe_tx_7_sigs[68:65] ),//
   .pipe_tx07_compliance                 ( ),//(pipe_tx00_compliance)
  //-----------------------------
  // pipe_tx_8_sigs[69:0]
   .pipe_tx08_data                       ( pipe_tx_8_sigs[31: 0] ),//(pipe_tx00_data[31:0])
   .pipe_tx08_char_is_k                  ( pipe_tx_8_sigs[33:32] ),//(pipe_tx00_char_is_k[1:0])
   .pipe_tx08_elec_idle                  ( pipe_tx_8_sigs[34]    ),//(pipe_tx00_elec_idle)
   .pipe_tx08_data_valid                 ( pipe_tx_8_sigs[35]    ),//(pipe_tx00_data_valid)
   .pipe_tx08_start_block                ( pipe_tx_8_sigs[36]    ),//(pipe_tx00_start_block)
   .pipe_tx08_sync_header                ( pipe_tx_8_sigs[38:37] ),//(pipe_tx00_sync_header[1:0])
   .pipe_rx08_polarity                   ( pipe_tx_8_sigs[39]    ),//(pipe_rx00_polarity)
   .pipe_tx08_powerdown                  ( pipe_tx_8_sigs[41:40] ),//(pipe_tx00_powerdown[1:0])
   .pipe_tx08_eq_control                 ( pipe_tx08_eq_control ),//(pipe_tx00_eq_control[1:0])
                                       //( pipe_tx_8_sigs[47:44] ),//
   .pipe_tx08_eq_deemph                  ( ),//(pipe_tx00_eq_deemph[5:0])
   .pipe_rx08_eq_control                 ( pipe_rx08_eq_control ),//(pipe_rx00_eq_control[1:0])
                                       //( pipe_tx_8_sigs[58:56] ),//
                                       //( pipe_tx_8_sigs[64:59] ),//
                                       //( pipe_tx_8_sigs[68:65] ),//
   .pipe_tx08_compliance                 (  ),//(pipe_tx00_compliance)
  //-----------------------------
  // pipe_tx_9_sigs[69:0]
   .pipe_tx09_data                       ( pipe_tx_9_sigs[31: 0] ),//(pipe_tx00_data[31:0])
   .pipe_tx09_char_is_k                  ( pipe_tx_9_sigs[33:32] ),//(pipe_tx00_char_is_k[1:0])
   .pipe_tx09_elec_idle                  ( pipe_tx_9_sigs[34]    ),//(pipe_tx00_elec_idle)
   .pipe_tx09_data_valid                 ( pipe_tx_9_sigs[35]    ),//(pipe_tx00_data_valid)
   .pipe_tx09_start_block                ( pipe_tx_9_sigs[36]    ),//(pipe_tx00_start_block)
   .pipe_tx09_sync_header                ( pipe_tx_9_sigs[38:37] ),//(pipe_tx00_sync_header[1:0])
   .pipe_rx09_polarity                   ( pipe_tx_9_sigs[39]    ),//(pipe_rx00_polarity)
   .pipe_tx09_powerdown                  ( pipe_tx_9_sigs[41:40] ),//(pipe_tx00_powerdown[1:0])
   .pipe_tx09_eq_control                 ( pipe_tx09_eq_control ),//(pipe_tx00_eq_control[1:0])
                                       //( pipe_tx_9_sigs[47:44] ),//
   .pipe_tx09_eq_deemph                  ( ),//(pipe_tx00_eq_deemph[5:0])
   .pipe_rx09_eq_control                 ( pipe_rx09_eq_control),//(pipe_rx00_eq_control[1:0])
                                       //( pipe_tx_9_sigs[58:56] ),//
                                       //( pipe_tx_9_sigs[64:59] ),//
                                       //( pipe_tx_9_sigs[68:65] ),//
   .pipe_tx09_compliance                 ( ),//(pipe_tx00_compliance)
  //-----------------------------
  // pipe_tx_10_sigs[69:0]
   .pipe_tx10_data                       ( pipe_tx_10_sigs[31: 0] ),//(pipe_tx00_data[31:0])
   .pipe_tx10_char_is_k                  ( pipe_tx_10_sigs[33:32] ),//(pipe_tx00_char_is_k[1:0])
   .pipe_tx10_elec_idle                  ( pipe_tx_10_sigs[34]    ),//(pipe_tx00_elec_idle)
   .pipe_tx10_data_valid                 ( pipe_tx_10_sigs[35]    ),//(pipe_tx00_data_valid)
   .pipe_tx10_start_block                ( pipe_tx_10_sigs[36]    ),//(pipe_tx00_start_block)
   .pipe_tx10_sync_header                ( pipe_tx_10_sigs[38:37] ),//(pipe_tx00_sync_header[1:0])
   .pipe_rx10_polarity                   ( pipe_tx_10_sigs[39]    ),//(pipe_rx00_polarity)
   .pipe_tx10_powerdown                  ( pipe_tx_10_sigs[41:40] ),//(pipe_tx00_powerdown[1:0])
   .pipe_tx10_eq_control                 ( pipe_tx10_eq_control ),//(pipe_tx00_eq_control[1:0])
                                       //( pipe_tx_10_sigs[47:44] ),//
   .pipe_tx10_eq_deemph                  ( ),//(pipe_tx00_eq_deemph[5:0])
   .pipe_rx10_eq_control                 ( pipe_rx10_eq_control ),//(pipe_rx00_eq_control[1:0])
                                       //( pipe_tx_10_sigs[58:56] ),//
                                       //( pipe_tx_10_sigs[64:59] ),//
                                       //( pipe_tx_10_sigs[68:65] ),//
   .pipe_tx10_compliance                 ( ),//(pipe_tx00_compliance)
  //-----------------------------
  // pipe_tx_11_sigs[69:0]
   .pipe_tx11_data                       ( pipe_tx_11_sigs[31: 0] ),//(pipe_tx00_data[31:0])
   .pipe_tx11_char_is_k                  ( pipe_tx_11_sigs[33:32] ),//(pipe_tx00_char_is_k[1:0])
   .pipe_tx11_elec_idle                  ( pipe_tx_11_sigs[34]    ),//(pipe_tx00_elec_idle)
   .pipe_tx11_data_valid                 ( pipe_tx_11_sigs[35]    ),//(pipe_tx00_data_valid)
   .pipe_tx11_start_block                ( pipe_tx_11_sigs[36]    ),//(pipe_tx00_start_block)
   .pipe_tx11_sync_header                ( pipe_tx_11_sigs[38:37] ),//(pipe_tx00_sync_header[1:0])
   .pipe_rx11_polarity                   ( pipe_tx_11_sigs[39]    ),//(pipe_rx00_polarity)
   .pipe_tx11_powerdown                  ( pipe_tx_11_sigs[41:40] ),//(pipe_tx00_powerdown[1:0])
   .pipe_tx11_eq_control                 ( pipe_tx11_eq_control ),//(pipe_tx00_eq_control[1:0])
                                       //( pipe_tx_11_sigs[47:44] ),//
   .pipe_tx11_eq_deemph                  ( ),//(pipe_tx00_eq_deemph[5:0])
   .pipe_rx11_eq_control                 ( pipe_rx11_eq_control ),//(pipe_rx00_eq_control[1:0])
                                       //( pipe_tx_11_sigs[58:56] ),//
                                       //( pipe_tx_11_sigs[64:59] ),//
                                       //( pipe_tx_11_sigs[68:65] ),//
   .pipe_tx11_compliance                 ( ),//(pipe_tx00_compliance)
  //-----------------------------
  // pipe_tx_12_sigs[69:0]
   .pipe_tx12_data                       ( pipe_tx_12_sigs[31: 0] ),//(pipe_tx00_data[31:0])
   .pipe_tx12_char_is_k                  ( pipe_tx_12_sigs[33:32] ),//(pipe_tx00_char_is_k[1:0])
   .pipe_tx12_elec_idle                  ( pipe_tx_12_sigs[34]    ),//(pipe_tx00_elec_idle)
   .pipe_tx12_data_valid                 ( pipe_tx_12_sigs[35]    ),//(pipe_tx00_data_valid)
   .pipe_tx12_start_block                ( pipe_tx_12_sigs[36]    ),//(pipe_tx00_start_block)
   .pipe_tx12_sync_header                ( pipe_tx_12_sigs[38:37] ),//(pipe_tx00_sync_header[1:0])
   .pipe_rx12_polarity                   ( pipe_tx_12_sigs[39]    ),//(pipe_rx00_polarity)
   .pipe_tx12_powerdown                  ( pipe_tx_12_sigs[41:40] ),//(pipe_tx00_powerdown[1:0])
   .pipe_tx12_eq_control                 ( pipe_tx12_eq_control ),//(pipe_tx00_eq_control[1:0])
                                       //( pipe_tx_12_sigs[47:44] ),//
   .pipe_tx12_eq_deemph                  ( ),//(pipe_tx00_eq_deemph[5:0])
   .pipe_rx12_eq_control                 ( pipe_rx12_eq_control ),//(pipe_rx00_eq_control[1:0])
                                       //( pipe_tx_12_sigs[58:56] ),//
                                       //( pipe_tx_12_sigs[64:59] ),//
                                       //( pipe_tx_12_sigs[68:65] ),//
   .pipe_tx12_compliance                 ( ),//(pipe_tx00_compliance)
  //-----------------------------
  // pipe_tx_13_sigs[69:0]
   .pipe_tx13_data                       ( pipe_tx_13_sigs[31: 0] ),//(pipe_tx00_data[31:0])
   .pipe_tx13_char_is_k                  ( pipe_tx_13_sigs[33:32] ),//(pipe_tx00_char_is_k[1:0])
   .pipe_tx13_elec_idle                  ( pipe_tx_13_sigs[34]    ),//(pipe_tx00_elec_idle)
   .pipe_tx13_data_valid                 ( pipe_tx_13_sigs[35]    ),//(pipe_tx00_data_valid)
   .pipe_tx13_start_block                ( pipe_tx_13_sigs[36]    ),//(pipe_tx00_start_block)
   .pipe_tx13_sync_header                ( pipe_tx_13_sigs[38:37] ),//(pipe_tx00_sync_header[1:0])
   .pipe_rx13_polarity                   ( pipe_tx_13_sigs[39]    ),//(pipe_rx00_polarity)
   .pipe_tx13_powerdown                  ( pipe_tx_13_sigs[41:40] ),//(pipe_tx00_powerdown[1:0])
   .pipe_tx13_eq_control                 ( pipe_tx13_eq_control ),//(pipe_tx00_eq_control[1:0])
                                       //( pipe_tx_13_sigs[47:44] ),//
   .pipe_tx13_eq_deemph                  (  ),//(pipe_tx00_eq_deemph[5:0])
   .pipe_rx13_eq_control                 ( pipe_rx13_eq_control ),//(pipe_rx00_eq_control[1:0])
                                       //( pipe_tx_13_sigs[58:56] ),//
                                       //( pipe_tx_13_sigs[64:59] ),//
                                       //( pipe_tx_13_sigs[68:65] ),//
   .pipe_tx13_compliance                 ( ),//(pipe_tx00_compliance)
  //-----------------------------
  // pipe_tx_14_sigs[69:0]
   .pipe_tx14_data                       ( pipe_tx_14_sigs[31: 0] ),//(pipe_tx00_data[31:0])
   .pipe_tx14_char_is_k                  ( pipe_tx_14_sigs[33:32] ),//(pipe_tx00_char_is_k[1:0])
   .pipe_tx14_elec_idle                  ( pipe_tx_14_sigs[34]    ),//(pipe_tx00_elec_idle)
   .pipe_tx14_data_valid                 ( pipe_tx_14_sigs[35]    ),//(pipe_tx00_data_valid)
   .pipe_tx14_start_block                ( pipe_tx_14_sigs[36]    ),//(pipe_tx00_start_block)
   .pipe_tx14_sync_header                ( pipe_tx_14_sigs[38:37] ),//(pipe_tx00_sync_header[1:0])
   .pipe_rx14_polarity                   ( pipe_tx_14_sigs[39]    ),//(pipe_rx00_polarity)
   .pipe_tx14_powerdown                  ( pipe_tx_14_sigs[41:40] ),//(pipe_tx00_powerdown[1:0])
   .pipe_tx14_eq_control                 ( pipe_tx14_eq_control ),//(pipe_tx00_eq_control[1:0])
                                       //( pipe_tx_14_sigs[47:44] ),//
   .pipe_tx14_eq_deemph                  ( ),//(pipe_tx00_eq_deemph[5:0])
   .pipe_rx14_eq_control                 ( pipe_rx14_eq_control ),//(pipe_rx00_eq_control[1:0])
                                       //( pipe_tx_14_sigs[58:56] ),//
                                       //( pipe_tx_14_sigs[64:59] ),//
                                       //( pipe_tx_14_sigs[68:65] ),//
   .pipe_tx14_compliance                 ( ),//(pipe_tx00_compliance)
  //-----------------------------
  // pipe_tx_15_sigs[69:0]
   .pipe_tx15_data                       ( pipe_tx_15_sigs[31: 0] ),//(pipe_tx00_data[31:0])
   .pipe_tx15_char_is_k                  ( pipe_tx_15_sigs[33:32] ),//(pipe_tx00_char_is_k[1:0])
   .pipe_tx15_elec_idle                  ( pipe_tx_15_sigs[34]    ),//(pipe_tx00_elec_idle)
   .pipe_tx15_data_valid                 ( pipe_tx_15_sigs[35]    ),//(pipe_tx00_data_valid)
   .pipe_tx15_start_block                ( pipe_tx_15_sigs[36]    ),//(pipe_tx00_start_block)
   .pipe_tx15_sync_header                ( pipe_tx_15_sigs[38:37] ),//(pipe_tx00_sync_header[1:0])
   .pipe_rx15_polarity                   ( pipe_tx_15_sigs[39]    ),//(pipe_rx00_polarity)
   .pipe_tx15_powerdown                  ( pipe_tx_15_sigs[41:40] ),//(pipe_tx00_powerdown[1:0])
   .pipe_tx15_eq_control                 ( pipe_tx15_eq_control ),//(pipe_tx00_eq_control[1:0])
                                       //( pipe_tx_15_sigs[47:44] ),//
   .pipe_tx15_eq_deemph                  ( ),//(pipe_tx00_eq_deemph[5:0])
   .pipe_rx15_eq_control                 ( pipe_rx15_eq_control ),//(pipe_rx00_eq_control[1:0])
                                       //( pipe_tx_15_sigs[58:56] ),//
                                       //( pipe_tx_15_sigs[64:59] ),//
                                       //( pipe_tx_15_sigs[68:65] ),//
   .pipe_tx15_compliance                 ( ),//(pipe_tx00_compliance)
  //-----------------------------
  // PIPE RX BUS Signals[83:0]
  //-----------------------------
  // pipe_rx00_sigs[83:0]
   .pipe_rx00_data                         ( pipe_rx_0_sigs[31: 0] ),//(pipe_rx00_data[31:0])
   .pipe_rx00_char_is_k                    ( pipe_rx_0_sigs[33:32] ),//(pipe_rx00_char_is_k[1:0])
   .pipe_rx00_data_valid                   ( pipe_rx_0_sigs[35]    ),//(pipe_rx00_data_valid)
   .pipe_rx00_elec_idle                    ( pipe_rx_0_sigs[34]    ),//(pipe_rx00_elec_idle)
   .pipe_rx00_start_block                  ( {1'b0, pipe_rx_0_sigs[36]}    ),//(pipe_rx00_start_block[1:0])
   .pipe_rx00_sync_header                  ( pipe_rx_0_sigs[38:37] ),//(pipe_rx00_sync_header[1:0])
   .pipe_rx00_status                       ( rx_status ),//(pipe_rx00_status[2:0])
   .pipe_rx00_valid                        ( ~pipe_rx_0_sigs[34]    ),//(pipe_rx00_valid)
   .pipe_rx00_phy_status                   ( phy_status ),//(pipe_rx00_phy_status)
   .pipe_tx00_eq_done                      ( pipe_tx00_eq_done   ),//(pipe_tx00_eq_done)
   .pipe_tx00_eq_coeff                     ( 18'h00904 ),//(pipe_tx00_eq_coeff[17:0])
   .pipe_rx00_eq_lp_new_tx_coeff_or_preset ( 18'h05 ),//(pipe_rx00_eq_lp_new_tx_coeff_or_preset[17:0])
   .pipe_rx00_eq_lp_lf_fs_sel              ( 1'b0    ),//(pipe_rx00_eq_lp_lf_fs_sel)
   .pipe_rx00_eq_lp_adapt_done             ( 1'b0   ),//(pipe_rx00_eq_lp_adapt_done)
   .pipe_rx00_eq_done                      ( pipe_rx00_eq_done    ),//(pipe_rx00_eq_done)
  //-----------------------------
  // pipe_rx01_sigs[83:0]
   .pipe_rx01_data                         ( pipe_rx_1_sigs[31: 0] ),//(pipe_rx00_data[31:0])
   .pipe_rx01_char_is_k                    ( pipe_rx_1_sigs[33:32] ),//(pipe_rx00_char_is_k[1:0])
   .pipe_rx01_data_valid                   ( pipe_rx_1_sigs[35]    ),//(pipe_rx00_data_valid)
   .pipe_rx01_elec_idle                    ( pipe_rx_1_sigs[34]    ),//(pipe_rx00_elec_idle)
   .pipe_rx01_start_block                  ( {1'b0, pipe_rx_1_sigs[36]}    ),//(pipe_rx00_start_block[1:0])
   .pipe_rx01_sync_header                  ( pipe_rx_1_sigs[38:37] ),//(pipe_rx00_sync_header[1:0])
   .pipe_rx01_status                       ( (PL_LINK_CAP_MAX_LINK_WIDTH >= 2 )? rx_status : 3'b0  ),//(pipe_rx00_status[2:0])
   .pipe_rx01_valid                        ( ~pipe_rx_1_sigs[34]    ),//(pipe_rx00_valid)
   .pipe_rx01_phy_status                   ( (PL_LINK_CAP_MAX_LINK_WIDTH >= 2 )? phy_status : 1'b0  ),//(pipe_rx00_phy_status)
   .pipe_tx01_eq_done                      ( pipe_tx01_eq_done    ),//(pipe_tx00_eq_done)
   .pipe_tx01_eq_coeff                     ( 18'h00904 ),//(pipe_tx00_eq_coeff[17:0])
   .pipe_rx01_eq_lp_new_tx_coeff_or_preset ( 18'h05 ),//(pipe_rx00_eq_lp_new_tx_coeff_or_preset[17:0])
   .pipe_rx01_eq_lp_lf_fs_sel              ( 1'b0    ),//(pipe_rx00_eq_lp_lf_fs_sel)
   .pipe_rx01_eq_lp_adapt_done             ( 1'b0    ),//(pipe_rx00_eq_lp_adapt_done)
   .pipe_rx01_eq_done                      ( pipe_rx01_eq_done    ),//(pipe_rx00_eq_done)
  //-----------------------------
  // pipe_rx02_sigs[83:0]
   .pipe_rx02_data                         ( pipe_rx_2_sigs[31: 0] ),//(pipe_rx00_data[31:0])
   .pipe_rx02_char_is_k                    ( pipe_rx_2_sigs[33:32] ),//(pipe_rx00_char_is_k[1:0])
   .pipe_rx02_data_valid                   ( pipe_rx_2_sigs[35]    ),//(pipe_rx00_data_valid)
   .pipe_rx02_elec_idle                    ( pipe_rx_2_sigs[34]    ),//(pipe_rx00_elec_idle)
   .pipe_rx02_start_block                  ( {1'b0, pipe_rx_2_sigs[36]}    ),//(pipe_rx00_start_block[1:0])
   .pipe_rx02_sync_header                  ( pipe_rx_2_sigs[38:37] ),//(pipe_rx00_sync_header[1:0])
   .pipe_rx02_status                       ( (PL_LINK_CAP_MAX_LINK_WIDTH >= 2 )? rx_status : 3'b0  ),//(pipe_rx00_status[2:0])
   .pipe_rx02_valid                        ( ~pipe_rx_2_sigs[34]    ),//(pipe_rx00_valid)
   .pipe_rx02_phy_status                   ( (PL_LINK_CAP_MAX_LINK_WIDTH >= 4 )? phy_status : 1'b0 ),//(pipe_rx00_phy_status)
   .pipe_tx02_eq_done                      ( pipe_tx02_eq_done    ),//(pipe_tx00_eq_done)
   .pipe_tx02_eq_coeff                     ( 18'h00904 ),//(pipe_tx00_eq_coeff[17:0])
   .pipe_rx02_eq_lp_new_tx_coeff_or_preset ( 18'h05 ),//(pipe_rx00_eq_lp_new_tx_coeff_or_preset[17:0])
   .pipe_rx02_eq_lp_lf_fs_sel              ( 1'b0    ),//(pipe_rx00_eq_lp_lf_fs_sel)
   .pipe_rx02_eq_lp_adapt_done             ( 1'b0    ),//(pipe_rx00_eq_lp_adapt_done)
   .pipe_rx02_eq_done                      ( pipe_rx02_eq_done    ),//(pipe_rx00_eq_done)
  //-----------------------------
  // pipe_rx03_sigs[83:0]
   .pipe_rx03_data                         ( pipe_rx_3_sigs[31: 0] ),//(pipe_rx00_data[31:0])
   .pipe_rx03_char_is_k                    ( pipe_rx_3_sigs[33:32] ),//(pipe_rx00_char_is_k[1:0])
   .pipe_rx03_data_valid                   ( pipe_rx_3_sigs[35]    ),//(pipe_rx00_data_valid)
   .pipe_rx03_elec_idle                    ( pipe_rx_3_sigs[34]    ),//(pipe_rx00_elec_idle)
   .pipe_rx03_start_block                  ( {1'b0, pipe_rx_3_sigs[36]}    ),//(pipe_rx00_start_block[1:0])
   .pipe_rx03_sync_header                  ( pipe_rx_3_sigs[38:37] ),//(pipe_rx00_sync_header[1:0])
   .pipe_rx03_status                       ( (PL_LINK_CAP_MAX_LINK_WIDTH >= 2 )? rx_status : 3'b0 ),//(pipe_rx00_status[2:0])
   .pipe_rx03_valid                        ( ~pipe_rx_3_sigs[34]    ),//(pipe_rx00_valid)
   .pipe_rx03_phy_status                   ( (PL_LINK_CAP_MAX_LINK_WIDTH >= 4 )? phy_status : 1'b0 ),//(pipe_rx00_phy_status)
   .pipe_tx03_eq_done                      ( pipe_tx03_eq_done    ),//(pipe_tx00_eq_done)
   .pipe_tx03_eq_coeff                     ( 18'h00904 ),//(pipe_tx00_eq_coeff[17:0])
   .pipe_rx03_eq_lp_new_tx_coeff_or_preset ( 18'h05 ),//(pipe_rx00_eq_lp_new_tx_coeff_or_preset[17:0])
   .pipe_rx03_eq_lp_lf_fs_sel              ( 1'b0    ),//(pipe_rx00_eq_lp_lf_fs_sel)
   .pipe_rx03_eq_lp_adapt_done             ( 1'b0    ),//(pipe_rx00_eq_lp_adapt_done)
   .pipe_rx03_eq_done                      ( pipe_rx03_eq_done    ),//(pipe_rx00_eq_done)
  //-----------------------------
  // pipe_rx04_sigs[83:0]
   .pipe_rx04_data                         ( pipe_rx_4_sigs[31: 0] ),//(pipe_rx00_data[31:0])
   .pipe_rx04_char_is_k                    ( pipe_rx_4_sigs[33:32] ),//(pipe_rx00_char_is_k[1:0])
   .pipe_rx04_data_valid                   ( pipe_rx_4_sigs[35]    ),//(pipe_rx00_data_valid)
   .pipe_rx04_elec_idle                    ( pipe_rx_4_sigs[34]    ),//(pipe_rx00_elec_idle)
   .pipe_rx04_start_block                  ({1'b0,  pipe_rx_4_sigs[36]}    ),//(pipe_rx00_start_block[1:0])
   .pipe_rx04_sync_header                  ( pipe_rx_4_sigs[38:37] ),//(pipe_rx00_sync_header[1:0])
   .pipe_rx04_status                       ( (PL_LINK_CAP_MAX_LINK_WIDTH >= 2 )? rx_status : 3'b0 ),//(pipe_rx00_status[2:0])
   .pipe_rx04_valid                        ( ~pipe_rx_4_sigs[34]    ),//(pipe_rx00_valid)
   .pipe_rx04_phy_status                   ( (PL_LINK_CAP_MAX_LINK_WIDTH >= 4 )? phy_status : 1'b0    ),//(pipe_rx00_phy_status)
   .pipe_tx04_eq_done                      ( pipe_tx04_eq_done    ),//(pipe_tx00_eq_done)
   .pipe_tx04_eq_coeff                     ( 18'h00904 ),//(pipe_tx00_eq_coeff[17:0])
   .pipe_rx04_eq_lp_new_tx_coeff_or_preset ( 18'h05 ),//(pipe_rx00_eq_lp_new_tx_coeff_or_preset[17:0])
   .pipe_rx04_eq_lp_lf_fs_sel              ( 1'b0    ),//(pipe_rx00_eq_lp_lf_fs_sel)
   .pipe_rx04_eq_lp_adapt_done             ( 1'b0    ),//(pipe_rx00_eq_lp_adapt_done)
   .pipe_rx04_eq_done                      ( pipe_rx04_eq_done    ),//(pipe_rx00_eq_done)
  //-----------------------------
  // pipe_rx05_sigs[83:0]
   .pipe_rx05_data                         ( pipe_rx_5_sigs[31: 0] ),//(pipe_rx00_data[31:0])
   .pipe_rx05_char_is_k                    ( pipe_rx_5_sigs[33:32] ),//(pipe_rx00_char_is_k[1:0])
   .pipe_rx05_data_valid                   ( pipe_rx_5_sigs[35]    ),//(pipe_rx00_data_valid)
   .pipe_rx05_elec_idle                    ( pipe_rx_5_sigs[34]    ),//(pipe_rx00_elec_idle)
   .pipe_rx05_start_block                  ( {1'b0, pipe_rx_5_sigs[36]}    ),//(pipe_rx00_start_block[1:0])
   .pipe_rx05_sync_header                  ( pipe_rx_5_sigs[38:37] ),//(pipe_rx00_sync_header[1:0])
   .pipe_rx05_status                       ( (PL_LINK_CAP_MAX_LINK_WIDTH >= 2 )? rx_status : 3'b0 ),//(pipe_rx00_status[2:0])
   .pipe_rx05_valid                        ( ~pipe_rx_5_sigs[34]    ),//(pipe_rx00_valid)
   .pipe_rx05_phy_status                   ( (PL_LINK_CAP_MAX_LINK_WIDTH >= 4 )? phy_status : 1'b0    ),//(pipe_rx00_phy_status)
   .pipe_tx05_eq_done                      ( pipe_tx05_eq_done    ),//(pipe_tx00_eq_done)
   .pipe_tx05_eq_coeff                     ( 18'h00904 ),//(pipe_tx00_eq_coeff[17:0])
   .pipe_rx05_eq_lp_new_tx_coeff_or_preset ( 18'h05 ),//(pipe_rx00_eq_lp_new_tx_coeff_or_preset[17:0])
   .pipe_rx05_eq_lp_lf_fs_sel              ( 1'b0    ),//(pipe_rx00_eq_lp_lf_fs_sel)
   .pipe_rx05_eq_lp_adapt_done             ( 1'b0    ),//(pipe_rx00_eq_lp_adapt_done)
   .pipe_rx05_eq_done                      ( pipe_rx05_eq_done    ),//(pipe_rx00_eq_done)
  //-----------------------------
  // pipe_rx06_sigs[83:0]
   .pipe_rx06_data                         ( pipe_rx_6_sigs[31: 0] ),//(pipe_rx00_data[31:0])
   .pipe_rx06_char_is_k                    ( pipe_rx_6_sigs[33:32] ),//(pipe_rx00_char_is_k[1:0])
   .pipe_rx06_data_valid                   ( pipe_rx_6_sigs[35]    ),//(pipe_rx00_data_valid)
   .pipe_rx06_elec_idle                    ( pipe_rx_6_sigs[34]    ),//(pipe_rx00_elec_idle)
   .pipe_rx06_start_block                  ( {1'b0, pipe_rx_6_sigs[36]}    ),//(pipe_rx00_start_block[1:0])
   .pipe_rx06_sync_header                  ( pipe_rx_6_sigs[38:37] ),//(pipe_rx00_sync_header[1:0])
   .pipe_rx06_status                       ( (PL_LINK_CAP_MAX_LINK_WIDTH >= 2 )? rx_status : 3'b0 ),//(pipe_rx00_status[2:0])
   .pipe_rx06_valid                        ( ~pipe_rx_6_sigs[34]    ),//(pipe_rx00_valid)
   .pipe_rx06_phy_status                   ( (PL_LINK_CAP_MAX_LINK_WIDTH >= 4 )? phy_status : 1'b0    ),//(pipe_rx00_phy_status)
   .pipe_tx06_eq_done                      ( pipe_tx06_eq_done    ),//(pipe_tx00_eq_done)
   .pipe_tx06_eq_coeff                     ( 18'h00904 ),//(pipe_tx00_eq_coeff[17:0])
   .pipe_rx06_eq_lp_new_tx_coeff_or_preset ( 18'h05 ),//(pipe_rx00_eq_lp_new_tx_coeff_or_preset[17:0])
   .pipe_rx06_eq_lp_lf_fs_sel              ( 1'b1    ),//(pipe_rx00_eq_lp_lf_fs_sel)
   .pipe_rx06_eq_lp_adapt_done             ( 1'b1    ),//(pipe_rx00_eq_lp_adapt_done)
   .pipe_rx06_eq_done                      ( pipe_rx06_eq_done    ),//(pipe_rx00_eq_done)
  //-----------------------------
  // pipe_rx07_sigs[83:0]
   .pipe_rx07_data                         ( pipe_rx_7_sigs[31: 0] ),//(pipe_rx00_data[31:0])
   .pipe_rx07_char_is_k                    ( pipe_rx_7_sigs[33:32] ),//(pipe_rx00_char_is_k[1:0])
   .pipe_rx07_data_valid                   ( pipe_rx_7_sigs[35]    ),//(pipe_rx00_data_valid)
   .pipe_rx07_elec_idle                    ( pipe_rx_7_sigs[34]    ),//(pipe_rx00_elec_idle)
   .pipe_rx07_start_block                  ( {1'b0, pipe_rx_7_sigs[36]}    ),//(pipe_rx00_start_block[1:0])
   .pipe_rx07_sync_header                  ( pipe_rx_7_sigs[38:37] ),//(pipe_rx00_sync_header[1:0])
   .pipe_rx07_status                       ( (PL_LINK_CAP_MAX_LINK_WIDTH >= 2 )? rx_status : 3'b0 ),//(pipe_rx00_status[2:0])
   .pipe_rx07_valid                        ( ~pipe_rx_7_sigs[34]    ),//(pipe_rx00_valid)
   .pipe_rx07_phy_status                   ( (PL_LINK_CAP_MAX_LINK_WIDTH >= 4 )? phy_status : 1'b0     ),//(pipe_rx00_phy_status)
   .pipe_tx07_eq_done                      ( pipe_tx07_eq_done    ),//(pipe_tx00_eq_done)
   .pipe_tx07_eq_coeff                     ( 18'h00904 ),//(pipe_tx00_eq_coeff[17:0])
   .pipe_rx07_eq_lp_new_tx_coeff_or_preset ( 18'h05 ),//(pipe_rx00_eq_lp_new_tx_coeff_or_preset[17:0])
   .pipe_rx07_eq_lp_lf_fs_sel              ( 1'b1   ),//(pipe_rx00_eq_lp_lf_fs_sel)
   .pipe_rx07_eq_lp_adapt_done             ( 1'b1    ),//(pipe_rx00_eq_lp_adapt_done)
   .pipe_rx07_eq_done                      ( pipe_rx07_eq_done    ),//(pipe_rx00_eq_done)
  //-----------------------------
  // pipe_rx08_sigs[83:0]
   .pipe_rx08_data                         ( pipe_rx_8_sigs[31: 0] ),//(pipe_rx00_data[31:0])
   .pipe_rx08_char_is_k                    ( pipe_rx_8_sigs[33:32] ),//(pipe_rx00_char_is_k[1:0])
   .pipe_rx08_data_valid                   ( pipe_rx_8_sigs[35]    ),//(pipe_rx00_data_valid)
   .pipe_rx08_elec_idle                    ( pipe_rx_8_sigs[34]    ),//(pipe_rx00_elec_idle)
   .pipe_rx08_start_block                  ( {1'b0, pipe_rx_8_sigs[36]}    ),//(pipe_rx00_start_block[1:0])
   .pipe_rx08_sync_header                  ( pipe_rx_8_sigs[38:37] ),//(pipe_rx00_sync_header[1:0])
   .pipe_rx08_status                       ( (PL_LINK_CAP_MAX_LINK_WIDTH >= 2 )? rx_status : 3'b0 ),//(pipe_rx00_status[2:0])
   .pipe_rx08_valid                        ( ~pipe_rx_8_sigs[34]    ),//(pipe_rx00_valid)
   .pipe_rx08_phy_status                   ( (PL_LINK_CAP_MAX_LINK_WIDTH >= 8 )? phy_status : 1'b0  ),//(pipe_rx00_phy_status)
   .pipe_tx08_eq_done                      ( pipe_tx08_eq_done    ),//(pipe_tx00_eq_done)
   .pipe_tx08_eq_coeff                     ( 18'h00904 ),//(pipe_tx00_eq_coeff[17:0])
   .pipe_rx08_eq_lp_new_tx_coeff_or_preset ( 18'h05 ),//(pipe_rx00_eq_lp_new_tx_coeff_or_preset[17:0])
   .pipe_rx08_eq_lp_lf_fs_sel              ( 1'b1    ),//(pipe_rx00_eq_lp_lf_fs_sel)
   .pipe_rx08_eq_lp_adapt_done             ( 1'b1    ),//(pipe_rx00_eq_lp_adapt_done)
   .pipe_rx08_eq_done                      ( pipe_rx08_eq_done    ),//(pipe_rx00_eq_done)
  //-----------------------------
  // pipe_rx09_sigs[83:0]
   .pipe_rx09_data                         ( pipe_rx_9_sigs[31: 0] ),//(pipe_rx00_data[31:0])
   .pipe_rx09_char_is_k                    ( pipe_rx_9_sigs[33:32] ),//(pipe_rx00_char_is_k[1:0])
   .pipe_rx09_data_valid                   ( pipe_rx_9_sigs[35]    ),//(pipe_rx00_data_valid)
   .pipe_rx09_elec_idle                    ( pipe_rx_9_sigs[34]    ),//(pipe_rx00_elec_idle)
   .pipe_rx09_start_block                  ( {1'b0, pipe_rx_9_sigs[36]}    ),//(pipe_rx00_start_block[1:0])
   .pipe_rx09_sync_header                  ( pipe_rx_9_sigs[38:37] ),//(pipe_rx00_sync_header[1:0])
   .pipe_rx09_status                       ( (PL_LINK_CAP_MAX_LINK_WIDTH >= 2 )? rx_status : 3'b0  ),//(pipe_rx00_status[2:0])
   .pipe_rx09_valid                        ( ~pipe_rx_9_sigs[34]    ),//(pipe_rx00_valid)
   .pipe_rx09_phy_status                   ( (PL_LINK_CAP_MAX_LINK_WIDTH >= 8 )? phy_status : 1'b0    ),//(pipe_rx00_phy_status)
   .pipe_tx09_eq_done                      ( pipe_tx09_eq_done    ),//(pipe_tx00_eq_done)
   .pipe_tx09_eq_coeff                     ( 18'h00904 ),//(pipe_tx00_eq_coeff[17:0])
   .pipe_rx09_eq_lp_new_tx_coeff_or_preset ( 18'h05 ),//(pipe_rx00_eq_lp_new_tx_coeff_or_preset[17:0])
   .pipe_rx09_eq_lp_lf_fs_sel              ( 1'b1    ),//(pipe_rx00_eq_lp_lf_fs_sel)
   .pipe_rx09_eq_lp_adapt_done             ( 1'b1    ),//(pipe_rx00_eq_lp_adapt_done)
   .pipe_rx09_eq_done                      ( pipe_rx09_eq_done    ),//(pipe_rx00_eq_done)
  //-----------------------------
  // pipe_rx10_sigs[83:0]
   .pipe_rx10_data                         ( pipe_rx_10_sigs[31: 0] ),//(pipe_rx00_data[31:0])
   .pipe_rx10_char_is_k                    ( pipe_rx_10_sigs[33:32] ),//(pipe_rx00_char_is_k[1:0])
   .pipe_rx10_data_valid                   ( pipe_rx_10_sigs[35]    ),//(pipe_rx00_data_valid)
   .pipe_rx10_elec_idle                    ( pipe_rx_10_sigs[34]    ),//(pipe_rx00_elec_idle)
   .pipe_rx10_start_block                  ( {1'b0, pipe_rx_10_sigs[36]}    ),//(pipe_rx00_start_block[1:0])
   .pipe_rx10_sync_header                  ( pipe_rx_10_sigs[38:37] ),//(pipe_rx00_sync_header[1:0])
   .pipe_rx10_status                       ( (PL_LINK_CAP_MAX_LINK_WIDTH >= 2 )? rx_status : 3'b0 ),//(pipe_rx00_status[2:0])
   .pipe_rx10_valid                        ( ~pipe_rx_10_sigs[34]    ),//(pipe_rx00_valid)
   .pipe_rx10_phy_status                   ( (PL_LINK_CAP_MAX_LINK_WIDTH >= 8 )? phy_status : 1'b0   ),//(pipe_rx00_phy_status)
   .pipe_tx10_eq_done                      ( pipe_tx10_eq_done    ),//(pipe_tx00_eq_done)
   .pipe_tx10_eq_coeff                     ( 18'h00904 ),//(pipe_tx00_eq_coeff[17:0])
   .pipe_rx10_eq_lp_new_tx_coeff_or_preset ( 18'h05 ),//(pipe_rx00_eq_lp_new_tx_coeff_or_preset[17:0])
   .pipe_rx10_eq_lp_lf_fs_sel              ( 1'b1    ),//(pipe_rx00_eq_lp_lf_fs_sel)
   .pipe_rx10_eq_lp_adapt_done             ( 1'b1    ),//(pipe_rx00_eq_lp_adapt_done)
   .pipe_rx10_eq_done                      ( pipe_rx10_eq_done    ),//(pipe_rx00_eq_done)
  //-----------------------------
  // pipe_rx11_sigs[83:0]
   .pipe_rx11_data                         ( pipe_rx_11_sigs[31: 0] ),//(pipe_rx00_data[31:0])
   .pipe_rx11_char_is_k                    ( pipe_rx_11_sigs[33:32] ),//(pipe_rx00_char_is_k[1:0])
   .pipe_rx11_data_valid                   ( pipe_rx_11_sigs[35]    ),//(pipe_rx00_data_valid)
   .pipe_rx11_elec_idle                    ( pipe_rx_11_sigs[34]    ),//(pipe_rx00_elec_idle)
   .pipe_rx11_start_block                  ( {1'b0, pipe_rx_11_sigs[36]}    ),//(pipe_rx00_start_block[1:0])
   .pipe_rx11_sync_header                  ( pipe_rx_11_sigs[38:37] ),//(pipe_rx00_sync_header[1:0])
   .pipe_rx11_status                       ( (PL_LINK_CAP_MAX_LINK_WIDTH >= 2 )? rx_status : 3'b0 ),//(pipe_rx00_status[2:0])
   .pipe_rx11_valid                        ( ~pipe_rx_11_sigs[34]    ),//(pipe_rx00_valid)
   .pipe_rx11_phy_status                   ( (PL_LINK_CAP_MAX_LINK_WIDTH >= 8 )? phy_status : 1'b0    ),//(pipe_rx00_phy_status)
   .pipe_tx11_eq_done                      ( pipe_tx11_eq_done    ),//(pipe_tx00_eq_done)
   .pipe_tx11_eq_coeff                     ( 18'h00904 ),//(pipe_tx00_eq_coeff[17:0])
   .pipe_rx11_eq_lp_new_tx_coeff_or_preset ( 18'h05 ),//(pipe_rx00_eq_lp_new_tx_coeff_or_preset[17:0])
   .pipe_rx11_eq_lp_lf_fs_sel              ( 1'b1    ),//(pipe_rx00_eq_lp_lf_fs_sel)
   .pipe_rx11_eq_lp_adapt_done             ( 1'b1    ),//(pipe_rx00_eq_lp_adapt_done)
   .pipe_rx11_eq_done                      ( pipe_rx11_eq_done    ),//(pipe_rx00_eq_done)
  //-----------------------------
  // pipe_rx12_sigs[83:0]
   .pipe_rx12_data                         ( pipe_rx_12_sigs[31: 0] ),//(pipe_rx00_data[31:0])
   .pipe_rx12_char_is_k                    ( pipe_rx_12_sigs[33:32] ),//(pipe_rx00_char_is_k[1:0])
   .pipe_rx12_data_valid                   ( pipe_rx_12_sigs[35]    ),//(pipe_rx00_data_valid)
   .pipe_rx12_elec_idle                    ( pipe_rx_12_sigs[34]    ),//(pipe_rx00_elec_idle)
   .pipe_rx12_start_block                  ( {1'b0, pipe_rx_12_sigs[36]}    ),//(pipe_rx00_start_block[1:0])
   .pipe_rx12_sync_header                  ( pipe_rx_12_sigs[38:37] ),//(pipe_rx00_sync_header[1:0])
   .pipe_rx12_status                       ( (PL_LINK_CAP_MAX_LINK_WIDTH >= 2 )? rx_status : 3'b0 ),//(pipe_rx00_status[2:0])
   .pipe_rx12_valid                        ( ~pipe_rx_12_sigs[34]    ),//(pipe_rx00_valid)
   .pipe_rx12_phy_status                   ( (PL_LINK_CAP_MAX_LINK_WIDTH >= 8 )? phy_status : 1'b0    ),//(pipe_rx00_phy_status)
   .pipe_tx12_eq_done                      ( pipe_tx12_eq_done    ),//(pipe_tx00_eq_done)
   .pipe_tx12_eq_coeff                     ( 18'h00904 ),//(pipe_tx00_eq_coeff[17:0])
   .pipe_rx12_eq_lp_new_tx_coeff_or_preset ( 18'h05 ),//(pipe_rx00_eq_lp_new_tx_coeff_or_preset[17:0])
   .pipe_rx12_eq_lp_lf_fs_sel              ( 1'b1    ),//(pipe_rx00_eq_lp_lf_fs_sel)
   .pipe_rx12_eq_lp_adapt_done             ( 1'b1    ),//(pipe_rx00_eq_lp_adapt_done)
   .pipe_rx12_eq_done                      ( pipe_rx12_eq_done    ),//(pipe_rx00_eq_done)
  //-----------------------------
  // pipe_rx13_sigs[83:0]
   .pipe_rx13_data                         ( pipe_rx_13_sigs[31: 0] ),//(pipe_rx00_data[31:0])
   .pipe_rx13_char_is_k                    ( pipe_rx_13_sigs[33:32] ),//(pipe_rx00_char_is_k[1:0])
   .pipe_rx13_data_valid                   ( pipe_rx_13_sigs[35]    ),//(pipe_rx00_data_valid)
   .pipe_rx13_elec_idle                    ( pipe_rx_13_sigs[34]    ),//(pipe_rx00_elec_idle)
   .pipe_rx13_start_block                  ( {1'b0, pipe_rx_13_sigs[36]}    ),//(pipe_rx00_start_block[1:0])
   .pipe_rx13_sync_header                  ( pipe_rx_13_sigs[38:37] ),//(pipe_rx00_sync_header[1:0])
   .pipe_rx13_status                       ( (PL_LINK_CAP_MAX_LINK_WIDTH >= 2 )? rx_status : 3'b0 ),//(pipe_rx00_status[2:0])
   .pipe_rx13_valid                        ( ~pipe_rx_13_sigs[34]    ),//(pipe_rx00_valid)
   .pipe_rx13_phy_status                   ( (PL_LINK_CAP_MAX_LINK_WIDTH >= 8 )? phy_status : 1'b0    ),//(pipe_rx00_phy_status)
   .pipe_tx13_eq_done                      ( pipe_tx13_eq_done    ),//(pipe_tx00_eq_done)
   .pipe_tx13_eq_coeff                     ( 18'h00904 ),//(pipe_tx00_eq_coeff[17:0])
   .pipe_rx13_eq_lp_new_tx_coeff_or_preset ( 18'h05 ),//(pipe_rx00_eq_lp_new_tx_coeff_or_preset[17:0])
   .pipe_rx13_eq_lp_lf_fs_sel              ( 1'b1    ),//(pipe_rx00_eq_lp_lf_fs_sel)
   .pipe_rx13_eq_lp_adapt_done             ( 1'b1    ),//(pipe_rx00_eq_lp_adapt_done)
   .pipe_rx13_eq_done                      ( pipe_rx13_eq_done    ),//(pipe_rx00_eq_done)
  //-----------------------------
  // pipe_rx14_sigs[83:0]
   .pipe_rx14_data                         ( pipe_rx_14_sigs[31: 0] ),//(pipe_rx00_data[31:0])
   .pipe_rx14_char_is_k                    ( pipe_rx_14_sigs[33:32] ),//(pipe_rx00_char_is_k[1:0])
   .pipe_rx14_data_valid                   ( pipe_rx_14_sigs[35]    ),//(pipe_rx00_data_valid)
   .pipe_rx14_elec_idle                    ( pipe_rx_14_sigs[34]    ),//(pipe_rx00_elec_idle)
   .pipe_rx14_start_block                  ( {1'b0, pipe_rx_14_sigs[36] }   ),//(pipe_rx00_start_block[1:0])
   .pipe_rx14_sync_header                  ( pipe_rx_14_sigs[38:37] ),//(pipe_rx00_sync_header[1:0])
   .pipe_rx14_status                       ( (PL_LINK_CAP_MAX_LINK_WIDTH >= 2 )? rx_status : 3'b0 ),//(pipe_rx00_status[2:0])
   .pipe_rx14_valid                        ( ~pipe_rx_14_sigs[34]    ),//(pipe_rx00_valid)
   .pipe_rx14_phy_status                   ( (PL_LINK_CAP_MAX_LINK_WIDTH >= 8 )? phy_status : 1'b0     ),//(pipe_rx00_phy_status)
   .pipe_tx14_eq_done                      ( pipe_tx14_eq_done    ),//(pipe_tx00_eq_done)
   .pipe_tx14_eq_coeff                     ( 18'h00904 ),//(pipe_tx00_eq_coeff[17:0])
   .pipe_rx14_eq_lp_new_tx_coeff_or_preset ( 18'h05 ),//(pipe_rx00_eq_lp_new_tx_coeff_or_preset[17:0])
   .pipe_rx14_eq_lp_lf_fs_sel              ( 1'b1    ),//(pipe_rx00_eq_lp_lf_fs_sel)
   .pipe_rx14_eq_lp_adapt_done             ( 1'b1    ),//(pipe_rx00_eq_lp_adapt_done)
   .pipe_rx14_eq_done                      ( pipe_rx14_eq_done    ),//(pipe_rx00_eq_done)
  //-----------------------------
  // pipe_rx15_sigs[83:0]
   .pipe_rx15_data                         ( pipe_rx_15_sigs[31: 0] ),//(pipe_rx00_data[31:0])
   .pipe_rx15_char_is_k                    ( pipe_rx_15_sigs[33:32] ),//(pipe_rx00_char_is_k[1:0])
   .pipe_rx15_data_valid                   ( pipe_rx_15_sigs[35]    ),//(pipe_rx00_data_valid)
   .pipe_rx15_elec_idle                    ( pipe_rx_15_sigs[34]    ),//(pipe_rx00_elec_idle)
   .pipe_rx15_start_block                  ( {1'b0, pipe_rx_15_sigs[36] }   ),//(pipe_rx00_start_block[1:0])
   .pipe_rx15_sync_header                  ( pipe_rx_15_sigs[38:37] ),//(pipe_rx00_sync_header[1:0])
   .pipe_rx15_status                       ( (PL_LINK_CAP_MAX_LINK_WIDTH >= 2 )? rx_status : 3'b0 ),//(pipe_rx00_status[2:0])
   .pipe_rx15_valid                        ( ~pipe_rx_15_sigs[34]    ),//(pipe_rx00_valid)
   .pipe_rx15_phy_status                   ( (PL_LINK_CAP_MAX_LINK_WIDTH >= 8 )? phy_status : 1'b0    ),//(pipe_rx00_phy_status)
   .pipe_tx15_eq_done                      ( pipe_tx15_eq_done    ),//(pipe_tx00_eq_done)
   .pipe_tx15_eq_coeff                     ( 18'h00904 ),//(pipe_tx00_eq_coeff[17:0])
   .pipe_rx15_eq_lp_new_tx_coeff_or_preset ( 18'h05 ),//(pipe_rx00_eq_lp_new_tx_coeff_or_preset[17:0])
   .pipe_rx15_eq_lp_lf_fs_sel              ( 1'b1    ),//(pipe_rx00_eq_lp_lf_fs_sel)
   .pipe_rx15_eq_lp_adapt_done             ( 1'b1    ),//(pipe_rx00_eq_lp_adapt_done)
   .pipe_rx15_eq_done                      ( pipe_rx15_eq_done    )//(pipe_rx00_eq_done)

  // -------------------------------------------------------------------------------------
   ,.pl_gen2_upstream_prefer_deemph(pl_gen2_upstream_prefer_deemph)
   ,.pl_eq_in_progress(pl_eq_in_progress)
   ,.pl_eq_phase(pl_eq_phase[1:0])
   ,.pl_eq_reset_eieos_count(1'b0)
   ,.pl_redo_eq(pl_redo_eq)
   ,.pl_redo_eq_speed(pl_redo_eq_speed)
   ,.pl_eq_mismatch(pl_eq_mismatch)
   ,.pl_redo_eq_pending(pl_redo_eq_pending)
   ,.m_axis_cq_tdata(m_axis_cq_tdata[AXI4_DATA_WIDTH-1:0])
   ,.s_axis_cc_tdata(s_axis_cc_tdata[AXI4_DATA_WIDTH-1:0])
   ,.s_axis_rq_tdata(s_axis_rq_tdata[AXI4_DATA_WIDTH-1:0])
   ,.m_axis_rc_tdata(m_axis_rc_tdata[AXI4_DATA_WIDTH-1:0])
   ,.m_axis_cq_tuser(m_axis_cq_tuser[AXI4_CQ_TUSER_WIDTH-1:0])
   ,.s_axis_cc_tuser(s_axis_cc_tuser[AXI4_CC_TUSER_WIDTH-1:0])
   ,.m_axis_cq_tlast(m_axis_cq_tlast)
   ,.s_axis_rq_tlast(s_axis_rq_tlast)
   ,.m_axis_rc_tlast(m_axis_rc_tlast)
   ,.s_axis_cc_tlast(s_axis_cc_tlast)
   ,.pcie_cq_np_req(pcie_cq_np_req_int[1:0])
   ,.pcie_cq_np_req_count(pcie_cq_np_req_count[5:0])
   ,.s_axis_rq_tuser(s_axis_rq_tuser[AXI4_RQ_TUSER_WIDTH-1:0])
   ,.m_axis_rc_tuser(m_axis_rc_tuser[AXI4_RC_TUSER_WIDTH-1:0])
   ,.m_axis_cq_tkeep(m_axis_cq_tkeep[AXI4_TKEEP_WIDTH-1:0])
   ,.s_axis_cc_tkeep(s_axis_cc_tkeep[AXI4_TKEEP_WIDTH-1:0])
   ,.s_axis_rq_tkeep(s_axis_rq_tkeep[AXI4_TKEEP_WIDTH-1:0])
   ,.m_axis_rc_tkeep(m_axis_rc_tkeep[AXI4_TKEEP_WIDTH-1:0])
   ,.m_axis_cq_tvalid(m_axis_cq_tvalid_int)
   ,.s_axis_cc_tvalid(s_axis_cc_tvalid_int)
   ,.s_axis_rq_tvalid(s_axis_rq_tvalid_int)
   ,.m_axis_rc_tvalid(m_axis_rc_tvalid_int)
   ,.m_axis_cq_tready({AXI4_CQ_TREADY_WIDTH{m_axis_cq_tready_int}})
   ,.s_axis_cc_tready(s_axis_cc_tready_int)
   ,.s_axis_rq_tready(s_axis_rq_tready_int)
   ,.m_axis_rc_tready({AXI4_RC_TREADY_WIDTH{m_axis_rc_tready_int}})
   ,.pcie_rq_seq_num0(pcie_rq_seq_num0[5:0])
   ,.pcie_rq_seq_num_vld0(pcie_rq_seq_num_vld0)
   ,.pcie_rq_seq_num1(pcie_rq_seq_num1[5:0])
   ,.pcie_rq_seq_num_vld1(pcie_rq_seq_num_vld1)
   ,.pcie_rq_tag0(pcie_rq_tag0[7:0])
   ,.pcie_rq_tag_vld0(pcie_rq_tag_vld0)
   ,.pcie_rq_tag1(pcie_rq_tag1[7:0])
   ,.pcie_rq_tag_vld1(pcie_rq_tag_vld1)
   ,.pcie_tfc_nph_av(pcie_tfc_nph_av[3:0])
   ,.pcie_tfc_npd_av(pcie_tfc_npd_av[3:0])
   ,.pcie_rq_tag_av(pcie_rq_tag_av[3:0])
   ,.axi_user_out( )
   ,.axi_user_in(8'h00)
   ,.cfg_mgmt_addr(cfg_mgmt_addr[9:0])
   ,.cfg_mgmt_function_number(cfg_mgmt_function_number[7:0])
   ,.cfg_mgmt_write(cfg_mgmt_write_int)
   ,.cfg_mgmt_write_data(cfg_mgmt_write_data[31:0])
   ,.cfg_mgmt_byte_enable(cfg_mgmt_byte_enable[3:0])
   ,.cfg_mgmt_read(cfg_mgmt_read_int)
   ,.cfg_mgmt_read_data(cfg_mgmt_read_data_sig[31:0])
   ,.cfg_mgmt_read_write_done(cfg_mgmt_read_write_done)
   ,.cfg_mgmt_debug_access(cfg_mgmt_debug_access)
   ,.cfg_phy_link_down(cfg_phy_link_down)
   ,.cfg_phy_link_status(cfg_phy_link_status[1:0])
   ,.cfg_negotiated_width(cfg_negotiated_width[2:0])
   ,.cfg_current_speed(cfg_current_speed[1:0])
   ,.cfg_max_payload(cfg_max_payload[1:0])
   ,.cfg_max_read_req(cfg_max_read_req[2:0])
   ,.cfg_function_status(cfg_function_status[15:0])
   ,.cfg_function_power_state(cfg_function_power_state[11:0])
   ,.cfg_link_power_state(cfg_link_power_state[1:0])
   ,.cfg_err_cor_out(cfg_err_cor_out)
   ,.cfg_err_nonfatal_out(cfg_err_nonfatal_out)
   ,.cfg_err_fatal_out(cfg_err_fatal_out)
   ,.cfg_local_error_valid(cfg_local_error_valid)
   ,.cfg_local_error_out(cfg_local_error_out[4:0])
   ,.cfg_ltr_enable()
   ,.cfg_ltssm_state(cfg_ltssm_state[5:0])
   ,.cfg_rx_pm_state(cfg_rx_pm_state[1:0])
   ,.cfg_tx_pm_state(cfg_tx_pm_state[1:0])
   ,.cfg_rcb_status(cfg_rcb_status[3:0])
   ,.cfg_obff_enable(cfg_obff_enable[1:0])
   ,.cfg_pl_status_change(cfg_pl_status_change)
   ,.cfg_tph_requester_enable(cfg_tph_requester_enable[3:0])
   ,.cfg_tph_st_mode(cfg_tph_st_mode[11:0])
   ,.cfg_msg_received(cfg_msg_received)
   ,.cfg_msg_received_data(cfg_msg_received_data[7:0])
   ,.cfg_msg_received_type(cfg_msg_received_type[4:0])
   ,.cfg_msg_transmit(cfg_msg_transmit_int)
   ,.cfg_msg_transmit_type(cfg_msg_transmit_type[2:0])
   ,.cfg_msg_transmit_data(cfg_msg_transmit_data[31:0])
   ,.cfg_msg_transmit_done(cfg_msg_transmit_done)
   ,.cfg_fc_ph(cfg_fc_ph[7:0])
   ,.cfg_fc_pd(cfg_fc_pd[11:0])
   ,.cfg_fc_nph(cfg_fc_nph[7:0])
   ,.cfg_fc_npd(cfg_fc_npd[11:0])
   ,.cfg_fc_cplh(cfg_fc_cplh[7:0])
   ,.cfg_fc_cpld(cfg_fc_cpld[11:0])
   ,.cfg_fc_sel(cfg_fc_sel[2:0])
   ,.cfg_fc_vc_sel(cfg_fc_vc_sel)
   ,.cfg_hot_reset_in(cfg_hot_reset_in_int)
   ,.cfg_hot_reset_out(cfg_hot_reset_out)
   ,.cfg_config_space_enable(cfg_config_space_enable_int)
   ,.cfg_dsn(cfg_dsn_int[63:0])
   ,.cfg_dev_id_pf0(cfg_dev_id_pf0[15:0])
   ,.cfg_dev_id_pf1(cfg_dev_id_pf1[15:0])
   ,.cfg_dev_id_pf2(cfg_dev_id_pf2[15:0])
   ,.cfg_dev_id_pf3(cfg_dev_id_pf3[15:0])
   ,.cfg_vend_id(cfg_vend_id[15:0])
   ,.cfg_rev_id_pf0(cfg_rev_id_pf0[7:0])
   ,.cfg_rev_id_pf1(cfg_rev_id_pf1[7:0])
   ,.cfg_rev_id_pf2(cfg_rev_id_pf2[7:0])
   ,.cfg_rev_id_pf3(cfg_rev_id_pf3[7:0])
   ,.cfg_subsys_id_pf0(cfg_subsys_id_pf0[15:0])
   ,.cfg_subsys_id_pf1(cfg_subsys_id_pf1[15:0])
   ,.cfg_subsys_id_pf2(cfg_subsys_id_pf2[15:0])
   ,.cfg_subsys_id_pf3(cfg_subsys_id_pf3[15:0])
   ,.cfg_subsys_vend_id(cfg_subsys_vend_id[15:0])
   ,.cfg_ds_port_number(cfg_ds_port_number[7:0])
   ,.cfg_ds_bus_number(cfg_ds_bus_number[7:0])
   ,.cfg_ds_device_number(cfg_ds_device_number[4:0])
   ,.cfg_ds_function_number(cfg_ds_function_number[2:0])
   ,.cfg_bus_number(cfg_bus_number[7:0])
   ,.cfg_power_state_change_ack(cfg_power_state_change_ack_int)
   ,.cfg_power_state_change_interrupt(cfg_power_state_change_interrupt)
   ,.cfg_err_cor_in(cfg_err_cor_in_int)
   ,.cfg_err_uncor_in(cfg_err_uncor_in_int)
   ,.cfg_flr_done(cfg_flr_done_int[3:0])
   ,.cfg_vf_flr_in_process(cfg_vf_flr_in_process[251:0])
   ,.cfg_vf_flr_done(cfg_vf_flr_done_int)
   ,.cfg_vf_flr_func_num(cfg_vf_flr_func_num_int[7:0])
   ,.cfg_vf_status(cfg_vf_status[503:0])
   ,.cfg_vf_power_state(cfg_vf_power_state[755:0])
   ,.cfg_vf_tph_requester_enable( cfg_vf_tph_requester_enable[251:0])
   ,.cfg_vf_tph_st_mode(cfg_vf_tph_st_mode[755:0])
   ,.cfg_interrupt_msix_vf_enable(cfg_interrupt_msix_vf_enable[251:0])
   ,.cfg_interrupt_msix_vf_mask(cfg_interrupt_msix_vf_mask[251:0])
   ,.cfg_pri_control(cfg_pri_control)                         // 2 bits per PF
   ,.cfg_ats_control_enable(cfg_ats_control_enable)           // 1 bit (E) per
   ,.cfg_vf_ats_control_enable(cfg_vf_ats_control_enable)     // 1 bit (E) per
   ,.cfg_pasid_control(cfg_pasid_control)                     // 3 bits per PF
   ,.cfg_max_pasid_width_control(cfg_max_pasid_width_control) // 5 bits per PF
   ,.cfg_flr_in_process(cfg_flr_in_process[3:0])
   ,.cfg_req_pm_transition_l23_ready(cfg_req_pm_transition_l23_ready_int)
   ,.cfg_link_training_enable(cfg_link_training_enable_int)
   ,.cfg_interrupt_int(cfg_interrupt_int_int[3:0])
   ,.cfg_interrupt_sent(cfg_interrupt_sent)
   ,.cfg_interrupt_pending(cfg_interrupt_pending_int[3:0])
   ,.cfg_interrupt_msi_enable(cfg_interrupt_msi_enable[3:0])
   ,.cfg_interrupt_msi_int(cfg_interrupt_msi_int_int[31:0])
   ,.cfg_interrupt_msi_sent(cfg_interrupt_msi_sent)
   ,.cfg_interrupt_msi_fail(cfg_interrupt_msi_fail)
   ,.cfg_interrupt_msi_mmenable(cfg_interrupt_msi_mmenable[11:0])
   ,.cfg_interrupt_msi_pending_status(cfg_interrupt_msi_pending_status[31:0])
   ,.cfg_interrupt_msi_pending_status_function_num(cfg_interrupt_msi_pending_status_function_num[1:0])
   ,.cfg_interrupt_msi_pending_status_data_enable(cfg_interrupt_msi_pending_status_data_enable_int)
   ,.cfg_interrupt_msi_mask_update(cfg_interrupt_msi_mask_update)
   ,.cfg_interrupt_msi_select(cfg_interrupt_msi_select[1:0])
   ,.cfg_interrupt_msi_data(cfg_interrupt_msi_data[31:0])
   ,.cfg_interrupt_msix_enable(cfg_interrupt_msix_enable[3:0])
   ,.cfg_interrupt_msix_mask(cfg_interrupt_msix_mask[3:0])
   ,.cfg_interrupt_msix_address(cfg_interrupt_msix_address[63:0])
   ,.cfg_interrupt_msix_data(cfg_interrupt_msix_data[31:0])
   ,.cfg_interrupt_msix_int(cfg_interrupt_msix_int_int)
   ,.cfg_interrupt_msix_vec_pending(cfg_interrupt_msix_vec_pending_int[1:0])
   ,.cfg_interrupt_msix_vec_pending_status(cfg_interrupt_msix_vec_pending_status)
   ,.cfg_interrupt_msi_attr(cfg_interrupt_msi_attr[2:0])
   ,.cfg_interrupt_msi_tph_present(cfg_interrupt_msi_tph_present)
   ,.cfg_interrupt_msi_tph_type(cfg_interrupt_msi_tph_type[1:0])
   ,.cfg_interrupt_msi_tph_st_tag(cfg_interrupt_msi_tph_st_tag[7:0])
   ,.cfg_interrupt_msi_function_number(cfg_interrupt_msi_function_number[7:0])
   ,.cfg_ext_read_received(cfg_ext_read_received_i)
   ,.cfg_ext_write_received(cfg_ext_write_received_i)
   ,.cfg_ext_register_number(cfg_ext_register_number_i[9:0])
   ,.cfg_ext_function_number(cfg_ext_function_number_i[7:0])
   ,.cfg_ext_write_data(cfg_ext_write_data_i[31:0])
   ,.cfg_ext_write_byte_enable(cfg_ext_write_byte_enable_i[3:0])
   ,.cfg_ext_read_data(cfg_ext_read_data_int[31:0])
   ,.cfg_ext_read_data_valid(cfg_ext_read_data_valid_int)
   ,.cfg_pm_aspm_l1_entry_reject(cfg_pm_aspm_l1_entry_reject_int)
   ,.cfg_pm_aspm_tx_l0s_entry_disable(cfg_pm_aspm_tx_l0s_entry_disable_int)
   ,.user_tph_stt_func_num(8'h00)
   ,.user_tph_stt_index(6'b0)
   ,.user_tph_stt_rd_en(1'b0)
   ,.user_tph_stt_rd_data()
   ,.conf_req_type (conf_req_type)
   ,.conf_req_reg_num (conf_req_reg_num)
   ,.conf_req_data (conf_req_data)
   ,.conf_req_valid(conf_req_valid_int)
   ,.conf_req_ready(conf_req_ready_int)
   ,.conf_resp_rdata(conf_resp_rdata[31:0])
   ,.conf_resp_valid(conf_resp_valid)
   ,.conf_mcap_design_switch (mcap_design_switch)
   ,.conf_mcap_eos()
   ,.conf_mcap_in_use_by_pcie(mcap_pcie_request)
   ,.conf_mcap_request_by_conf(mcap_external_request_int)

   ,.drp_clk(drp_clk_int)
   ,.drp_en(drp_en_int)
   ,.drp_we(drp_we_int)
   ,.drp_addr(drp_addr_int)
   ,.drp_di(drp_di_int)
   ,.drp_rdy(drp_rdy_int)
   ,.drp_do(drp_do_int)
   ,.pipe_clk(pipe_clk)
   ,.core_clk(core_clk)
   ,.user_clk(user_clk)
   ,.user_clk2(user_clk2)
   ,.user_clk_en(user_clk_en)
   ,.mcap_clk(mcap_clk_int)
   ,.mcap_rst_b(mcap_rst_b)
   ,.pcie_perst0_b(pcie_perst0_b)
   ,.pcie_perst1_b(pcie_perst1_b)
   ,.mgmt_reset_n(mgmt_reset_n)
   ,.phy_rdy(phy_rdy)
  //-------------------------------------------
  // CCIX Transmit TLP Interface
  //-------------------------------------------
   ,.s_axis_ccix_tx_tdata(s_axis_ccix_tx_tdata)
   ,.s_axis_ccix_tx_tvalid(s_axis_ccix_tx_tvalid)
   ,.s_axis_ccix_tx_tuser(s_axis_ccix_tx_tuser)
   ,.ccix_tx_credit_gnt(ccix_tx_credit_gnt)
   ,.ccix_tx_credit_rtn(ccix_tx_credit_rtn)
   ,.ccix_tx_active_req(ccix_tx_active_req)
   ,.ccix_tx_active_ack(ccix_tx_active_ack)
   ,.ccix_tx_deact_hint(ccix_tx_deact_hint)
  //-----------------------------------------------------------------------
  // CCIX Receive TLP Interface
  // Data to CCIX protocol processing block
  //-----------------------------------------------------------------------
   ,.m_axis_ccix_rx_tdata(m_axis_ccix_rx_tdata) // 256-bit data
   ,.m_axis_ccix_rx_tvalid(m_axis_ccix_rx_tvalid)
   ,.m_axis_ccix_rx_tuser(m_axis_ccix_rx_tuser) // tuser bus
   ,.ccix_rx_credit_grant(ccix_rx_credit_grant)
   ,.ccix_rx_credit_return(ccix_rx_credit_return)
   ,.ccix_rx_credit_av(ccix_rx_credit_av)
   ,.ccix_rx_active_req (ccix_rx_active_req)
   ,.ccix_rx_active_ack (ccix_rx_active_ack)
   ,.ccix_rx_deact_hint (ccix_rx_deact_hint)
   ,.cfg_vc1_enable (cfg_vc1_enable)
   ,.cfg_vc1_negotiation_pending (cfg_vc1_negotiation_pending)
   ,.ccix_optimized_tlp_tx_and_rx_enable (ccix_optimized_tlp_tx_and_rx_enable_i)
  );

  reg [3:0] pipe_rx00_eq_control_reg = 4'b0;
  reg [3:0] pipe_rx01_eq_control_reg = 4'b0;
  reg [3:0] pipe_rx02_eq_control_reg = 4'b0;
  reg [3:0] pipe_rx03_eq_control_reg = 4'b0;
  reg [3:0] pipe_rx04_eq_control_reg = 4'b0;
  reg [3:0] pipe_rx05_eq_control_reg = 4'b0;
  reg [3:0] pipe_rx06_eq_control_reg = 4'b0;
  reg [3:0] pipe_rx07_eq_control_reg = 4'b0;
  reg [3:0] pipe_rx08_eq_control_reg = 4'b0;
  reg [3:0] pipe_rx09_eq_control_reg = 4'b0;
  reg [3:0] pipe_rx10_eq_control_reg = 4'b0;
  reg [3:0] pipe_rx11_eq_control_reg = 4'b0;
  reg [3:0] pipe_rx12_eq_control_reg = 4'b0;
  reg [3:0] pipe_rx13_eq_control_reg = 4'b0;
  reg [3:0] pipe_rx14_eq_control_reg = 4'b0;
  reg [3:0] pipe_rx15_eq_control_reg = 4'b0;
  reg [3:0] pipe_tx00_eq_control_reg = 4'b0;
  reg [3:0] pipe_tx01_eq_control_reg = 4'b0;
  reg [3:0] pipe_tx02_eq_control_reg = 4'b0;
  reg [3:0] pipe_tx03_eq_control_reg = 4'b0;
  reg [3:0] pipe_tx04_eq_control_reg = 4'b0;
  reg [3:0] pipe_tx05_eq_control_reg = 4'b0;
  reg [3:0] pipe_tx06_eq_control_reg = 4'b0;
  reg [3:0] pipe_tx07_eq_control_reg = 4'b0;
  reg [3:0] pipe_tx08_eq_control_reg = 4'b0;
  reg [3:0] pipe_tx09_eq_control_reg = 4'b0;
  reg [3:0] pipe_tx10_eq_control_reg = 4'b0;
  reg [3:0] pipe_tx11_eq_control_reg = 4'b0;
  reg [3:0] pipe_tx12_eq_control_reg = 4'b0;
  reg [3:0] pipe_tx13_eq_control_reg = 4'b0;
  reg [3:0] pipe_tx14_eq_control_reg = 4'b0;
  reg [3:0] pipe_tx15_eq_control_reg = 4'b0;

  always @ (posedge pipe_clk)
  begin
   pipe_rx00_eq_control_reg     <= {pipe_rx00_eq_control_reg[1:0], pipe_rx00_eq_control};
   pipe_rx01_eq_control_reg     <= {pipe_rx01_eq_control_reg[1:0], pipe_rx01_eq_control};
   pipe_rx02_eq_control_reg     <= {pipe_rx02_eq_control_reg[1:0], pipe_rx02_eq_control};
   pipe_rx03_eq_control_reg     <= {pipe_rx03_eq_control_reg[1:0], pipe_rx03_eq_control};
   pipe_rx04_eq_control_reg     <= {pipe_rx04_eq_control_reg[1:0], pipe_rx04_eq_control};
   pipe_rx05_eq_control_reg     <= {pipe_rx05_eq_control_reg[1:0], pipe_rx05_eq_control};
   pipe_rx06_eq_control_reg     <= {pipe_rx06_eq_control_reg[1:0], pipe_rx06_eq_control};
   pipe_rx07_eq_control_reg     <= {pipe_rx07_eq_control_reg[1:0], pipe_rx07_eq_control};
   pipe_rx08_eq_control_reg     <= {pipe_rx08_eq_control_reg[1:0], pipe_rx08_eq_control};
   pipe_rx09_eq_control_reg     <= {pipe_rx09_eq_control_reg[1:0], pipe_rx09_eq_control};
   pipe_rx10_eq_control_reg     <= {pipe_rx10_eq_control_reg[1:0], pipe_rx10_eq_control};
   pipe_rx11_eq_control_reg     <= {pipe_rx11_eq_control_reg[1:0], pipe_rx11_eq_control};
   pipe_rx12_eq_control_reg     <= {pipe_rx12_eq_control_reg[1:0], pipe_rx12_eq_control};
   pipe_rx13_eq_control_reg     <= {pipe_rx13_eq_control_reg[1:0], pipe_rx13_eq_control};
   pipe_rx14_eq_control_reg     <= {pipe_rx14_eq_control_reg[1:0], pipe_rx14_eq_control};
   pipe_rx15_eq_control_reg     <= {pipe_rx15_eq_control_reg[1:0], pipe_rx15_eq_control};

   pipe_tx00_eq_control_reg     <= {pipe_tx00_eq_control_reg[1:0], pipe_tx00_eq_control};
   pipe_tx01_eq_control_reg     <= {pipe_tx01_eq_control_reg[1:0], pipe_tx01_eq_control};
   pipe_tx02_eq_control_reg     <= {pipe_tx02_eq_control_reg[1:0], pipe_tx02_eq_control};
   pipe_tx03_eq_control_reg     <= {pipe_tx03_eq_control_reg[1:0], pipe_tx03_eq_control};
   pipe_tx04_eq_control_reg     <= {pipe_tx04_eq_control_reg[1:0], pipe_tx04_eq_control};
   pipe_tx05_eq_control_reg     <= {pipe_tx05_eq_control_reg[1:0], pipe_tx05_eq_control};
   pipe_tx06_eq_control_reg     <= {pipe_tx06_eq_control_reg[1:0], pipe_tx06_eq_control};
   pipe_tx07_eq_control_reg     <= {pipe_tx07_eq_control_reg[1:0], pipe_tx07_eq_control};
   pipe_tx08_eq_control_reg     <= {pipe_tx08_eq_control_reg[1:0], pipe_tx08_eq_control};
   pipe_tx09_eq_control_reg     <= {pipe_tx09_eq_control_reg[1:0], pipe_tx09_eq_control};
   pipe_tx10_eq_control_reg     <= {pipe_tx10_eq_control_reg[1:0], pipe_tx10_eq_control};
   pipe_tx11_eq_control_reg     <= {pipe_tx11_eq_control_reg[1:0], pipe_tx11_eq_control};
   pipe_tx12_eq_control_reg     <= {pipe_tx12_eq_control_reg[1:0], pipe_tx12_eq_control};
   pipe_tx13_eq_control_reg     <= {pipe_tx13_eq_control_reg[1:0], pipe_tx13_eq_control};
   pipe_tx14_eq_control_reg     <= {pipe_tx14_eq_control_reg[1:0], pipe_tx14_eq_control};
   pipe_tx15_eq_control_reg     <= {pipe_tx15_eq_control_reg[1:0], pipe_tx15_eq_control};

  end


  // generate rx*_eq_done
  assign pipe_rx00_eq_done = (pipe_rx00_eq_control_reg[3:2] != pipe_rx00_eq_control)? 1'b1 : 1'b0;
  assign pipe_rx01_eq_done = (pipe_rx01_eq_control_reg[3:2] != pipe_rx01_eq_control)? 1'b1 : 1'b0;
  assign pipe_rx02_eq_done = (pipe_rx02_eq_control_reg[3:2] != pipe_rx02_eq_control)? 1'b1 : 1'b0;
  assign pipe_rx03_eq_done = (pipe_rx03_eq_control_reg[3:2] != pipe_rx03_eq_control)? 1'b1 : 1'b0;
  assign pipe_rx04_eq_done = (pipe_rx04_eq_control_reg[3:2] != pipe_rx04_eq_control)? 1'b1 : 1'b0;
  assign pipe_rx05_eq_done = (pipe_rx05_eq_control_reg[3:2] != pipe_rx05_eq_control)? 1'b1 : 1'b0;
  assign pipe_rx06_eq_done = (pipe_rx06_eq_control_reg[3:2] != pipe_rx06_eq_control)? 1'b1 : 1'b0;
  assign pipe_rx07_eq_done = (pipe_rx07_eq_control_reg[3:2] != pipe_rx07_eq_control)? 1'b1 : 1'b0;
  assign pipe_rx08_eq_done = (pipe_rx08_eq_control_reg[3:2] != pipe_rx08_eq_control)? 1'b1 : 1'b0;
  assign pipe_rx09_eq_done = (pipe_rx09_eq_control_reg[3:2] != pipe_rx09_eq_control)? 1'b1 : 1'b0;
  assign pipe_rx10_eq_done = (pipe_rx10_eq_control_reg[3:2] != pipe_rx10_eq_control)? 1'b1 : 1'b0;
  assign pipe_rx11_eq_done = (pipe_rx11_eq_control_reg[3:2] != pipe_rx11_eq_control)? 1'b1 : 1'b0;
  assign pipe_rx12_eq_done = (pipe_rx12_eq_control_reg[3:2] != pipe_rx12_eq_control)? 1'b1 : 1'b0;
  assign pipe_rx13_eq_done = (pipe_rx13_eq_control_reg[3:2] != pipe_rx13_eq_control)? 1'b1 : 1'b0;
  assign pipe_rx14_eq_done = (pipe_rx14_eq_control_reg[3:2] != pipe_rx14_eq_control)? 1'b1 : 1'b0;
  assign pipe_rx15_eq_done = (pipe_rx15_eq_control_reg[3:2] != pipe_rx15_eq_control)? 1'b1 : 1'b0;
  // generate tx*_eq_done
  assign pipe_tx00_eq_done = (pipe_tx00_eq_control_reg[3:2] != pipe_tx00_eq_control)? 1'b1 : 1'b0;
  assign pipe_tx01_eq_done = (pipe_tx01_eq_control_reg[3:2] != pipe_tx01_eq_control)? 1'b1 : 1'b0;
  assign pipe_tx02_eq_done = (pipe_tx02_eq_control_reg[3:2] != pipe_tx02_eq_control)? 1'b1 : 1'b0;
  assign pipe_tx03_eq_done = (pipe_tx03_eq_control_reg[3:2] != pipe_tx03_eq_control)? 1'b1 : 1'b0;
  assign pipe_tx04_eq_done = (pipe_tx04_eq_control_reg[3:2] != pipe_tx04_eq_control)? 1'b1 : 1'b0;
  assign pipe_tx05_eq_done = (pipe_tx05_eq_control_reg[3:2] != pipe_tx05_eq_control)? 1'b1 : 1'b0;
  assign pipe_tx06_eq_done = (pipe_tx06_eq_control_reg[3:2] != pipe_tx06_eq_control)? 1'b1 : 1'b0;
  assign pipe_tx07_eq_done = (pipe_tx07_eq_control_reg[3:2] != pipe_tx07_eq_control)? 1'b1 : 1'b0;
  assign pipe_tx08_eq_done = (pipe_tx08_eq_control_reg[3:2] != pipe_tx08_eq_control)? 1'b1 : 1'b0;
  assign pipe_tx09_eq_done = (pipe_tx09_eq_control_reg[3:2] != pipe_tx09_eq_control)? 1'b1 : 1'b0;
  assign pipe_tx10_eq_done = (pipe_tx10_eq_control_reg[3:2] != pipe_tx10_eq_control)? 1'b1 : 1'b0;
  assign pipe_tx11_eq_done = (pipe_tx11_eq_control_reg[3:2] != pipe_tx11_eq_control)? 1'b1 : 1'b0;
  assign pipe_tx12_eq_done = (pipe_tx12_eq_control_reg[3:2] != pipe_tx12_eq_control)? 1'b1 : 1'b0;
  assign pipe_tx13_eq_done = (pipe_tx13_eq_control_reg[3:2] != pipe_tx13_eq_control)? 1'b1 : 1'b0;
  assign pipe_tx14_eq_done = (pipe_tx14_eq_control_reg[3:2] != pipe_tx14_eq_control)? 1'b1 : 1'b0;
  assign pipe_tx15_eq_done = (pipe_tx15_eq_control_reg[3:2] != pipe_tx15_eq_control)? 1'b1 : 1'b0;

 // Pipe mode tie-offs
 assign  common_commands_out[0]     = pipe_clk;
 assign  common_commands_out[3]     = pipe_tx0_rcvr_det;
 assign  common_commands_out[25:10] = 16'b0;
 assign  pipe_tx_0_sigs[83:42]      = 42'b0;
 assign  pipe_tx_1_sigs[83:42]      = 42'b0;
 assign  pipe_tx_2_sigs[83:42]      = 42'b0;
 assign  pipe_tx_3_sigs[83:42]      = 42'b0;
 assign  pipe_tx_4_sigs[83:42]      = 42'b0;
 assign  pipe_tx_5_sigs[83:42]      = 42'b0;
 assign  pipe_tx_6_sigs[83:42]      = 42'b0;
 assign  pipe_tx_7_sigs[83:42]      = 42'b0;
 assign  pipe_tx_8_sigs[83:42]      = 42'b0;
 assign  pipe_tx_9_sigs[83:42]      = 42'b0;
 assign  pipe_tx_10_sigs[83:42]     = 42'b0;
 assign  pipe_tx_11_sigs[83:42]     = 42'b0;
 assign  pipe_tx_12_sigs[83:42]     = 42'b0;
 assign  pipe_tx_13_sigs[83:42]     = 42'b0;
 assign  pipe_tx_14_sigs[83:42]     = 42'b0;
 assign  pipe_tx_15_sigs[83:42]     = 42'b0;

 end
endgenerate

generate if (EXT_PIPESIM == "FALSE")
begin
  pcie_bridge_ep_pcie4c_ip_pipe
 #(
    .TCQ(TCQ)
   ,.IMPL_TARGET(IMPL_TARGET)
   ,.AXISTEN_IF_EXT_512_INTFC_RAM_STYLE(AXISTEN_IF_EXT_512_INTFC_RAM_STYLE)
   ,.CRM_CORE_CLK_FREQ_500(CRM_CORE_CLK_FREQ_500)
   ,.CRM_USER_CLK_FREQ(CRM_USER_CLK_FREQ)
   ,.AXISTEN_IF_WIDTH(AXISTEN_IF_WIDTH)
   ,.AXISTEN_IF_EXT_512_CQ_STRADDLE(AXISTEN_IF_EXT_512_CQ_STRADDLE)
   ,.AXISTEN_IF_EXT_512_CC_STRADDLE(AXISTEN_IF_EXT_512_CC_STRADDLE)
   ,.AXISTEN_IF_EXT_512_RQ_STRADDLE(AXISTEN_IF_EXT_512_RQ_STRADDLE)
   ,.AXISTEN_IF_EXT_512_RC_STRADDLE(AXISTEN_IF_EXT_512_RC_STRADDLE)
   ,.AXISTEN_IF_EXT_512_RC_4TLP_STRADDLE(AXISTEN_IF_EXT_512_RC_4TLP_STRADDLE)
   ,.AXISTEN_IF_EXT_512(AXISTEN_IF_EXT_512)
   ,.AXISTEN_IF_CQ_ALIGNMENT_MODE(AXISTEN_IF_CQ_ALIGNMENT_MODE)
   ,.AXISTEN_IF_CC_ALIGNMENT_MODE(AXISTEN_IF_CC_ALIGNMENT_MODE)
   ,.AXISTEN_IF_RQ_ALIGNMENT_MODE(AXISTEN_IF_RQ_ALIGNMENT_MODE)
   ,.AXISTEN_IF_RC_ALIGNMENT_MODE(AXISTEN_IF_RC_ALIGNMENT_MODE)
   ,.AXISTEN_IF_RC_STRADDLE(AXISTEN_IF_RC_STRADDLE)
   ,.AXI4_DATA_WIDTH(AXI4_DATA_WIDTH)
   ,.AXI4_TKEEP_WIDTH(AXI4_TKEEP_WIDTH)
   ,.AXI4_CQ_TUSER_WIDTH(AXI4_CQ_TUSER_WIDTH)
   ,.AXI4_CC_TUSER_WIDTH(AXI4_CC_TUSER_WIDTH)
   ,.AXI4_RQ_TUSER_WIDTH(AXI4_RQ_TUSER_WIDTH)
   ,.AXI4_RC_TUSER_WIDTH(AXI4_RC_TUSER_WIDTH)
   ,.AXI4_CQ_TREADY_WIDTH(AXI4_CQ_TREADY_WIDTH)
   ,.AXI4_CC_TREADY_WIDTH(AXI4_CC_TREADY_WIDTH)
   ,.AXI4_RQ_TREADY_WIDTH(AXI4_RQ_TREADY_WIDTH)
   ,.AXI4_RC_TREADY_WIDTH(AXI4_RC_TREADY_WIDTH)
   ,.AXIS_CCIX_TX_TDATA_WIDTH(AXIS_CCIX_TX_TDATA_WIDTH)
   ,.AXIS_CCIX_RX_TDATA_WIDTH(AXIS_CCIX_RX_TDATA_WIDTH)
   ,.AXIS_CCIX_TX_TUSER_WIDTH(AXIS_CCIX_TX_TUSER_WIDTH)
   ,.AXIS_CCIX_RX_TUSER_WIDTH(AXIS_CCIX_RX_TUSER_WIDTH)
   ,.AXISTEN_IF_ENABLE_RX_MSG_INTFC(AXISTEN_IF_ENABLE_RX_MSG_INTFC)
   ,.AXISTEN_IF_ENABLE_MSG_ROUTE(AXISTEN_IF_ENABLE_MSG_ROUTE)
   ,.AXISTEN_IF_RX_PARITY_EN(AXISTEN_IF_RX_PARITY_EN)
   ,.AXISTEN_IF_TX_PARITY_EN(AXISTEN_IF_TX_PARITY_EN)
   ,.AXISTEN_IF_ENABLE_CLIENT_TAG(AXISTEN_IF_ENABLE_CLIENT_TAG)
   ,.AXISTEN_IF_ENABLE_256_TAGS(AXISTEN_IF_ENABLE_256_TAGS)
   ,.AXISTEN_IF_COMPL_TIMEOUT_REG0(AXISTEN_IF_COMPL_TIMEOUT_REG0)
   ,.AXISTEN_IF_COMPL_TIMEOUT_REG1(AXISTEN_IF_COMPL_TIMEOUT_REG1)
   ,.AXISTEN_IF_LEGACY_MODE_ENABLE(AXISTEN_IF_LEGACY_MODE_ENABLE)
   ,.AXISTEN_IF_ENABLE_MESSAGE_RID_CHECK(AXISTEN_IF_ENABLE_MESSAGE_RID_CHECK)
   ,.AXISTEN_IF_MSIX_TO_RAM_PIPELINE(AXISTEN_IF_MSIX_TO_RAM_PIPELINE)
   ,.AXISTEN_IF_MSIX_FROM_RAM_PIPELINE(AXISTEN_IF_MSIX_FROM_RAM_PIPELINE)
   ,.AXISTEN_IF_MSIX_RX_PARITY_EN(AXISTEN_IF_MSIX_RX_PARITY_EN)
   ,.AXISTEN_IF_ENABLE_INTERNAL_MSIX_TABLE(AXISTEN_IF_ENABLE_INTERNAL_MSIX_TABLE)
   ,.AXISTEN_IF_SIM_SHORT_CPL_TIMEOUT(AXISTEN_IF_SIM_SHORT_CPL_TIMEOUT)
   ,.AXISTEN_IF_CQ_EN_POISONED_MEM_WR(AXISTEN_IF_CQ_EN_POISONED_MEM_WR)
   ,.AXISTEN_IF_RQ_CC_REGISTERED_TREADY(AXISTEN_IF_RQ_CC_REGISTERED_TREADY)
   ,.PM_ASPML0S_TIMEOUT(PM_ASPML0S_TIMEOUT)
   ,.PM_L1_REENTRY_DELAY(PM_L1_REENTRY_DELAY)
   ,.PM_ASPML1_ENTRY_DELAY(PM_ASPML1_ENTRY_DELAY)
   ,.PM_ENABLE_SLOT_POWER_CAPTURE(PM_ENABLE_SLOT_POWER_CAPTURE)
   ,.PM_PME_SERVICE_TIMEOUT_DELAY(PM_PME_SERVICE_TIMEOUT_DELAY)
   ,.PM_PME_TURNOFF_ACK_DELAY(PM_PME_TURNOFF_ACK_DELAY)
   ,.PL_UPSTREAM_FACING(PL_UPSTREAM_FACING)
   ,.PL_LINK_CAP_MAX_LINK_WIDTH(PL_LINK_CAP_MAX_LINK_WIDTH)
   ,.PL_LINK_CAP_MAX_LINK_SPEED(PL_LINK_CAP_MAX_LINK_SPEED)
   ,.PL_DISABLE_DC_BALANCE(PL_DISABLE_DC_BALANCE)
   ,.PL_DISABLE_EI_INFER_IN_L0(PL_DISABLE_EI_INFER_IN_L0)
   ,.PL_N_FTS(PL_N_FTS)
   ,.PL_DISABLE_UPCONFIG_CAPABLE(PL_DISABLE_UPCONFIG_CAPABLE)
   ,.PL_DISABLE_RETRAIN_ON_FRAMING_ERROR(PL_DISABLE_RETRAIN_ON_FRAMING_ERROR)
   ,.PL_DISABLE_RETRAIN_ON_EB_ERROR(PL_DISABLE_RETRAIN_ON_EB_ERROR)
   ,.PL_DISABLE_RETRAIN_ON_SPECIFIC_FRAMING_ERROR(PL_DISABLE_RETRAIN_ON_SPECIFIC_FRAMING_ERROR)
   ,.PL_REPORT_ALL_PHY_ERRORS(PL_REPORT_ALL_PHY_ERRORS)
   ,.PL_DISABLE_LFSR_UPDATE_ON_SKP(PL_DISABLE_LFSR_UPDATE_ON_SKP)
   ,.PL_LANE0_EQ_CONTROL(PL_LANE0_EQ_CONTROL)
   ,.PL_LANE1_EQ_CONTROL(PL_LANE1_EQ_CONTROL)
   ,.PL_LANE2_EQ_CONTROL(PL_LANE2_EQ_CONTROL)
   ,.PL_LANE3_EQ_CONTROL(PL_LANE3_EQ_CONTROL)
   ,.PL_LANE4_EQ_CONTROL(PL_LANE4_EQ_CONTROL)
   ,.PL_LANE5_EQ_CONTROL(PL_LANE5_EQ_CONTROL)
   ,.PL_LANE6_EQ_CONTROL(PL_LANE6_EQ_CONTROL)
   ,.PL_LANE7_EQ_CONTROL(PL_LANE7_EQ_CONTROL)
   ,.PL_LANE8_EQ_CONTROL(PL_LANE8_EQ_CONTROL)
   ,.PL_LANE9_EQ_CONTROL(PL_LANE9_EQ_CONTROL)
   ,.PL_LANE10_EQ_CONTROL(PL_LANE10_EQ_CONTROL)
   ,.PL_LANE11_EQ_CONTROL(PL_LANE11_EQ_CONTROL)
   ,.PL_LANE12_EQ_CONTROL(PL_LANE12_EQ_CONTROL)
   ,.PL_LANE13_EQ_CONTROL(PL_LANE13_EQ_CONTROL)
   ,.PL_LANE14_EQ_CONTROL(PL_LANE14_EQ_CONTROL)
   ,.PL_LANE15_EQ_CONTROL(PL_LANE15_EQ_CONTROL)
    //pragma translate_off
   ,.PL_EQ_BYPASS_PHASE23(PL_EQ_BYPASS_PHASE23)
    //pragma translate_on
   ,.PL_EQ_ADAPT_ITER_COUNT(PL_EQ_ADAPT_ITER_COUNT)
   ,.PL_EQ_ADAPT_REJECT_RETRY_COUNT(PL_EQ_ADAPT_REJECT_RETRY_COUNT)
   ,.PL_EQ_SHORT_ADAPT_PHASE(PL_EQ_SHORT_ADAPT_PHASE)
   ,.PL_EQ_ADAPT_DISABLE_COEFF_CHECK(PL_EQ_ADAPT_DISABLE_COEFF_CHECK)
   ,.PL_EQ_ADAPT_DISABLE_PRESET_CHECK(PL_EQ_ADAPT_DISABLE_PRESET_CHECK)
   ,.PL_EQ_DEFAULT_TX_PRESET(PL_EQ_DEFAULT_TX_PRESET)
   ,.PL_EQ_DEFAULT_RX_PRESET_HINT(PL_EQ_DEFAULT_RX_PRESET_HINT)
   ,.PL_EQ_RX_ADAPT_EQ_PHASE0(PL_EQ_RX_ADAPT_EQ_PHASE0)
   ,.PL_EQ_RX_ADAPT_EQ_PHASE1(PL_EQ_RX_ADAPT_EQ_PHASE1)
   ,.PL_EQ_DISABLE_MISMATCH_CHECK(PL_EQ_DISABLE_MISMATCH_CHECK)
   ,.PL_RX_L0S_EXIT_TO_RECOVERY(PL_RX_L0S_EXIT_TO_RECOVERY)
   ,.PL_EQ_TX_8G_EQ_TS2_ENABLE(PL_EQ_TX_8G_EQ_TS2_ENABLE)
   ,.PL_DISABLE_AUTO_EQ_SPEED_CHANGE_TO_GEN4(PL_DISABLE_AUTO_EQ_SPEED_CHANGE_TO_GEN4)
   ,.PL_DISABLE_AUTO_EQ_SPEED_CHANGE_TO_GEN3(PL_DISABLE_AUTO_EQ_SPEED_CHANGE_TO_GEN3)
   ,.PL_DISABLE_AUTO_SPEED_CHANGE_TO_GEN2(PL_DISABLE_AUTO_SPEED_CHANGE_TO_GEN2)
   ,.PL_DESKEW_ON_SKIP_IN_GEN12(PL_DESKEW_ON_SKIP_IN_GEN12)
   ,.PL_INFER_EI_DISABLE_REC_RC(PL_INFER_EI_DISABLE_REC_RC)
   ,.PL_INFER_EI_DISABLE_REC_SPD(PL_INFER_EI_DISABLE_REC_SPD)
   ,.PL_INFER_EI_DISABLE_LPBK_ACTIVE(PL_INFER_EI_DISABLE_LPBK_ACTIVE)
   ,.PL_RX_ADAPT_TIMER_RRL_GEN3(PL_RX_ADAPT_TIMER_RRL_GEN3)
   ,.PL_RX_ADAPT_TIMER_RRL_CLOBBER_TX_TS(PL_RX_ADAPT_TIMER_RRL_CLOBBER_TX_TS)
   ,.PL_RX_ADAPT_TIMER_RRL_GEN4(PL_RX_ADAPT_TIMER_RRL_GEN4)
   ,.PL_RX_ADAPT_TIMER_CLWS_GEN3(PL_RX_ADAPT_TIMER_CLWS_GEN3)
   ,.PL_RX_ADAPT_TIMER_CLWS_CLOBBER_TX_TS(PL_RX_ADAPT_TIMER_CLWS_CLOBBER_TX_TS)
   ,.PL_RX_ADAPT_TIMER_CLWS_GEN4(PL_RX_ADAPT_TIMER_CLWS_GEN4)
   ,.PL_DISABLE_LANE_REVERSAL(PL_DISABLE_LANE_REVERSAL)
   ,.PL_CFG_STATE_ROBUSTNESS_ENABLE(PL_CFG_STATE_ROBUSTNESS_ENABLE)
   ,.PL_REDO_EQ_SOURCE_SELECT(PL_REDO_EQ_SOURCE_SELECT)
   ,.PL_DEEMPH_SOURCE_SELECT(PL_DEEMPH_SOURCE_SELECT)
   ,.PL_EXIT_LOOPBACK_ON_EI_ENTRY(PL_EXIT_LOOPBACK_ON_EI_ENTRY)
   ,.PL_QUIESCE_GUARANTEE_DISABLE(PL_QUIESCE_GUARANTEE_DISABLE)
   ,.PL_SRIS_ENABLE(PL_SRIS_ENABLE)
   ,.PL_SRIS_SKPOS_GEN_SPD_VEC(PL_SRIS_SKPOS_GEN_SPD_VEC)
   ,.PL_SRIS_SKPOS_REC_SPD_VEC(PL_SRIS_SKPOS_REC_SPD_VEC)
  // synthesis translate_off
   ,.PL_SIM_FAST_LINK_TRAINING(PL_SIM_FAST_LINK_TRAINING)
  // synthesis translate_on
   ,.PL_USER_SPARE(PL_USER_SPARE)
   ,.LL_ACK_TIMEOUT_EN(LL_ACK_TIMEOUT_EN)
   ,.LL_ACK_TIMEOUT(LL_ACK_TIMEOUT)
   ,.LL_ACK_TIMEOUT_FUNC(LL_ACK_TIMEOUT_FUNC)
   ,.LL_REPLAY_TIMEOUT_EN(LL_REPLAY_TIMEOUT_EN)
   ,.LL_REPLAY_TIMEOUT(LL_REPLAY_TIMEOUT)
   ,.LL_REPLAY_TIMEOUT_FUNC(LL_REPLAY_TIMEOUT_FUNC)
   ,.LL_REPLAY_TO_RAM_PIPELINE(LL_REPLAY_TO_RAM_PIPELINE)
   ,.LL_REPLAY_FROM_RAM_PIPELINE(LL_REPLAY_FROM_RAM_PIPELINE)
   ,.LL_DISABLE_SCHED_TX_NAK(LL_DISABLE_SCHED_TX_NAK)
   ,.LL_TX_TLP_PARITY_CHK(LL_TX_TLP_PARITY_CHK)
   ,.LL_RX_TLP_PARITY_GEN(LL_RX_TLP_PARITY_GEN)
   ,.LL_USER_SPARE(LL_USER_SPARE)
   ,.IS_SWITCH_PORT(IS_SWITCH_PORT)
   ,.CFG_BYPASS_MODE_ENABLE(CFG_BYPASS_MODE_ENABLE)
   ,.TL_PF_ENABLE_REG(TL_PF_ENABLE_REG)
   ,.TL_CREDITS_CD(TL_CREDITS_CD)
   ,.TL_CREDITS_CH(TL_CREDITS_CH)
   ,.TL_COMPLETION_RAM_SIZE(TL_COMPLETION_RAM_SIZE)
   ,.TL_COMPLETION_RAM_NUM_TLPS(TL_COMPLETION_RAM_NUM_TLPS)
   ,.TL_CREDITS_NPD(TL_CREDITS_NPD)
   ,.TL_CREDITS_NPH(TL_CREDITS_NPH)
   ,.TL_CREDITS_PD(TL_CREDITS_PD)
   ,.TL_CREDITS_PH(TL_CREDITS_PH)
   ,.TL_RX_COMPLETION_TO_RAM_WRITE_PIPELINE(TL_RX_COMPLETION_TO_RAM_WRITE_PIPELINE)
   ,.TL_RX_COMPLETION_TO_RAM_READ_PIPELINE(TL_RX_COMPLETION_TO_RAM_READ_PIPELINE)
   ,.TL_RX_COMPLETION_FROM_RAM_READ_PIPELINE(TL_RX_COMPLETION_FROM_RAM_READ_PIPELINE)
   ,.TL_POSTED_RAM_SIZE(TL_POSTED_RAM_SIZE)
   ,.TL_RX_POSTED_TO_RAM_WRITE_PIPELINE(TL_RX_POSTED_TO_RAM_WRITE_PIPELINE)
   ,.TL_RX_POSTED_TO_RAM_READ_PIPELINE(TL_RX_POSTED_TO_RAM_READ_PIPELINE)
   ,.TL_RX_POSTED_FROM_RAM_READ_PIPELINE(TL_RX_POSTED_FROM_RAM_READ_PIPELINE)
   ,.TL_TX_MUX_STRICT_PRIORITY(TL_TX_MUX_STRICT_PRIORITY)
   ,.TL_TX_TLP_STRADDLE_ENABLE(TL_TX_TLP_STRADDLE_ENABLE)
   ,.TL_TX_TLP_TERMINATE_PARITY(TL_TX_TLP_TERMINATE_PARITY)
   ,.TL_FC_UPDATE_MIN_INTERVAL_TLP_COUNT(TL_FC_UPDATE_MIN_INTERVAL_TLP_COUNT)
   ,.TL_FC_UPDATE_MIN_INTERVAL_TIME(TL_FC_UPDATE_MIN_INTERVAL_TIME)
   ,.TL_USER_SPARE(TL_USER_SPARE)
   ,.PF0_CLASS_CODE(PF0_CLASS_CODE)
   ,.PF1_CLASS_CODE(PF1_CLASS_CODE)
   ,.PF2_CLASS_CODE(PF2_CLASS_CODE)
   ,.PF3_CLASS_CODE(PF3_CLASS_CODE)
   ,.PF0_INTERRUPT_PIN(PF0_INTERRUPT_PIN)
   ,.PF1_INTERRUPT_PIN(PF1_INTERRUPT_PIN)
   ,.PF2_INTERRUPT_PIN(PF2_INTERRUPT_PIN)
   ,.PF3_INTERRUPT_PIN(PF3_INTERRUPT_PIN)
   ,.PF0_CAPABILITY_POINTER(PF0_CAPABILITY_POINTER)
   ,.PF1_CAPABILITY_POINTER(PF1_CAPABILITY_POINTER)
   ,.PF2_CAPABILITY_POINTER(PF2_CAPABILITY_POINTER)
   ,.PF3_CAPABILITY_POINTER(PF3_CAPABILITY_POINTER)
   ,.VF0_CAPABILITY_POINTER(VF0_CAPABILITY_POINTER)
   ,.LEGACY_CFG_EXTEND_INTERFACE_ENABLE(LEGACY_CFG_EXTEND_INTERFACE_ENABLE)
   ,.EXTENDED_CFG_EXTEND_INTERFACE_ENABLE(EXTENDED_CFG_EXTEND_INTERFACE_ENABLE)
   ,.TL2CFG_IF_PARITY_CHK(TL2CFG_IF_PARITY_CHK)
   ,.HEADER_TYPE_OVERRIDE(HEADER_TYPE_OVERRIDE)
   ,.PF0_BAR0_CONTROL(PF0_BAR0_CONTROL)
   ,.PF1_BAR0_CONTROL(PF1_BAR0_CONTROL)
   ,.PF2_BAR0_CONTROL(PF2_BAR0_CONTROL)
   ,.PF3_BAR0_CONTROL(PF3_BAR0_CONTROL)
   ,.PF0_BAR0_APERTURE_SIZE(PF0_BAR0_APERTURE_SIZE)
   ,.PF1_BAR0_APERTURE_SIZE(PF1_BAR0_APERTURE_SIZE)
   ,.PF2_BAR0_APERTURE_SIZE(PF2_BAR0_APERTURE_SIZE)
   ,.PF3_BAR0_APERTURE_SIZE(PF3_BAR0_APERTURE_SIZE)
   ,.PF0_BAR1_CONTROL(PF0_BAR1_CONTROL)
   ,.PF1_BAR1_CONTROL(PF1_BAR1_CONTROL)
   ,.PF2_BAR1_CONTROL(PF2_BAR1_CONTROL)
   ,.PF3_BAR1_CONTROL(PF3_BAR1_CONTROL)
   ,.PF0_BAR1_APERTURE_SIZE(PF0_BAR1_APERTURE_SIZE)
   ,.PF1_BAR1_APERTURE_SIZE(PF1_BAR1_APERTURE_SIZE)
   ,.PF2_BAR1_APERTURE_SIZE(PF2_BAR1_APERTURE_SIZE)
   ,.PF3_BAR1_APERTURE_SIZE(PF3_BAR1_APERTURE_SIZE)
   ,.PF0_BAR2_CONTROL(PF0_BAR2_CONTROL)
   ,.PF1_BAR2_CONTROL(PF1_BAR2_CONTROL)
   ,.PF2_BAR2_CONTROL(PF2_BAR2_CONTROL)
   ,.PF3_BAR2_CONTROL(PF3_BAR2_CONTROL)
   ,.PF0_BAR2_APERTURE_SIZE(PF0_BAR2_APERTURE_SIZE)
   ,.PF1_BAR2_APERTURE_SIZE(PF1_BAR2_APERTURE_SIZE)
   ,.PF2_BAR2_APERTURE_SIZE(PF2_BAR2_APERTURE_SIZE)
   ,.PF3_BAR2_APERTURE_SIZE(PF3_BAR2_APERTURE_SIZE)
   ,.PF0_BAR3_CONTROL(PF0_BAR3_CONTROL)
   ,.PF1_BAR3_CONTROL(PF1_BAR3_CONTROL)
   ,.PF2_BAR3_CONTROL(PF2_BAR3_CONTROL)
   ,.PF3_BAR3_CONTROL(PF3_BAR3_CONTROL)
   ,.PF0_BAR3_APERTURE_SIZE(PF0_BAR3_APERTURE_SIZE)
   ,.PF1_BAR3_APERTURE_SIZE(PF1_BAR3_APERTURE_SIZE)
   ,.PF2_BAR3_APERTURE_SIZE(PF2_BAR3_APERTURE_SIZE)
   ,.PF3_BAR3_APERTURE_SIZE(PF3_BAR3_APERTURE_SIZE)
   ,.PF0_BAR4_CONTROL(PF0_BAR4_CONTROL)
   ,.PF1_BAR4_CONTROL(PF1_BAR4_CONTROL)
   ,.PF2_BAR4_CONTROL(PF2_BAR4_CONTROL)
   ,.PF3_BAR4_CONTROL(PF3_BAR4_CONTROL)
   ,.PF0_BAR4_APERTURE_SIZE(PF0_BAR4_APERTURE_SIZE)
   ,.PF1_BAR4_APERTURE_SIZE(PF1_BAR4_APERTURE_SIZE)
   ,.PF2_BAR4_APERTURE_SIZE(PF2_BAR4_APERTURE_SIZE)
   ,.PF3_BAR4_APERTURE_SIZE(PF3_BAR4_APERTURE_SIZE)
   ,.PF0_BAR5_CONTROL(PF0_BAR5_CONTROL)
   ,.PF1_BAR5_CONTROL(PF1_BAR5_CONTROL)
   ,.PF2_BAR5_CONTROL(PF2_BAR5_CONTROL)
   ,.PF3_BAR5_CONTROL(PF3_BAR5_CONTROL)
   ,.PF0_BAR5_APERTURE_SIZE(PF0_BAR5_APERTURE_SIZE)
   ,.PF1_BAR5_APERTURE_SIZE(PF1_BAR5_APERTURE_SIZE)
   ,.PF2_BAR5_APERTURE_SIZE(PF2_BAR5_APERTURE_SIZE)
   ,.PF3_BAR5_APERTURE_SIZE(PF3_BAR5_APERTURE_SIZE)
   ,.PF0_EXPANSION_ROM_ENABLE(PF0_EXPANSION_ROM_ENABLE)
   ,.PF1_EXPANSION_ROM_ENABLE(PF1_EXPANSION_ROM_ENABLE)
   ,.PF2_EXPANSION_ROM_ENABLE(PF2_EXPANSION_ROM_ENABLE)
   ,.PF3_EXPANSION_ROM_ENABLE(PF3_EXPANSION_ROM_ENABLE)
   ,.PF0_EXPANSION_ROM_APERTURE_SIZE(PF0_EXPANSION_ROM_APERTURE_SIZE)
   ,.PF1_EXPANSION_ROM_APERTURE_SIZE(PF1_EXPANSION_ROM_APERTURE_SIZE)
   ,.PF2_EXPANSION_ROM_APERTURE_SIZE(PF2_EXPANSION_ROM_APERTURE_SIZE)
   ,.PF3_EXPANSION_ROM_APERTURE_SIZE(PF3_EXPANSION_ROM_APERTURE_SIZE)
   ,.PF0_PCIE_CAP_NEXTPTR(PF0_PCIE_CAP_NEXTPTR)
   ,.PF1_PCIE_CAP_NEXTPTR(PF1_PCIE_CAP_NEXTPTR)
   ,.PF2_PCIE_CAP_NEXTPTR(PF2_PCIE_CAP_NEXTPTR)
   ,.PF3_PCIE_CAP_NEXTPTR(PF3_PCIE_CAP_NEXTPTR)
   ,.VFG0_PCIE_CAP_NEXTPTR(VFG0_PCIE_CAP_NEXTPTR)
   ,.VFG1_PCIE_CAP_NEXTPTR(VFG1_PCIE_CAP_NEXTPTR)
   ,.VFG2_PCIE_CAP_NEXTPTR(VFG2_PCIE_CAP_NEXTPTR)
   ,.VFG3_PCIE_CAP_NEXTPTR(VFG3_PCIE_CAP_NEXTPTR)
   ,.PF0_DEV_CAP_MAX_PAYLOAD_SIZE(PF0_DEV_CAP_MAX_PAYLOAD_SIZE)
   ,.PF1_DEV_CAP_MAX_PAYLOAD_SIZE(PF1_DEV_CAP_MAX_PAYLOAD_SIZE)
   ,.PF2_DEV_CAP_MAX_PAYLOAD_SIZE(PF2_DEV_CAP_MAX_PAYLOAD_SIZE)
   ,.PF3_DEV_CAP_MAX_PAYLOAD_SIZE(PF3_DEV_CAP_MAX_PAYLOAD_SIZE)
   ,.PF0_DEV_CAP_EXT_TAG_SUPPORTED(PF0_DEV_CAP_EXT_TAG_SUPPORTED)
   ,.PF0_DEV_CAP_ENDPOINT_L0S_LATENCY(PF0_DEV_CAP_ENDPOINT_L0S_LATENCY)
   ,.PF0_DEV_CAP_ENDPOINT_L1_LATENCY(PF0_DEV_CAP_ENDPOINT_L1_LATENCY)
   ,.PF0_DEV_CAP_FUNCTION_LEVEL_RESET_CAPABLE(PF0_DEV_CAP_FUNCTION_LEVEL_RESET_CAPABLE)
   ,.PF0_LINK_CAP_ASPM_SUPPORT(PF0_LINK_CAP_ASPM_SUPPORT)
   ,.PF0_LINK_CONTROL_RCB(PF0_LINK_CONTROL_RCB)
   ,.PF0_LINK_STATUS_SLOT_CLOCK_CONFIG(PF0_LINK_STATUS_SLOT_CLOCK_CONFIG)
   ,.PF0_LINK_CAP_L0S_EXIT_LATENCY_COMCLK_GEN1(PF0_LINK_CAP_L0S_EXIT_LATENCY_COMCLK_GEN1)
   ,.PF0_LINK_CAP_L0S_EXIT_LATENCY_COMCLK_GEN2(PF0_LINK_CAP_L0S_EXIT_LATENCY_COMCLK_GEN2)
   ,.PF0_LINK_CAP_L0S_EXIT_LATENCY_COMCLK_GEN3(PF0_LINK_CAP_L0S_EXIT_LATENCY_COMCLK_GEN3)
   ,.PF0_LINK_CAP_L0S_EXIT_LATENCY_COMCLK_GEN4(PF0_LINK_CAP_L0S_EXIT_LATENCY_COMCLK_GEN4)
   ,.PF0_LINK_CAP_L0S_EXIT_LATENCY_GEN1(PF0_LINK_CAP_L0S_EXIT_LATENCY_GEN1)
   ,.PF0_LINK_CAP_L0S_EXIT_LATENCY_GEN2(PF0_LINK_CAP_L0S_EXIT_LATENCY_GEN2)
   ,.PF0_LINK_CAP_L0S_EXIT_LATENCY_GEN3(PF0_LINK_CAP_L0S_EXIT_LATENCY_GEN3)
   ,.PF0_LINK_CAP_L0S_EXIT_LATENCY_GEN4(PF0_LINK_CAP_L0S_EXIT_LATENCY_GEN4)
   ,.PF0_LINK_CAP_L1_EXIT_LATENCY_COMCLK_GEN1(PF0_LINK_CAP_L1_EXIT_LATENCY_COMCLK_GEN1)
   ,.PF0_LINK_CAP_L1_EXIT_LATENCY_COMCLK_GEN2(PF0_LINK_CAP_L1_EXIT_LATENCY_COMCLK_GEN2)
   ,.PF0_LINK_CAP_L1_EXIT_LATENCY_COMCLK_GEN3(PF0_LINK_CAP_L1_EXIT_LATENCY_COMCLK_GEN3)
   ,.PF0_LINK_CAP_L1_EXIT_LATENCY_COMCLK_GEN4(PF0_LINK_CAP_L1_EXIT_LATENCY_COMCLK_GEN4)
   ,.PF0_LINK_CAP_L1_EXIT_LATENCY_GEN1(PF0_LINK_CAP_L1_EXIT_LATENCY_GEN1)
   ,.PF0_LINK_CAP_L1_EXIT_LATENCY_GEN2(PF0_LINK_CAP_L1_EXIT_LATENCY_GEN2)
   ,.PF0_LINK_CAP_L1_EXIT_LATENCY_GEN3(PF0_LINK_CAP_L1_EXIT_LATENCY_GEN3)
   ,.PF0_LINK_CAP_L1_EXIT_LATENCY_GEN4(PF0_LINK_CAP_L1_EXIT_LATENCY_GEN4)
   ,.PF0_DEV_CAP2_CPL_TIMEOUT_DISABLE(PF0_DEV_CAP2_CPL_TIMEOUT_DISABLE)
   ,.PF0_DEV_CAP2_32B_ATOMIC_COMPLETER_SUPPORT(PF0_DEV_CAP2_32B_ATOMIC_COMPLETER_SUPPORT)
   ,.PF0_DEV_CAP2_64B_ATOMIC_COMPLETER_SUPPORT(PF0_DEV_CAP2_64B_ATOMIC_COMPLETER_SUPPORT)
   ,.PF0_DEV_CAP2_128B_CAS_ATOMIC_COMPLETER_SUPPORT(PF0_DEV_CAP2_128B_CAS_ATOMIC_COMPLETER_SUPPORT)
   ,.PF0_DEV_CAP2_LTR_SUPPORT(PF0_DEV_CAP2_LTR_SUPPORT)
   ,.PF0_DEV_CAP2_TPH_COMPLETER_SUPPORT(PF0_DEV_CAP2_TPH_COMPLETER_SUPPORT)
   ,.PF0_DEV_CAP2_OBFF_SUPPORT(PF0_DEV_CAP2_OBFF_SUPPORT)
   ,.PF0_DEV_CAP2_ARI_FORWARD_ENABLE(PF0_DEV_CAP2_ARI_FORWARD_ENABLE)
   ,.PF0_MSI_CAP_NEXTPTR(PF0_MSI_CAP_NEXTPTR)
   ,.PF1_MSI_CAP_NEXTPTR(PF1_MSI_CAP_NEXTPTR)
   ,.PF2_MSI_CAP_NEXTPTR(PF2_MSI_CAP_NEXTPTR)
   ,.PF3_MSI_CAP_NEXTPTR(PF3_MSI_CAP_NEXTPTR)
   ,.PF0_MSI_CAP_PERVECMASKCAP(PF0_MSI_CAP_PERVECMASKCAP)
   ,.PF1_MSI_CAP_PERVECMASKCAP(PF1_MSI_CAP_PERVECMASKCAP)
   ,.PF2_MSI_CAP_PERVECMASKCAP(PF2_MSI_CAP_PERVECMASKCAP)
   ,.PF3_MSI_CAP_PERVECMASKCAP(PF3_MSI_CAP_PERVECMASKCAP)
   ,.PF0_MSI_CAP_MULTIMSGCAP(PF0_MSI_CAP_MULTIMSGCAP)
   ,.PF1_MSI_CAP_MULTIMSGCAP(PF1_MSI_CAP_MULTIMSGCAP)
   ,.PF2_MSI_CAP_MULTIMSGCAP(PF2_MSI_CAP_MULTIMSGCAP)
   ,.PF3_MSI_CAP_MULTIMSGCAP(PF3_MSI_CAP_MULTIMSGCAP)
   ,.PF0_MSIX_CAP_NEXTPTR(PF0_MSIX_CAP_NEXTPTR)
   ,.PF1_MSIX_CAP_NEXTPTR(PF1_MSIX_CAP_NEXTPTR)
   ,.PF2_MSIX_CAP_NEXTPTR(PF2_MSIX_CAP_NEXTPTR)
   ,.PF3_MSIX_CAP_NEXTPTR(PF3_MSIX_CAP_NEXTPTR)
   ,.VFG0_MSIX_CAP_NEXTPTR(VFG0_MSIX_CAP_NEXTPTR)
   ,.VFG1_MSIX_CAP_NEXTPTR(VFG1_MSIX_CAP_NEXTPTR)
   ,.VFG2_MSIX_CAP_NEXTPTR(VFG2_MSIX_CAP_NEXTPTR)
   ,.VFG3_MSIX_CAP_NEXTPTR(VFG3_MSIX_CAP_NEXTPTR)
   ,.PF0_MSIX_CAP_PBA_BIR(PF0_MSIX_CAP_PBA_BIR)
   ,.PF1_MSIX_CAP_PBA_BIR(PF1_MSIX_CAP_PBA_BIR)
   ,.PF2_MSIX_CAP_PBA_BIR(PF2_MSIX_CAP_PBA_BIR)
   ,.PF3_MSIX_CAP_PBA_BIR(PF3_MSIX_CAP_PBA_BIR)
   ,.VFG0_MSIX_CAP_PBA_BIR(VFG0_MSIX_CAP_PBA_BIR)
   ,.VFG1_MSIX_CAP_PBA_BIR(VFG1_MSIX_CAP_PBA_BIR)
   ,.VFG2_MSIX_CAP_PBA_BIR(VFG2_MSIX_CAP_PBA_BIR)
   ,.VFG3_MSIX_CAP_PBA_BIR(VFG3_MSIX_CAP_PBA_BIR)
   ,.PF0_MSIX_CAP_PBA_OFFSET ({3'b000,PF0_MSIX_CAP_PBA_OFFSET[28:3]})
   ,.PF1_MSIX_CAP_PBA_OFFSET ({3'b000,PF1_MSIX_CAP_PBA_OFFSET[28:3]})
   ,.PF2_MSIX_CAP_PBA_OFFSET ({3'b000,PF2_MSIX_CAP_PBA_OFFSET[28:3]})
   ,.PF3_MSIX_CAP_PBA_OFFSET ({3'b000,PF3_MSIX_CAP_PBA_OFFSET[28:3]})
   ,.VFG0_MSIX_CAP_PBA_OFFSET({3'b000,VFG0_MSIX_CAP_PBA_OFFSET[28:3]})
   ,.VFG1_MSIX_CAP_PBA_OFFSET({3'b000,VFG1_MSIX_CAP_PBA_OFFSET[28:3]})
   ,.VFG2_MSIX_CAP_PBA_OFFSET({3'b000,VFG2_MSIX_CAP_PBA_OFFSET[28:3]})
   ,.VFG3_MSIX_CAP_PBA_OFFSET({3'b000,VFG3_MSIX_CAP_PBA_OFFSET[28:3]})
   ,.PF0_MSIX_CAP_TABLE_BIR(PF0_MSIX_CAP_TABLE_BIR)
   ,.PF1_MSIX_CAP_TABLE_BIR(PF1_MSIX_CAP_TABLE_BIR)
   ,.PF2_MSIX_CAP_TABLE_BIR(PF2_MSIX_CAP_TABLE_BIR)
   ,.PF3_MSIX_CAP_TABLE_BIR(PF3_MSIX_CAP_TABLE_BIR)
   ,.VFG0_MSIX_CAP_TABLE_BIR(VFG0_MSIX_CAP_TABLE_BIR)
   ,.VFG1_MSIX_CAP_TABLE_BIR(VFG1_MSIX_CAP_TABLE_BIR)
   ,.VFG2_MSIX_CAP_TABLE_BIR(VFG2_MSIX_CAP_TABLE_BIR)
   ,.VFG3_MSIX_CAP_TABLE_BIR(VFG3_MSIX_CAP_TABLE_BIR)
   ,.PF0_MSIX_CAP_TABLE_OFFSET ({3'b000,PF0_MSIX_CAP_TABLE_OFFSET[28:3]})
   ,.PF1_MSIX_CAP_TABLE_OFFSET ({3'b000,PF1_MSIX_CAP_TABLE_OFFSET[28:3]})
   ,.PF2_MSIX_CAP_TABLE_OFFSET ({3'b000,PF2_MSIX_CAP_TABLE_OFFSET[28:3]})
   ,.PF3_MSIX_CAP_TABLE_OFFSET ({3'b000,PF3_MSIX_CAP_TABLE_OFFSET[28:3]})
   ,.VFG0_MSIX_CAP_TABLE_OFFSET({3'b000,VFG0_MSIX_CAP_TABLE_OFFSET[28:3]})
   ,.VFG1_MSIX_CAP_TABLE_OFFSET({3'b000,VFG1_MSIX_CAP_TABLE_OFFSET[28:3]})
   ,.VFG2_MSIX_CAP_TABLE_OFFSET({3'b000,VFG2_MSIX_CAP_TABLE_OFFSET[28:3]})
   ,.VFG3_MSIX_CAP_TABLE_OFFSET({3'b000,VFG3_MSIX_CAP_TABLE_OFFSET[28:3]})
   ,.PF0_MSIX_CAP_TABLE_SIZE(PF0_MSIX_CAP_TABLE_SIZE)
   ,.PF1_MSIX_CAP_TABLE_SIZE(PF1_MSIX_CAP_TABLE_SIZE)
   ,.PF2_MSIX_CAP_TABLE_SIZE(PF2_MSIX_CAP_TABLE_SIZE)
   ,.PF3_MSIX_CAP_TABLE_SIZE(PF3_MSIX_CAP_TABLE_SIZE)
   ,.VFG0_MSIX_CAP_TABLE_SIZE(VFG0_MSIX_CAP_TABLE_SIZE)
   ,.VFG1_MSIX_CAP_TABLE_SIZE(VFG1_MSIX_CAP_TABLE_SIZE)
   ,.VFG2_MSIX_CAP_TABLE_SIZE(VFG2_MSIX_CAP_TABLE_SIZE)
   ,.VFG3_MSIX_CAP_TABLE_SIZE(VFG3_MSIX_CAP_TABLE_SIZE)
   ,.PF0_MSIX_VECTOR_COUNT(PF0_MSIX_VECTOR_COUNT)
   ,.PF0_PM_CAP_ID(PF0_PM_CAP_ID)
   ,.PF0_PM_CAP_NEXTPTR(PF0_PM_CAP_NEXTPTR)
   ,.PF1_PM_CAP_NEXTPTR(PF1_PM_CAP_NEXTPTR)
   ,.PF2_PM_CAP_NEXTPTR(PF2_PM_CAP_NEXTPTR)
   ,.PF3_PM_CAP_NEXTPTR(PF3_PM_CAP_NEXTPTR)
   ,.PF0_PM_CAP_PMESUPPORT_D3HOT(PF0_PM_CAP_PMESUPPORT_D3HOT)
   ,.PF0_PM_CAP_PMESUPPORT_D1(PF0_PM_CAP_PMESUPPORT_D1)
   ,.PF0_PM_CAP_PMESUPPORT_D0(PF0_PM_CAP_PMESUPPORT_D0)
   ,.PF0_PM_CAP_SUPP_D1_STATE(PF0_PM_CAP_SUPP_D1_STATE)
   ,.PF0_PM_CAP_VER_ID(PF0_PM_CAP_VER_ID)
   ,.PF0_PM_CSR_NOSOFTRESET(PF0_PM_CSR_NOSOFTRESET)
   ,.PM_ENABLE_L23_ENTRY(PM_ENABLE_L23_ENTRY)
   ,.DNSTREAM_LINK_NUM(DNSTREAM_LINK_NUM)
   ,.AUTO_FLR_RESPONSE(AUTO_FLR_RESPONSE)
   ,.PF0_DSN_CAP_NEXTPTR(PF0_DSN_CAP_NEXTPTR)
   ,.PF1_DSN_CAP_NEXTPTR(PF1_DSN_CAP_NEXTPTR)
   ,.PF2_DSN_CAP_NEXTPTR(PF2_DSN_CAP_NEXTPTR)
   ,.PF3_DSN_CAP_NEXTPTR(PF3_DSN_CAP_NEXTPTR)
   ,.DSN_CAP_ENABLE(DSN_CAP_ENABLE)
   ,.PF0_VC_CAP_VER(PF0_VC_CAP_VER)
   ,.PF0_VC_CAP_NEXTPTR(PF0_VC_CAP_NEXTPTR)
   ,.PF0_VC_CAP_ENABLE(PF0_VC_CAP_ENABLE)
   ,.PF0_SECONDARY_PCIE_CAP_NEXTPTR(PF0_SECONDARY_PCIE_CAP_NEXTPTR)
   ,.PF0_AER_CAP_NEXTPTR(PF0_AER_CAP_NEXTPTR)
   ,.PF1_AER_CAP_NEXTPTR(PF1_AER_CAP_NEXTPTR)
   ,.PF2_AER_CAP_NEXTPTR(PF2_AER_CAP_NEXTPTR)
   ,.PF3_AER_CAP_NEXTPTR(PF3_AER_CAP_NEXTPTR)
   ,.PF0_AER_CAP_ECRC_GEN_AND_CHECK_CAPABLE(PF0_AER_CAP_ECRC_GEN_AND_CHECK_CAPABLE)
   ,.ARI_CAP_ENABLE(ARI_CAP_ENABLE)
   ,.PF0_ARI_CAP_NEXTPTR(PF0_ARI_CAP_NEXTPTR)
   ,.PF1_ARI_CAP_NEXTPTR(PF1_ARI_CAP_NEXTPTR)
   ,.PF2_ARI_CAP_NEXTPTR(PF2_ARI_CAP_NEXTPTR)
   ,.PF3_ARI_CAP_NEXTPTR(PF3_ARI_CAP_NEXTPTR)
   ,.VFG0_ARI_CAP_NEXTPTR(VFG0_ARI_CAP_NEXTPTR)
   ,.VFG1_ARI_CAP_NEXTPTR(VFG1_ARI_CAP_NEXTPTR)
   ,.VFG2_ARI_CAP_NEXTPTR(VFG2_ARI_CAP_NEXTPTR)
   ,.VFG3_ARI_CAP_NEXTPTR(VFG3_ARI_CAP_NEXTPTR)
   ,.PF0_ARI_CAP_VER(PF0_ARI_CAP_VER)
   ,.PF0_ARI_CAP_NEXT_FUNC(PF0_ARI_CAP_NEXT_FUNC)
   ,.PF1_ARI_CAP_NEXT_FUNC(PF1_ARI_CAP_NEXT_FUNC)
   ,.PF2_ARI_CAP_NEXT_FUNC(PF2_ARI_CAP_NEXT_FUNC)
   ,.PF3_ARI_CAP_NEXT_FUNC(PF3_ARI_CAP_NEXT_FUNC)
   ,.PF0_LTR_CAP_NEXTPTR(PF0_LTR_CAP_NEXTPTR)
   ,.PF0_LTR_CAP_VER(PF0_LTR_CAP_VER)
   ,.PF0_LTR_CAP_MAX_SNOOP_LAT(PF0_LTR_CAP_MAX_SNOOP_LAT)
   ,.PF0_LTR_CAP_MAX_NOSNOOP_LAT(PF0_LTR_CAP_MAX_NOSNOOP_LAT)
   ,.LTR_TX_MESSAGE_ON_LTR_ENABLE(LTR_TX_MESSAGE_ON_LTR_ENABLE)
   ,.LTR_TX_MESSAGE_ON_FUNC_POWER_STATE_CHANGE(LTR_TX_MESSAGE_ON_FUNC_POWER_STATE_CHANGE)
   ,.LTR_TX_MESSAGE_MINIMUM_INTERVAL(LTR_TX_MESSAGE_MINIMUM_INTERVAL)
   ,.SRIOV_CAP_ENABLE(SRIOV_CAP_ENABLE)
   ,.PF0_SRIOV_CAP_NEXTPTR(PF0_SRIOV_CAP_NEXTPTR)
   ,.PF1_SRIOV_CAP_NEXTPTR(PF1_SRIOV_CAP_NEXTPTR)
   ,.PF2_SRIOV_CAP_NEXTPTR(PF2_SRIOV_CAP_NEXTPTR)
   ,.PF3_SRIOV_CAP_NEXTPTR(PF3_SRIOV_CAP_NEXTPTR)
   ,.PF0_SRIOV_CAP_VER(PF0_SRIOV_CAP_VER)
   ,.PF1_SRIOV_CAP_VER(PF1_SRIOV_CAP_VER)
   ,.PF2_SRIOV_CAP_VER(PF2_SRIOV_CAP_VER)
   ,.PF3_SRIOV_CAP_VER(PF3_SRIOV_CAP_VER)
   ,.PF0_SRIOV_ARI_CAPBL_HIER_PRESERVED(PF0_SRIOV_ARI_CAPBL_HIER_PRESERVED)
   ,.PF1_SRIOV_ARI_CAPBL_HIER_PRESERVED(PF1_SRIOV_ARI_CAPBL_HIER_PRESERVED)
   ,.PF2_SRIOV_ARI_CAPBL_HIER_PRESERVED(PF2_SRIOV_ARI_CAPBL_HIER_PRESERVED)
   ,.PF3_SRIOV_ARI_CAPBL_HIER_PRESERVED(PF3_SRIOV_ARI_CAPBL_HIER_PRESERVED)
   ,.PF0_SRIOV_CAP_INITIAL_VF(PF0_SRIOV_CAP_INITIAL_VF)
   ,.PF1_SRIOV_CAP_INITIAL_VF(PF1_SRIOV_CAP_INITIAL_VF)
   ,.PF2_SRIOV_CAP_INITIAL_VF(PF2_SRIOV_CAP_INITIAL_VF)
   ,.PF3_SRIOV_CAP_INITIAL_VF(PF3_SRIOV_CAP_INITIAL_VF)
   ,.PF0_SRIOV_CAP_TOTAL_VF(PF0_SRIOV_CAP_TOTAL_VF)
   ,.PF1_SRIOV_CAP_TOTAL_VF(PF1_SRIOV_CAP_TOTAL_VF)
   ,.PF2_SRIOV_CAP_TOTAL_VF(PF2_SRIOV_CAP_TOTAL_VF)
   ,.PF3_SRIOV_CAP_TOTAL_VF(PF3_SRIOV_CAP_TOTAL_VF)
   ,.PF0_SRIOV_FUNC_DEP_LINK(PF0_SRIOV_FUNC_DEP_LINK)
   ,.PF1_SRIOV_FUNC_DEP_LINK(PF1_SRIOV_FUNC_DEP_LINK)
   ,.PF2_SRIOV_FUNC_DEP_LINK(PF2_SRIOV_FUNC_DEP_LINK)
   ,.PF3_SRIOV_FUNC_DEP_LINK(PF3_SRIOV_FUNC_DEP_LINK)
   ,.PF0_SRIOV_FIRST_VF_OFFSET(PF0_SRIOV_FIRST_VF_OFFSET)
   ,.PF1_SRIOV_FIRST_VF_OFFSET(PF1_SRIOV_FIRST_VF_OFFSET)
   ,.PF2_SRIOV_FIRST_VF_OFFSET(PF2_SRIOV_FIRST_VF_OFFSET)
   ,.PF3_SRIOV_FIRST_VF_OFFSET(PF3_SRIOV_FIRST_VF_OFFSET)
   ,.PF0_SRIOV_VF_DEVICE_ID(PF0_SRIOV_VF_DEVICE_ID)
   ,.PF1_SRIOV_VF_DEVICE_ID(PF1_SRIOV_VF_DEVICE_ID)
   ,.PF2_SRIOV_VF_DEVICE_ID(PF2_SRIOV_VF_DEVICE_ID)
   ,.PF3_SRIOV_VF_DEVICE_ID(PF3_SRIOV_VF_DEVICE_ID)
   ,.PF0_SRIOV_SUPPORTED_PAGE_SIZE(PF0_SRIOV_SUPPORTED_PAGE_SIZE)
   ,.PF1_SRIOV_SUPPORTED_PAGE_SIZE(PF1_SRIOV_SUPPORTED_PAGE_SIZE)
   ,.PF2_SRIOV_SUPPORTED_PAGE_SIZE(PF2_SRIOV_SUPPORTED_PAGE_SIZE)
   ,.PF3_SRIOV_SUPPORTED_PAGE_SIZE(PF3_SRIOV_SUPPORTED_PAGE_SIZE)
   ,.PF0_SRIOV_BAR0_CONTROL(PF0_SRIOV_BAR0_CONTROL)
   ,.PF1_SRIOV_BAR0_CONTROL(PF1_SRIOV_BAR0_CONTROL)
   ,.PF2_SRIOV_BAR0_CONTROL(PF2_SRIOV_BAR0_CONTROL)
   ,.PF3_SRIOV_BAR0_CONTROL(PF3_SRIOV_BAR0_CONTROL)
   ,.PF0_SRIOV_BAR0_APERTURE_SIZE(PF0_SRIOV_BAR0_APERTURE_SIZE)
   ,.PF1_SRIOV_BAR0_APERTURE_SIZE(PF1_SRIOV_BAR0_APERTURE_SIZE)
   ,.PF2_SRIOV_BAR0_APERTURE_SIZE(PF2_SRIOV_BAR0_APERTURE_SIZE)
   ,.PF3_SRIOV_BAR0_APERTURE_SIZE(PF3_SRIOV_BAR0_APERTURE_SIZE)
   ,.PF0_SRIOV_BAR1_CONTROL(PF0_SRIOV_BAR1_CONTROL)
   ,.PF1_SRIOV_BAR1_CONTROL(PF1_SRIOV_BAR1_CONTROL)
   ,.PF2_SRIOV_BAR1_CONTROL(PF2_SRIOV_BAR1_CONTROL)
   ,.PF3_SRIOV_BAR1_CONTROL(PF3_SRIOV_BAR1_CONTROL)
   ,.PF0_SRIOV_BAR1_APERTURE_SIZE(PF0_SRIOV_BAR1_APERTURE_SIZE)
   ,.PF1_SRIOV_BAR1_APERTURE_SIZE(PF1_SRIOV_BAR1_APERTURE_SIZE)
   ,.PF2_SRIOV_BAR1_APERTURE_SIZE(PF2_SRIOV_BAR1_APERTURE_SIZE)
   ,.PF3_SRIOV_BAR1_APERTURE_SIZE(PF3_SRIOV_BAR1_APERTURE_SIZE)
   ,.PF0_SRIOV_BAR2_CONTROL(PF0_SRIOV_BAR2_CONTROL)
   ,.PF1_SRIOV_BAR2_CONTROL(PF1_SRIOV_BAR2_CONTROL)
   ,.PF2_SRIOV_BAR2_CONTROL(PF2_SRIOV_BAR2_CONTROL)
   ,.PF3_SRIOV_BAR2_CONTROL(PF3_SRIOV_BAR2_CONTROL)
   ,.PF0_SRIOV_BAR2_APERTURE_SIZE(PF0_SRIOV_BAR2_APERTURE_SIZE)
   ,.PF1_SRIOV_BAR2_APERTURE_SIZE(PF1_SRIOV_BAR2_APERTURE_SIZE)
   ,.PF2_SRIOV_BAR2_APERTURE_SIZE(PF2_SRIOV_BAR2_APERTURE_SIZE)
   ,.PF3_SRIOV_BAR2_APERTURE_SIZE(PF3_SRIOV_BAR2_APERTURE_SIZE)
   ,.PF0_SRIOV_BAR3_CONTROL(PF0_SRIOV_BAR3_CONTROL)
   ,.PF1_SRIOV_BAR3_CONTROL(PF1_SRIOV_BAR3_CONTROL)
   ,.PF2_SRIOV_BAR3_CONTROL(PF2_SRIOV_BAR3_CONTROL)
   ,.PF3_SRIOV_BAR3_CONTROL(PF3_SRIOV_BAR3_CONTROL)
   ,.PF0_SRIOV_BAR3_APERTURE_SIZE(PF0_SRIOV_BAR3_APERTURE_SIZE)
   ,.PF1_SRIOV_BAR3_APERTURE_SIZE(PF1_SRIOV_BAR3_APERTURE_SIZE)
   ,.PF2_SRIOV_BAR3_APERTURE_SIZE(PF2_SRIOV_BAR3_APERTURE_SIZE)
   ,.PF3_SRIOV_BAR3_APERTURE_SIZE(PF3_SRIOV_BAR3_APERTURE_SIZE)
   ,.PF0_SRIOV_BAR4_CONTROL(PF0_SRIOV_BAR4_CONTROL)
   ,.PF1_SRIOV_BAR4_CONTROL(PF1_SRIOV_BAR4_CONTROL)
   ,.PF2_SRIOV_BAR4_CONTROL(PF2_SRIOV_BAR4_CONTROL)
   ,.PF3_SRIOV_BAR4_CONTROL(PF3_SRIOV_BAR4_CONTROL)
   ,.PF0_SRIOV_BAR4_APERTURE_SIZE(PF0_SRIOV_BAR4_APERTURE_SIZE)
   ,.PF1_SRIOV_BAR4_APERTURE_SIZE(PF1_SRIOV_BAR4_APERTURE_SIZE)
   ,.PF2_SRIOV_BAR4_APERTURE_SIZE(PF2_SRIOV_BAR4_APERTURE_SIZE)
   ,.PF3_SRIOV_BAR4_APERTURE_SIZE(PF3_SRIOV_BAR4_APERTURE_SIZE)
   ,.PF0_SRIOV_BAR5_CONTROL(PF0_SRIOV_BAR5_CONTROL)
   ,.PF1_SRIOV_BAR5_CONTROL(PF1_SRIOV_BAR5_CONTROL)
   ,.PF2_SRIOV_BAR5_CONTROL(PF2_SRIOV_BAR5_CONTROL)
   ,.PF3_SRIOV_BAR5_CONTROL(PF3_SRIOV_BAR5_CONTROL)
   ,.PF0_SRIOV_BAR5_APERTURE_SIZE(PF0_SRIOV_BAR5_APERTURE_SIZE)
   ,.PF1_SRIOV_BAR5_APERTURE_SIZE(PF1_SRIOV_BAR5_APERTURE_SIZE)
   ,.PF2_SRIOV_BAR5_APERTURE_SIZE(PF2_SRIOV_BAR5_APERTURE_SIZE)
   ,.PF3_SRIOV_BAR5_APERTURE_SIZE(PF3_SRIOV_BAR5_APERTURE_SIZE)
   ,.PF0_TPHR_CAP_NEXTPTR(PF0_TPHR_CAP_NEXTPTR)
   ,.PF1_TPHR_CAP_NEXTPTR(PF1_TPHR_CAP_NEXTPTR)
   ,.PF2_TPHR_CAP_NEXTPTR(PF2_TPHR_CAP_NEXTPTR)
   ,.PF3_TPHR_CAP_NEXTPTR(PF3_TPHR_CAP_NEXTPTR)
   ,.VFG0_TPHR_CAP_NEXTPTR(VFG0_TPHR_CAP_NEXTPTR)
   ,.VFG1_TPHR_CAP_NEXTPTR(VFG1_TPHR_CAP_NEXTPTR)
   ,.VFG2_TPHR_CAP_NEXTPTR(VFG2_TPHR_CAP_NEXTPTR)
   ,.VFG3_TPHR_CAP_NEXTPTR(VFG3_TPHR_CAP_NEXTPTR)
   ,.PF0_TPHR_CAP_VER(PF0_TPHR_CAP_VER)
   ,.PF0_TPHR_CAP_INT_VEC_MODE(PF0_TPHR_CAP_INT_VEC_MODE)
   ,.PF0_TPHR_CAP_DEV_SPECIFIC_MODE(PF0_TPHR_CAP_DEV_SPECIFIC_MODE)
   ,.PF0_TPHR_CAP_ST_TABLE_LOC(PF0_TPHR_CAP_ST_TABLE_LOC)
   ,.PF0_TPHR_CAP_ST_TABLE_SIZE(PF0_TPHR_CAP_ST_TABLE_SIZE)
   ,.PF0_TPHR_CAP_ST_MODE_SEL(PF0_TPHR_CAP_ST_MODE_SEL)
   ,.PF1_TPHR_CAP_ST_MODE_SEL(PF1_TPHR_CAP_ST_MODE_SEL)
   ,.PF2_TPHR_CAP_ST_MODE_SEL(PF2_TPHR_CAP_ST_MODE_SEL)
   ,.PF3_TPHR_CAP_ST_MODE_SEL(PF3_TPHR_CAP_ST_MODE_SEL)
   ,.VFG0_TPHR_CAP_ST_MODE_SEL(VFG0_TPHR_CAP_ST_MODE_SEL)
   ,.VFG1_TPHR_CAP_ST_MODE_SEL(VFG1_TPHR_CAP_ST_MODE_SEL)
   ,.VFG2_TPHR_CAP_ST_MODE_SEL(VFG2_TPHR_CAP_ST_MODE_SEL)
   ,.VFG3_TPHR_CAP_ST_MODE_SEL(VFG3_TPHR_CAP_ST_MODE_SEL)
   ,.PF0_TPHR_CAP_ENABLE(PF0_TPHR_CAP_ENABLE)
   ,.TPH_TO_RAM_PIPELINE(TPH_TO_RAM_PIPELINE)
   ,.TPH_FROM_RAM_PIPELINE(TPH_FROM_RAM_PIPELINE)
   ,.MCAP_ENABLE(MCAP_ENABLE)
   ,.ECC_PIPELINE(ECC_PIPELINE)
   ,.MCAP_CONFIGURE_OVERRIDE(MCAP_CONFIGURE_OVERRIDE)
   ,.MCAP_CAP_NEXTPTR(MCAP_CAP_NEXTPTR)
   ,.MCAP_VSEC_ID(MCAP_VSEC_ID)
   ,.MCAP_VSEC_REV(MCAP_VSEC_REV)
   ,.MCAP_VSEC_LEN(MCAP_VSEC_LEN)
   ,.MCAP_FPGA_BITSTREAM_VERSION(MCAP_FPGA_BITSTREAM_VERSION)
   ,.MCAP_INTERRUPT_ON_MCAP_EOS(MCAP_INTERRUPT_ON_MCAP_EOS)
   ,.MCAP_INTERRUPT_ON_MCAP_ERROR(MCAP_INTERRUPT_ON_MCAP_ERROR)
   ,.MCAP_INPUT_GATE_DESIGN_SWITCH(MCAP_INPUT_GATE_DESIGN_SWITCH)
   ,.MCAP_EOS_DESIGN_SWITCH(MCAP_EOS_DESIGN_SWITCH)
   ,.MCAP_GATE_MEM_ENABLE_DESIGN_SWITCH(MCAP_GATE_MEM_ENABLE_DESIGN_SWITCH)
   ,.MCAP_GATE_IO_ENABLE_DESIGN_SWITCH(MCAP_GATE_IO_ENABLE_DESIGN_SWITCH)
   ,.SIM_JTAG_IDCODE(SIM_JTAG_IDCODE)
   ,.DEBUG_AXIST_DISABLE_FEATURE_BIT(DEBUG_AXIST_DISABLE_FEATURE_BIT)
   ,.DEBUG_TL_DISABLE_RX_TLP_ORDER_CHECKS(DEBUG_TL_DISABLE_RX_TLP_ORDER_CHECKS)
   ,.DEBUG_TL_DISABLE_FC_TIMEOUT(DEBUG_TL_DISABLE_FC_TIMEOUT)
   ,.DEBUG_PL_DISABLE_SCRAMBLING(DEBUG_PL_DISABLE_SCRAMBLING)
   ,.DEBUG_PL_DISABLE_REC_ENTRY_ON_DYNAMIC_DSKEW_FAIL (DEBUG_PL_DISABLE_REC_ENTRY_ON_DYNAMIC_DSKEW_FAIL )
   ,.DEBUG_PL_DISABLE_REC_ENTRY_ON_RX_BUFFER_UNDER_OVER_FLOW (DEBUG_PL_DISABLE_REC_ENTRY_ON_RX_BUFFER_UNDER_OVER_FLOW )
   ,.DEBUG_PL_DISABLE_LES_UPDATE_ON_SKP_ERROR(DEBUG_PL_DISABLE_LES_UPDATE_ON_SKP_ERROR)
   ,.DEBUG_PL_DISABLE_LES_UPDATE_ON_SKP_PARITY_ERROR(DEBUG_PL_DISABLE_LES_UPDATE_ON_SKP_PARITY_ERROR)
   ,.DEBUG_PL_DISABLE_LES_UPDATE_ON_DEFRAMER_ERROR(DEBUG_PL_DISABLE_LES_UPDATE_ON_DEFRAMER_ERROR)
   ,.DEBUG_PL_SIM_RESET_LFSR(DEBUG_PL_SIM_RESET_LFSR)
   ,.DEBUG_PL_SPARE(DEBUG_PL_SPARE)
   ,.DEBUG_LL_SPARE(DEBUG_LL_SPARE)
   ,.DEBUG_TL_SPARE(DEBUG_TL_SPARE)
   ,.DEBUG_AXI4ST_SPARE(DEBUG_AXI4ST_SPARE)
   ,.DEBUG_CFG_SPARE(DEBUG_CFG_SPARE)
   ,.DEBUG_CAR_SPARE(DEBUG_CAR_SPARE)
   ,.TEST_MODE_PIN_CHAR(TEST_MODE_PIN_CHAR)
   ,.SPARE_BIT0(SPARE_BIT0)
   ,.SPARE_BIT1(SPARE_BIT1)
   ,.SPARE_BIT2(SPARE_BIT2)
   ,.SPARE_BIT3(SPARE_BIT3)
   ,.SPARE_BIT4(SPARE_BIT4)
   ,.SPARE_BIT5(SPARE_BIT5)
   ,.SPARE_BIT6(SPARE_BIT6)
   ,.SPARE_BIT7(SPARE_BIT7)
   ,.SPARE_BIT8(SPARE_BIT8)
   ,.SPARE_BYTE0(SPARE_BYTE0)
   ,.SPARE_BYTE1(SPARE_BYTE1)
   ,.SPARE_BYTE2(SPARE_BYTE2)
   ,.SPARE_BYTE3(SPARE_BYTE3)
   ,.SPARE_WORD0(SPARE_WORD0)
   ,.SPARE_WORD1(SPARE_WORD1)
   ,.SPARE_WORD2(SPARE_WORD2)
   ,.SPARE_WORD3(SPARE_WORD3)

   ,.AXISTEN_IF_CCIX_RX_CREDIT_LIMIT(AXISTEN_IF_CCIX_RX_CREDIT_LIMIT)
   ,.AXISTEN_IF_CCIX_TX_CREDIT_LIMIT(AXISTEN_IF_CCIX_TX_CREDIT_LIMIT)
   ,.AXISTEN_IF_CCIX_TX_REGISTERED_TREADY(AXISTEN_IF_CCIX_TX_REGISTERED_TREADY)
   ,.CCIX_DIRECT_ATTACH_MODE(CCIX_DIRECT_ATTACH_MODE)
   ,.CCIX_ENABLE(CCIX_ENABLE)
   ,.CCIX_VENDOR_ID(CCIX_VENDOR_ID)
   ,.PF0_ATS_CAP_INV_QUEUE_DEPTH(PF0_ATS_CAP_INV_QUEUE_DEPTH)
   ,.PF0_ATS_CAP_NEXTPTR(PF0_ATS_CAP_NEXTPTR)
   ,.PF0_ATS_CAP_ON(PF0_ATS_CAP_ON)
   ,.PF0_PRI_CAP_NEXTPTR(PF0_PRI_CAP_NEXTPTR)
   ,.PF0_PRI_CAP_ON(PF0_PRI_CAP_ON)
   ,.PF0_PRI_OST_PR_CAPACITY(PF0_PRI_OST_PR_CAPACITY)
   ,.PF0_VC_ARB_CAPABILITY(PF0_VC_ARB_CAPABILITY)
   ,.PF0_VC_ARB_TBL_OFFSET(PF0_VC_ARB_TBL_OFFSET)
   ,.PF0_VC_EXTENDED_COUNT(PF0_VC_EXTENDED_COUNT)
   ,.PF0_VC_LOW_PRIORITY_EXTENDED_COUNT(PF0_VC_LOW_PRIORITY_EXTENDED_COUNT)
   ,.PF1_ATS_CAP_INV_QUEUE_DEPTH(PF1_ATS_CAP_INV_QUEUE_DEPTH)
   ,.PF1_ATS_CAP_NEXTPTR(PF1_ATS_CAP_NEXTPTR)
   ,.PF1_ATS_CAP_ON(PF1_ATS_CAP_ON)
   ,.PF1_PRI_CAP_NEXTPTR(PF1_PRI_CAP_NEXTPTR)
   ,.PF1_PRI_CAP_ON(PF1_PRI_CAP_ON)
   ,.PF1_PRI_OST_PR_CAPACITY(PF1_PRI_OST_PR_CAPACITY)
   ,.PF2_ATS_CAP_INV_QUEUE_DEPTH(PF2_ATS_CAP_INV_QUEUE_DEPTH)
   ,.PF2_ATS_CAP_NEXTPTR(PF2_ATS_CAP_NEXTPTR)
   ,.PF2_ATS_CAP_ON(PF2_ATS_CAP_ON)
   ,.PF2_PRI_CAP_NEXTPTR(PF2_PRI_CAP_NEXTPTR)
   ,.PF2_PRI_CAP_ON(PF2_PRI_CAP_ON)
   ,.PF2_PRI_OST_PR_CAPACITY(PF2_PRI_OST_PR_CAPACITY)
   ,.PF3_ATS_CAP_INV_QUEUE_DEPTH(PF3_ATS_CAP_INV_QUEUE_DEPTH)
   ,.PF3_ATS_CAP_NEXTPTR(PF3_ATS_CAP_NEXTPTR)
   ,.PF3_ATS_CAP_ON(PF3_ATS_CAP_ON)
   ,.PF3_PRI_CAP_NEXTPTR(PF3_PRI_CAP_NEXTPTR)
   ,.PF3_PRI_CAP_ON(PF3_PRI_CAP_ON)
   ,.PF3_PRI_OST_PR_CAPACITY(PF3_PRI_OST_PR_CAPACITY)
   ,.PL_CTRL_SKP_GEN_ENABLE(PL_CTRL_SKP_GEN_ENABLE)
   ,.PL_CTRL_SKP_PARITY_AND_CRC_CHECK_DISABLE(PL_CTRL_SKP_PARITY_AND_CRC_CHECK_DISABLE)
   ,.PL_USER_SPARE2(PL_USER_SPARE2)
   ,.TL_CREDITS_CD_VC1(TL_CREDITS_CD_VC1)
   ,.TL_CREDITS_CH_VC1(TL_CREDITS_CH_VC1)
   ,.TL_CREDITS_NPD_VC1(TL_CREDITS_NPD_VC1)
   ,.TL_CREDITS_NPH_VC1(TL_CREDITS_NPH_VC1)
   ,.TL_CREDITS_PD_VC1(TL_CREDITS_PD_VC1)
   ,.TL_CREDITS_PH_VC1(TL_CREDITS_PH_VC1)
   ,.TL_FC_UPDATE_MIN_INTERVAL_TIME_VC1(TL_FC_UPDATE_MIN_INTERVAL_TIME_VC1)
   ,.TL_FC_UPDATE_MIN_INTERVAL_TLP_COUNT_VC1(TL_FC_UPDATE_MIN_INTERVAL_TLP_COUNT_VC1)
   ,.TL_FEATURE_ENABLE_FC_SCALING(TL_FEATURE_ENABLE_FC_SCALING)
   ,.VFG0_ATS_CAP_INV_QUEUE_DEPTH(VFG0_ATS_CAP_INV_QUEUE_DEPTH)
   ,.VFG0_ATS_CAP_NEXTPTR(VFG0_ATS_CAP_NEXTPTR)
   ,.VFG0_ATS_CAP_ON(VFG0_ATS_CAP_ON)
   ,.VFG1_ATS_CAP_INV_QUEUE_DEPTH(VFG1_ATS_CAP_INV_QUEUE_DEPTH)
   ,.VFG1_ATS_CAP_NEXTPTR(VFG1_ATS_CAP_NEXTPTR)
   ,.VFG1_ATS_CAP_ON(VFG1_ATS_CAP_ON)
   ,.VFG2_ATS_CAP_INV_QUEUE_DEPTH(VFG2_ATS_CAP_INV_QUEUE_DEPTH)
   ,.VFG2_ATS_CAP_NEXTPTR(VFG2_ATS_CAP_NEXTPTR)
   ,.VFG2_ATS_CAP_ON(VFG2_ATS_CAP_ON)
   ,.VFG3_ATS_CAP_INV_QUEUE_DEPTH(VFG3_ATS_CAP_INV_QUEUE_DEPTH)
   ,.VFG3_ATS_CAP_NEXTPTR(VFG3_ATS_CAP_NEXTPTR)
   ,.VFG3_ATS_CAP_ON(VFG3_ATS_CAP_ON)
   ,.ENABLE_MSIX_32VEC(ENABLE_MSIX_32VEC)
  ) pcie_bridge_ep_pcie4c_ip_pcie_4_0_pipe_inst (

    .pipe_rx00_char_is_k(pipe_rx00_char_is_k[1:0])
   ,.pipe_rx01_char_is_k(pipe_rx01_char_is_k[1:0])
   ,.pipe_rx02_char_is_k(pipe_rx02_char_is_k[1:0])
   ,.pipe_rx03_char_is_k(pipe_rx03_char_is_k[1:0])
   ,.pipe_rx04_char_is_k(pipe_rx04_char_is_k[1:0])
   ,.pipe_rx05_char_is_k(pipe_rx05_char_is_k[1:0])
   ,.pipe_rx06_char_is_k(pipe_rx06_char_is_k[1:0])
   ,.pipe_rx07_char_is_k(pipe_rx07_char_is_k[1:0])
   ,.pipe_rx08_char_is_k(pipe_rx08_char_is_k[1:0])
   ,.pipe_rx09_char_is_k(pipe_rx09_char_is_k[1:0])
   ,.pipe_rx10_char_is_k(pipe_rx10_char_is_k[1:0])
   ,.pipe_rx11_char_is_k(pipe_rx11_char_is_k[1:0])
   ,.pipe_rx12_char_is_k(pipe_rx12_char_is_k[1:0])
   ,.pipe_rx13_char_is_k(pipe_rx13_char_is_k[1:0])
   ,.pipe_rx14_char_is_k(pipe_rx14_char_is_k[1:0])
   ,.pipe_rx15_char_is_k(pipe_rx15_char_is_k[1:0])
   ,.pipe_rx00_valid(pipe_rx00_valid)
   ,.pipe_rx01_valid(pipe_rx01_valid)
   ,.pipe_rx02_valid(pipe_rx02_valid)
   ,.pipe_rx03_valid(pipe_rx03_valid)
   ,.pipe_rx04_valid(pipe_rx04_valid)
   ,.pipe_rx05_valid(pipe_rx05_valid)
   ,.pipe_rx06_valid(pipe_rx06_valid)
   ,.pipe_rx07_valid(pipe_rx07_valid)
   ,.pipe_rx08_valid(pipe_rx08_valid)
   ,.pipe_rx09_valid(pipe_rx09_valid)
   ,.pipe_rx10_valid(pipe_rx10_valid)
   ,.pipe_rx11_valid(pipe_rx11_valid)
   ,.pipe_rx12_valid(pipe_rx12_valid)
   ,.pipe_rx13_valid(pipe_rx13_valid)
   ,.pipe_rx14_valid(pipe_rx14_valid)
   ,.pipe_rx15_valid(pipe_rx15_valid)
   ,.pipe_rx00_data(pipe_rx00_data[31:0])
   ,.pipe_rx01_data(pipe_rx01_data[31:0])
   ,.pipe_rx02_data(pipe_rx02_data[31:0])
   ,.pipe_rx03_data(pipe_rx03_data[31:0])
   ,.pipe_rx04_data(pipe_rx04_data[31:0])
   ,.pipe_rx05_data(pipe_rx05_data[31:0])
   ,.pipe_rx06_data(pipe_rx06_data[31:0])
   ,.pipe_rx07_data(pipe_rx07_data[31:0])
   ,.pipe_rx08_data( pipe_tx_rate_i==2'b11 ? pipe_rx00_data[63:32] : pipe_rx08_data[31:0] )
   ,.pipe_rx09_data( pipe_tx_rate_i==2'b11 ? pipe_rx01_data[63:32] : pipe_rx09_data[31:0] )
   ,.pipe_rx10_data( pipe_tx_rate_i==2'b11 ? pipe_rx02_data[63:32] : pipe_rx10_data[31:0] )
   ,.pipe_rx11_data( pipe_tx_rate_i==2'b11 ? pipe_rx03_data[63:32] : pipe_rx11_data[31:0] )
   ,.pipe_rx12_data( pipe_tx_rate_i==2'b11 ? pipe_rx04_data[63:32] : pipe_rx12_data[31:0] )
   ,.pipe_rx13_data( pipe_tx_rate_i==2'b11 ? pipe_rx05_data[63:32] : pipe_rx13_data[31:0] )
   ,.pipe_rx14_data( pipe_tx_rate_i==2'b11 ? pipe_rx06_data[63:32] : pipe_rx14_data[31:0] )
   ,.pipe_rx15_data( pipe_tx_rate_i==2'b11 ? pipe_rx07_data[63:32] : pipe_rx15_data[31:0] )
   ,.pipe_rx00_polarity(pipe_rx00_polarity)
   ,.pipe_rx01_polarity(pipe_rx01_polarity)
   ,.pipe_rx02_polarity(pipe_rx02_polarity)
   ,.pipe_rx03_polarity(pipe_rx03_polarity)
   ,.pipe_rx04_polarity(pipe_rx04_polarity)
   ,.pipe_rx05_polarity(pipe_rx05_polarity)
   ,.pipe_rx06_polarity(pipe_rx06_polarity)
   ,.pipe_rx07_polarity(pipe_rx07_polarity)
   ,.pipe_rx08_polarity(pipe_rx08_polarity)
   ,.pipe_rx09_polarity(pipe_rx09_polarity)
   ,.pipe_rx10_polarity(pipe_rx10_polarity)
   ,.pipe_rx11_polarity(pipe_rx11_polarity)
   ,.pipe_rx12_polarity(pipe_rx12_polarity)
   ,.pipe_rx13_polarity(pipe_rx13_polarity)
   ,.pipe_rx14_polarity(pipe_rx14_polarity)
   ,.pipe_rx15_polarity(pipe_rx15_polarity)
   ,.pipe_rx00_status(pipe_rx00_status[2:0])
   ,.pipe_rx01_status(pipe_rx01_status[2:0])
   ,.pipe_rx02_status(pipe_rx02_status[2:0])
   ,.pipe_rx03_status(pipe_rx03_status[2:0])
   ,.pipe_rx04_status(pipe_rx04_status[2:0])
   ,.pipe_rx05_status(pipe_rx05_status[2:0])
   ,.pipe_rx06_status(pipe_rx06_status[2:0])
   ,.pipe_rx07_status(pipe_rx07_status[2:0])
   ,.pipe_rx08_status(pipe_rx08_status[2:0])
   ,.pipe_rx09_status(pipe_rx09_status[2:0])
   ,.pipe_rx10_status(pipe_rx10_status[2:0])
   ,.pipe_rx11_status(pipe_rx11_status[2:0])
   ,.pipe_rx12_status(pipe_rx12_status[2:0])
   ,.pipe_rx13_status(pipe_rx13_status[2:0])
   ,.pipe_rx14_status(pipe_rx14_status[2:0])
   ,.pipe_rx15_status(pipe_rx15_status[2:0])
   ,.pipe_rx00_phy_status(pipe_rx00_phy_status)
   ,.pipe_rx01_phy_status(pipe_rx01_phy_status)
   ,.pipe_rx02_phy_status(pipe_rx02_phy_status)
   ,.pipe_rx03_phy_status(pipe_rx03_phy_status)
   ,.pipe_rx04_phy_status(pipe_rx04_phy_status)
   ,.pipe_rx05_phy_status(pipe_rx05_phy_status)
   ,.pipe_rx06_phy_status(pipe_rx06_phy_status)
   ,.pipe_rx07_phy_status(pipe_rx07_phy_status)
   ,.pipe_rx08_phy_status(pipe_rx08_phy_status)
   ,.pipe_rx09_phy_status(pipe_rx09_phy_status)
   ,.pipe_rx10_phy_status(pipe_rx10_phy_status)
   ,.pipe_rx11_phy_status(pipe_rx11_phy_status)
   ,.pipe_rx12_phy_status(pipe_rx12_phy_status)
   ,.pipe_rx13_phy_status(pipe_rx13_phy_status)
   ,.pipe_rx14_phy_status(pipe_rx14_phy_status)
   ,.pipe_rx15_phy_status(pipe_rx15_phy_status)
   ,.pipe_rx00_elec_idle(pipe_rx00_elec_idle)
   ,.pipe_rx01_elec_idle(pipe_rx01_elec_idle)
   ,.pipe_rx02_elec_idle(pipe_rx02_elec_idle)
   ,.pipe_rx03_elec_idle(pipe_rx03_elec_idle)
   ,.pipe_rx04_elec_idle(pipe_rx04_elec_idle)
   ,.pipe_rx05_elec_idle(pipe_rx05_elec_idle)
   ,.pipe_rx06_elec_idle(pipe_rx06_elec_idle)
   ,.pipe_rx07_elec_idle(pipe_rx07_elec_idle)
   ,.pipe_rx08_elec_idle(pipe_rx08_elec_idle)
   ,.pipe_rx09_elec_idle(pipe_rx09_elec_idle)
   ,.pipe_rx10_elec_idle(pipe_rx10_elec_idle)
   ,.pipe_rx11_elec_idle(pipe_rx11_elec_idle)
   ,.pipe_rx12_elec_idle(pipe_rx12_elec_idle)
   ,.pipe_rx13_elec_idle(pipe_rx13_elec_idle)
   ,.pipe_rx14_elec_idle(pipe_rx14_elec_idle)
   ,.pipe_rx15_elec_idle(pipe_rx15_elec_idle)
   ,.pipe_rx00_data_valid(pipe_rx00_data_valid)
   ,.pipe_rx01_data_valid(pipe_rx01_data_valid)
   ,.pipe_rx02_data_valid(pipe_rx02_data_valid)
   ,.pipe_rx03_data_valid(pipe_rx03_data_valid)
   ,.pipe_rx04_data_valid(pipe_rx04_data_valid)
   ,.pipe_rx05_data_valid(pipe_rx05_data_valid)
   ,.pipe_rx06_data_valid(pipe_rx06_data_valid)
   ,.pipe_rx07_data_valid(pipe_rx07_data_valid)
   ,.pipe_rx08_data_valid(pipe_rx08_data_valid)
   ,.pipe_rx09_data_valid(pipe_rx09_data_valid)
   ,.pipe_rx10_data_valid(pipe_rx10_data_valid)
   ,.pipe_rx11_data_valid(pipe_rx11_data_valid)
   ,.pipe_rx12_data_valid(pipe_rx12_data_valid)
   ,.pipe_rx13_data_valid(pipe_rx13_data_valid)
   ,.pipe_rx14_data_valid(pipe_rx14_data_valid)
   ,.pipe_rx15_data_valid(pipe_rx15_data_valid)
   ,.pipe_rx00_start_block(pipe_rx00_start_block[1:0])
   ,.pipe_rx01_start_block(pipe_rx01_start_block[1:0])
   ,.pipe_rx02_start_block(pipe_rx02_start_block[1:0])
   ,.pipe_rx03_start_block(pipe_rx03_start_block[1:0])
   ,.pipe_rx04_start_block(pipe_rx04_start_block[1:0])
   ,.pipe_rx05_start_block(pipe_rx05_start_block[1:0])
   ,.pipe_rx06_start_block(pipe_rx06_start_block[1:0])
   ,.pipe_rx07_start_block(pipe_rx07_start_block[1:0])
   ,.pipe_rx08_start_block(pipe_rx08_start_block[1:0])
   ,.pipe_rx09_start_block(pipe_rx09_start_block[1:0])
   ,.pipe_rx10_start_block(pipe_rx10_start_block[1:0])
   ,.pipe_rx11_start_block(pipe_rx11_start_block[1:0])
   ,.pipe_rx12_start_block(pipe_rx12_start_block[1:0])
   ,.pipe_rx13_start_block(pipe_rx13_start_block[1:0])
   ,.pipe_rx14_start_block(pipe_rx14_start_block[1:0])
   ,.pipe_rx15_start_block(pipe_rx15_start_block[1:0])
   ,.pipe_rx00_sync_header(pipe_rx00_sync_header[1:0])
   ,.pipe_rx01_sync_header(pipe_rx01_sync_header[1:0])
   ,.pipe_rx02_sync_header(pipe_rx02_sync_header[1:0])
   ,.pipe_rx03_sync_header(pipe_rx03_sync_header[1:0])
   ,.pipe_rx04_sync_header(pipe_rx04_sync_header[1:0])
   ,.pipe_rx05_sync_header(pipe_rx05_sync_header[1:0])
   ,.pipe_rx06_sync_header(pipe_rx06_sync_header[1:0])
   ,.pipe_rx07_sync_header(pipe_rx07_sync_header[1:0])
   ,.pipe_rx08_sync_header(pipe_rx08_sync_header[1:0])
   ,.pipe_rx09_sync_header(pipe_rx09_sync_header[1:0])
   ,.pipe_rx10_sync_header(pipe_rx10_sync_header[1:0])
   ,.pipe_rx11_sync_header(pipe_rx11_sync_header[1:0])
   ,.pipe_rx12_sync_header(pipe_rx12_sync_header[1:0])
   ,.pipe_rx13_sync_header(pipe_rx13_sync_header[1:0])
   ,.pipe_rx14_sync_header(pipe_rx14_sync_header[1:0])
   ,.pipe_rx15_sync_header(pipe_rx15_sync_header[1:0])
   ,.pipe_tx00_compliance(pipe_tx00_compliance)
   ,.pipe_tx01_compliance(pipe_tx01_compliance)
   ,.pipe_tx02_compliance(pipe_tx02_compliance)
   ,.pipe_tx03_compliance(pipe_tx03_compliance)
   ,.pipe_tx04_compliance(pipe_tx04_compliance)
   ,.pipe_tx05_compliance(pipe_tx05_compliance)
   ,.pipe_tx06_compliance(pipe_tx06_compliance)
   ,.pipe_tx07_compliance(pipe_tx07_compliance)
   ,.pipe_tx08_compliance(pipe_tx08_compliance)
   ,.pipe_tx09_compliance(pipe_tx09_compliance)
   ,.pipe_tx10_compliance(pipe_tx10_compliance)
   ,.pipe_tx11_compliance(pipe_tx11_compliance)
   ,.pipe_tx12_compliance(pipe_tx12_compliance)
   ,.pipe_tx13_compliance(pipe_tx13_compliance)
   ,.pipe_tx14_compliance(pipe_tx14_compliance)
   ,.pipe_tx15_compliance(pipe_tx15_compliance)
   ,.pipe_tx00_char_is_k(pipe_tx00_char_is_k[1:0])
   ,.pipe_tx01_char_is_k(pipe_tx01_char_is_k[1:0])
   ,.pipe_tx02_char_is_k(pipe_tx02_char_is_k[1:0])
   ,.pipe_tx03_char_is_k(pipe_tx03_char_is_k[1:0])
   ,.pipe_tx04_char_is_k(pipe_tx04_char_is_k[1:0])
   ,.pipe_tx05_char_is_k(pipe_tx05_char_is_k[1:0])
   ,.pipe_tx06_char_is_k(pipe_tx06_char_is_k[1:0])
   ,.pipe_tx07_char_is_k(pipe_tx07_char_is_k[1:0])
   ,.pipe_tx08_char_is_k(pipe_tx08_char_is_k[1:0])
   ,.pipe_tx09_char_is_k(pipe_tx09_char_is_k[1:0])
   ,.pipe_tx10_char_is_k(pipe_tx10_char_is_k[1:0])
   ,.pipe_tx11_char_is_k(pipe_tx11_char_is_k[1:0])
   ,.pipe_tx12_char_is_k(pipe_tx12_char_is_k[1:0])
   ,.pipe_tx13_char_is_k(pipe_tx13_char_is_k[1:0])
   ,.pipe_tx14_char_is_k(pipe_tx14_char_is_k[1:0])
   ,.pipe_tx15_char_is_k(pipe_tx15_char_is_k[1:0])
   ,.pipe_tx00_data(pipe_tx00_data[31:0])
   ,.pipe_tx01_data(pipe_tx01_data[31:0])
   ,.pipe_tx02_data(pipe_tx02_data[31:0])
   ,.pipe_tx03_data(pipe_tx03_data[31:0])
   ,.pipe_tx04_data(pipe_tx04_data[31:0])
   ,.pipe_tx05_data(pipe_tx05_data[31:0])
   ,.pipe_tx06_data(pipe_tx06_data[31:0])
   ,.pipe_tx07_data(pipe_tx07_data[31:0])
   ,.pipe_tx08_data(pipe_tx08_data[31:0])
   ,.pipe_tx09_data(pipe_tx09_data[31:0])
   ,.pipe_tx10_data(pipe_tx10_data[31:0])
   ,.pipe_tx11_data(pipe_tx11_data[31:0])
   ,.pipe_tx12_data(pipe_tx12_data[31:0])
   ,.pipe_tx13_data(pipe_tx13_data[31:0])
   ,.pipe_tx14_data(pipe_tx14_data[31:0])
   ,.pipe_tx15_data(pipe_tx15_data[31:0])
   ,.pipe_tx00_elec_idle(pipe_tx00_elec_idle)
   ,.pipe_tx01_elec_idle(pipe_tx01_elec_idle)
   ,.pipe_tx02_elec_idle(pipe_tx02_elec_idle)
   ,.pipe_tx03_elec_idle(pipe_tx03_elec_idle)
   ,.pipe_tx04_elec_idle(pipe_tx04_elec_idle)
   ,.pipe_tx05_elec_idle(pipe_tx05_elec_idle)
   ,.pipe_tx06_elec_idle(pipe_tx06_elec_idle)
   ,.pipe_tx07_elec_idle(pipe_tx07_elec_idle)
   ,.pipe_tx08_elec_idle(pipe_tx08_elec_idle)
   ,.pipe_tx09_elec_idle(pipe_tx09_elec_idle)
   ,.pipe_tx10_elec_idle(pipe_tx10_elec_idle)
   ,.pipe_tx11_elec_idle(pipe_tx11_elec_idle)
   ,.pipe_tx12_elec_idle(pipe_tx12_elec_idle)
   ,.pipe_tx13_elec_idle(pipe_tx13_elec_idle)
   ,.pipe_tx14_elec_idle(pipe_tx14_elec_idle)
   ,.pipe_tx15_elec_idle(pipe_tx15_elec_idle)
   ,.pipe_tx00_powerdown(pipe_tx00_powerdown[1:0])
   ,.pipe_tx01_powerdown(pipe_tx01_powerdown[1:0])
   ,.pipe_tx02_powerdown(pipe_tx02_powerdown[1:0])
   ,.pipe_tx03_powerdown(pipe_tx03_powerdown[1:0])
   ,.pipe_tx04_powerdown(pipe_tx04_powerdown[1:0])
   ,.pipe_tx05_powerdown(pipe_tx05_powerdown[1:0])
   ,.pipe_tx06_powerdown(pipe_tx06_powerdown[1:0])
   ,.pipe_tx07_powerdown(pipe_tx07_powerdown[1:0])
   ,.pipe_tx08_powerdown(pipe_tx08_powerdown[1:0])
   ,.pipe_tx09_powerdown(pipe_tx09_powerdown[1:0])
   ,.pipe_tx10_powerdown(pipe_tx10_powerdown[1:0])
   ,.pipe_tx11_powerdown(pipe_tx11_powerdown[1:0])
   ,.pipe_tx12_powerdown(pipe_tx12_powerdown[1:0])
   ,.pipe_tx13_powerdown(pipe_tx13_powerdown[1:0])
   ,.pipe_tx14_powerdown(pipe_tx14_powerdown[1:0])
   ,.pipe_tx15_powerdown(pipe_tx15_powerdown[1:0])
   ,.pipe_tx00_data_valid(pipe_tx00_data_valid)
   ,.pipe_tx01_data_valid(pipe_tx01_data_valid)
   ,.pipe_tx02_data_valid(pipe_tx02_data_valid)
   ,.pipe_tx03_data_valid(pipe_tx03_data_valid)
   ,.pipe_tx04_data_valid(pipe_tx04_data_valid)
   ,.pipe_tx05_data_valid(pipe_tx05_data_valid)
   ,.pipe_tx06_data_valid(pipe_tx06_data_valid)
   ,.pipe_tx07_data_valid(pipe_tx07_data_valid)
   ,.pipe_tx08_data_valid(pipe_tx08_data_valid)
   ,.pipe_tx09_data_valid(pipe_tx09_data_valid)
   ,.pipe_tx10_data_valid(pipe_tx10_data_valid)
   ,.pipe_tx11_data_valid(pipe_tx11_data_valid)
   ,.pipe_tx12_data_valid(pipe_tx12_data_valid)
   ,.pipe_tx13_data_valid(pipe_tx13_data_valid)
   ,.pipe_tx14_data_valid(pipe_tx14_data_valid)
   ,.pipe_tx15_data_valid(pipe_tx15_data_valid)
   ,.pipe_tx00_start_block(pipe_tx00_start_block)
   ,.pipe_tx01_start_block(pipe_tx01_start_block)
   ,.pipe_tx02_start_block(pipe_tx02_start_block)
   ,.pipe_tx03_start_block(pipe_tx03_start_block)
   ,.pipe_tx04_start_block(pipe_tx04_start_block)
   ,.pipe_tx05_start_block(pipe_tx05_start_block)
   ,.pipe_tx06_start_block(pipe_tx06_start_block)
   ,.pipe_tx07_start_block(pipe_tx07_start_block)
   ,.pipe_tx08_start_block(pipe_tx08_start_block)
   ,.pipe_tx09_start_block(pipe_tx09_start_block)
   ,.pipe_tx10_start_block(pipe_tx10_start_block)
   ,.pipe_tx11_start_block(pipe_tx11_start_block)
   ,.pipe_tx12_start_block(pipe_tx12_start_block)
   ,.pipe_tx13_start_block(pipe_tx13_start_block)
   ,.pipe_tx14_start_block(pipe_tx14_start_block)
   ,.pipe_tx15_start_block(pipe_tx15_start_block)
   ,.pipe_tx00_sync_header(pipe_tx00_sync_header[1:0])
   ,.pipe_tx01_sync_header(pipe_tx01_sync_header[1:0])
   ,.pipe_tx02_sync_header(pipe_tx02_sync_header[1:0])
   ,.pipe_tx03_sync_header(pipe_tx03_sync_header[1:0])
   ,.pipe_tx04_sync_header(pipe_tx04_sync_header[1:0])
   ,.pipe_tx05_sync_header(pipe_tx05_sync_header[1:0])
   ,.pipe_tx06_sync_header(pipe_tx06_sync_header[1:0])
   ,.pipe_tx07_sync_header(pipe_tx07_sync_header[1:0])
   ,.pipe_tx08_sync_header(pipe_tx08_sync_header[1:0])
   ,.pipe_tx09_sync_header(pipe_tx09_sync_header[1:0])
   ,.pipe_tx10_sync_header(pipe_tx10_sync_header[1:0])
   ,.pipe_tx11_sync_header(pipe_tx11_sync_header[1:0])
   ,.pipe_tx12_sync_header(pipe_tx12_sync_header[1:0])
   ,.pipe_tx13_sync_header(pipe_tx13_sync_header[1:0])
   ,.pipe_tx14_sync_header(pipe_tx14_sync_header[1:0])
   ,.pipe_tx15_sync_header(pipe_tx15_sync_header[1:0])
   ,.pipe_rx00_eq_control(pipe_rx00_eq_control[1:0])
   ,.pipe_rx01_eq_control(pipe_rx01_eq_control[1:0])
   ,.pipe_rx02_eq_control(pipe_rx02_eq_control[1:0])
   ,.pipe_rx03_eq_control(pipe_rx03_eq_control[1:0])
   ,.pipe_rx04_eq_control(pipe_rx04_eq_control[1:0])
   ,.pipe_rx05_eq_control(pipe_rx05_eq_control[1:0])
   ,.pipe_rx06_eq_control(pipe_rx06_eq_control[1:0])
   ,.pipe_rx07_eq_control(pipe_rx07_eq_control[1:0])
   ,.pipe_rx08_eq_control(pipe_rx08_eq_control[1:0])
   ,.pipe_rx09_eq_control(pipe_rx09_eq_control[1:0])
   ,.pipe_rx10_eq_control(pipe_rx10_eq_control[1:0])
   ,.pipe_rx11_eq_control(pipe_rx11_eq_control[1:0])
   ,.pipe_rx12_eq_control(pipe_rx12_eq_control[1:0])
   ,.pipe_rx13_eq_control(pipe_rx13_eq_control[1:0])
   ,.pipe_rx14_eq_control(pipe_rx14_eq_control[1:0])
   ,.pipe_rx15_eq_control(pipe_rx15_eq_control[1:0])
   ,.pipe_rx00_eq_lp_lf_fs_sel(pipe_rx00_eq_lp_lf_fs_sel)
   ,.pipe_rx01_eq_lp_lf_fs_sel(pipe_rx01_eq_lp_lf_fs_sel)
   ,.pipe_rx02_eq_lp_lf_fs_sel(pipe_rx02_eq_lp_lf_fs_sel)
   ,.pipe_rx03_eq_lp_lf_fs_sel(pipe_rx03_eq_lp_lf_fs_sel)
   ,.pipe_rx04_eq_lp_lf_fs_sel(pipe_rx04_eq_lp_lf_fs_sel)
   ,.pipe_rx05_eq_lp_lf_fs_sel(pipe_rx05_eq_lp_lf_fs_sel)
   ,.pipe_rx06_eq_lp_lf_fs_sel(pipe_rx06_eq_lp_lf_fs_sel)
   ,.pipe_rx07_eq_lp_lf_fs_sel(pipe_rx07_eq_lp_lf_fs_sel)
   ,.pipe_rx08_eq_lp_lf_fs_sel(pipe_rx08_eq_lp_lf_fs_sel)
   ,.pipe_rx09_eq_lp_lf_fs_sel(pipe_rx09_eq_lp_lf_fs_sel)
   ,.pipe_rx10_eq_lp_lf_fs_sel(pipe_rx10_eq_lp_lf_fs_sel)
   ,.pipe_rx11_eq_lp_lf_fs_sel(pipe_rx11_eq_lp_lf_fs_sel)
   ,.pipe_rx12_eq_lp_lf_fs_sel(pipe_rx12_eq_lp_lf_fs_sel)
   ,.pipe_rx13_eq_lp_lf_fs_sel(pipe_rx13_eq_lp_lf_fs_sel)
   ,.pipe_rx14_eq_lp_lf_fs_sel(pipe_rx14_eq_lp_lf_fs_sel)
   ,.pipe_rx15_eq_lp_lf_fs_sel(pipe_rx15_eq_lp_lf_fs_sel)
   ,.pipe_rx00_eq_lp_new_tx_coeff_or_preset(pipe_rx00_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.pipe_rx01_eq_lp_new_tx_coeff_or_preset(pipe_rx01_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.pipe_rx02_eq_lp_new_tx_coeff_or_preset(pipe_rx02_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.pipe_rx03_eq_lp_new_tx_coeff_or_preset(pipe_rx03_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.pipe_rx04_eq_lp_new_tx_coeff_or_preset(pipe_rx04_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.pipe_rx05_eq_lp_new_tx_coeff_or_preset(pipe_rx05_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.pipe_rx06_eq_lp_new_tx_coeff_or_preset(pipe_rx06_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.pipe_rx07_eq_lp_new_tx_coeff_or_preset(pipe_rx07_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.pipe_rx08_eq_lp_new_tx_coeff_or_preset(pipe_rx08_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.pipe_rx09_eq_lp_new_tx_coeff_or_preset(pipe_rx09_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.pipe_rx10_eq_lp_new_tx_coeff_or_preset(pipe_rx10_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.pipe_rx11_eq_lp_new_tx_coeff_or_preset(pipe_rx11_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.pipe_rx12_eq_lp_new_tx_coeff_or_preset(pipe_rx12_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.pipe_rx13_eq_lp_new_tx_coeff_or_preset(pipe_rx13_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.pipe_rx14_eq_lp_new_tx_coeff_or_preset(pipe_rx14_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.pipe_rx15_eq_lp_new_tx_coeff_or_preset(pipe_rx15_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.pipe_rx00_eq_lp_adapt_done(pipe_rx00_eq_lp_adapt_done)
   ,.pipe_rx01_eq_lp_adapt_done(pipe_rx01_eq_lp_adapt_done)
   ,.pipe_rx02_eq_lp_adapt_done(pipe_rx02_eq_lp_adapt_done)
   ,.pipe_rx03_eq_lp_adapt_done(pipe_rx03_eq_lp_adapt_done)
   ,.pipe_rx04_eq_lp_adapt_done(pipe_rx04_eq_lp_adapt_done)
   ,.pipe_rx05_eq_lp_adapt_done(pipe_rx05_eq_lp_adapt_done)
   ,.pipe_rx06_eq_lp_adapt_done(pipe_rx06_eq_lp_adapt_done)
   ,.pipe_rx07_eq_lp_adapt_done(pipe_rx07_eq_lp_adapt_done)
   ,.pipe_rx08_eq_lp_adapt_done(pipe_rx08_eq_lp_adapt_done)
   ,.pipe_rx09_eq_lp_adapt_done(pipe_rx09_eq_lp_adapt_done)
   ,.pipe_rx10_eq_lp_adapt_done(pipe_rx10_eq_lp_adapt_done)
   ,.pipe_rx11_eq_lp_adapt_done(pipe_rx11_eq_lp_adapt_done)
   ,.pipe_rx12_eq_lp_adapt_done(pipe_rx12_eq_lp_adapt_done)
   ,.pipe_rx13_eq_lp_adapt_done(pipe_rx13_eq_lp_adapt_done)
   ,.pipe_rx14_eq_lp_adapt_done(pipe_rx14_eq_lp_adapt_done)
   ,.pipe_rx15_eq_lp_adapt_done(pipe_rx15_eq_lp_adapt_done)
   ,.pipe_rx00_eq_done(pipe_rx00_eq_done)
   ,.pipe_rx01_eq_done(pipe_rx01_eq_done)
   ,.pipe_rx02_eq_done(pipe_rx02_eq_done)
   ,.pipe_rx03_eq_done(pipe_rx03_eq_done)
   ,.pipe_rx04_eq_done(pipe_rx04_eq_done)
   ,.pipe_rx05_eq_done(pipe_rx05_eq_done)
   ,.pipe_rx06_eq_done(pipe_rx06_eq_done)
   ,.pipe_rx07_eq_done(pipe_rx07_eq_done)
   ,.pipe_rx08_eq_done(pipe_rx08_eq_done)
   ,.pipe_rx09_eq_done(pipe_rx09_eq_done)
   ,.pipe_rx10_eq_done(pipe_rx10_eq_done)
   ,.pipe_rx11_eq_done(pipe_rx11_eq_done)
   ,.pipe_rx12_eq_done(pipe_rx12_eq_done)
   ,.pipe_rx13_eq_done(pipe_rx13_eq_done)
   ,.pipe_rx14_eq_done(pipe_rx14_eq_done)
   ,.pipe_rx15_eq_done(pipe_rx15_eq_done)
   ,.pipe_tx00_eq_control(pipe_tx00_eq_control[1:0])
   ,.pipe_tx01_eq_control(pipe_tx01_eq_control[1:0])
   ,.pipe_tx02_eq_control(pipe_tx02_eq_control[1:0])
   ,.pipe_tx03_eq_control(pipe_tx03_eq_control[1:0])
   ,.pipe_tx04_eq_control(pipe_tx04_eq_control[1:0])
   ,.pipe_tx05_eq_control(pipe_tx05_eq_control[1:0])
   ,.pipe_tx06_eq_control(pipe_tx06_eq_control[1:0])
   ,.pipe_tx07_eq_control(pipe_tx07_eq_control[1:0])
   ,.pipe_tx08_eq_control(pipe_tx08_eq_control[1:0])
   ,.pipe_tx09_eq_control(pipe_tx09_eq_control[1:0])
   ,.pipe_tx10_eq_control(pipe_tx10_eq_control[1:0])
   ,.pipe_tx11_eq_control(pipe_tx11_eq_control[1:0])
   ,.pipe_tx12_eq_control(pipe_tx12_eq_control[1:0])
   ,.pipe_tx13_eq_control(pipe_tx13_eq_control[1:0])
   ,.pipe_tx14_eq_control(pipe_tx14_eq_control[1:0])
   ,.pipe_tx15_eq_control(pipe_tx15_eq_control[1:0])
   ,.pipe_tx00_eq_deemph(pipe_tx00_eq_deemph[5:0])
   ,.pipe_tx01_eq_deemph(pipe_tx01_eq_deemph[5:0])
   ,.pipe_tx02_eq_deemph(pipe_tx02_eq_deemph[5:0])
   ,.pipe_tx03_eq_deemph(pipe_tx03_eq_deemph[5:0])
   ,.pipe_tx04_eq_deemph(pipe_tx04_eq_deemph[5:0])
   ,.pipe_tx05_eq_deemph(pipe_tx05_eq_deemph[5:0])
   ,.pipe_tx06_eq_deemph(pipe_tx06_eq_deemph[5:0])
   ,.pipe_tx07_eq_deemph(pipe_tx07_eq_deemph[5:0])
   ,.pipe_tx08_eq_deemph(pipe_tx08_eq_deemph[5:0])
   ,.pipe_tx09_eq_deemph(pipe_tx09_eq_deemph[5:0])
   ,.pipe_tx10_eq_deemph(pipe_tx10_eq_deemph[5:0])
   ,.pipe_tx11_eq_deemph(pipe_tx11_eq_deemph[5:0])
   ,.pipe_tx12_eq_deemph(pipe_tx12_eq_deemph[5:0])
   ,.pipe_tx13_eq_deemph(pipe_tx13_eq_deemph[5:0])
   ,.pipe_tx14_eq_deemph(pipe_tx14_eq_deemph[5:0])
   ,.pipe_tx15_eq_deemph(pipe_tx15_eq_deemph[5:0])
   ,.pipe_tx00_eq_coeff(pipe_tx00_eq_coeff[17:0])
   ,.pipe_tx01_eq_coeff(pipe_tx01_eq_coeff[17:0])
   ,.pipe_tx02_eq_coeff(pipe_tx02_eq_coeff[17:0])
   ,.pipe_tx03_eq_coeff(pipe_tx03_eq_coeff[17:0])
   ,.pipe_tx04_eq_coeff(pipe_tx04_eq_coeff[17:0])
   ,.pipe_tx05_eq_coeff(pipe_tx05_eq_coeff[17:0])
   ,.pipe_tx06_eq_coeff(pipe_tx06_eq_coeff[17:0])
   ,.pipe_tx07_eq_coeff(pipe_tx07_eq_coeff[17:0])
   ,.pipe_tx08_eq_coeff(pipe_tx08_eq_coeff[17:0])
   ,.pipe_tx09_eq_coeff(pipe_tx09_eq_coeff[17:0])
   ,.pipe_tx10_eq_coeff(pipe_tx10_eq_coeff[17:0])
   ,.pipe_tx11_eq_coeff(pipe_tx11_eq_coeff[17:0])
   ,.pipe_tx12_eq_coeff(pipe_tx12_eq_coeff[17:0])
   ,.pipe_tx13_eq_coeff(pipe_tx13_eq_coeff[17:0])
   ,.pipe_tx14_eq_coeff(pipe_tx14_eq_coeff[17:0])
   ,.pipe_tx15_eq_coeff(pipe_tx15_eq_coeff[17:0])
   ,.pipe_tx00_eq_done(pipe_tx00_eq_done)
   ,.pipe_tx01_eq_done(pipe_tx01_eq_done)
   ,.pipe_tx02_eq_done(pipe_tx02_eq_done)
   ,.pipe_tx03_eq_done(pipe_tx03_eq_done)
   ,.pipe_tx04_eq_done(pipe_tx04_eq_done)
   ,.pipe_tx05_eq_done(pipe_tx05_eq_done)
   ,.pipe_tx06_eq_done(pipe_tx06_eq_done)
   ,.pipe_tx07_eq_done(pipe_tx07_eq_done)
   ,.pipe_tx08_eq_done(pipe_tx08_eq_done)
   ,.pipe_tx09_eq_done(pipe_tx09_eq_done)
   ,.pipe_tx10_eq_done(pipe_tx10_eq_done)
   ,.pipe_tx11_eq_done(pipe_tx11_eq_done)
   ,.pipe_tx12_eq_done(pipe_tx12_eq_done)
   ,.pipe_tx13_eq_done(pipe_tx13_eq_done)
   ,.pipe_tx14_eq_done(pipe_tx14_eq_done)
   ,.pipe_tx15_eq_done(pipe_tx15_eq_done)
   ,.pipe_rx_eq_lp_tx_preset(pipe_rx_eq_lp_tx_preset[3:0])
   ,.pipe_rx_eq_lp_lf_fs(pipe_rx_eq_lp_lf_fs[5:0])
   ,.pipe_tx_rcvr_det(pipe_tx_rcvr_det)
   ,.pipe_tx_rate(pipe_tx_rate_o[1:0])
   ,.pipe_tx_deemph(pipe_tx_deemph)
   ,.pipe_tx_margin(pipe_tx_margin[2:0])
   ,.pipe_tx_swing(pipe_tx_swing)
   ,.pipe_tx_reset(pipe_tx_reset)
   ,.pipe_eq_fs(pipe_eq_fs_temp)
   ,.pipe_eq_lf(pipe_eq_lf_temp)
   ,.pl_gen2_upstream_prefer_deemph(pl_gen2_upstream_prefer_deemph)
   ,.pl_eq_in_progress(pl_eq_in_progress)
   ,.pl_eq_phase(pl_eq_phase[1:0])
   ,.pl_eq_reset_eieos_count(1'b0)
   ,.pl_redo_eq(pl_redo_eq)
   ,.pl_redo_eq_speed(pl_redo_eq_speed)
   ,.pl_eq_mismatch(pl_eq_mismatch)
   ,.pl_redo_eq_pending(pl_redo_eq_pending)
   ,.m_axis_cq_tdata(m_axis_cq_tdata[AXI4_DATA_WIDTH-1:0])
   ,.s_axis_cc_tdata(s_axis_cc_tdata[AXI4_DATA_WIDTH-1:0])
   ,.s_axis_rq_tdata(s_axis_rq_tdata[AXI4_DATA_WIDTH-1:0])
   ,.m_axis_rc_tdata(m_axis_rc_tdata[AXI4_DATA_WIDTH-1:0])
   ,.m_axis_cq_tuser(m_axis_cq_tuser[AXI4_CQ_TUSER_WIDTH-1:0])
   ,.s_axis_cc_tuser(s_axis_cc_tuser[AXI4_CC_TUSER_WIDTH-1:0])
   ,.m_axis_cq_tlast(m_axis_cq_tlast)
   ,.s_axis_rq_tlast(s_axis_rq_tlast)
   ,.m_axis_rc_tlast(m_axis_rc_tlast)
   ,.s_axis_cc_tlast(s_axis_cc_tlast)
   ,.pcie_cq_np_req(pcie_cq_np_req_int[1:0])
   ,.pcie_cq_np_req_count(pcie_cq_np_req_count[5:0])
   ,.s_axis_rq_tuser(s_axis_rq_tuser[AXI4_RQ_TUSER_WIDTH-1:0])
   ,.m_axis_rc_tuser(m_axis_rc_tuser[AXI4_RC_TUSER_WIDTH-1:0])
   ,.m_axis_cq_tkeep(m_axis_cq_tkeep[AXI4_TKEEP_WIDTH-1:0])
   ,.s_axis_cc_tkeep(s_axis_cc_tkeep[AXI4_TKEEP_WIDTH-1:0])
   ,.s_axis_rq_tkeep(s_axis_rq_tkeep[AXI4_TKEEP_WIDTH-1:0])
   ,.m_axis_rc_tkeep(m_axis_rc_tkeep[AXI4_TKEEP_WIDTH-1:0])
   ,.m_axis_cq_tvalid(m_axis_cq_tvalid_int)
   ,.s_axis_cc_tvalid(s_axis_cc_tvalid_int)
   ,.s_axis_rq_tvalid(s_axis_rq_tvalid_int)
   ,.m_axis_rc_tvalid(m_axis_rc_tvalid_int)
   ,.m_axis_cq_tready({AXI4_CQ_TREADY_WIDTH{m_axis_cq_tready_int}})
   ,.s_axis_cc_tready(s_axis_cc_tready_int)
   ,.s_axis_rq_tready(s_axis_rq_tready_int)
   ,.m_axis_rc_tready({AXI4_RC_TREADY_WIDTH{m_axis_rc_tready_int}})
   ,.pcie_rq_seq_num0(pcie_rq_seq_num0[5:0])
   ,.pcie_rq_seq_num_vld0(pcie_rq_seq_num_vld0)
   ,.pcie_rq_seq_num1(pcie_rq_seq_num1[5:0])
   ,.pcie_rq_seq_num_vld1(pcie_rq_seq_num_vld1)
   ,.pcie_rq_tag0(pcie_rq_tag0[7:0])
   ,.pcie_rq_tag_vld0(pcie_rq_tag_vld0)
   ,.pcie_rq_tag1(pcie_rq_tag1[7:0])
   ,.pcie_rq_tag_vld1(pcie_rq_tag_vld1)
   ,.pcie_tfc_nph_av(pcie_tfc_nph_av[3:0])
   ,.pcie_tfc_npd_av(pcie_tfc_npd_av[3:0])
   ,.pcie_rq_tag_av(pcie_rq_tag_av[3:0])
   ,.axi_user_out( )
   ,.axi_user_in(8'h00)
   ,.cfg_mgmt_addr(cfg_mgmt_addr[9:0])
   ,.cfg_mgmt_function_number(cfg_mgmt_function_number[7:0])
   ,.cfg_mgmt_write(cfg_mgmt_write_int)
   ,.cfg_mgmt_write_data(cfg_mgmt_write_data[31:0])
   ,.cfg_mgmt_byte_enable(cfg_mgmt_byte_enable[3:0])
   ,.cfg_mgmt_read(cfg_mgmt_read_int)
   ,.cfg_mgmt_read_data(cfg_mgmt_read_data_sig[31:0])
   ,.cfg_mgmt_read_write_done(cfg_mgmt_read_write_done)
   ,.cfg_mgmt_debug_access(cfg_mgmt_debug_access)
   ,.cfg_phy_link_down(cfg_phy_link_down)
   ,.cfg_phy_link_status(cfg_phy_link_status[1:0])
   ,.cfg_negotiated_width(cfg_negotiated_width[2:0])
   ,.cfg_current_speed(cfg_current_speed[1:0])
   ,.cfg_max_payload(cfg_max_payload[1:0])
   ,.cfg_max_read_req(cfg_max_read_req[2:0])
   ,.cfg_function_status(cfg_function_status[15:0])
   ,.cfg_function_power_state(cfg_function_power_state[11:0])
   ,.cfg_link_power_state(cfg_link_power_state[1:0])
   ,.cfg_err_cor_out(cfg_err_cor_out)
   ,.cfg_err_nonfatal_out(cfg_err_nonfatal_out)
   ,.cfg_err_fatal_out(cfg_err_fatal_out)
   ,.cfg_local_error_valid(cfg_local_error_valid)
   ,.cfg_local_error_out(cfg_local_error_out[4:0])
   ,.cfg_ltr_enable()
   ,.cfg_ltssm_state(cfg_ltssm_state[5:0])
   ,.cfg_rx_pm_state(cfg_rx_pm_state[1:0])
   ,.cfg_tx_pm_state(cfg_tx_pm_state[1:0])
   ,.cfg_rcb_status(cfg_rcb_status[3:0])
   ,.cfg_obff_enable(cfg_obff_enable[1:0])
   ,.cfg_pl_status_change(cfg_pl_status_change)
   ,.cfg_tph_requester_enable(cfg_tph_requester_enable[3:0])
   ,.cfg_tph_st_mode(cfg_tph_st_mode[11:0])
   ,.cfg_msg_received(cfg_msg_received)
   ,.cfg_msg_received_data(cfg_msg_received_data[7:0])
   ,.cfg_msg_received_type(cfg_msg_received_type[4:0])
   ,.cfg_msg_transmit(cfg_msg_transmit_int)
   ,.cfg_msg_transmit_type(cfg_msg_transmit_type[2:0])
   ,.cfg_msg_transmit_data(cfg_msg_transmit_data[31:0])
   ,.cfg_msg_transmit_done(cfg_msg_transmit_done)
   ,.cfg_fc_ph(cfg_fc_ph[7:0])
   ,.cfg_fc_pd(cfg_fc_pd[11:0])
   ,.cfg_fc_nph(cfg_fc_nph[7:0])
   ,.cfg_fc_npd(cfg_fc_npd[11:0])
   ,.cfg_fc_cplh(cfg_fc_cplh[7:0])
   ,.cfg_fc_cpld(cfg_fc_cpld[11:0])
   ,.cfg_fc_sel(cfg_fc_sel[2:0])
   ,.cfg_fc_vc_sel(cfg_fc_vc_sel)
   ,.cfg_hot_reset_in(cfg_hot_reset_in_int)
   ,.cfg_hot_reset_out(cfg_hot_reset_out)
   ,.cfg_config_space_enable(cfg_config_space_enable_int)
   ,.cfg_dsn(cfg_dsn_int[63:0])
   ,.cfg_dev_id_pf0(cfg_dev_id_pf0[15:0])
   ,.cfg_dev_id_pf1(cfg_dev_id_pf1[15:0])
   ,.cfg_dev_id_pf2(cfg_dev_id_pf2[15:0])
   ,.cfg_dev_id_pf3(cfg_dev_id_pf3[15:0])
   ,.cfg_vend_id(cfg_vend_id[15:0])
   ,.cfg_rev_id_pf0(cfg_rev_id_pf0[7:0])
   ,.cfg_rev_id_pf1(cfg_rev_id_pf1[7:0])
   ,.cfg_rev_id_pf2(cfg_rev_id_pf2[7:0])
   ,.cfg_rev_id_pf3(cfg_rev_id_pf3[7:0])
   ,.cfg_subsys_id_pf0(cfg_subsys_id_pf0[15:0])
   ,.cfg_subsys_id_pf1(cfg_subsys_id_pf1[15:0])
   ,.cfg_subsys_id_pf2(cfg_subsys_id_pf2[15:0])
   ,.cfg_subsys_id_pf3(cfg_subsys_id_pf3[15:0])
   ,.cfg_subsys_vend_id(cfg_subsys_vend_id[15:0])
   ,.cfg_ds_port_number(cfg_ds_port_number[7:0])
   ,.cfg_ds_bus_number(cfg_ds_bus_number[7:0])
   ,.cfg_ds_device_number(cfg_ds_device_number[4:0])
   ,.cfg_ds_function_number(cfg_ds_function_number[2:0])
   ,.cfg_bus_number(cfg_bus_number[7:0])
   ,.cfg_power_state_change_ack(cfg_power_state_change_ack_int)
   ,.cfg_power_state_change_interrupt(cfg_power_state_change_interrupt)
   ,.cfg_err_cor_in(cfg_err_cor_in_int)
   ,.cfg_err_uncor_in(cfg_err_uncor_in_int)
   ,.cfg_flr_done(cfg_flr_done_int[3:0])
   ,.cfg_vf_flr_in_process(cfg_vf_flr_in_process[251:0])
   ,.cfg_vf_flr_done(cfg_vf_flr_done_int)
   ,.cfg_vf_flr_func_num(cfg_vf_flr_func_num_int[7:0])
   ,.cfg_vf_status(cfg_vf_status[503:0])
   ,.cfg_vf_power_state(cfg_vf_power_state[755:0])
   ,.cfg_vf_tph_requester_enable( cfg_vf_tph_requester_enable[251:0])
   ,.cfg_vf_tph_st_mode(cfg_vf_tph_st_mode[755:0])
   ,.cfg_interrupt_msix_vf_enable(cfg_interrupt_msix_vf_enable[251:0])
   ,.cfg_interrupt_msix_vf_mask(cfg_interrupt_msix_vf_mask[251:0])
   ,.cfg_pri_control(cfg_pri_control)                         // 2 bits per PF
   ,.cfg_ats_control_enable(cfg_ats_control_enable)           // 1 bit (E) per
   ,.cfg_vf_ats_control_enable(cfg_vf_ats_control_enable)     // 1 bit (E) per
   ,.cfg_pasid_control(cfg_pasid_control)                     // 3 bits per PF
   ,.cfg_max_pasid_width_control(cfg_max_pasid_width_control) // 5 bits per PF
   ,.cfg_flr_in_process(cfg_flr_in_process[3:0])
   ,.cfg_req_pm_transition_l23_ready(cfg_req_pm_transition_l23_ready_int)
   ,.cfg_link_training_enable(cfg_link_training_enable_int)
   ,.cfg_interrupt_int(cfg_interrupt_int_int[3:0])
   ,.cfg_interrupt_sent(cfg_interrupt_sent)
   ,.cfg_interrupt_pending(cfg_interrupt_pending_int[3:0])
   ,.cfg_interrupt_msi_enable(cfg_interrupt_msi_enable[3:0])
   ,.cfg_interrupt_msi_int(cfg_interrupt_msi_int_int[31:0])
   ,.cfg_interrupt_msi_sent(cfg_interrupt_msi_sent)
   ,.cfg_interrupt_msi_fail(cfg_interrupt_msi_fail)
   ,.cfg_interrupt_msi_mmenable(cfg_interrupt_msi_mmenable[11:0])
   ,.cfg_interrupt_msi_pending_status(cfg_interrupt_msi_pending_status[31:0])
   ,.cfg_interrupt_msi_pending_status_function_num(cfg_interrupt_msi_pending_status_function_num[1:0])
   ,.cfg_interrupt_msi_pending_status_data_enable(cfg_interrupt_msi_pending_status_data_enable_int)
   ,.cfg_interrupt_msi_mask_update(cfg_interrupt_msi_mask_update)
   ,.cfg_interrupt_msi_select(cfg_interrupt_msi_select[1:0])
   ,.cfg_interrupt_msi_data(cfg_interrupt_msi_data[31:0])
   ,.cfg_interrupt_msix_enable(cfg_interrupt_msix_enable[3:0])
   ,.cfg_interrupt_msix_mask(cfg_interrupt_msix_mask[3:0])
   ,.cfg_interrupt_msix_address(cfg_interrupt_msix_address[63:0])
   ,.cfg_interrupt_msix_data(cfg_interrupt_msix_data[31:0])
   ,.cfg_interrupt_msix_int(cfg_interrupt_msix_int_int)
   ,.cfg_interrupt_msix_vec_pending(cfg_interrupt_msix_vec_pending_int[1:0])
   ,.cfg_interrupt_msix_vec_pending_status(cfg_interrupt_msix_vec_pending_status)
   ,.cfg_interrupt_msi_attr(cfg_interrupt_msi_attr[2:0])
   ,.cfg_interrupt_msi_tph_present(cfg_interrupt_msi_tph_present)
   ,.cfg_interrupt_msi_tph_type(cfg_interrupt_msi_tph_type[1:0])
   ,.cfg_interrupt_msi_tph_st_tag(cfg_interrupt_msi_tph_st_tag[7:0])
   ,.cfg_interrupt_msi_function_number(cfg_interrupt_msi_function_number[7:0])
   ,.cfg_ext_read_received(cfg_ext_read_received_i)
   ,.cfg_ext_write_received(cfg_ext_write_received_i)
   ,.cfg_ext_register_number(cfg_ext_register_number_i[9:0])
   ,.cfg_ext_function_number(cfg_ext_function_number_i[7:0])
   ,.cfg_ext_write_data(cfg_ext_write_data_i[31:0])
   ,.cfg_ext_write_byte_enable(cfg_ext_write_byte_enable_i[3:0])
   ,.cfg_ext_read_data(cfg_ext_read_data_int[31:0])
   ,.cfg_ext_read_data_valid(cfg_ext_read_data_valid_int)
   ,.cfg_pm_aspm_l1_entry_reject(cfg_pm_aspm_l1_entry_reject_int)
   ,.cfg_pm_aspm_tx_l0s_entry_disable(cfg_pm_aspm_tx_l0s_entry_disable_int)
   ,.user_tph_stt_func_num(8'h00)
   ,.user_tph_stt_index(6'b0)
   ,.user_tph_stt_rd_en(1'b0)
   ,.user_tph_stt_rd_data()
   ,.conf_req_type (conf_req_type)
   ,.conf_req_reg_num (conf_req_reg_num)
   ,.conf_req_data (conf_req_data)
   ,.conf_req_valid(conf_req_valid_int)
   ,.conf_req_ready(conf_req_ready_int)
   ,.conf_resp_rdata(conf_resp_rdata[31:0])
   ,.conf_resp_valid(conf_resp_valid)
   ,.conf_mcap_design_switch (mcap_design_switch)
   ,.conf_mcap_eos()
   ,.conf_mcap_in_use_by_pcie(mcap_pcie_request)
   ,.conf_mcap_request_by_conf(mcap_external_request_int)

   ,.drp_clk(drp_clk_int)
   ,.drp_en(drp_en_int)
   ,.drp_we(drp_we_int)
   ,.drp_addr(drp_addr_int)
   ,.drp_di(drp_di_int)
   ,.drp_rdy(drp_rdy_int)
   ,.drp_do(drp_do_int)
   ,.pipe_clk(pipe_clk)
   ,.core_clk(core_clk)
   ,.user_clk(user_clk)
   ,.user_clk2(user_clk2)
   ,.user_clk_en(user_clk_en)
   ,.mcap_clk(mcap_clk_int)
   ,.mcap_rst_b(mcap_rst_b)
   ,.pcie_perst0_b(pcie_perst0_b)
   ,.pcie_perst1_b(pcie_perst1_b)
   ,.mgmt_reset_n(mgmt_reset_n)
   ,.phy_rdy(phy_rdy)
  //-------------------------------------------
  // CCIX Transmit TLP Interface
  //-------------------------------------------
   ,.s_axis_ccix_tx_tdata(s_axis_ccix_tx_tdata)
   ,.s_axis_ccix_tx_tvalid(s_axis_ccix_tx_tvalid)
   ,.s_axis_ccix_tx_tuser(s_axis_ccix_tx_tuser)
   ,.ccix_tx_credit_gnt(ccix_tx_credit_gnt)
   ,.ccix_tx_credit_rtn(ccix_tx_credit_rtn)
   ,.ccix_tx_active_req(ccix_tx_active_req)
   ,.ccix_tx_active_ack(ccix_tx_active_ack)
   ,.ccix_tx_deact_hint(ccix_tx_deact_hint)
  //-----------------------------------------------------------------------
  // CCIX Receive TLP Interface
  // Data to CCIX protocol processing block
  //-----------------------------------------------------------------------
   ,.m_axis_ccix_rx_tdata(m_axis_ccix_rx_tdata) // 256-bit data
   ,.m_axis_ccix_rx_tvalid(m_axis_ccix_rx_tvalid)
   ,.m_axis_ccix_rx_tuser(m_axis_ccix_rx_tuser) // tuser bus
   ,.ccix_rx_credit_grant(ccix_rx_credit_grant)
   ,.ccix_rx_credit_return(ccix_rx_credit_return)
   ,.ccix_rx_credit_av(ccix_rx_credit_av)
   ,.ccix_rx_active_req (ccix_rx_active_req)
   ,.ccix_rx_active_ack (ccix_rx_active_ack)
   ,.ccix_rx_deact_hint (ccix_rx_deact_hint)
   ,.cfg_vc1_enable (cfg_vc1_enable)
   ,.cfg_vc1_negotiation_pending (cfg_vc1_negotiation_pending)
   ,.ccix_optimized_tlp_tx_and_rx_enable (ccix_optimized_tlp_tx_and_rx_enable_i)
  );

  wire sync_sc_ce;
  wire sync_sc_clr;
  BUFG_GT bufg_gt_sysclk (.CE (sync_sc_ce), .CEMASK (1'd0), .CLR (sync_sc_clr), .CLRMASK (1'd0), .DIV (3'd0), .I (sys_clk), .O (sys_clk_bufg));
  BUFG_GT_SYNC sync_sys_clk (.CESYNC(sync_sc_ce), .CLRSYNC(sync_sc_clr), .CE(gt_gtpowergood[0]), .CLK(sys_clk), .CLR(1'b0));
  assign sys_clk_ce_out = gt_gtpowergood[0];

  always @(posedge user_clk or posedge sys_or_hot_rst_uclk) begin
   if (sys_or_hot_rst_uclk) begin
      as_cdr_hold_req_user    <= 1'b0;
      as_mac_in_detect_user   <= 1'b1;
   end else begin
      // If LTSSM state is Recovery.Speed, L1.Entry, L1.Idle, Loopback.Entry_slave, or Loopback.Speed
      as_cdr_hold_req_user    <= (cfg_ltssm_state == 6'h0C) | (cfg_ltssm_state == 6'h17) |
                                 (cfg_ltssm_state == 6'h18) | (cfg_ltssm_state == 6'h24) |
                                 (cfg_ltssm_state == 6'h2D);
      // If LTSSM state is Detect.Quiet or Detect.Active
      as_mac_in_detect_user   <= (cfg_ltssm_state == 6'h00) | (cfg_ltssm_state == 6'h01);
   end
  end

  // Sync to PIPE_CLK
  always @(posedge pipe_clk or posedge sys_or_hot_rst_pclk) begin
   if (sys_or_hot_rst_pclk) begin
      as_cdr_hold_req_ff    <= 1'b0;
      as_cdr_hold_req_ff1   <= 1'b0;
      as_mac_in_detect_ff   <= 1'b1;
      as_mac_in_detect_ff1  <= 1'b1;
   end else begin
      as_cdr_hold_req_ff    <= as_cdr_hold_req_user;
      as_cdr_hold_req_ff1   <= as_cdr_hold_req_ff;
      as_mac_in_detect_ff   <= as_mac_in_detect_user;
      as_mac_in_detect_ff1  <= as_mac_in_detect_ff;
   end
  end
	assign pipe_rx_eq_lp_tx_preset_temp = pipe_rx_eq_lp_tx_preset;
	assign pipe_tx_rcvr_det_temp = pipe_tx_rcvr_det;
	assign pipe_tx00_powerdown_temp = pipe_tx00_powerdown;
	assign pipe_tx_rate_i_temp = pipe_tx_rate_i;
	assign pipe_tx_deemph_temp = pipe_tx_deemph;
	assign pipe_tx_margin_temp = pipe_tx_margin;
	assign pipe_tx_swing_temp = pipe_tx_swing;
	assign PHY_TXEQ_DONE_TEMP = PHY_TXEQ_DONE;
	assign PHY_TXEQ_NEW_COEFF_TEMP = PHY_TXEQ_NEW_COEFF;
////////////////////////////////////
    localparam GEN4_RXDATA_WAIT = "TRUE";

//  Rx Signals
	assign PHY_RXDATA_TEMP           =    
    //pragma translate_off
    (GEN4_RXDATA_WAIT == "TRUE") ? PHY_RXDATA :
    //pragma translate_on
                                   PHY_RXDATA_REG;
	assign PHY_RXDATAK_TEMP          =   
    //pragma translate_off
    (GEN4_RXDATA_WAIT == "TRUE") ? PHY_RXDATAK :
    //pragma translate_on
                                   PHY_RXDATAK_REG;
	assign PHY_RXVALID_TEMP          =   
    //pragma translate_off
    (GEN4_RXDATA_WAIT == "TRUE") ? PHY_RXVALID :
    //pragma translate_on
                                   PHY_RXVALID_REG;
	assign PHY_RXDATA_VALID_TEMP     =  
    //pragma translate_off
    (GEN4_RXDATA_WAIT == "TRUE") ? PHY_RXDATA_VALID :
    //pragma translate_on
                                   PHY_RXDATA_VALID_REG;
	assign PHY_RXSTATUS_TEMP         =    
    //pragma translate_off
    (GEN4_RXDATA_WAIT == "TRUE") ? PHY_RXSTATUS :
    //pragma translate_on
                                   PHY_RXSTATUS_REG;
	assign PHY_PHYSTATUS_TEMP        =    
    //pragma translate_off
    (GEN4_RXDATA_WAIT == "TRUE") ? PHY_PHYSTATUS :
    //pragma translate_on
                                   PHY_PHYSTATUS_REG;
	assign PHY_RXELECIDLE_TEMP       =    
    //pragma translate_off
    (GEN4_RXDATA_WAIT == "TRUE") ? PHY_RXELECIDLE :
    //pragma translate_on
                                   PHY_RXELECIDLE_REG;
	assign rxsync_header_nogate_temp = 
    //pragma translate_off
    (GEN4_RXDATA_WAIT == "TRUE") ? rxsync_header_nogate :
    //pragma translate_on
                                   rxsync_header_nogate_reg;
	assign PHY_RXSTART_BLOCK_TEMP    = 
    //pragma translate_off
    (GEN4_RXDATA_WAIT == "TRUE") ? PHY_RXSTART_BLOCK :
    //pragma translate_on
                                   PHY_RXSTART_BLOCK_REG;
  // Original
	//assign PHY_RXDATA_TEMP           = PHY_RXDATA;
	//assign PHY_RXDATAK_TEMP          = PHY_RXDATAK;
	//assign PHY_RXVALID_TEMP          = PHY_RXVALID;
	//assign PHY_RXDATA_VALID_TEMP     = PHY_RXDATA_VALID;
	//assign PHY_RXSTATUS_TEMP         = PHY_RXSTATUS;
	//assign PHY_PHYSTATUS_TEMP        = PHY_PHYSTATUS;
	//assign PHY_RXELECIDLE_TEMP       = PHY_RXELECIDLE;
	//assign rxsync_header_nogate_temp = rxsync_header_nogate;
	//assign PHY_RXSTART_BLOCK_TEMP    = PHY_RXSTART_BLOCK;
/////////////////////////////////////
	assign PHY_RXEQ_DONE_TEMP = PHY_RXEQ_DONE;
	assign PHY_RXEQ_ADAPT_DONE_TEMP = PHY_RXEQ_ADAPT_DONE;
	assign PHY_RXEQ_LFFS_SEL_TEMP = PHY_RXEQ_LFFS_SEL;
	assign PHY_RXEQ_NEW_TXCOEFF_TEMP = PHY_RXEQ_NEW_TXCOEFF;
	assign PHY_RXPOLARITY_TEMP = PHY_RXPOLARITY;
	assign PHY_RXEQ_CTRL_TEMP = PHY_RXEQ_CTRL;
	assign PHY_TXEQ_COEFF_TEMP = PHY_TXEQ_COEFF;
	assign PHY_TXEQ_PRESET_TEMP = PHY_TXEQ_PRESET;
	assign PHY_TXEQ_CTRL_TEMP = PHY_TXEQ_CTRL;
	assign PHY_TXSYNC_HEADER_TEMP = PHY_TXSYNC_HEADER;
	assign PHY_TXSTART_BLOCK_TEMP = PHY_TXSTART_BLOCK;
	assign PHY_TXDATA_VALID_TEMP = PHY_TXDATA_VALID;
	assign PHY_TXELECIDLE_TEMP = PHY_TXELECIDLE;
	assign PHY_TXDATAK_TEMP = PHY_TXDATAK;
	assign PHY_TXCOMPLIANCE_TEMP = PHY_TXCOMPLIANCE;
	assign PHY_TXDATA_TEMP = PHY_TXDATA;
	assign pipe_eq_lf_temp = pipe_eq_lf;
	assign pipe_eq_fs_temp = pipe_eq_fs;
pcie_bridge_ep_pcie4c_ip_phy_top #
  (
    //--------------------------------------------------------------------------
    //  Parameters
    //--------------------------------------------------------------------------
    .FPGA_FAMILY      ( FPGA_FAMILY ),
    .FPGA_XCVR        ( FPGA_XCVR ),
    .PIPELINE_STAGES  ( PIPE_PIPELINE_STAGES ),
  // synthesis translate_off
    .PHY_SIM_EN       ( ((PL_SIM_FAST_LINK_TRAINING != 2'b0) ? "TRUE" : "FALSE") ),
  // synthesis translate_on
    .PHY_LANE        ( PL_LINK_CAP_MAX_LINK_WIDTH ),
    .PHY_MAX_SPEED    ( (PL_LINK_CAP_MAX_LINK_SPEED[3] ? 4 : (PL_LINK_CAP_MAX_LINK_SPEED[2] ? 3 : (PL_LINK_CAP_MAX_LINK_SPEED[1] ? 2 : 1))) ),
    .PHY_ASYNC_EN     ( ((PF0_LINK_STATUS_SLOT_CLOCK_CONFIG == "TRUE") ? "FALSE" : "TRUE" ) ),
    .PHY_REFCLK_FREQ  ( PHY_REFCLK_FREQ ),
    .PHY_MCAPCLK_FREQ ( (((CRM_USER_CLK_FREQ == 2'b00) & (CRM_MCAP_CLK_FREQ == 1'b0)) ? 1 : 2) ),
    .PHY_USERCLK_FREQ ( (((CRM_USER_CLK_FREQ == 2'b10) | ((CRM_USER_CLK_FREQ == 2'b11) & (CRM_CORE_CLK_FREQ_500 == "TRUE"))) ? ((FPGA_XCVR == "HLF")? 2: 3) :
                                                                                                                               (CRM_USER_CLK_FREQ == 2'b01) ? 2 : 1) ),
    .PHY_CORECLK_FREQ ( ((CRM_CORE_CLK_FREQ_500 == "TRUE") ? ((FPGA_XCVR == "HLF")? 1: 2) : 1) ),
    .PHY_LP_TXPRESET  ( PHY_LP_TXPRESET )
  ) pcie_bridge_ep_pcie4c_ip_gt_top_i (


    //--------------------------------------------------------------------------
    //  Clock & Reset Ports
    //--------------------------------------------------------------------------
    .PHY_REFCLK          ( sys_clk_bufg ),
    .PHY_USERCLK         ( user_clk ),
    .PHY_MCAPCLK         ( mcap_clk_int ),
    .PHY_GTREFCLK        ( sys_clk_gt ),
    .PHY_RST_N           ( sys_rst_n ),

    .PHY_PCLK            ( pipe_clk ),
    .PHY_CORECLK         ( core_clk ),
    .GT_DRP_CLK_125M     ( gt_drp_clk ),

    //---------- Internal GT COMMON Ports ----------------------
    .int_qpll0lock_out      ( int_qpll0lock_out ),
    .int_qpll0outrefclk_out ( int_qpll0outrefclk_out ),
    .int_qpll0outclk_out    ( int_qpll0outclk_out ),
    .int_qpll1lock_out      ( int_qpll1lock_out ),
    .int_qpll1outrefclk_out ( int_qpll1outrefclk_out ),
    .int_qpll1outclk_out    ( int_qpll1outclk_out ),
    //---------- External GT COMMON Ports ----------------------
    .ext_qpllxrefclk        ( ext_qpllxrefclk ),
    .ext_qpllxrate          ( ext_qpllxrate ),
    .ext_qpllxrcalenb       ( ext_qpllxrcalenb ),

    .ext_qpll0pd            ( ext_qpll0pd ),
    .ext_qpll0reset         ( ext_qpll0reset ),
    .ext_qpll0lock_out      ( ext_qpll0lock_out ),
    .ext_qpll0outclk_out    ( ext_qpll0outclk_out ),
    .ext_qpll0outrefclk_out ( ext_qpll0outrefclk_out ),
    .ext_qpll1pd            ( ext_qpll1pd ),
    .ext_qpll1reset         ( ext_qpll1reset ),
    .ext_qpll1lock_out      ( ext_qpll1lock_out ),
    .ext_qpll1outclk_out    ( ext_qpll1outclk_out ),
    .ext_qpll1outrefclk_out ( ext_qpll1outrefclk_out ),
    //--------------------------------------------------------------------------
    .free_run_clock_in      (free_run_clock),
    .ibert_txprecursor_in   (txeq_precursor_o),
    .ibert_txpostcursor_in  (txeq_postcursor_o),
    .ibert_eyescanreset_in  ({PL_LINK_CAP_MAX_LINK_WIDTH{1'b0}}),
    .ibert_rxlpmen_in       (~gt_pcierategen3_o),
    .ibert_txdiffctrl_in    ({PL_LINK_CAP_MAX_LINK_WIDTH{5'b11000}}),

    .txeq_precursor_o        (txeq_precursor_o),
    .txeq_postcursor_o       (txeq_postcursor_o),
    .gt_pcierategen3_o       (gt_pcierategen3_o),
    //--------------------------------------------------------------------------
    // GT Channel DRP Port
    //--------------------------------------------------------------------------
    .gt_drpclk             ( ext_ch_gt_drpclk ),

    .gt_drpaddr            ( ext_ch_gt_drpaddr ),
    .gt_drpen              ( ext_ch_gt_drpen_int ),
    .gt_drpwe              ( ext_ch_gt_drpwe ),
    .gt_drpdi              ( ext_ch_gt_drpdi ),
    .gt_drprdy             ( ext_ch_gt_drprdy ),
    .gt_drpdo              ( ext_ch_gt_drpdo ),

    //--------------------------------------------------------------------------
    // GT Common DRP Port
    //--------------------------------------------------------------------------
    .gtcom_drpaddr         ( {((((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2)+1) * 16){1'b0}} ),
    .gtcom_drpen           ( {((((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2)+1) * 1 ){1'b0}} ),
    .gtcom_drpwe           ( {((((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2)+1) * 1 ){1'b0}} ),
    .gtcom_drpdi           ( {((((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2)+1) * 16){1'b0}} ),

    .gtcom_drprdy          (  ),
    .gtcom_drpdo           (  ),
    //--------------------------------------------------------------------------
    //  Serial Line Ports
    //--------------------------------------------------------------------------

    .PHY_RXP            ( pci_exp_rxp ),
    .PHY_RXN            ( pci_exp_rxn ),

    .PHY_TXP            ( pci_exp_txp ),
    .PHY_TXN            ( pci_exp_txn ),

    //--------------------------------------------------------------------------
    //  TX Data Ports
    //--------------------------------------------------------------------------

    .PHY_TXDATA         (PHY_TXDATA_TEMP),
    .PHY_TXDATAK        (PHY_TXDATAK_TEMP),
    .PHY_TXDATA_VALID   (PHY_TXDATA_VALID_TEMP),
    .PHY_TXSTART_BLOCK  (PHY_TXSTART_BLOCK_TEMP),
    .PHY_TXSYNC_HEADER  (PHY_TXSYNC_HEADER_TEMP),

    //--------------------------------------------------------------------------
    //  RX Data Ports
    //--------------------------------------------------------------------------

    .PHY_RXDATA         ( PHY_RXDATA ),
    .PHY_RXDATAK        ( PHY_RXDATAK ),
    .PHY_RXDATA_VALID   ( PHY_RXDATA_VALID ),
    .PHY_RXSTART_BLOCK  ( PHY_RXSTART_BLOCK ),
    .PHY_RXSYNC_HEADER  ( rxsync_header_nogate ),

    //--------------------------------------------------------------------------
    //  PHY Command Port
    //--------------------------------------------------------------------------

    .PHY_TXDETECTRX     ( pipe_tx_rcvr_det_temp ),
    .PHY_TXELECIDLE     (PHY_TXELECIDLE_TEMP),
    .PHY_TXCOMPLIANCE   (PHY_TXCOMPLIANCE_TEMP),
    .PHY_RXPOLARITY     (PHY_RXPOLARITY_TEMP),
    .PHY_POWERDOWN      ( pipe_tx00_powerdown_temp ),
    .PHY_RATE           ( pipe_tx_rate_i_temp ),

    //--------------------------------------------------------------------------
    //  PHY Status Ports
    //--------------------------------------------------------------------------

    .PHY_RXVALID        ( PHY_RXVALID  ),
    .PHY_PHYSTATUS      ( PHY_PHYSTATUS  ),
    .PHY_PHYSTATUS_RST  ( phy_rdy_phystatus ),
    .PHY_RXELECIDLE     ( PHY_RXELECIDLE ),
    .PHY_RXSTATUS       ( PHY_RXSTATUS  ),

    //--------------------------------------------------------------------------
    //  TX Driver Ports
    //--------------------------------------------------------------------------

    .PHY_TXMARGIN       ( pipe_tx_margin_temp ),
    .PHY_TXSWING        ( pipe_tx_swing_temp  ),
    .PHY_TXDEEMPH       ( pipe_tx_deemph_temp  ),

    //--------------------------------------------------------------------------
    //  TX Equalization Ports for Gen3
    //--------------------------------------------------------------------------

    .PHY_TXEQ_CTRL      (PHY_TXEQ_CTRL_TEMP),
    .PHY_TXEQ_PRESET    (PHY_TXEQ_PRESET_TEMP),
    .PHY_TXEQ_COEFF     (PHY_TXEQ_COEFF_TEMP),
    .PHY_TXEQ_FS        ( pipe_eq_fs ),
    .PHY_TXEQ_LF        ( pipe_eq_lf ),
    .PHY_TXEQ_NEW_COEFF ( PHY_TXEQ_NEW_COEFF ),
    .PHY_TXEQ_DONE      ( PHY_TXEQ_DONE ),

    //--------------------------------------------------------------------------
    //  RX Equalization Ports for Gen3
    //--------------------------------------------------------------------------

    .PHY_RXEQ_CTRL        (PHY_RXEQ_CTRL_TEMP),
    .PHY_RXEQ_TXPRESET    ( {PL_LINK_CAP_MAX_LINK_WIDTH{pipe_rx_eq_lp_tx_preset_temp}} ),
    .PHY_RXEQ_PRESET_SEL  ( PHY_RXEQ_LFFS_SEL  ),
    .PHY_RXEQ_NEW_TXCOEFF ( PHY_RXEQ_NEW_TXCOEFF ),
    .PHY_RXEQ_DONE        ( PHY_RXEQ_DONE  ),
    .PHY_RXEQ_ADAPT_DONE  ( PHY_RXEQ_ADAPT_DONE ),
    //------------------------------------------------------------------
    .GT_PCIEUSERRATEDONE  ( gt_pcieuserratedone_int ),
    .GT_LOOPBACK          ( gt_loopback_int         ),
    .GT_TXPRBSFORCEERR    ( gt_txprbsforceerr_int   ),
    .GT_TXINHIBIT         ( gt_txinhibit_int        ),
    .GT_TXPRBSSEL         ( gt_txprbssel_int        ),
    .GT_RXPRBSSEL         ( gt_rxprbssel_int        ),
    .GT_RXPRBSCNTRESET    ( gt_rxprbscntreset_int   ),
    .GT_RXCDRLOCK         ( gt_rxcdrlock        ),
    .GT_PCIERATEIDLE      ( gt_pcierateidle     ),
    .GT_PCIEUSERRATESTART ( gt_pcieuserratestart),
    .GT_GTPOWERGOOD       ( gt_gtpowergood      ),
    .GT_RXOUTCLK          ( gt_rxoutclk         ),
    .GT_RXRECCLKOUT       ( gt_rxrecclkout      ),
    .GT_TXRESETDONE       ( gt_txresetdone      ),
    .GT_RXPMARESETDONE    ( gt_rxpmaresetdone   ),
    .GT_RXRESETDONE       ( gt_rxresetdone      ),
    .GT_RXBUFSTATUS       ( gt_rxbufstatus      ),
    .GT_TXPHALIGNDONE     ( gt_txphaligndone    ),
    .GT_TXPHINITDONE      ( gt_txphinitdone     ),
    .GT_TXDLYSRESETDONE   ( gt_txdlysresetdone  ),
    .GT_RXPHALIGNDONE     ( gt_rxphaligndone    ),
    .GT_RXDLYSRESETDONE   ( gt_rxdlysresetdone  ),
    .GT_RXSYNCDONE        ( gt_rxsyncdone       ),
    .GT_CPLLLOCK          ( gt_cplllock         ),
    .GT_QPLL0LOCK         ( gt_qpll0lock        ),
    .GT_QPLL1LOCK         ( gt_qpll1lock        ),
    .GT_EYESCANDATAERROR  ( gt_eyescandataerror ),
    .GT_RXPRBSERR         ( gt_rxprbserr        ),
    .GT_DMONFIFORESET     ( gt_dmonfiforeset_int    ),
    .GT_DMONITORCLK       ( gt_dmonitorclk_int      ),
    .GT_DMONITOROUT       ( gt_dmonitorout      ),
    .GT_RXCOMMADET        ( gt_rxcommadet       ),
    .GT_RXSTATUS          ( gt_rxstatus         ),
    .GT_TXELECIDLE        ( gt_txelecidle       ),
    .GT_PHYSTATUS         ( gt_phystatus        ),
    .GT_RXVALID           ( gt_rxvalid          ),
    .GT_BUFGTDIV          ( gt_bufgtdiv         ),
    .PHY_RRST_N           ( phy_rrst_n          ),
    .PHY_PRST_N           ( phy_prst_n          ),
    .TXEQ_CTRL            ( phy_txeq_ctrl       ),
    .TXEQ_PRESET          ( phy_txeq_preset     ),
    .PHY_RST_FSM          ( phy_rst_fsm         ),
    .PHY_TXEQ_FSM         ( phy_txeq_fsm        ),
    .PHY_RXEQ_FSM         ( phy_rxeq_fsm        ),
    .PHY_RST_IDLE         ( phy_rst_idle        ),
    .GT_GEN34_EIOS_DET    ( gt_gen34_eios_det ),
    .GT_TXOUTCLK          ( gt_txoutclk ),
    .GT_TXOUTCLKFABRIC    ( gt_txoutclkfabric ),
    .GT_RXOUTCLKFABRIC    ( gt_rxoutclkfabric ),
    .GT_TXOUTCLKPCS       ( gt_txoutclkpcs ),
    .GT_RXOUTCLKPCS       ( gt_rxoutclkpcs ),
    .GT_TXPMARESET        ( gt_txpmareset_int ),
    .GT_RXPMARESET        ( gt_rxpmareset_int ),
    .GT_TXPCSRESET        ( gt_txpcsreset_int ),
    .GT_RXPCSRESET        ( gt_rxpcsreset_int ),
    .GT_RXBUFRESET        ( gt_rxbufreset_int ),
    .GT_RXCDRRESET        ( gt_rxcdrreset_int ),
    .GT_RXDFELPMRESET     ( gt_rxdfelpmreset_int ),
    .GT_TXPROGDIVRESETDONE( gt_txprogdivresetdone ),
    .GT_TXPMARESETDONE    ( gt_txpmaresetdone ),
    .GT_TXSYNCDONE        ( gt_txsyncdone ),
    .GT_RXPRBSLOCKED      ( gt_rxprbslocked ),
    .GT_RXLPMEN           (gt_rxlpmen),
    //--------------------------------------------------------------------------
    //  Assist Signals
    //--------------------------------------------------------------------------

    .AS_MAC_IN_DETECT     ( as_mac_in_detect_ff1 ),
    .AS_CDR_HOLD_REQ      ( as_cdr_hold_req_ff1 ),
    .cfg_ltssm_state      ( cfg_ltssm_state )
);

 assign  common_commands_out = 26'd0;
 assign  pipe_tx_0_sigs      = 84'd0;
 assign  pipe_tx_1_sigs      = 84'd0;
 assign  pipe_tx_2_sigs      = 84'd0;
 assign  pipe_tx_3_sigs      = 84'd0;
 assign  pipe_tx_4_sigs      = 84'd0;
 assign  pipe_tx_5_sigs      = 84'd0;
 assign  pipe_tx_6_sigs      = 84'd0;
 assign  pipe_tx_7_sigs      = 84'd0;
 assign  pipe_tx_8_sigs      = 84'd0;
 assign  pipe_tx_9_sigs      = 84'd0;
 assign  pipe_tx_10_sigs     = 84'd0;
 assign  pipe_tx_11_sigs     = 84'd0;
 assign  pipe_tx_12_sigs     = 84'd0;
 assign  pipe_tx_13_sigs     = 84'd0;
 assign  pipe_tx_14_sigs     = 84'd0;
 assign  pipe_tx_15_sigs     = 84'd0;
 assign  phy_rdy             = ~phy_rdy_phystatus;
end
endgenerate

assign { pipe_rx15_data[63:0], pipe_rx14_data[63:0],
	       pipe_rx13_data[63:0], pipe_rx12_data[63:0],
	       pipe_rx11_data[63:0], pipe_rx10_data[63:0],
	       pipe_rx09_data[63:0], pipe_rx08_data[63:0],
	       pipe_rx07_data[63:0], pipe_rx06_data[63:0],
	       pipe_rx05_data[63:0], pipe_rx04_data[63:0],
         pipe_rx03_data[63:0], pipe_rx02_data[63:0],
	       pipe_rx01_data[63:0], pipe_rx00_data[63:0]} = (PL_LINK_CAP_MAX_LINK_WIDTH == 16 ? PHY_RXDATA_TEMP : {{((16-PL_LINK_CAP_MAX_LINK_WIDTH) * 64){1'b0}},PHY_RXDATA_TEMP});

assign { pipe_rx15_char_is_k[1:0], pipe_rx14_char_is_k[1:0],
	       pipe_rx13_char_is_k[1:0], pipe_rx12_char_is_k[1:0],
         pipe_rx11_char_is_k[1:0], pipe_rx10_char_is_k[1:0],
	       pipe_rx09_char_is_k[1:0], pipe_rx08_char_is_k[1:0],
         pipe_rx07_char_is_k[1:0], pipe_rx06_char_is_k[1:0],
	       pipe_rx05_char_is_k[1:0], pipe_rx04_char_is_k[1:0],
         pipe_rx03_char_is_k[1:0], pipe_rx02_char_is_k[1:0],
	       pipe_rx01_char_is_k[1:0], pipe_rx00_char_is_k[1:0]} = (PL_LINK_CAP_MAX_LINK_WIDTH == 16 ? PHY_RXDATAK_TEMP : {{((16-PL_LINK_CAP_MAX_LINK_WIDTH) * 2){1'b0}},PHY_RXDATAK_TEMP});

assign { pipe_rx15_data_valid, pipe_rx14_data_valid,
	       pipe_rx13_data_valid, pipe_rx12_data_valid,
         pipe_rx11_data_valid, pipe_rx10_data_valid,
	       pipe_rx09_data_valid, pipe_rx08_data_valid,
         pipe_rx07_data_valid, pipe_rx06_data_valid,
	       pipe_rx05_data_valid, pipe_rx04_data_valid,
         pipe_rx03_data_valid, pipe_rx02_data_valid,
	       pipe_rx01_data_valid, pipe_rx00_data_valid} = (PL_LINK_CAP_MAX_LINK_WIDTH == 16 ? PHY_RXDATA_VALID_TEMP : {{((16-PL_LINK_CAP_MAX_LINK_WIDTH) * 1){1'b0}},PHY_RXDATA_VALID_TEMP});

assign { pipe_rx15_start_block[1:0], pipe_rx14_start_block[1:0],
	       pipe_rx13_start_block[1:0], pipe_rx12_start_block[1:0],
         pipe_rx11_start_block[1:0], pipe_rx10_start_block[1:0],
	       pipe_rx09_start_block[1:0], pipe_rx08_start_block[1:0],
         pipe_rx07_start_block[1:0], pipe_rx06_start_block[1:0],
	       pipe_rx05_start_block[1:0], pipe_rx04_start_block[1:0],
         pipe_rx03_start_block[1:0], pipe_rx02_start_block[1:0],
	       pipe_rx01_start_block[1:0], pipe_rx00_start_block[1:0]} = (PL_LINK_CAP_MAX_LINK_WIDTH == 16 ? PHY_RXSTART_BLOCK_TEMP : {{((16-PL_LINK_CAP_MAX_LINK_WIDTH) * 2){1'b0}},PHY_RXSTART_BLOCK_TEMP});

assign { pipe_rx15_sync_header[1:0], pipe_rx14_sync_header[1:0],
	       pipe_rx13_sync_header[1:0], pipe_rx12_sync_header[1:0],
         pipe_rx11_sync_header[1:0], pipe_rx10_sync_header[1:0],
	       pipe_rx09_sync_header[1:0], pipe_rx08_sync_header[1:0],
         pipe_rx07_sync_header[1:0], pipe_rx06_sync_header[1:0],
	       pipe_rx05_sync_header[1:0], pipe_rx04_sync_header[1:0],
         pipe_rx03_sync_header[1:0], pipe_rx02_sync_header[1:0],
	       pipe_rx01_sync_header[1:0], pipe_rx00_sync_header[1:0]} = (PL_LINK_CAP_MAX_LINK_WIDTH == 16 ? PHY_RXSYNC_HEADER : {{((16-PL_LINK_CAP_MAX_LINK_WIDTH) * 2){1'b0}},PHY_RXSYNC_HEADER});

assign { pipe_rx15_valid, pipe_rx14_valid,
	       pipe_rx13_valid, pipe_rx12_valid,
         pipe_rx11_valid, pipe_rx10_valid,
	       pipe_rx09_valid, pipe_rx08_valid,
         pipe_rx07_valid, pipe_rx06_valid,
	       pipe_rx05_valid, pipe_rx04_valid,
         pipe_rx03_valid, pipe_rx02_valid,
	       pipe_rx01_valid, pipe_rx00_valid} = (PL_LINK_CAP_MAX_LINK_WIDTH == 16 ? PHY_RXVALID_TEMP : {{((16-PL_LINK_CAP_MAX_LINK_WIDTH) * 1){1'b0}},PHY_RXVALID_TEMP});


// Soft fix to pass phystatus[0] (the last-done lane) to all other lanes in TO_2_DETECT state to make sure all other lanes are done.

always @(posedge pipe_clk or posedge sys_or_hot_rst_pclk) begin
   if (sys_or_hot_rst_pclk) begin
      pipe_tx_rate_ff   <= 2'b00;
   end else begin
      pipe_tx_rate_ff   <= pipe_tx_rate_i;
   end
end

always @(posedge pipe_clk or posedge sys_or_hot_rst_pclk) begin
   if (sys_or_hot_rst_pclk) begin
      speed_change_in_progress <= 1'b0;
   end else if (pipe_tx_rate_i != pipe_tx_rate_ff) begin
      speed_change_in_progress <= 1'b1;
   end else if (pipe_rx00_phy_status) begin
      speed_change_in_progress <= 1'b0;
   end
end

assign phy_status_fix   = (speed_change_in_progress)? {PL_LINK_CAP_MAX_LINK_WIDTH{PHY_PHYSTATUS_TEMP[0]}}: PHY_PHYSTATUS_TEMP;
assign { pipe_rx15_phy_status, pipe_rx14_phy_status,
	       pipe_rx13_phy_status, pipe_rx12_phy_status,
         pipe_rx11_phy_status, pipe_rx10_phy_status,
	       pipe_rx09_phy_status, pipe_rx08_phy_status,
         pipe_rx07_phy_status, pipe_rx06_phy_status,
	       pipe_rx05_phy_status, pipe_rx04_phy_status,
         pipe_rx03_phy_status, pipe_rx02_phy_status,
	       pipe_rx01_phy_status, pipe_rx00_phy_status} = (PL_LINK_CAP_MAX_LINK_WIDTH == 16 ? phy_status_fix : {{((16-PL_LINK_CAP_MAX_LINK_WIDTH) * 1){1'b0}},phy_status_fix});

assign { pipe_rx15_elec_idle, pipe_rx14_elec_idle, pipe_rx13_elec_idle, pipe_rx12_elec_idle,
         pipe_rx11_elec_idle, pipe_rx10_elec_idle, pipe_rx09_elec_idle, pipe_rx08_elec_idle,
         pipe_rx07_elec_idle, pipe_rx06_elec_idle, pipe_rx05_elec_idle, pipe_rx04_elec_idle,
         pipe_rx03_elec_idle, pipe_rx02_elec_idle, pipe_rx01_elec_idle, pipe_rx00_elec_idle} = (PL_LINK_CAP_MAX_LINK_WIDTH == 16 ? PHY_RXELECIDLE_TEMP : {{((16-PL_LINK_CAP_MAX_LINK_WIDTH) * 1){1'b0}},PHY_RXELECIDLE_TEMP});

assign { pipe_rx15_status, pipe_rx14_status, pipe_rx13_status, pipe_rx12_status,
         pipe_rx11_status, pipe_rx10_status, pipe_rx09_status, pipe_rx08_status,
         pipe_rx07_status, pipe_rx06_status, pipe_rx05_status, pipe_rx04_status,
         pipe_rx03_status, pipe_rx02_status, pipe_rx01_status, pipe_rx00_status} = (PL_LINK_CAP_MAX_LINK_WIDTH == 16 ? PHY_RXSTATUS_TEMP : {{((16-PL_LINK_CAP_MAX_LINK_WIDTH) * 3){1'b0}},PHY_RXSTATUS_TEMP});

assign { pipe_tx15_eq_coeff, pipe_tx14_eq_coeff,
	       pipe_tx13_eq_coeff, pipe_tx12_eq_coeff,
         pipe_tx11_eq_coeff, pipe_tx10_eq_coeff,
	       pipe_tx09_eq_coeff, pipe_tx08_eq_coeff,
         pipe_tx07_eq_coeff, pipe_tx06_eq_coeff,
	       pipe_tx05_eq_coeff, pipe_tx04_eq_coeff,
         pipe_tx03_eq_coeff, pipe_tx02_eq_coeff,
	       pipe_tx01_eq_coeff, pipe_tx00_eq_coeff} = (PL_LINK_CAP_MAX_LINK_WIDTH == 16 ? PHY_TXEQ_NEW_COEFF_TEMP : {{((16-PL_LINK_CAP_MAX_LINK_WIDTH) * 18){1'b0}},PHY_TXEQ_NEW_COEFF_TEMP});

assign { pipe_tx15_eq_done, pipe_tx14_eq_done,
	       pipe_tx13_eq_done, pipe_tx12_eq_done,
         pipe_tx11_eq_done, pipe_tx10_eq_done,
	       pipe_tx09_eq_done, pipe_tx08_eq_done,
         pipe_tx07_eq_done, pipe_tx06_eq_done,
	       pipe_tx05_eq_done, pipe_tx04_eq_done,
         pipe_tx03_eq_done, pipe_tx02_eq_done,
	       pipe_tx01_eq_done, pipe_tx00_eq_done} = (PL_LINK_CAP_MAX_LINK_WIDTH == 16 ? PHY_TXEQ_DONE_TEMP : {{((16-PL_LINK_CAP_MAX_LINK_WIDTH) * 1){1'b0}},PHY_TXEQ_DONE_TEMP});

assign { pipe_rx15_eq_lp_lf_fs_sel, pipe_rx14_eq_lp_lf_fs_sel,
	       pipe_rx13_eq_lp_lf_fs_sel, pipe_rx12_eq_lp_lf_fs_sel,
         pipe_rx11_eq_lp_lf_fs_sel, pipe_rx10_eq_lp_lf_fs_sel,
	       pipe_rx09_eq_lp_lf_fs_sel, pipe_rx08_eq_lp_lf_fs_sel,
         pipe_rx07_eq_lp_lf_fs_sel, pipe_rx06_eq_lp_lf_fs_sel,
	       pipe_rx05_eq_lp_lf_fs_sel, pipe_rx04_eq_lp_lf_fs_sel,
         pipe_rx03_eq_lp_lf_fs_sel, pipe_rx02_eq_lp_lf_fs_sel,
	       pipe_rx01_eq_lp_lf_fs_sel, pipe_rx00_eq_lp_lf_fs_sel} = (PL_LINK_CAP_MAX_LINK_WIDTH == 16 ? PHY_RXEQ_LFFS_SEL_TEMP : {{((16-PL_LINK_CAP_MAX_LINK_WIDTH) * 1){1'b0}},PHY_RXEQ_LFFS_SEL_TEMP});

assign { pipe_rx15_eq_lp_new_tx_coeff_or_preset, pipe_rx14_eq_lp_new_tx_coeff_or_preset,
	       pipe_rx13_eq_lp_new_tx_coeff_or_preset, pipe_rx12_eq_lp_new_tx_coeff_or_preset,
         pipe_rx11_eq_lp_new_tx_coeff_or_preset, pipe_rx10_eq_lp_new_tx_coeff_or_preset,
	       pipe_rx09_eq_lp_new_tx_coeff_or_preset, pipe_rx08_eq_lp_new_tx_coeff_or_preset,
         pipe_rx07_eq_lp_new_tx_coeff_or_preset, pipe_rx06_eq_lp_new_tx_coeff_or_preset,
	       pipe_rx05_eq_lp_new_tx_coeff_or_preset, pipe_rx04_eq_lp_new_tx_coeff_or_preset,
         pipe_rx03_eq_lp_new_tx_coeff_or_preset, pipe_rx02_eq_lp_new_tx_coeff_or_preset,
	       pipe_rx01_eq_lp_new_tx_coeff_or_preset, pipe_rx00_eq_lp_new_tx_coeff_or_preset} = (PL_LINK_CAP_MAX_LINK_WIDTH == 16 ? PHY_RXEQ_NEW_TXCOEFF_TEMP : {{((16-PL_LINK_CAP_MAX_LINK_WIDTH) * 18){1'b0}},PHY_RXEQ_NEW_TXCOEFF_TEMP});

assign { pipe_rx15_eq_done, pipe_rx14_eq_done, pipe_rx13_eq_done, pipe_rx12_eq_done,
         pipe_rx11_eq_done, pipe_rx10_eq_done, pipe_rx09_eq_done, pipe_rx08_eq_done,
         pipe_rx07_eq_done, pipe_rx06_eq_done, pipe_rx05_eq_done, pipe_rx04_eq_done,
         pipe_rx03_eq_done, pipe_rx02_eq_done, pipe_rx01_eq_done, pipe_rx00_eq_done} = (PL_LINK_CAP_MAX_LINK_WIDTH == 16 ? PHY_RXEQ_DONE_TEMP : {{((16-PL_LINK_CAP_MAX_LINK_WIDTH) * 1){1'b0}},PHY_RXEQ_DONE_TEMP});

assign { pipe_rx15_eq_lp_adapt_done, pipe_rx14_eq_lp_adapt_done,
	       pipe_rx13_eq_lp_adapt_done, pipe_rx12_eq_lp_adapt_done,
         pipe_rx11_eq_lp_adapt_done, pipe_rx10_eq_lp_adapt_done,
	       pipe_rx09_eq_lp_adapt_done, pipe_rx08_eq_lp_adapt_done,
         pipe_rx07_eq_lp_adapt_done, pipe_rx06_eq_lp_adapt_done,
	       pipe_rx05_eq_lp_adapt_done, pipe_rx04_eq_lp_adapt_done,
         pipe_rx03_eq_lp_adapt_done, pipe_rx02_eq_lp_adapt_done,
	       pipe_rx01_eq_lp_adapt_done, pipe_rx00_eq_lp_adapt_done} = (PL_LINK_CAP_MAX_LINK_WIDTH == 16 ? PHY_RXEQ_ADAPT_DONE_TEMP : {{((16-PL_LINK_CAP_MAX_LINK_WIDTH) * 1){1'b0}},PHY_RXEQ_ADAPT_DONE_TEMP});

assign   sys_reset_in_n = sys_reset; // Convert to always active low reset
// Syncronize sys_reset input to sys_clk
xpm_cdc_async_rst #(
   .DEST_SYNC_FF(2),
   .INIT_SYNC_FF(0),
   .RST_ACTIVE_HIGH(0)
)
sys_reset_in_async_rst_inst (
   .dest_arst(sys_reset_in_n_sync),
   .dest_clk(sys_clk_bufg),
   .src_arst(sys_reset_in_n)
);

assign   sys_rst_n = sys_reset_in_n_sync; //pcie_perst0_b; // Use the reset from pcie_4_0_pipe

assign   mcap_rst_b = 1'b0; //~sys_reset_in_n_sync;
assign   user_lnk_up_int = (cfg_phy_link_status == 2'b11 && sys_rst_n) ? 1'b1 : 1'b0;
assign   sys_or_hot_rst_int = ~sys_rst_n || cfg_hot_reset_out;

xpm_cdc_async_rst #(
   .DEST_SYNC_FF(2),
   .INIT_SYNC_FF(0),
   .RST_ACTIVE_HIGH(1)
)
sys_or_hot_rst_pclk_inst (
   .dest_arst(sys_or_hot_rst_pclk),
   .dest_clk(pipe_clk),
   .src_arst(sys_or_hot_rst_int)
);

xpm_cdc_async_rst #(
   .DEST_SYNC_FF(2),
   .INIT_SYNC_FF(0),
   .RST_ACTIVE_HIGH(1)
)
sys_or_hot_rst_uclk_inst (
   .dest_arst(sys_or_hot_rst_uclk),
   .dest_clk(user_clk),
   .src_arst(sys_or_hot_rst_int)
);
// CDC for the user_lnk_up output
// this will deassert asynchronously with sys_rst_n and assert synchronously
xpm_cdc_async_rst #(
  .DEST_SYNC_FF          (2),
  .RST_ACTIVE_HIGH       (0)
) user_lnk_up_cdc (
  .src_arst              (user_lnk_up_int),
  .dest_arst             (user_lnk_up_cdc_o),
  .dest_clk              (user_clk)
);
  // Additional reset register that can be replicated by the tools to facilitate timing closure
  always @(posedge user_clk or negedge user_lnk_up_int) begin
    if(!user_lnk_up_int) begin
      user_lnk_up <= #TCQ 1'b0;
    end else begin
      user_lnk_up <= #TCQ user_lnk_up_cdc_o;
    end
  end

// CDC for the user_reset output
// this will assert asynchronously with sys_rst_n and deassert synchronously
  assign user_reset_int = sys_or_hot_rst_uclk || cfg_phy_link_down || !cfg_phy_link_status[1] || ds_pulse;
  xpm_cdc_async_rst #(
    .DEST_SYNC_FF          (2),
    .RST_ACTIVE_HIGH       (1)
  ) user_reset_cdc (
    .src_arst              (user_reset_int),
    .dest_arst             (user_reset_cdc_o),
    .dest_clk              (user_clk)
  );
  // Additional reset register that can be replicated by the tools to facilitate timing closure
  always @(posedge user_clk or posedge user_reset_int) begin
    if(user_reset_int) begin
     user_reset <= #TCQ 1'b1;
    end else begin
      user_reset <= #TCQ user_reset_cdc_o;
    end
  end

assign PHY_TXDATA = ( PL_LINK_CAP_MAX_LINK_WIDTH==16 ?
                         { 32'h0, pipe_tx15_data[31:0], 32'h0, pipe_tx14_data[31:0],
			                     32'h0, pipe_tx13_data[31:0], 32'h0, pipe_tx12_data[31:0],
			                     32'h0, pipe_tx11_data[31:0], 32'h0, pipe_tx10_data[31:0],
			                     32'h0, pipe_tx09_data[31:0], 32'h0, pipe_tx08_data[31:0],
			                     pipe_tx15_data[31:0], pipe_tx07_data[31:0], pipe_tx14_data[31:0], pipe_tx06_data[31:0],
                           pipe_tx13_data[31:0], pipe_tx05_data[31:0], pipe_tx12_data[31:0], pipe_tx04_data[31:0],
                           pipe_tx11_data[31:0], pipe_tx03_data[31:0], pipe_tx10_data[31:0], pipe_tx02_data[31:0],
                           pipe_tx09_data[31:0], pipe_tx01_data[31:0], pipe_tx08_data[31:0], pipe_tx00_data[31:0]} :
                      PL_LINK_CAP_MAX_LINK_WIDTH==8 ?
			                   { pipe_tx15_data[31:0], pipe_tx07_data[31:0], pipe_tx14_data[31:0], pipe_tx06_data[31:0],
			                     pipe_tx13_data[31:0], pipe_tx05_data[31:0], pipe_tx12_data[31:0], pipe_tx04_data[31:0],
                           pipe_tx11_data[31:0], pipe_tx03_data[31:0], pipe_tx10_data[31:0], pipe_tx02_data[31:0],
			                     pipe_tx09_data[31:0], pipe_tx01_data[31:0], pipe_tx08_data[31:0], pipe_tx00_data[31:0]} :
                      PL_LINK_CAP_MAX_LINK_WIDTH==4 ?
			                   { pipe_tx11_data[31:0], pipe_tx03_data[31:0], pipe_tx10_data[31:0], pipe_tx02_data[31:0],
			                     pipe_tx09_data[31:0], pipe_tx01_data[31:0], pipe_tx08_data[31:0], pipe_tx00_data[31:0]} :
                      PL_LINK_CAP_MAX_LINK_WIDTH==2 ?
			                   { pipe_tx09_data[31:0], pipe_tx01_data[31:0], pipe_tx08_data[31:0], pipe_tx00_data[31:0]} :
			                   {pipe_tx08_data[31:0], pipe_tx00_data[31:0]} );

 assign PHY_TXDATAK = ( PL_LINK_CAP_MAX_LINK_WIDTH==16 ?
                         { pipe_tx15_char_is_k[1:0], pipe_tx14_char_is_k[1:0], pipe_tx13_char_is_k[1:0], pipe_tx12_char_is_k[1:0],
                           pipe_tx11_char_is_k[1:0], pipe_tx10_char_is_k[1:0], pipe_tx09_char_is_k[1:0], pipe_tx08_char_is_k[1:0],
                           pipe_tx07_char_is_k[1:0], pipe_tx06_char_is_k[1:0], pipe_tx05_char_is_k[1:0], pipe_tx04_char_is_k[1:0],
                           pipe_tx03_char_is_k[1:0], pipe_tx02_char_is_k[1:0], pipe_tx01_char_is_k[1:0], pipe_tx00_char_is_k[1:0]} :
                        PL_LINK_CAP_MAX_LINK_WIDTH==8 ?
                         { pipe_tx07_char_is_k[1:0], pipe_tx06_char_is_k[1:0], pipe_tx05_char_is_k[1:0], pipe_tx04_char_is_k[1:0],
                           pipe_tx03_char_is_k[1:0], pipe_tx02_char_is_k[1:0], pipe_tx01_char_is_k[1:0], pipe_tx00_char_is_k[1:0]} :
                        PL_LINK_CAP_MAX_LINK_WIDTH==4 ?
                         { pipe_tx03_char_is_k[1:0], pipe_tx02_char_is_k[1:0], pipe_tx01_char_is_k[1:0], pipe_tx00_char_is_k[1:0]} :
                        PL_LINK_CAP_MAX_LINK_WIDTH==2 ?
                         { pipe_tx01_char_is_k[1:0], pipe_tx00_char_is_k[1:0]} : pipe_tx00_char_is_k[1:0] );

assign PHY_TXDATA_VALID = ( PL_LINK_CAP_MAX_LINK_WIDTH==16 ?
                         { pipe_tx15_data_valid, pipe_tx14_data_valid, pipe_tx13_data_valid, pipe_tx12_data_valid,
                           pipe_tx11_data_valid, pipe_tx10_data_valid, pipe_tx09_data_valid, pipe_tx08_data_valid,
                           pipe_tx07_data_valid, pipe_tx06_data_valid, pipe_tx05_data_valid, pipe_tx04_data_valid,
                           pipe_tx03_data_valid, pipe_tx02_data_valid, pipe_tx01_data_valid, pipe_tx00_data_valid} :
                          PL_LINK_CAP_MAX_LINK_WIDTH==8 ?
                         { pipe_tx07_data_valid, pipe_tx06_data_valid, pipe_tx05_data_valid, pipe_tx04_data_valid,
                           pipe_tx03_data_valid, pipe_tx02_data_valid, pipe_tx01_data_valid, pipe_tx00_data_valid} :
                          PL_LINK_CAP_MAX_LINK_WIDTH==4 ?
                         { pipe_tx03_data_valid, pipe_tx02_data_valid, pipe_tx01_data_valid, pipe_tx00_data_valid} :
                          PL_LINK_CAP_MAX_LINK_WIDTH==2 ?
                         { pipe_tx01_data_valid, pipe_tx00_data_valid} : pipe_tx00_data_valid );

assign PHY_TXSTART_BLOCK = ( PL_LINK_CAP_MAX_LINK_WIDTH==16 ?
                         { pipe_tx15_start_block, pipe_tx15_start_block, pipe_tx15_start_block, pipe_tx15_start_block,
                           pipe_tx11_start_block, pipe_tx10_start_block, pipe_tx09_start_block, pipe_tx08_start_block,
                           pipe_tx07_start_block, pipe_tx06_start_block, pipe_tx05_start_block, pipe_tx04_start_block,
                           pipe_tx03_start_block, pipe_tx02_start_block, pipe_tx01_start_block, pipe_tx00_start_block} :
                          PL_LINK_CAP_MAX_LINK_WIDTH==8 ?
                         { pipe_tx07_start_block, pipe_tx06_start_block, pipe_tx05_start_block, pipe_tx04_start_block,
                           pipe_tx03_start_block, pipe_tx02_start_block, pipe_tx01_start_block, pipe_tx00_start_block} :
                          PL_LINK_CAP_MAX_LINK_WIDTH==4 ?
                         { pipe_tx03_start_block, pipe_tx02_start_block, pipe_tx01_start_block, pipe_tx00_start_block} :
                          PL_LINK_CAP_MAX_LINK_WIDTH==2 ?
                         { pipe_tx01_start_block, pipe_tx00_start_block} : pipe_tx00_start_block );

assign PHY_TXSYNC_HEADER = ( PL_LINK_CAP_MAX_LINK_WIDTH==16 ?
                         { pipe_tx15_sync_header[1:0], pipe_tx14_sync_header[1:0], pipe_tx13_sync_header[1:0], pipe_tx12_sync_header[1:0],
                           pipe_tx11_sync_header[1:0], pipe_tx10_sync_header[1:0], pipe_tx09_sync_header[1:0], pipe_tx08_sync_header[1:0],
                           pipe_tx07_sync_header[1:0], pipe_tx06_sync_header[1:0], pipe_tx05_sync_header[1:0], pipe_tx04_sync_header[1:0],
                           pipe_tx03_sync_header[1:0], pipe_tx02_sync_header[1:0], pipe_tx01_sync_header[1:0], pipe_tx00_sync_header[1:0]} :
                          PL_LINK_CAP_MAX_LINK_WIDTH==8 ?
                         { pipe_tx07_sync_header[1:0], pipe_tx06_sync_header[1:0], pipe_tx05_sync_header[1:0], pipe_tx04_sync_header[1:0],
                           pipe_tx03_sync_header[1:0], pipe_tx02_sync_header[1:0], pipe_tx01_sync_header[1:0], pipe_tx00_sync_header[1:0]} :
                          PL_LINK_CAP_MAX_LINK_WIDTH==4 ?
                         { pipe_tx03_sync_header[1:0], pipe_tx02_sync_header[1:0], pipe_tx01_sync_header[1:0], pipe_tx00_sync_header[1:0]} :
                          PL_LINK_CAP_MAX_LINK_WIDTH==2 ?
                         { pipe_tx01_sync_header[1:0], pipe_tx00_sync_header[1:0]} : pipe_tx00_sync_header[1:0] );

assign PHY_TXELECIDLE = ( PL_LINK_CAP_MAX_LINK_WIDTH==16 ?
                        { pipe_tx15_elec_idle, pipe_tx14_elec_idle, pipe_tx13_elec_idle, pipe_tx12_elec_idle,
                          pipe_tx11_elec_idle, pipe_tx10_elec_idle, pipe_tx09_elec_idle, pipe_tx08_elec_idle,
                          pipe_tx07_elec_idle, pipe_tx06_elec_idle, pipe_tx05_elec_idle, pipe_tx04_elec_idle,
                          pipe_tx03_elec_idle, pipe_tx02_elec_idle, pipe_tx01_elec_idle, pipe_tx00_elec_idle} :
                          PL_LINK_CAP_MAX_LINK_WIDTH==8 ?
                        { pipe_tx07_elec_idle, pipe_tx06_elec_idle, pipe_tx05_elec_idle, pipe_tx04_elec_idle,
                          pipe_tx03_elec_idle, pipe_tx02_elec_idle, pipe_tx01_elec_idle, pipe_tx00_elec_idle} :
                          PL_LINK_CAP_MAX_LINK_WIDTH==4 ?
                        { pipe_tx03_elec_idle, pipe_tx02_elec_idle, pipe_tx01_elec_idle, pipe_tx00_elec_idle} :
                          PL_LINK_CAP_MAX_LINK_WIDTH==2 ?
                        { pipe_tx01_elec_idle, pipe_tx00_elec_idle} : pipe_tx00_elec_idle );


assign PHY_TXCOMPLIANCE = ( PL_LINK_CAP_MAX_LINK_WIDTH==16 ?
                        { pipe_tx15_compliance, pipe_tx14_compliance, pipe_tx13_compliance, pipe_tx12_compliance,
                          pipe_tx11_compliance, pipe_tx10_compliance, pipe_tx09_compliance, pipe_tx08_compliance,
                          pipe_tx07_compliance, pipe_tx06_compliance, pipe_tx05_compliance, pipe_tx04_compliance,
                          pipe_tx03_compliance, pipe_tx02_compliance, pipe_tx01_compliance, pipe_tx00_compliance} :
                          PL_LINK_CAP_MAX_LINK_WIDTH==8 ?
                        { pipe_tx07_compliance, pipe_tx06_compliance, pipe_tx05_compliance, pipe_tx04_compliance,
                          pipe_tx03_compliance, pipe_tx02_compliance, pipe_tx01_compliance, pipe_tx00_compliance} :
                          PL_LINK_CAP_MAX_LINK_WIDTH==4 ?
                        { pipe_tx03_compliance, pipe_tx02_compliance, pipe_tx01_compliance, pipe_tx00_compliance} :
                          PL_LINK_CAP_MAX_LINK_WIDTH==2 ?
                        { pipe_tx01_compliance, pipe_tx00_compliance} : pipe_tx00_compliance );

assign PHY_RXPOLARITY =  (
                          PL_LINK_CAP_MAX_LINK_WIDTH==16 ?
                        { pipe_rx15_polarity, pipe_rx14_polarity, pipe_rx13_polarity, pipe_rx12_polarity,
                          pipe_rx11_polarity, pipe_rx10_polarity, pipe_rx09_polarity, pipe_rx08_polarity,
                          pipe_rx07_polarity, pipe_rx06_polarity, pipe_rx05_polarity, pipe_rx04_polarity,
                          pipe_rx03_polarity, pipe_rx02_polarity, pipe_rx01_polarity, pipe_rx00_polarity} :
                          PL_LINK_CAP_MAX_LINK_WIDTH==8 ?
                        { pipe_rx07_polarity, pipe_rx06_polarity, pipe_rx05_polarity, pipe_rx04_polarity,
                          pipe_rx03_polarity, pipe_rx02_polarity, pipe_rx01_polarity, pipe_rx00_polarity} :
                          PL_LINK_CAP_MAX_LINK_WIDTH==4 ?
                        { pipe_rx03_polarity, pipe_rx02_polarity, pipe_rx01_polarity, pipe_rx00_polarity} :
                          PL_LINK_CAP_MAX_LINK_WIDTH==2 ?
                        { pipe_rx01_polarity, pipe_rx00_polarity} : pipe_rx00_polarity );

assign PHY_TXEQ_CTRL = ( PL_LINK_CAP_MAX_LINK_WIDTH==16 ?
                          { pipe_tx15_eq_control, pipe_tx14_eq_control, pipe_tx13_eq_control, pipe_tx12_eq_control,
			                      pipe_tx11_eq_control, pipe_tx10_eq_control, pipe_tx09_eq_control, pipe_tx08_eq_control,
			                      pipe_tx07_eq_control, pipe_tx06_eq_control, pipe_tx05_eq_control, pipe_tx04_eq_control,
                            pipe_tx03_eq_control, pipe_tx02_eq_control, pipe_tx01_eq_control, pipe_tx00_eq_control} :
                          PL_LINK_CAP_MAX_LINK_WIDTH==8 ?
                          { pipe_tx07_eq_control, pipe_tx06_eq_control, pipe_tx05_eq_control, pipe_tx04_eq_control,
                            pipe_tx03_eq_control, pipe_tx02_eq_control, pipe_tx01_eq_control, pipe_tx00_eq_control} :
                          PL_LINK_CAP_MAX_LINK_WIDTH==4 ?
                          { pipe_tx03_eq_control, pipe_tx02_eq_control, pipe_tx01_eq_control, pipe_tx00_eq_control} :
                          PL_LINK_CAP_MAX_LINK_WIDTH==2 ?
                          { pipe_tx01_eq_control, pipe_tx00_eq_control} : pipe_tx00_eq_control );

assign PHY_TXEQ_PRESET = (  PL_LINK_CAP_MAX_LINK_WIDTH==16 ?
                          { pipe_tx15_eq_deemph[3:0], pipe_tx14_eq_deemph[3:0], pipe_tx13_eq_deemph[3:0], pipe_tx12_eq_deemph[3:0],
                            pipe_tx11_eq_deemph[3:0], pipe_tx10_eq_deemph[3:0], pipe_tx09_eq_deemph[3:0], pipe_tx08_eq_deemph[3:0],
                            pipe_tx07_eq_deemph[3:0], pipe_tx06_eq_deemph[3:0], pipe_tx05_eq_deemph[3:0], pipe_tx04_eq_deemph[3:0],
                            pipe_tx03_eq_deemph[3:0], pipe_tx02_eq_deemph[3:0], pipe_tx01_eq_deemph[3:0], pipe_tx00_eq_deemph[3:0]} :
                          PL_LINK_CAP_MAX_LINK_WIDTH==8 ?
                          { pipe_tx07_eq_deemph[3:0], pipe_tx06_eq_deemph[3:0], pipe_tx05_eq_deemph[3:0], pipe_tx04_eq_deemph[3:0],
                            pipe_tx03_eq_deemph[3:0], pipe_tx02_eq_deemph[3:0], pipe_tx01_eq_deemph[3:0], pipe_tx00_eq_deemph[3:0]} :
                          PL_LINK_CAP_MAX_LINK_WIDTH==4 ?
                          { pipe_tx03_eq_deemph[3:0], pipe_tx02_eq_deemph[3:0], pipe_tx01_eq_deemph[3:0], pipe_tx00_eq_deemph[3:0]} :
                          PL_LINK_CAP_MAX_LINK_WIDTH==2 ?
                          { pipe_tx01_eq_deemph[3:0], pipe_tx00_eq_deemph[3:0]} :  pipe_tx00_eq_deemph[3:0] );

assign PHY_TXEQ_COEFF = ( PL_LINK_CAP_MAX_LINK_WIDTH==16 ?
                          { pipe_tx15_eq_deemph, pipe_tx14_eq_deemph, pipe_tx13_eq_deemph, pipe_tx12_eq_deemph,
                            pipe_tx11_eq_deemph, pipe_tx10_eq_deemph, pipe_tx09_eq_deemph, pipe_tx08_eq_deemph,
                            pipe_tx07_eq_deemph, pipe_tx06_eq_deemph, pipe_tx05_eq_deemph, pipe_tx04_eq_deemph,
                            pipe_tx03_eq_deemph, pipe_tx02_eq_deemph, pipe_tx01_eq_deemph, pipe_tx00_eq_deemph} :
                          PL_LINK_CAP_MAX_LINK_WIDTH==8 ?
                          { pipe_tx07_eq_deemph, pipe_tx06_eq_deemph, pipe_tx05_eq_deemph, pipe_tx04_eq_deemph,
                            pipe_tx03_eq_deemph, pipe_tx02_eq_deemph, pipe_tx01_eq_deemph, pipe_tx00_eq_deemph} :
                          PL_LINK_CAP_MAX_LINK_WIDTH==4 ?
                          { pipe_tx03_eq_deemph, pipe_tx02_eq_deemph, pipe_tx01_eq_deemph, pipe_tx00_eq_deemph} :
                          PL_LINK_CAP_MAX_LINK_WIDTH==2 ?
                          { pipe_tx01_eq_deemph, pipe_tx00_eq_deemph} : pipe_tx00_eq_deemph );

assign PHY_RXEQ_CTRL = ( PL_LINK_CAP_MAX_LINK_WIDTH==16 ?
                          { pipe_rx15_eq_control, pipe_rx14_eq_control, pipe_rx13_eq_control, pipe_rx12_eq_control,
                            pipe_rx11_eq_control, pipe_rx10_eq_control, pipe_rx09_eq_control, pipe_rx08_eq_control,
                            pipe_rx07_eq_control, pipe_rx06_eq_control, pipe_rx05_eq_control, pipe_rx04_eq_control,
                            pipe_rx03_eq_control, pipe_rx02_eq_control, pipe_rx01_eq_control, pipe_rx00_eq_control} :
                          PL_LINK_CAP_MAX_LINK_WIDTH==8 ?
                          { pipe_rx07_eq_control, pipe_rx06_eq_control, pipe_rx05_eq_control, pipe_rx04_eq_control,
                            pipe_rx03_eq_control, pipe_rx02_eq_control, pipe_rx01_eq_control, pipe_rx00_eq_control} :
                          PL_LINK_CAP_MAX_LINK_WIDTH==4 ?
                          { pipe_rx03_eq_control, pipe_rx02_eq_control, pipe_rx01_eq_control, pipe_rx00_eq_control} :
                          PL_LINK_CAP_MAX_LINK_WIDTH==2 ?
                          { pipe_rx01_eq_control, pipe_rx00_eq_control} : pipe_rx00_eq_control );

// Generate the cap_req, cap_gnt, and cap_rel signals.
assign cap_req = mcap_pcie_request;
assign mcap_external_request = (~cap_gnt) | cap_rel;

generate if (MCAP_ENABLEMENT == "NONE" || MCAP_ENABLEMENT == "PR") begin
    // A Tandem mode is not enabled
    // Muxing of critical signals is not required.
    // Tie the mux-switch value to constant 1.
    assign design_switch = 1'b1;
    // tie-off flr counter since it won't be used.
    always @(posedge user_clk)
       flr_cntr <= 8'b0;
    // tie-off the design_switch pulse signals
    always @(posedge user_clk)
      ds_srl <= 6'b0;
    assign ds_pulse = 1'b0;
    // tie-off np_req_wait since it won't be used
    always @(posedge user_clk)
      np_req_wait <= 6'b000000;
  end else begin
    // A Tandem mode is enabled
    // Muxing of critical signals is required.
    // Tie the mux-switch value to constant the mcap_design_switch.
    assign design_switch = mcap_design_switch;
    // Create a counter for the flr to continuously achnowledge flr
    // The counter is only used during stage1.
    always @(posedge user_clk)
       if (design_switch)
           flr_cntr <= 8'b0;
       else
           flr_cntr <= #TCQ flr_cntr + 1;
    // Create a design_switch pulse to reset user-reset after the design_switch is asserted.
    always @(posedge user_clk)
      ds_srl <= {ds_srl[4:0], design_switch};
    assign ds_pulse = design_switch & ~ds_srl[5];
    // Logic to only allocate one np_req credit.
    // The wait counter ensures np_req is only asserted once every 32 clock cycles.
    // This avoids np_req being asserted twice before np_req_count is updated.
    always @(posedge user_clk)
      if (design_switch || np_req_wait[5] || pcie_cq_np_req_count != 6'b000000)
        np_req_wait <= #TCQ 6'b000000;
      else
        np_req_wait <= #TCQ np_req_wait + 1;
  end
endgenerate


// muxing of critical signals when required.
assign mcap_external_request_int                        = (design_switch) ? mcap_external_request : 1'b0;
assign pcie_cq_np_req_int                               = (design_switch) ? pcie_cq_np_req : {1'b0,np_req_wait[5]};
// assign pcie_cq_np_req_int                               = (design_switch) ? pcie_cq_np_req : 2'b01;

assign m_axis_cq_tvalid                                 = (design_switch) ? m_axis_cq_tvalid_int : 1'b0;
assign s_axis_cc_tvalid_int                             = (design_switch) ? s_axis_cc_tvalid : 1'b0;
assign s_axis_rq_tvalid_int                             = (design_switch) ? s_axis_rq_tvalid : 1'b0;
assign m_axis_rc_tvalid                                 = (design_switch) ? m_axis_rc_tvalid_int : 1'b0;
assign m_axis_cq_tready_int                             = (design_switch) ? m_axis_cq_tready : 1'b1;
assign s_axis_cc_tready                                 = (design_switch) ? s_axis_cc_tready_int : {AXI4_CC_TREADY_WIDTH{1'b0}};
assign s_axis_rq_tready                                 = (design_switch) ? s_axis_rq_tready_int : {AXI4_RQ_TREADY_WIDTH{1'b0}};
assign m_axis_rc_tready_int                             = (design_switch) ? m_axis_rc_tready : 1'b0;

assign cfg_mgmt_write_int                               = (design_switch) ? cfg_mgmt_write : 1'b0;
assign cfg_mgmt_read_int                                = (design_switch) ? cfg_mgmt_read : 1'b0;
assign cfg_msg_transmit_wire                            = (design_switch) ? cfg_msg_transmit : 1'b0;
assign cfg_hot_reset_in_int = (design_switch) ? cfg_hot_reset_in : 1'b0;
assign cfg_config_space_enable_int                      = (design_switch) ? cfg_config_space_enable : 1'b1;
assign cfg_dsn_int                                      = (design_switch) ? cfg_dsn : 64'b0;
// If a request comes in during stage1                   
// ack it immediately.
assign cfg_power_state_change_ack_int                   = (design_switch) ? cfg_power_state_change_ack : cfg_power_state_change_interrupt;
assign cfg_err_cor_in_int                               = (design_switch) ? cfg_err_cor_in : 1'b0;
assign cfg_err_uncor_in_int                             = (design_switch) ? cfg_err_uncor_in : 1'b0;
// If a request comes in during stage1 
// reply done immediately
assign cfg_flr_done_int                                 = (design_switch) ? cfg_flr_done : cfg_flr_in_process;

assign cfg_req_pm_transition_l23_ready_int              = (design_switch) ? cfg_req_pm_transition_l23_ready : 1'b0;
assign cfg_link_training_enable_int                     = (design_switch) ? cfg_link_training_enable : 1'b1;
assign cfg_interrupt_int_int                            = (design_switch) ? cfg_interrupt_int : 4'b0;
assign cfg_interrupt_pending_int                        = (design_switch) ? cfg_interrupt_pending : 4'b0;
assign cfg_interrupt_msi_int_int                        = (design_switch) ? cfg_interrupt_msi_int : 32'b0;
assign cfg_interrupt_msi_pending_status_data_enable_int = (design_switch) ? cfg_interrupt_msi_pending_status_data_enable : 1'b0;

assign cfg_interrupt_msix_int_int                       = (design_switch) ? cfg_interrupt_msix_int : 1'b0;
assign cfg_interrupt_msix_vec_pending_int               = (design_switch) ? cfg_interrupt_msix_vec_pending : 2'b0;
// Continuously acknowledge vf flr during stage1.
assign cfg_vf_flr_func_num_int                          = (design_switch) ? cfg_vf_flr_func_num : flr_cntr;
assign cfg_vf_flr_done_int                              = (design_switch) ? cfg_vf_flr_done : 1'b1;
assign cfg_pm_aspm_l1_entry_reject_int                  = (design_switch) ? cfg_pm_aspm_l1_entry_reject : 1'b0;
assign cfg_pm_aspm_tx_l0s_entry_disable_int             = (design_switch) ? cfg_pm_aspm_tx_l0s_entry_disable : 1'b0;
assign conf_req_valid_int                               = (design_switch) ? conf_req_valid : 1'b0;
assign conf_req_ready                                   = (design_switch) ? conf_req_ready_int : 1'b0;
assign ext_ch_gt_drpen_int                              = (design_switch) ? ext_ch_gt_drpen : {PL_LINK_CAP_MAX_LINK_WIDTH{1'b0}};
assign drp_en_local                                     = (design_switch) ? drp_en : 1'b0;
assign gt_pcieuserratedone_int                          = (design_switch) ? gt_pcieuserratedone : {PL_LINK_CAP_MAX_LINK_WIDTH{1'b0}};
assign gt_loopback_int                                  = (design_switch) ? gt_loopback : {(PL_LINK_CAP_MAX_LINK_WIDTH * 3){1'b0}};
assign gt_txprbsforceerr_int                            = (design_switch) ? gt_txprbsforceerr : {PL_LINK_CAP_MAX_LINK_WIDTH{1'b0}};
assign gt_txinhibit_int                                 = (design_switch) ? gt_txinhibit : {PL_LINK_CAP_MAX_LINK_WIDTH{1'b0}};
assign gt_txprbssel_int                                 = (design_switch) ? gt_txprbssel : {(PL_LINK_CAP_MAX_LINK_WIDTH * 4){1'b0}};
assign gt_rxprbssel_int                                 = (design_switch) ? gt_rxprbssel : {(PL_LINK_CAP_MAX_LINK_WIDTH * 4){1'b0}};
assign gt_rxprbscntreset_int                            = (design_switch) ? gt_rxprbscntreset : {PL_LINK_CAP_MAX_LINK_WIDTH{1'b0}};
assign gt_dmonfiforeset_int                             = (design_switch) ? gt_dmonfiforeset : {PL_LINK_CAP_MAX_LINK_WIDTH{1'b0}};
assign gt_dmonitorclk_int                               = (design_switch) ? gt_dmonitorclk : {PL_LINK_CAP_MAX_LINK_WIDTH{1'b0}};
assign gt_txpmareset_int                                = (design_switch) ? gt_txpmareset : {PL_LINK_CAP_MAX_LINK_WIDTH{1'b0}};
assign gt_rxpmareset_int                                = (design_switch) ? gt_rxpmareset : {PL_LINK_CAP_MAX_LINK_WIDTH{1'b0}};
assign gt_txpcsreset_int                                = (design_switch) ? gt_txpcsreset : {PL_LINK_CAP_MAX_LINK_WIDTH{1'b0}};
assign gt_rxpcsreset_int                                = (design_switch) ? gt_rxpcsreset : {PL_LINK_CAP_MAX_LINK_WIDTH{1'b0}};
assign gt_rxbufreset_int                                = (design_switch) ? gt_rxbufreset : {PL_LINK_CAP_MAX_LINK_WIDTH{1'b0}};
assign gt_rxcdrreset_int                                = (design_switch) ? gt_rxcdrreset : {PL_LINK_CAP_MAX_LINK_WIDTH{1'b0}};
assign gt_rxdfelpmreset_int                             = (design_switch) ? gt_rxdfelpmreset : {PL_LINK_CAP_MAX_LINK_WIDTH{1'b0}};

///////////////////////////////////////// To LTSSM JTAG Debugger ////////////////////////////////////////////
assign pipe_tx0_rcvr_det  = pipe_tx_rcvr_det;
assign pipe_tx0_powerdown = pipe_tx00_powerdown;
//

  assign acs_cfg_ext_read_data = 32'b0;
  assign acs_cfg_ext_read_data_valid = 1'b0;

  assign rbar_cfg_ext_read_data = 32'b0;
  assign rbar_cfg_ext_read_data_valid = 1'b0;
  assign drp_rdy = drp_rdy_int;
  assign drp_do = drp_do_int;
  assign drp_clk_int = drp_clk;
  assign drp_en_int = drp_en_local;
  assign drp_we_int = drp_we;
  assign drp_addr_int = drp_addr;
  assign drp_di_int = drp_di;
  assign  rbar_bar_size = 6'b0;
  assign  rbar_function_number = 8'h0;
  assign  rbar_write_enable_bar0 = 1'b0;
  assign  rbar_write_enable_bar1 = 1'b0;
  assign  rbar_write_enable_bar2 = 1'b0;
  assign  rbar_write_enable_bar3 = 1'b0;
  assign  rbar_write_enable_bar4 = 1'b0;
  assign  rbar_write_enable_bar5 = 1'b0;

  localparam   MAX_WATCHDOG_CNT          = 20'h4FFFF;
  localparam   GEN_VALID_AT_WATCHDOG_CNT = 20'h40000; // timeout count rounded to nearest 2^n

  reg   [19:0] read_rcvd_watchDog_cnt = MAX_WATCHDOG_CNT;
  reg          cfg_ext_read_data_valid_dummy = 'h0;
  wire         is_reg_num_cfg_ext_space;
  assign       is_reg_num_cfg_ext_space = (cfg_ext_register_number >= 'h2C  && cfg_ext_register_number <= 'h3F) ||
                                          (cfg_ext_register_number >= 'h100 && cfg_ext_register_number <= 'h3FF);

  // Mux Control for the two PCIe Extended Capabilities. Only one outstanding transaction is
  // aloud at a time. So a simple select mux on the cfg_ext_read_data is sufficient.
  assign cfg_ext_read_data_valid_int = acs_cfg_ext_read_data_valid | cfg_ext_read_data_valid | dvsec_cfg_ext_read_data_valid | rbar_cfg_ext_read_data_valid | cfg_ext_read_data_valid_dummy;
  assign cfg_ext_read_data_int       =  acs_cfg_ext_read_data_valid   ? acs_cfg_ext_read_data
                                      : dvsec_cfg_ext_read_data_valid ? dvsec_cfg_ext_read_data
                                      : rbar_cfg_ext_read_data_valid ? rbar_cfg_ext_read_data
                                      :                                 cfg_ext_read_data;

  always @(posedge user_clk)
  begin
    if(cfg_ext_read_received && is_reg_num_cfg_ext_space)
      read_rcvd_watchDog_cnt <= 'd0;
    else if (acs_cfg_ext_read_data_valid | cfg_ext_read_data_valid | dvsec_cfg_ext_read_data_valid | rbar_cfg_ext_read_data_valid )
      read_rcvd_watchDog_cnt <= MAX_WATCHDOG_CNT;
    else if (read_rcvd_watchDog_cnt >= MAX_WATCHDOG_CNT)
      read_rcvd_watchDog_cnt <= read_rcvd_watchDog_cnt;
    else
      read_rcvd_watchDog_cnt <= read_rcvd_watchDog_cnt + 1'b1;

    cfg_ext_read_data_valid_dummy <= (read_rcvd_watchDog_cnt == GEN_VALID_AT_WATCHDOG_CNT) ? 1'b1 : 1'b0;

  end




  assign pipe_tx_rate_i = pipe_tx_rate_o;

 assign phy_rdy_out = phy_rdy;



// CXS Remap block to convert ccix_tx and ccix_rx to cxs_rx and cxs_tx
pcie_bridge_ep_pcie4c_ip_cxs_remap #(
    .AXIS_CCIX_RX_TDATA_WIDTH(AXIS_CCIX_RX_TDATA_WIDTH),
    .AXIS_CCIX_TX_TDATA_WIDTH(AXIS_CCIX_TX_TDATA_WIDTH),
    .AXIS_CCIX_RX_TUSER_WIDTH(AXIS_CCIX_RX_TUSER_WIDTH),
    .AXIS_CCIX_TX_TUSER_WIDTH(AXIS_CCIX_TX_TUSER_WIDTH)
) cxs_remap_i (
   .ccix_rx_tdata(m_axis_ccix_rx_tdata),
   .ccix_rx_tuser(m_axis_ccix_rx_tuser),
   .ccix_rx_tvalid(m_axis_ccix_rx_tvalid),
   .ccix_rx_credit_grant(ccix_rx_credit_grant),
   .ccix_rx_credit_return(ccix_rx_credit_return),
   .ccix_rx_credit_av(ccix_rx_credit_av),
   .ccix_rx_active_req (ccix_rx_active_req),
   .ccix_rx_active_ack (ccix_rx_active_ack),
   .ccix_rx_deact_hint (ccix_rx_deact_hint),

   .ccix_tx_tdata(s_axis_ccix_tx_tdata),
   .ccix_tx_tuser(s_axis_ccix_tx_tuser),
   .ccix_tx_tvalid(s_axis_ccix_tx_tvalid),
   .ccix_tx_credit_gnt(ccix_tx_credit_gnt),
   .ccix_tx_credit_rtn(ccix_tx_credit_rtn),
   .ccix_tx_active_req(ccix_tx_active_req),
   .ccix_tx_active_ack(ccix_tx_active_ack),
   .ccix_tx_deact_hint(ccix_tx_deact_hint),

   .CXS0_ACTIVE_REQ_TX(cxs0_active_req_tx),
   .CXS0_ACTIVE_ACK_TX(cxs0_active_ack_tx),
   .CXS0_DEACT_HINT_TX(cxs0_deact_hint_tx),
   .CXS0_VALID_TX(cxs0_valid_tx),
   .CXS0_CRDGNT_TX(cxs0_crdgnt_tx),
   .CXS0_CRDRTN_TX(cxs0_crdrtn_tx),
   .CXS0_CNTL_TX(cxs0_cntl_tx),
   .CXS0_DATA_TX(cxs0_data_tx),
   .CXS0_VALID_CHK_TX(cxs0_valid_chk_tx),
   .CXS0_CRDGNT_CHK_TX(cxs0_crdgnt_chk_tx),
   .CXS0_CRDRTN_CHK_TX(cxs0_crdrtn_chk_tx),
   .CXS0_CNTL_CHK_TX(cxs0_cntl_chk_tx),
   .CXS0_DATA_CHK_TX(cxs0_data_chk_tx),
   .CXS0_ACTIVE_REQ_RX(cxs0_active_req_rx),
   .CXS0_ACTIVE_ACK_RX(cxs0_active_ack_rx),
   .CXS0_DEACT_HINT_RX(cxs0_deact_hint_rx),
   .CXS0_VALID_RX(cxs0_valid_rx),
   .CXS0_CRDGNT_RX(cxs0_crdgnt_rx),
   .CXS0_CRDRTN_RX(cxs0_crdrtn_rx),
   .CXS0_CNTL_RX(cxs0_cntl_rx),
   .CXS0_DATA_RX(cxs0_data_rx),
   .CXS0_VALID_CHK_RX(cxs0_valid_chk_rx),
   .CXS0_CRDGNT_CHK_RX(cxs0_crdgnt_chk_rx),
   .CXS0_CRDRTN_CHK_RX(cxs0_crdrtn_chk_rx),
   .CXS0_CNTL_CHK_RX(cxs0_cntl_chk_rx),
   .CXS0_DATA_CHK_RX(cxs0_data_chk_rx),

   .cfg_vc1_en(cfg_vc1_enable),
   .cfg_vc1_neg_pend(cfg_vc1_negotiation_pending),

   .ccix_rst(~user_reset),
   .ccix_clk(user_clk)
);






 assign mcap_clk = mcap_clk_int;


//-----------------------------------------------------------------------
//   delay rx_data_valid for clean PIPE RX data
//-----------------------------------------------------------------------
reg [18:0] count_250us;
reg data_valid_high;
reg [1:0] speed_pipe_clk0, speed_pipe_clk1, speed_pipe_clk2;
reg [5:0] ltssm_pipe_clk0, ltssm_pipe_clk1;
reg [(PL_LINK_CAP_MAX_LINK_WIDTH*2)-1:0] state;

//input reg
always @ (posedge pipe_clk) begin
  {speed_pipe_clk2, speed_pipe_clk1, speed_pipe_clk0} <= {speed_pipe_clk1, speed_pipe_clk0, cfg_current_speed};
  {ltssm_pipe_clk1, ltssm_pipe_clk0} <= {ltssm_pipe_clk0, cfg_ltssm_state};
end


localparam TCQI = 1;
// state machine states
localparam IDLE            = 2'd0;
localparam R_SPEED         = 2'd1;
localparam GO_TO_R_LOCK    = 2'd2;
localparam RELEASE_RX_GATE = 2'd3;

  always @(posedge pipe_clk) begin
    if (!sys_reset) begin
       count_250us     <= #TCQI 19'b0;
       data_valid_high <= 1'b0;
    end else begin
      case (state[1 : 0]) 
        IDLE: begin
          count_250us <= #TCQI 19'b0;
          data_valid_high <= 1'b0;
        end // IDLE
        R_SPEED: begin
          count_250us <= #TCQI 19'b0;
          data_valid_high <= 1'b0;
        end //R_SPEED

        GO_TO_R_LOCK: begin // In R.Lock, Gate PIPE Signals & start counting 250us
          if (count_250us[17]  || ~data_valid_high) begin 
          //if (count_250us[11] ) begin 
            count_250us            <= 19'b0;
          end else begin
            count_250us            <= count_250us + 1'b1;
          end
          
          if(~data_valid_high) begin
            //wait for data_valid goes high
            if(|PHY_RXDATA_VALID) begin
              data_valid_high <= 1'b1;
            end else begin
              data_valid_high <= 1'b0;
            end
          end else begin
            data_valid_high <= 1'b1; // keep it high once goes high
          end
        end // GO_TO_R_LOCK
      endcase
    end // else - if(!rst_n)
  end // always

genvar i;

generate 
  for (i=0; i < PL_LINK_CAP_MAX_LINK_WIDTH; i=i+1) begin : workaround

  always @(posedge pipe_clk) begin
    if (!sys_reset) begin
       state[(i*2) +1 : i*2] <= #TCQI IDLE;
       PHY_RXDATA_VALID_REG[i]                  <= #TCQI 1'b0;
       PHY_RXVALID_REG[i]                       <= #TCQI 1'b0;  
       PHY_RXDATA_REG[(64*i)+63:(64*i)]         <= #TCQI 'h0;   
       PHY_RXSTART_BLOCK_REG[(i*2) +1 : i*2]    <= #TCQI 2'b00;
       rxsync_header_nogate_reg[(i*2) +1 : i*2] <= #TCQI 2'b00; 
    end else begin
      case (state[(i*2) +1 : i*2]) 
        IDLE: begin
          //In R.speed @ speed change + new speed = Gen3 | Gen4. Gate all RX signals 
          if (ltssm_pipe_clk1 == 6'h0C && speed_pipe_clk1[1] && (speed_pipe_clk2 != speed_pipe_clk1)) begin 
            state[(i*2) +1 : i*2] <= #TCQI R_SPEED;
            // PIPE Signals
            PHY_RXDATA_REG[(64*i)+63:(64*i)]         <= #TCQI 64'h00;
            PHY_RXVALID_REG[i]                       <= #TCQI 1'b0; 
            PHY_RXDATA_VALID_REG[i]                  <= #TCQI 1'b0;
            PHY_RXSTART_BLOCK_REG[(i*2) +1 : i*2]    <= #TCQI 2'b0;
            rxsync_header_nogate_reg[(i*2) +1 : i*2] <= #TCQI 2'b0; 
          end else begin
            state[(i*2) +1 : i*2] <= #TCQI IDLE;
            // PIPE Signals
            PHY_RXDATA_REG[(64*i)+63:(64*i)]         <= #TCQI PHY_RXDATA[(64*i)+63:(64*i)] ;
            PHY_RXSTART_BLOCK_REG[(i*2) +1 : i*2]    <= #TCQI PHY_RXSTART_BLOCK[(i*2) +1 : i*2];
            rxsync_header_nogate_reg[(i*2) +1 : i*2] <= #TCQI rxsync_header_nogate[(i*2) +1 : i*2]; 
            PHY_RXVALID_REG[i]                       <= #TCQI PHY_RXVALID[i]; 
            PHY_RXDATA_VALID_REG[i]                  <= #TCQI PHY_RXDATA_VALID[i];  
          end       
        end // IDLE

        R_SPEED: begin
          if (ltssm_pipe_clk1 == 6'h0B && speed_pipe_clk1[1]) begin //In R.speed @ (Gen3 | Gen4). Gate all RX signals
            state[(i*2) +1 : i*2] <= #TCQI GO_TO_R_LOCK;
          end else begin
            // Go back to IDLE if not h0C -> h0B
            state[(i*2) +1 : i*2] <= #TCQI (ltssm_pipe_clk1 == 'h0C && speed_pipe_clk1[1]) ?  R_SPEED : IDLE; 
          end       
          // PIPE Signals
          PHY_RXDATA_REG[(64*i)+63:(64*i)]         <= #TCQI 64'h00;
          PHY_RXVALID_REG[i]                       <= #TCQI 1'b0; 
          PHY_RXDATA_VALID_REG[i]                  <= #TCQI 1'b0;
          PHY_RXSTART_BLOCK_REG[(i*2) +1 : i*2]    <= #TCQI 2'b0;
          rxsync_header_nogate_reg[(i*2) +1 : i*2] <= #TCQI 2'b0; 
        end //R_SPEED
/*
        R_SPEED: begin
          if (ltssm_pipe_clk1 == 6'h0B && speed_pipe_clk1[1]) begin //In R.speed @ (Gen3 | Gen4). Gate all RX signals
            state[(i*2) +1 : i*2] <= #TCQI GO_TO_R_LOCK;
            // PIPE Signals
            PHY_RXDATA_REG[(64*i)+63:(64*i)]         <= #TCQI 64'h00;
            PHY_RXVALID_REG[i]                       <= #TCQI 1'b0; 
            PHY_RXDATA_VALID_REG[i]                  <= #TCQI 1'b0;
            PHY_RXSTART_BLOCK_REG[(i*2) +1 : i*2]    <= #TCQI 2'b0;
            rxsync_header_nogate_reg[(i*2) +1 : i*2] <= #TCQI 2'b0; 
          end else begin
            state[(i*2) +1 : i*2] <= #TCQI (ltssm_pipe_clk1 == 'h0C) ?  R_SPEED : IDLE; // Go back to IDLE if not h0C -> h0B
            // PIPE Signals
            PHY_RXDATA_REG[(64*i)+63:(64*i)]         <= #TCQI PHY_RXDATA[(64*i)+63:(64*i)] ;
            PHY_RXSTART_BLOCK_REG[(i*2) +1 : i*2]    <= #TCQI PHY_RXSTART_BLOCK[(i*2) +1 : i*2];
            rxsync_header_nogate_reg[(i*2) +1 : i*2] <= #TCQI rxsync_header_nogate[(i*2) +1 : i*2]; 
            PHY_RXVALID_REG[i]                       <= #TCQI PHY_RXVALID[i]; 
            PHY_RXDATA_VALID_REG[i]                  <= #TCQI PHY_RXDATA_VALID[i];  
          end       
        end //R_SPEED
*/
        GO_TO_R_LOCK: begin // In R.Lock, Gate PIPE Signals & start counting 250us
          // PIPE Signals
          PHY_RXDATA_REG[(64*i)+63:(64*i)]         <= #TCQI 64'h00;
          PHY_RXVALID_REG[i]                       <= #TCQI 1'b0; 
          PHY_RXDATA_VALID_REG[i]                  <= #TCQI 1'b0;
          PHY_RXSTART_BLOCK_REG[(i*2) +1 : i*2]    <= #TCQI 2'b0;
          rxsync_header_nogate_reg[(i*2) +1 : i*2] <= #TCQI 2'b0;
          if (count_250us[17] ) begin 
          //if (count_250us[11] ) begin 
            state[(i*2) +1 : i*2]  <= RELEASE_RX_GATE; 
          end else begin
            state[(i*2) +1 : i*2]  <= GO_TO_R_LOCK; 
          end
        end // GO_TO_R_LOCK

        RELEASE_RX_GATE: begin
          //G3 EIEOS
          if (pipe_tx_rate_i == 2'h2 &&  (PHY_RXDATA [(64*i)+63:(64*i)] == 64'hFF00_FF00)  && PHY_RXDATA_VALID[i] == 1'b1) begin  
            state[(i*2) +1 : i*2] <= #TCQI IDLE;
            // PIPE Signals
            PHY_RXDATA_REG[(64*i)+63:(64*i)]         <= #TCQI PHY_RXDATA[(64*i)+63:(64*i)] ;
            PHY_RXSTART_BLOCK_REG[(i*2) +1 : i*2]    <= #TCQI PHY_RXSTART_BLOCK[(i*2) +1 : i*2];
            rxsync_header_nogate_reg[(i*2) +1 : i*2] <= #TCQI rxsync_header_nogate[(i*2) +1 : i*2]; 
            PHY_RXVALID_REG[i]                       <= #TCQI PHY_RXVALID[i]; 
            PHY_RXDATA_VALID_REG[i]                  <= #TCQI PHY_RXDATA_VALID[i];  
          //G4 EIEOS
          end else if (pipe_tx_rate_i == 2'h3 &&  (PHY_RXDATA [(64*i)+63:(64*i)] == 64'hFFFF0000_FFFF_0000)  && PHY_RXDATA_VALID[i] == 1'b1)  begin
            state[(i*2) +1 : i*2] <= #TCQI IDLE;
            // PIPE Signals
            PHY_RXDATA_REG[(64*i)+63:(64*i)]         <= #TCQI PHY_RXDATA[(64*i)+63:(64*i)] ;
            PHY_RXSTART_BLOCK_REG[(i*2) +1 : i*2]    <= #TCQI PHY_RXSTART_BLOCK[(i*2) +1 : i*2];
            rxsync_header_nogate_reg[(i*2) +1 : i*2] <= #TCQI rxsync_header_nogate[(i*2) +1 : i*2]; 
            PHY_RXVALID_REG[i]                       <= #TCQI PHY_RXVALID[i]; 
            PHY_RXDATA_VALID_REG[i]                  <= #TCQI PHY_RXDATA_VALID[i]; 
          end else begin
            state[(i*2) +1 : i*2] <= #TCQI RELEASE_RX_GATE;
            // PIPE Signals
            PHY_RXDATA_REG[(64*i)+63:(64*i)]         <= #TCQI 64'h00;
            PHY_RXVALID_REG[i]                       <= #TCQI 1'b0; 
            PHY_RXDATA_VALID_REG[i]                  <= #TCQI 1'b0;
            PHY_RXSTART_BLOCK_REG[(i*2) +1 : i*2]    <= #TCQI 2'b0;
            rxsync_header_nogate_reg[(i*2) +1 : i*2] <= #TCQI 2'b0;
          end       
        end // RELEASE_RX_GATE
      endcase
    end // else - if(!rst_n)
  end // always
end // for
endgenerate

 always @(posedge pipe_clk) begin
   if (!sys_reset) begin
       PHY_RXDATAK_REG      <= #TCQI 'h0;
       PHY_RXSTATUS_REG     <= #TCQI 'h0; 
       PHY_PHYSTATUS_REG    <= #TCQI 'h0; 
       PHY_RXELECIDLE_REG   <= #TCQI 'h0; 
   //    PHY_RXDATA_REG       <= #TCQI 'b0;
    //   PHY_RXVALID_REG      <= #TCQI 'h0; 
    //   PHY_RXSTART_BLOCK_REG <=  #TCQI 'h0;
    //   rxsync_header_nogate_reg <= #TCQI 'h0; 
    //   PHY_RXDATA_VALID_REG            <= #TCQI 'h0;
   end else begin
       PHY_RXDATAK_REG      <= #TCQI PHY_RXDATAK;
       PHY_RXSTATUS_REG     <= #TCQI PHY_RXSTATUS; 
       PHY_PHYSTATUS_REG    <= #TCQI PHY_PHYSTATUS; 
       PHY_RXELECIDLE_REG   <= #TCQI PHY_RXELECIDLE; 
    //   PHY_RXDATA_REG       <= #TCQI PHY_RXDATA;
    //   PHY_RXVALID_REG      <= #TCQI PHY_RXVALID; 
    //   PHY_RXSTART_BLOCK_REG <=  #TCQI PHY_RXSTART_BLOCK;
    //   rxsync_header_nogate_reg <= #TCQI rxsync_header_nogate;  
    //   PHY_RXDATA_VALID_REG             <= #TCQI PHY_RXDATA_VALID_TEMP;  
   end
 end

//   delay rx_data_valid for clean PIPE RX data

//---------------------------------------------------------------------------------------------------------//
//  
//---------------------------------------------------------------------------------------------------------//

  assign conf_mcap_design_switch = mcap_design_switch;
  // Tie-off unused signals
  assign conf_mcap_design_switch_o = 1'b1;
  assign startup_eos = 1'b0;
  assign startup_cfgclk = 1'b0;
  assign startup_cfgmclk = 1'b0;
  assign startup_di = 4'b0000;
  assign startup_preq = 1'b0;


endmodule



