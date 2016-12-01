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
// File       : pcie4_uscale_plus_0_pipe.v
// Version    : 1.1 
//-----------------------------------------------------------------------------
/////////////////////////////////////////////////////////////////////////////

`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie4_uscale_plus_0_pipe 
#(
     parameter           TCQ = 100
   , parameter           IMPL_TARGET = "SOFT"
   , parameter           SIM_DEVICE = "ULTRASCALE_PLUS_ES1"
   , parameter           AXISTEN_IF_EXT_512_INTFC_RAM_STYLE = "BRAM"

   , parameter           AXI4_DATA_WIDTH = 512
   , parameter           AXI4_TKEEP_WIDTH = 16
   , parameter           AXI4_CQ_TUSER_WIDTH = 183
   , parameter           AXI4_CC_TUSER_WIDTH = 81
   , parameter           AXI4_RQ_TUSER_WIDTH = 137
   , parameter           AXI4_RC_TUSER_WIDTH = 161
   , parameter           AXI4_CQ_TREADY_WIDTH = 1
   , parameter           AXI4_CC_TREADY_WIDTH = 1
   , parameter           AXI4_RQ_TREADY_WIDTH = 1
   , parameter           AXI4_RC_TREADY_WIDTH = 1

   , parameter           CRM_CORE_CLK_FREQ_500="TRUE"
   , parameter [1:0]     CRM_USER_CLK_FREQ=2'b10
   , parameter [1:0]     AXISTEN_IF_WIDTH=2'b10
   , parameter           AXISTEN_IF_EXT_512="FALSE"
   , parameter           AXISTEN_IF_EXT_512_CQ_STRADDLE="FALSE"
   , parameter           AXISTEN_IF_EXT_512_CC_STRADDLE="FALSE"
   , parameter           AXISTEN_IF_EXT_512_RQ_STRADDLE="FALSE"
   , parameter           AXISTEN_IF_EXT_512_RC_STRADDLE="FALSE"
   , parameter           AXISTEN_IF_EXT_512_RC_4TLP_STRADDLE="TRUE"
   , parameter [1:0]     AXISTEN_IF_CQ_ALIGNMENT_MODE=2'b00
   , parameter [1:0]     AXISTEN_IF_CC_ALIGNMENT_MODE=2'b00
   , parameter [1:0]     AXISTEN_IF_RQ_ALIGNMENT_MODE=2'b00
   , parameter [1:0]     AXISTEN_IF_RC_ALIGNMENT_MODE=2'b00
   , parameter           AXISTEN_IF_RC_STRADDLE="FALSE"
   , parameter           AXISTEN_IF_ENABLE_RX_MSG_INTFC="FALSE"
   , parameter [17:0]    AXISTEN_IF_ENABLE_MSG_ROUTE=18'h0
   , parameter           AXISTEN_IF_RX_PARITY_EN="TRUE"
   , parameter           AXISTEN_IF_TX_PARITY_EN="TRUE"
   , parameter           AXISTEN_IF_ENABLE_CLIENT_TAG="FALSE"
   , parameter           AXISTEN_IF_ENABLE_256_TAGS="FALSE"
   , parameter [23:0]    AXISTEN_IF_COMPL_TIMEOUT_REG0=24'hBEBC20
   , parameter [27:0]    AXISTEN_IF_COMPL_TIMEOUT_REG1=28'h2FAF080
   , parameter           AXISTEN_IF_LEGACY_MODE_ENABLE="FALSE"
   , parameter           AXISTEN_IF_ENABLE_MESSAGE_RID_CHECK="TRUE"
   , parameter           AXISTEN_IF_MSIX_TO_RAM_PIPELINE="FALSE"
   , parameter           AXISTEN_IF_MSIX_FROM_RAM_PIPELINE="FALSE"
   , parameter           AXISTEN_IF_MSIX_RX_PARITY_EN="TRUE"
   , parameter           AXISTEN_IF_ENABLE_INTERNAL_MSIX_TABLE="FALSE"
   , parameter           AXISTEN_IF_CQ_EN_POISONED_MEM_WR="FALSE"
   , parameter           AXISTEN_IF_SIM_SHORT_CPL_TIMEOUT="FALSE"
   , parameter           AXISTEN_IF_RQ_CC_REGISTERED_TREADY="TRUE"
   , parameter [15:0]    PM_ASPML0S_TIMEOUT=16'h1500
   , parameter [31:0]    PM_L1_REENTRY_DELAY=32'h0
   , parameter [19:0]    PM_ASPML1_ENTRY_DELAY=20'h0
   , parameter           PM_ENABLE_SLOT_POWER_CAPTURE="TRUE"
   , parameter [19:0]    PM_PME_SERVICE_TIMEOUT_DELAY=20'h0
   , parameter [15:0]    PM_PME_TURNOFF_ACK_DELAY=16'h100
   , parameter           PL_UPSTREAM_FACING="TRUE"
   , parameter [4:0]     PL_LINK_CAP_MAX_LINK_WIDTH=5'b01000
   , parameter [3:0]     PL_LINK_CAP_MAX_LINK_SPEED=4'b100
   , parameter           PL_DISABLE_DC_BALANCE="FALSE"
   , parameter           PL_DISABLE_EI_INFER_IN_L0="FALSE"
   , parameter integer   PL_N_FTS=255
   , parameter           PL_DISABLE_UPCONFIG_CAPABLE="FALSE"
   , parameter           PL_DISABLE_RETRAIN_ON_FRAMING_ERROR="FALSE"
   , parameter           PL_DISABLE_RETRAIN_ON_EB_ERROR="FALSE"
   , parameter [15:0]    PL_DISABLE_RETRAIN_ON_SPECIFIC_FRAMING_ERROR=16'b0000000000000000
   , parameter [7:0]     PL_REPORT_ALL_PHY_ERRORS=8'b00000000
   , parameter [1:0]     PL_DISABLE_LFSR_UPDATE_ON_SKP=2'b00
   , parameter [31:0]    PL_LANE0_EQ_CONTROL=32'h3F00
   , parameter [31:0]    PL_LANE1_EQ_CONTROL=32'h3F00
   , parameter [31:0]    PL_LANE2_EQ_CONTROL=32'h3F00
   , parameter [31:0]    PL_LANE3_EQ_CONTROL=32'h3F00
   , parameter [31:0]    PL_LANE4_EQ_CONTROL=32'h3F00
   , parameter [31:0]    PL_LANE5_EQ_CONTROL=32'h3F00
   , parameter [31:0]    PL_LANE6_EQ_CONTROL=32'h3F00
   , parameter [31:0]    PL_LANE7_EQ_CONTROL=32'h3F00
   , parameter [31:0]    PL_LANE8_EQ_CONTROL=32'h3F00
   , parameter [31:0]    PL_LANE9_EQ_CONTROL=32'h3F00
   , parameter [31:0]    PL_LANE10_EQ_CONTROL=32'h3F00
   , parameter [31:0]    PL_LANE11_EQ_CONTROL=32'h3F00
   , parameter [31:0]    PL_LANE12_EQ_CONTROL=32'h3F00
   , parameter [31:0]    PL_LANE13_EQ_CONTROL=32'h3F00
   , parameter [31:0]    PL_LANE14_EQ_CONTROL=32'h3F00
   , parameter [31:0]    PL_LANE15_EQ_CONTROL=32'h3F00
   , parameter [1:0]     PL_EQ_BYPASS_PHASE23=2'b00
   , parameter [4:0]     PL_EQ_ADAPT_ITER_COUNT=5'h2
   , parameter [1:0]     PL_EQ_ADAPT_REJECT_RETRY_COUNT=2'h1
   , parameter           PL_EQ_SHORT_ADAPT_PHASE="FALSE"
   , parameter [1:0]     PL_EQ_ADAPT_DISABLE_COEFF_CHECK=2'b0
   , parameter [1:0]     PL_EQ_ADAPT_DISABLE_PRESET_CHECK=2'b0
   , parameter [7:0]     PL_EQ_DEFAULT_TX_PRESET=8'h44
   , parameter [5:0]     PL_EQ_DEFAULT_RX_PRESET_HINT=6'h33
   , parameter [1:0]     PL_EQ_RX_ADAPT_EQ_PHASE0=2'b00
   , parameter [1:0]     PL_EQ_RX_ADAPT_EQ_PHASE1=2'b00
   , parameter           PL_EQ_DISABLE_MISMATCH_CHECK="TRUE"
   , parameter [1:0]     PL_RX_L0S_EXIT_TO_RECOVERY=2'b00
   , parameter           PL_EQ_TX_8G_EQ_TS2_ENABLE="FALSE"
   , parameter           PL_DISABLE_AUTO_EQ_SPEED_CHANGE_TO_GEN4="FALSE"
   , parameter           PL_DISABLE_AUTO_EQ_SPEED_CHANGE_TO_GEN3="FALSE"
   , parameter           PL_DISABLE_AUTO_SPEED_CHANGE_TO_GEN2="FALSE"
   , parameter           PL_DESKEW_ON_SKIP_IN_GEN12="FALSE"
   , parameter           PL_INFER_EI_DISABLE_REC_RC="FALSE"
   , parameter           PL_INFER_EI_DISABLE_REC_SPD="FALSE"
   , parameter           PL_INFER_EI_DISABLE_LPBK_ACTIVE="FALSE"
   , parameter [3:0]     PL_RX_ADAPT_TIMER_RRL_GEN3=4'h0
   , parameter [1:0]     PL_RX_ADAPT_TIMER_RRL_CLOBBER_TX_TS=2'b00
   , parameter [3:0]     PL_RX_ADAPT_TIMER_RRL_GEN4=4'h0
   , parameter [3:0]     PL_RX_ADAPT_TIMER_CLWS_GEN3=4'h0
   , parameter [1:0]     PL_RX_ADAPT_TIMER_CLWS_CLOBBER_TX_TS=2'b00
   , parameter [3:0]     PL_RX_ADAPT_TIMER_CLWS_GEN4=4'h0
   , parameter           PL_DISABLE_LANE_REVERSAL="FALSE"
   , parameter           PL_CFG_STATE_ROBUSTNESS_ENABLE="TRUE"
   , parameter           PL_REDO_EQ_SOURCE_SELECT="TRUE"
   , parameter           PL_DEEMPH_SOURCE_SELECT="TRUE"
   , parameter           PL_EXIT_LOOPBACK_ON_EI_ENTRY="FALSE"
   , parameter           PL_QUIESCE_GUARANTEE_DISABLE="FALSE"
   , parameter           PL_SRIS_ENABLE="FALSE"
   , parameter [6:0]     PL_SRIS_SKPOS_GEN_SPD_VEC=7'h0
   , parameter [6:0]     PL_SRIS_SKPOS_REC_SPD_VEC=7'h0
   , parameter [1:0]     PL_SIM_FAST_LINK_TRAINING=2'h0
   , parameter [15:0]    PL_USER_SPARE=16'h0
   , parameter           LL_ACK_TIMEOUT_EN="FALSE"
   , parameter [8:0]     LL_ACK_TIMEOUT=9'h0
   , parameter integer   LL_ACK_TIMEOUT_FUNC=0
   , parameter           LL_REPLAY_TIMEOUT_EN="FALSE"
   , parameter [8:0]     LL_REPLAY_TIMEOUT=9'h0
   , parameter integer   LL_REPLAY_TIMEOUT_FUNC=0
   , parameter           LL_REPLAY_TO_RAM_PIPELINE="FALSE"
   , parameter           LL_REPLAY_FROM_RAM_PIPELINE="FALSE"
   , parameter           LL_DISABLE_SCHED_TX_NAK="FALSE"
   , parameter           LL_TX_TLP_PARITY_CHK="TRUE"
   , parameter           LL_RX_TLP_PARITY_GEN="TRUE"
   , parameter [15:0]    LL_USER_SPARE=16'h0
   , parameter           IS_SWITCH_PORT="FALSE"
   , parameter           CFG_BYPASS_MODE_ENABLE="FALSE"
   , parameter [1:0]     TL_PF_ENABLE_REG=2'h0
   , parameter [11:0]    TL_CREDITS_CD=12'h1C0
   , parameter [7:0]     TL_CREDITS_CH=8'h20
   , parameter [1:0]     TL_COMPLETION_RAM_SIZE=2'b01
   , parameter [1:0]     TL_COMPLETION_RAM_NUM_TLPS=2'b00
   , parameter [11:0]    TL_CREDITS_NPD=12'h4
   , parameter [7:0]     TL_CREDITS_NPH=8'h20
   , parameter [11:0]    TL_CREDITS_PD=12'he0
   , parameter [7:0]     TL_CREDITS_PH=8'h20
   , parameter           TL_RX_COMPLETION_TO_RAM_WRITE_PIPELINE="FALSE"
   , parameter           TL_RX_COMPLETION_TO_RAM_READ_PIPELINE="FALSE"
   , parameter           TL_RX_COMPLETION_FROM_RAM_READ_PIPELINE="FALSE"
   , parameter           TL_POSTED_RAM_SIZE=1'b0
   , parameter           TL_RX_POSTED_TO_RAM_WRITE_PIPELINE="FALSE"
   , parameter           TL_RX_POSTED_TO_RAM_READ_PIPELINE="FALSE"
   , parameter           TL_RX_POSTED_FROM_RAM_READ_PIPELINE="FALSE"
   , parameter           TL_TX_MUX_STRICT_PRIORITY="TRUE"
   , parameter           TL_TX_TLP_STRADDLE_ENABLE="FALSE"
   , parameter           TL_TX_TLP_TERMINATE_PARITY="FALSE"
   , parameter [4:0]     TL_FC_UPDATE_MIN_INTERVAL_TLP_COUNT=5'h8
   , parameter [4:0]     TL_FC_UPDATE_MIN_INTERVAL_TIME=5'h2
   , parameter [15:0]    TL_USER_SPARE=16'h0
   , parameter [23:0]    PF0_CLASS_CODE=24'h000000
   , parameter [23:0]    PF1_CLASS_CODE=24'h000000
   , parameter [23:0]    PF2_CLASS_CODE=24'h000000
   , parameter [23:0]    PF3_CLASS_CODE=24'h000000
   , parameter [2:0]     PF0_INTERRUPT_PIN=3'h1
   , parameter [2:0]     PF1_INTERRUPT_PIN=3'h1
   , parameter [2:0]     PF2_INTERRUPT_PIN=3'h1
   , parameter [2:0]     PF3_INTERRUPT_PIN=3'h1
   , parameter [7:0]     PF0_CAPABILITY_POINTER=8'h80
   , parameter [7:0]     PF1_CAPABILITY_POINTER=8'h80
   , parameter [7:0]     PF2_CAPABILITY_POINTER=8'h80
   , parameter [7:0]     PF3_CAPABILITY_POINTER=8'h80
   , parameter [7:0]     VF0_CAPABILITY_POINTER=8'h80
   , parameter           LEGACY_CFG_EXTEND_INTERFACE_ENABLE="FALSE"
   , parameter           EXTENDED_CFG_EXTEND_INTERFACE_ENABLE="FALSE"
   , parameter           TL2CFG_IF_PARITY_CHK="TRUE"
   , parameter           HEADER_TYPE_OVERRIDE="FALSE"
   , parameter [2:0]     PF0_BAR0_CONTROL=3'b100
   , parameter [2:0]     PF1_BAR0_CONTROL=3'b100
   , parameter [2:0]     PF2_BAR0_CONTROL=3'b100
   , parameter [2:0]     PF3_BAR0_CONTROL=3'b100
   , parameter [5:0]     PF0_BAR0_APERTURE_SIZE=6'b000011
   , parameter [5:0]     PF1_BAR0_APERTURE_SIZE=6'b000011
   , parameter [5:0]     PF2_BAR0_APERTURE_SIZE=6'b000011
   , parameter [5:0]     PF3_BAR0_APERTURE_SIZE=6'b000011
   , parameter [2:0]     PF0_BAR1_CONTROL=3'b0
   , parameter [2:0]     PF1_BAR1_CONTROL=3'b0
   , parameter [2:0]     PF2_BAR1_CONTROL=3'b0
   , parameter [2:0]     PF3_BAR1_CONTROL=3'b0
   , parameter [4:0]     PF0_BAR1_APERTURE_SIZE=5'b0
   , parameter [4:0]     PF1_BAR1_APERTURE_SIZE=5'b0
   , parameter [4:0]     PF2_BAR1_APERTURE_SIZE=5'b0
   , parameter [4:0]     PF3_BAR1_APERTURE_SIZE=5'b0
   , parameter [2:0]     PF0_BAR2_CONTROL=3'b100
   , parameter [2:0]     PF1_BAR2_CONTROL=3'b100
   , parameter [2:0]     PF2_BAR2_CONTROL=3'b100
   , parameter [2:0]     PF3_BAR2_CONTROL=3'b100
   , parameter [5:0]     PF0_BAR2_APERTURE_SIZE=6'b00011
   , parameter [5:0]     PF1_BAR2_APERTURE_SIZE=6'b00011
   , parameter [5:0]     PF2_BAR2_APERTURE_SIZE=6'b00011
   , parameter [5:0]     PF3_BAR2_APERTURE_SIZE=6'b00011
   , parameter [2:0]     PF0_BAR3_CONTROL=3'b0
   , parameter [2:0]     PF1_BAR3_CONTROL=3'b0
   , parameter [2:0]     PF2_BAR3_CONTROL=3'b0
   , parameter [2:0]     PF3_BAR3_CONTROL=3'b0
   , parameter [4:0]     PF0_BAR3_APERTURE_SIZE=5'b00011
   , parameter [4:0]     PF1_BAR3_APERTURE_SIZE=5'b00011
   , parameter [4:0]     PF2_BAR3_APERTURE_SIZE=5'b00011
   , parameter [4:0]     PF3_BAR3_APERTURE_SIZE=5'b00011
   , parameter [2:0]     PF0_BAR4_CONTROL=3'b100
   , parameter [2:0]     PF1_BAR4_CONTROL=3'b100
   , parameter [2:0]     PF2_BAR4_CONTROL=3'b100
   , parameter [2:0]     PF3_BAR4_CONTROL=3'b100
   , parameter [5:0]     PF0_BAR4_APERTURE_SIZE=6'b00011
   , parameter [5:0]     PF1_BAR4_APERTURE_SIZE=6'b00011
   , parameter [5:0]     PF2_BAR4_APERTURE_SIZE=6'b00011
   , parameter [5:0]     PF3_BAR4_APERTURE_SIZE=6'b00011
   , parameter [2:0]     PF0_BAR5_CONTROL=3'b0
   , parameter [2:0]     PF1_BAR5_CONTROL=3'b0
   , parameter [2:0]     PF2_BAR5_CONTROL=3'b0
   , parameter [2:0]     PF3_BAR5_CONTROL=3'b0
   , parameter [4:0]     PF0_BAR5_APERTURE_SIZE=5'b00011
   , parameter [4:0]     PF1_BAR5_APERTURE_SIZE=5'b00011
   , parameter [4:0]     PF2_BAR5_APERTURE_SIZE=5'b00011
   , parameter [4:0]     PF3_BAR5_APERTURE_SIZE=5'b00011
   , parameter           PF0_EXPANSION_ROM_ENABLE="FALSE"
   , parameter           PF1_EXPANSION_ROM_ENABLE="FALSE"
   , parameter           PF2_EXPANSION_ROM_ENABLE="FALSE"
   , parameter           PF3_EXPANSION_ROM_ENABLE="FALSE"
   , parameter [4:0]     PF0_EXPANSION_ROM_APERTURE_SIZE=5'b00011
   , parameter [4:0]     PF1_EXPANSION_ROM_APERTURE_SIZE=5'b00011
   , parameter [4:0]     PF2_EXPANSION_ROM_APERTURE_SIZE=5'b00011
   , parameter [4:0]     PF3_EXPANSION_ROM_APERTURE_SIZE=5'b00011
   , parameter [7:0]     PF0_PCIE_CAP_NEXTPTR=8'h0
   , parameter [7:0]     PF1_PCIE_CAP_NEXTPTR=8'h0
   , parameter [7:0]     PF2_PCIE_CAP_NEXTPTR=8'h0
   , parameter [7:0]     PF3_PCIE_CAP_NEXTPTR=8'h0
   , parameter [7:0]     VFG0_PCIE_CAP_NEXTPTR=8'h0
   , parameter [7:0]     VFG1_PCIE_CAP_NEXTPTR=8'h0
   , parameter [7:0]     VFG2_PCIE_CAP_NEXTPTR=8'h0
   , parameter [7:0]     VFG3_PCIE_CAP_NEXTPTR=8'h0
   , parameter [2:0]     PF0_DEV_CAP_MAX_PAYLOAD_SIZE=3'b011
   , parameter [2:0]     PF1_DEV_CAP_MAX_PAYLOAD_SIZE=3'b011
   , parameter [2:0]     PF2_DEV_CAP_MAX_PAYLOAD_SIZE=3'b011
   , parameter [2:0]     PF3_DEV_CAP_MAX_PAYLOAD_SIZE=3'b011
   , parameter           PF0_DEV_CAP_EXT_TAG_SUPPORTED="TRUE"
   , parameter integer   PF0_DEV_CAP_ENDPOINT_L0S_LATENCY=0
   , parameter integer   PF0_DEV_CAP_ENDPOINT_L1_LATENCY=0
   , parameter           PF0_DEV_CAP_FUNCTION_LEVEL_RESET_CAPABLE="TRUE"
   , parameter integer   PF0_LINK_CAP_ASPM_SUPPORT=0
   , parameter [0:0]     PF0_LINK_CONTROL_RCB=1'b0
   , parameter           PF0_LINK_STATUS_SLOT_CLOCK_CONFIG="TRUE"
   , parameter integer   PF0_LINK_CAP_L0S_EXIT_LATENCY_COMCLK_GEN1=7
   , parameter integer   PF0_LINK_CAP_L0S_EXIT_LATENCY_COMCLK_GEN2=7
   , parameter integer   PF0_LINK_CAP_L0S_EXIT_LATENCY_COMCLK_GEN3=7
   , parameter integer   PF0_LINK_CAP_L0S_EXIT_LATENCY_COMCLK_GEN4=7
   , parameter integer   PF0_LINK_CAP_L0S_EXIT_LATENCY_GEN1=7
   , parameter integer   PF0_LINK_CAP_L0S_EXIT_LATENCY_GEN2=7
   , parameter integer   PF0_LINK_CAP_L0S_EXIT_LATENCY_GEN3=7
   , parameter integer   PF0_LINK_CAP_L0S_EXIT_LATENCY_GEN4=7
   , parameter integer   PF0_LINK_CAP_L1_EXIT_LATENCY_COMCLK_GEN1=7
   , parameter integer   PF0_LINK_CAP_L1_EXIT_LATENCY_COMCLK_GEN2=7
   , parameter integer   PF0_LINK_CAP_L1_EXIT_LATENCY_COMCLK_GEN3=7
   , parameter integer   PF0_LINK_CAP_L1_EXIT_LATENCY_COMCLK_GEN4=7
   , parameter integer   PF0_LINK_CAP_L1_EXIT_LATENCY_GEN1=7
   , parameter integer   PF0_LINK_CAP_L1_EXIT_LATENCY_GEN2=7
   , parameter integer   PF0_LINK_CAP_L1_EXIT_LATENCY_GEN3=7
   , parameter integer   PF0_LINK_CAP_L1_EXIT_LATENCY_GEN4=7
   , parameter           PF0_DEV_CAP2_CPL_TIMEOUT_DISABLE="TRUE"
   , parameter           PF0_DEV_CAP2_32B_ATOMIC_COMPLETER_SUPPORT="TRUE"
   , parameter           PF0_DEV_CAP2_64B_ATOMIC_COMPLETER_SUPPORT="TRUE"
   , parameter           PF0_DEV_CAP2_128B_CAS_ATOMIC_COMPLETER_SUPPORT="TRUE"
   , parameter           PF0_DEV_CAP2_LTR_SUPPORT="TRUE"
   , parameter           PF0_DEV_CAP2_TPH_COMPLETER_SUPPORT="FALSE"
   , parameter [1:0]     PF0_DEV_CAP2_OBFF_SUPPORT=2'b00
   , parameter           PF0_DEV_CAP2_ARI_FORWARD_ENABLE="FALSE"
   , parameter [7:0]     PF0_MSI_CAP_NEXTPTR=8'h0
   , parameter [7:0]     PF1_MSI_CAP_NEXTPTR=8'h0
   , parameter [7:0]     PF2_MSI_CAP_NEXTPTR=8'h0
   , parameter [7:0]     PF3_MSI_CAP_NEXTPTR=8'h0
   , parameter           PF0_MSI_CAP_PERVECMASKCAP="FALSE"
   , parameter           PF1_MSI_CAP_PERVECMASKCAP="FALSE"
   , parameter           PF2_MSI_CAP_PERVECMASKCAP="FALSE"
   , parameter           PF3_MSI_CAP_PERVECMASKCAP="FALSE"
   , parameter integer   PF0_MSI_CAP_MULTIMSGCAP=0
   , parameter integer   PF1_MSI_CAP_MULTIMSGCAP=0
   , parameter integer   PF2_MSI_CAP_MULTIMSGCAP=0
   , parameter integer   PF3_MSI_CAP_MULTIMSGCAP=0
   , parameter [7:0]     PF0_MSIX_CAP_NEXTPTR=8'h0
   , parameter [7:0]     PF1_MSIX_CAP_NEXTPTR=8'h0
   , parameter [7:0]     PF2_MSIX_CAP_NEXTPTR=8'h0
   , parameter [7:0]     PF3_MSIX_CAP_NEXTPTR=8'h0
   , parameter [7:0]     VFG0_MSIX_CAP_NEXTPTR=8'h0
   , parameter [7:0]     VFG1_MSIX_CAP_NEXTPTR=8'h0
   , parameter [7:0]     VFG2_MSIX_CAP_NEXTPTR=8'h0
   , parameter [7:0]     VFG3_MSIX_CAP_NEXTPTR=8'h0
   , parameter integer   PF0_MSIX_CAP_PBA_BIR=0
   , parameter integer   PF1_MSIX_CAP_PBA_BIR=0
   , parameter integer   PF2_MSIX_CAP_PBA_BIR=0
   , parameter integer   PF3_MSIX_CAP_PBA_BIR=0
   , parameter integer   VFG0_MSIX_CAP_PBA_BIR=0
   , parameter integer   VFG1_MSIX_CAP_PBA_BIR=0
   , parameter integer   VFG2_MSIX_CAP_PBA_BIR=0
   , parameter integer   VFG3_MSIX_CAP_PBA_BIR=0
   , parameter [28:0]    PF0_MSIX_CAP_PBA_OFFSET=29'h50
   , parameter [28:0]    PF1_MSIX_CAP_PBA_OFFSET=29'h50
   , parameter [28:0]    PF2_MSIX_CAP_PBA_OFFSET=29'h50
   , parameter [28:0]    PF3_MSIX_CAP_PBA_OFFSET=29'h50
   , parameter [28:0]    VFG0_MSIX_CAP_PBA_OFFSET=29'h50
   , parameter [28:0]    VFG1_MSIX_CAP_PBA_OFFSET=29'h50
   , parameter [28:0]    VFG2_MSIX_CAP_PBA_OFFSET=29'h50
   , parameter [28:0]    VFG3_MSIX_CAP_PBA_OFFSET=29'h50
   , parameter integer   PF0_MSIX_CAP_TABLE_BIR=0
   , parameter integer   PF1_MSIX_CAP_TABLE_BIR=0
   , parameter integer   PF2_MSIX_CAP_TABLE_BIR=0
   , parameter integer   PF3_MSIX_CAP_TABLE_BIR=0
   , parameter integer   VFG0_MSIX_CAP_TABLE_BIR=0
   , parameter integer   VFG1_MSIX_CAP_TABLE_BIR=0
   , parameter integer   VFG2_MSIX_CAP_TABLE_BIR=0
   , parameter integer   VFG3_MSIX_CAP_TABLE_BIR=0
   , parameter [28:0]    PF0_MSIX_CAP_TABLE_OFFSET=29'h40
   , parameter [28:0]    PF1_MSIX_CAP_TABLE_OFFSET=29'h40
   , parameter [28:0]    PF2_MSIX_CAP_TABLE_OFFSET=29'h40
   , parameter [28:0]    PF3_MSIX_CAP_TABLE_OFFSET=29'h40
   , parameter [28:0]    VFG0_MSIX_CAP_TABLE_OFFSET=29'h40
   , parameter [28:0]    VFG1_MSIX_CAP_TABLE_OFFSET=29'h40
   , parameter [28:0]    VFG2_MSIX_CAP_TABLE_OFFSET=29'h40
   , parameter [28:0]    VFG3_MSIX_CAP_TABLE_OFFSET=29'h40
   , parameter [10:0]    PF0_MSIX_CAP_TABLE_SIZE=11'h0
   , parameter [10:0]    PF1_MSIX_CAP_TABLE_SIZE=11'h0
   , parameter [10:0]    PF2_MSIX_CAP_TABLE_SIZE=11'h0
   , parameter [10:0]    PF3_MSIX_CAP_TABLE_SIZE=11'h0
   , parameter [10:0]    VFG0_MSIX_CAP_TABLE_SIZE=11'h0
   , parameter [10:0]    VFG1_MSIX_CAP_TABLE_SIZE=11'h0
   , parameter [10:0]    VFG2_MSIX_CAP_TABLE_SIZE=11'h0
   , parameter [10:0]    VFG3_MSIX_CAP_TABLE_SIZE=11'h0
   , parameter [5:0]     PF0_MSIX_VECTOR_COUNT=6'h4
   , parameter [7:0]     PF0_PM_CAP_ID=8'h1
   , parameter [7:0]     PF0_PM_CAP_NEXTPTR=8'h0
   , parameter [7:0]     PF1_PM_CAP_NEXTPTR=8'h0
   , parameter [7:0]     PF2_PM_CAP_NEXTPTR=8'h0
   , parameter [7:0]     PF3_PM_CAP_NEXTPTR=8'h0
   , parameter           PF0_PM_CAP_PMESUPPORT_D3HOT="TRUE"
   , parameter           PF0_PM_CAP_PMESUPPORT_D1="TRUE"
   , parameter           PF0_PM_CAP_PMESUPPORT_D0="TRUE"
   , parameter           PF0_PM_CAP_SUPP_D1_STATE="TRUE"
   , parameter [2:0]     PF0_PM_CAP_VER_ID=3'h3
   , parameter           PF0_PM_CSR_NOSOFTRESET="TRUE"
   , parameter           PM_ENABLE_L23_ENTRY="FALSE"
   , parameter [7:0]     DNSTREAM_LINK_NUM=8'h0
   , parameter           AUTO_FLR_RESPONSE="FALSE"
   , parameter [11:0]    PF0_DSN_CAP_NEXTPTR=12'h10C
   , parameter [11:0]    PF1_DSN_CAP_NEXTPTR=12'h10C
   , parameter [11:0]    PF2_DSN_CAP_NEXTPTR=12'h10C
   , parameter [11:0]    PF3_DSN_CAP_NEXTPTR=12'h10C
   , parameter           DSN_CAP_ENABLE="FALSE"
   , parameter [3:0]     PF0_VC_CAP_VER=4'h1
   , parameter [11:0]    PF0_VC_CAP_NEXTPTR=12'h0
   , parameter           PF0_VC_CAP_ENABLE="FALSE"
   , parameter [11:0]    PF0_SECONDARY_PCIE_CAP_NEXTPTR=12'h0
   , parameter [11:0]    PF0_AER_CAP_NEXTPTR=12'h0
   , parameter [11:0]    PF1_AER_CAP_NEXTPTR=12'h0
   , parameter [11:0]    PF2_AER_CAP_NEXTPTR=12'h0
   , parameter [11:0]    PF3_AER_CAP_NEXTPTR=12'h0
   , parameter           PF0_AER_CAP_ECRC_GEN_AND_CHECK_CAPABLE="FALSE"
   , parameter           ARI_CAP_ENABLE="FALSE"
   , parameter [11:0]    PF0_ARI_CAP_NEXTPTR=12'h0
   , parameter [11:0]    PF1_ARI_CAP_NEXTPTR=12'h0
   , parameter [11:0]    PF2_ARI_CAP_NEXTPTR=12'h0
   , parameter [11:0]    PF3_ARI_CAP_NEXTPTR=12'h0
   , parameter [11:0]    VFG0_ARI_CAP_NEXTPTR=12'h0
   , parameter [11:0]    VFG1_ARI_CAP_NEXTPTR=12'h0
   , parameter [11:0]    VFG2_ARI_CAP_NEXTPTR=12'h0
   , parameter [11:0]    VFG3_ARI_CAP_NEXTPTR=12'h0
   , parameter [3:0]     PF0_ARI_CAP_VER=4'h1
   , parameter [7:0]     PF0_ARI_CAP_NEXT_FUNC=8'h0
   , parameter [7:0]     PF1_ARI_CAP_NEXT_FUNC=8'h0
   , parameter [7:0]     PF2_ARI_CAP_NEXT_FUNC=8'h0
   , parameter [7:0]     PF3_ARI_CAP_NEXT_FUNC=8'h0
   , parameter [11:0]    PF0_LTR_CAP_NEXTPTR=12'h0
   , parameter [3:0]     PF0_LTR_CAP_VER=4'h1
   , parameter [9:0]     PF0_LTR_CAP_MAX_SNOOP_LAT=10'h0
   , parameter [9:0]     PF0_LTR_CAP_MAX_NOSNOOP_LAT=10'h0
   , parameter           LTR_TX_MESSAGE_ON_LTR_ENABLE="FALSE"
   , parameter           LTR_TX_MESSAGE_ON_FUNC_POWER_STATE_CHANGE="FALSE"
   , parameter [9:0]     LTR_TX_MESSAGE_MINIMUM_INTERVAL=10'h250
   , parameter [3:0]     SRIOV_CAP_ENABLE=4'h0
   , parameter [11:0]    PF0_SRIOV_CAP_NEXTPTR=12'h0
   , parameter [11:0]    PF1_SRIOV_CAP_NEXTPTR=12'h0
   , parameter [11:0]    PF2_SRIOV_CAP_NEXTPTR=12'h0
   , parameter [11:0]    PF3_SRIOV_CAP_NEXTPTR=12'h0
   , parameter [3:0]     PF0_SRIOV_CAP_VER=4'h1
   , parameter [3:0]     PF1_SRIOV_CAP_VER=4'h1
   , parameter [3:0]     PF2_SRIOV_CAP_VER=4'h1
   , parameter [3:0]     PF3_SRIOV_CAP_VER=4'h1
   , parameter           PF0_SRIOV_ARI_CAPBL_HIER_PRESERVED="FALSE"
   , parameter           PF1_SRIOV_ARI_CAPBL_HIER_PRESERVED="FALSE"
   , parameter           PF2_SRIOV_ARI_CAPBL_HIER_PRESERVED="FALSE"
   , parameter           PF3_SRIOV_ARI_CAPBL_HIER_PRESERVED="FALSE"
   , parameter [15:0]    PF0_SRIOV_CAP_INITIAL_VF=16'h0
   , parameter [15:0]    PF1_SRIOV_CAP_INITIAL_VF=16'h0
   , parameter [15:0]    PF2_SRIOV_CAP_INITIAL_VF=16'h0
   , parameter [15:0]    PF3_SRIOV_CAP_INITIAL_VF=16'h0
   , parameter [15:0]    PF0_SRIOV_CAP_TOTAL_VF=16'h0
   , parameter [15:0]    PF1_SRIOV_CAP_TOTAL_VF=16'h0
   , parameter [15:0]    PF2_SRIOV_CAP_TOTAL_VF=16'h0
   , parameter [15:0]    PF3_SRIOV_CAP_TOTAL_VF=16'h0
   , parameter [15:0]    PF0_SRIOV_FUNC_DEP_LINK=16'h0
   , parameter [15:0]    PF1_SRIOV_FUNC_DEP_LINK=16'h0
   , parameter [15:0]    PF2_SRIOV_FUNC_DEP_LINK=16'h0
   , parameter [15:0]    PF3_SRIOV_FUNC_DEP_LINK=16'h0
   , parameter [15:0]    PF0_SRIOV_FIRST_VF_OFFSET=16'h0
   , parameter [15:0]    PF1_SRIOV_FIRST_VF_OFFSET=16'h0
   , parameter [15:0]    PF2_SRIOV_FIRST_VF_OFFSET=16'h0
   , parameter [15:0]    PF3_SRIOV_FIRST_VF_OFFSET=16'h0
   , parameter [15:0]    PF0_SRIOV_VF_DEVICE_ID=16'h0
   , parameter [15:0]    PF1_SRIOV_VF_DEVICE_ID=16'h0
   , parameter [15:0]    PF2_SRIOV_VF_DEVICE_ID=16'h0
   , parameter [15:0]    PF3_SRIOV_VF_DEVICE_ID=16'h0
   , parameter [31:0]    PF0_SRIOV_SUPPORTED_PAGE_SIZE=32'h0
   , parameter [31:0]    PF1_SRIOV_SUPPORTED_PAGE_SIZE=32'h0
   , parameter [31:0]    PF2_SRIOV_SUPPORTED_PAGE_SIZE=32'h0
   , parameter [31:0]    PF3_SRIOV_SUPPORTED_PAGE_SIZE=32'h0
   , parameter [2:0]     PF0_SRIOV_BAR0_CONTROL=3'b100
   , parameter [2:0]     PF1_SRIOV_BAR0_CONTROL=3'b100
   , parameter [2:0]     PF2_SRIOV_BAR0_CONTROL=3'b100
   , parameter [2:0]     PF3_SRIOV_BAR0_CONTROL=3'b100
   , parameter [5:0]     PF0_SRIOV_BAR0_APERTURE_SIZE=6'b000011
   , parameter [5:0]     PF1_SRIOV_BAR0_APERTURE_SIZE=6'b000011
   , parameter [5:0]     PF2_SRIOV_BAR0_APERTURE_SIZE=6'b000011
   , parameter [5:0]     PF3_SRIOV_BAR0_APERTURE_SIZE=6'b000011
   , parameter [2:0]     PF0_SRIOV_BAR1_CONTROL=3'b0
   , parameter [2:0]     PF1_SRIOV_BAR1_CONTROL=3'b0
   , parameter [2:0]     PF2_SRIOV_BAR1_CONTROL=3'b0
   , parameter [2:0]     PF3_SRIOV_BAR1_CONTROL=3'b0
   , parameter [4:0]     PF0_SRIOV_BAR1_APERTURE_SIZE=5'b0
   , parameter [4:0]     PF1_SRIOV_BAR1_APERTURE_SIZE=5'b0
   , parameter [4:0]     PF2_SRIOV_BAR1_APERTURE_SIZE=5'b0
   , parameter [4:0]     PF3_SRIOV_BAR1_APERTURE_SIZE=5'b0
   , parameter [2:0]     PF0_SRIOV_BAR2_CONTROL=3'b100
   , parameter [2:0]     PF1_SRIOV_BAR2_CONTROL=3'b100
   , parameter [2:0]     PF2_SRIOV_BAR2_CONTROL=3'b100
   , parameter [2:0]     PF3_SRIOV_BAR2_CONTROL=3'b100
   , parameter [5:0]     PF0_SRIOV_BAR2_APERTURE_SIZE=6'b000011
   , parameter [5:0]     PF1_SRIOV_BAR2_APERTURE_SIZE=6'b000011
   , parameter [5:0]     PF2_SRIOV_BAR2_APERTURE_SIZE=6'b000011
   , parameter [5:0]     PF3_SRIOV_BAR2_APERTURE_SIZE=6'b000011
   , parameter [2:0]     PF0_SRIOV_BAR3_CONTROL=3'b0
   , parameter [2:0]     PF1_SRIOV_BAR3_CONTROL=3'b0
   , parameter [2:0]     PF2_SRIOV_BAR3_CONTROL=3'b0
   , parameter [2:0]     PF3_SRIOV_BAR3_CONTROL=3'b0
   , parameter [4:0]     PF0_SRIOV_BAR3_APERTURE_SIZE=5'b00011
   , parameter [4:0]     PF1_SRIOV_BAR3_APERTURE_SIZE=5'b00011
   , parameter [4:0]     PF2_SRIOV_BAR3_APERTURE_SIZE=5'b00011
   , parameter [4:0]     PF3_SRIOV_BAR3_APERTURE_SIZE=5'b00011
   , parameter [2:0]     PF0_SRIOV_BAR4_CONTROL=3'b100
   , parameter [2:0]     PF1_SRIOV_BAR4_CONTROL=3'b100
   , parameter [2:0]     PF2_SRIOV_BAR4_CONTROL=3'b100
   , parameter [2:0]     PF3_SRIOV_BAR4_CONTROL=3'b100
   , parameter [5:0]     PF0_SRIOV_BAR4_APERTURE_SIZE=6'b000011
   , parameter [5:0]     PF1_SRIOV_BAR4_APERTURE_SIZE=6'b000011
   , parameter [5:0]     PF2_SRIOV_BAR4_APERTURE_SIZE=6'b000011
   , parameter [5:0]     PF3_SRIOV_BAR4_APERTURE_SIZE=6'b000011
   , parameter [2:0]     PF0_SRIOV_BAR5_CONTROL=3'b0
   , parameter [2:0]     PF1_SRIOV_BAR5_CONTROL=3'b0
   , parameter [2:0]     PF2_SRIOV_BAR5_CONTROL=3'b0
   , parameter [2:0]     PF3_SRIOV_BAR5_CONTROL=3'b0
   , parameter [4:0]     PF0_SRIOV_BAR5_APERTURE_SIZE=5'b00011
   , parameter [4:0]     PF1_SRIOV_BAR5_APERTURE_SIZE=5'b00011
   , parameter [4:0]     PF2_SRIOV_BAR5_APERTURE_SIZE=5'b00011
   , parameter [4:0]     PF3_SRIOV_BAR5_APERTURE_SIZE=5'b00011
   , parameter [11:0]    PF0_TPHR_CAP_NEXTPTR=12'h0
   , parameter [11:0]    PF1_TPHR_CAP_NEXTPTR=12'h0
   , parameter [11:0]    PF2_TPHR_CAP_NEXTPTR=12'h0
   , parameter [11:0]    PF3_TPHR_CAP_NEXTPTR=12'h0
   , parameter [11:0]    VFG0_TPHR_CAP_NEXTPTR=12'h0
   , parameter [11:0]    VFG1_TPHR_CAP_NEXTPTR=12'h0
   , parameter [11:0]    VFG2_TPHR_CAP_NEXTPTR=12'h0
   , parameter [11:0]    VFG3_TPHR_CAP_NEXTPTR=12'h0
   , parameter [3:0]     PF0_TPHR_CAP_VER=4'h1
   , parameter           PF0_TPHR_CAP_INT_VEC_MODE="TRUE"
   , parameter           PF0_TPHR_CAP_DEV_SPECIFIC_MODE="TRUE"
   , parameter [1:0]     PF0_TPHR_CAP_ST_TABLE_LOC=2'h0
   , parameter [10:0]    PF0_TPHR_CAP_ST_TABLE_SIZE=11'h0
   , parameter [2:0]     PF0_TPHR_CAP_ST_MODE_SEL=3'h0
   , parameter [2:0]     PF1_TPHR_CAP_ST_MODE_SEL=3'h0
   , parameter [2:0]     PF2_TPHR_CAP_ST_MODE_SEL=3'h0
   , parameter [2:0]     PF3_TPHR_CAP_ST_MODE_SEL=3'h0
   , parameter [2:0]     VFG0_TPHR_CAP_ST_MODE_SEL=3'h0
   , parameter [2:0]     VFG1_TPHR_CAP_ST_MODE_SEL=3'h0
   , parameter [2:0]     VFG2_TPHR_CAP_ST_MODE_SEL=3'h0
   , parameter [2:0]     VFG3_TPHR_CAP_ST_MODE_SEL=3'h0
   , parameter           PF0_TPHR_CAP_ENABLE="FALSE"
   , parameter           TPH_TO_RAM_PIPELINE="FALSE"
   , parameter           TPH_FROM_RAM_PIPELINE="FALSE"
   , parameter           MCAP_ENABLE="FALSE"
   , parameter           MCAP_CONFIGURE_OVERRIDE="FALSE"
   , parameter [11:0]    MCAP_CAP_NEXTPTR=12'h0
   , parameter [15:0]    MCAP_VSEC_ID=16'h0
   , parameter [3:0]     MCAP_VSEC_REV=4'h0
   , parameter [11:0]    MCAP_VSEC_LEN=12'h2C
   , parameter [31:0]    MCAP_FPGA_BITSTREAM_VERSION=32'h0
   , parameter           MCAP_INTERRUPT_ON_MCAP_EOS="FALSE"
   , parameter           MCAP_INTERRUPT_ON_MCAP_ERROR="FALSE"
   , parameter           MCAP_INPUT_GATE_DESIGN_SWITCH="FALSE"
   , parameter           MCAP_EOS_DESIGN_SWITCH="FALSE"
   , parameter           MCAP_GATE_MEM_ENABLE_DESIGN_SWITCH="FALSE"
   , parameter           MCAP_GATE_IO_ENABLE_DESIGN_SWITCH="FALSE"
   , parameter [31:0]    SIM_JTAG_IDCODE=32'h0
   , parameter [7:0]     DEBUG_AXIST_DISABLE_FEATURE_BIT=8'h0
   , parameter           DEBUG_TL_DISABLE_RX_TLP_ORDER_CHECKS="FALSE"
   , parameter           DEBUG_TL_DISABLE_FC_TIMEOUT="FALSE"
   , parameter           DEBUG_PL_DISABLE_SCRAMBLING="FALSE"
   , parameter           DEBUG_PL_DISABLE_REC_ENTRY_ON_DYNAMIC_DSKEW_FAIL ="FALSE"
   , parameter           DEBUG_PL_DISABLE_REC_ENTRY_ON_RX_BUFFER_UNDER_OVER_FLOW ="FALSE"
   , parameter           DEBUG_PL_DISABLE_LES_UPDATE_ON_SKP_ERROR="FALSE"
   , parameter           DEBUG_PL_DISABLE_LES_UPDATE_ON_SKP_PARITY_ERROR="FALSE"
   , parameter           DEBUG_PL_DISABLE_LES_UPDATE_ON_DEFRAMER_ERROR="FALSE"
   , parameter           DEBUG_PL_SIM_RESET_LFSR="FALSE"
   , parameter [15:0]    DEBUG_PL_SPARE=16'h0
   , parameter [15:0]    DEBUG_LL_SPARE=16'h0
   , parameter [15:0]    DEBUG_TL_SPARE=16'h0
   , parameter [15:0]    DEBUG_AXI4ST_SPARE=16'h0
   , parameter [15:0]    DEBUG_CFG_SPARE=16'h0
   , parameter [3:0]     DEBUG_CAR_SPARE=4'h0
   , parameter           TEST_MODE_PIN_CHAR="FALSE"
   , parameter           SPARE_BIT0="FALSE"
   , parameter           SPARE_BIT1=1'b0
   , parameter           SPARE_BIT2=1'b0
   , parameter           SPARE_BIT3="FALSE"
   , parameter           SPARE_BIT4=1'b0
   , parameter           SPARE_BIT5=1'b0
   , parameter           SPARE_BIT6=1'b0
   , parameter           SPARE_BIT7=1'b0
   , parameter           SPARE_BIT8=1'b0
   , parameter [7:0]     SPARE_BYTE0=8'h0
   , parameter [7:0]     SPARE_BYTE1=8'h0
   , parameter [7:0]     SPARE_BYTE2=8'h0
   , parameter [7:0]     SPARE_BYTE3=8'h0
   , parameter [31:0]    SPARE_WORD0=32'h0
   , parameter [31:0]    SPARE_WORD1=32'h0
   , parameter [31:0]    SPARE_WORD2=32'h0
   , parameter [31:0]    SPARE_WORD3=32'h0
  ) (
    input  wire [1:0]     pipe_rx00_char_is_k
   ,input  wire [1:0]     pipe_rx01_char_is_k
   ,input  wire [1:0]     pipe_rx02_char_is_k
   ,input  wire [1:0]     pipe_rx03_char_is_k
   ,input  wire [1:0]     pipe_rx04_char_is_k
   ,input  wire [1:0]     pipe_rx05_char_is_k
   ,input  wire [1:0]     pipe_rx06_char_is_k
   ,input  wire [1:0]     pipe_rx07_char_is_k
   ,input  wire [1:0]     pipe_rx08_char_is_k
   ,input  wire [1:0]     pipe_rx09_char_is_k
   ,input  wire [1:0]     pipe_rx10_char_is_k
   ,input  wire [1:0]     pipe_rx11_char_is_k
   ,input  wire [1:0]     pipe_rx12_char_is_k
   ,input  wire [1:0]     pipe_rx13_char_is_k
   ,input  wire [1:0]     pipe_rx14_char_is_k
   ,input  wire [1:0]     pipe_rx15_char_is_k
   ,input  wire           pipe_rx00_valid
   ,input  wire           pipe_rx01_valid
   ,input  wire           pipe_rx02_valid
   ,input  wire           pipe_rx03_valid
   ,input  wire           pipe_rx04_valid
   ,input  wire           pipe_rx05_valid
   ,input  wire           pipe_rx06_valid
   ,input  wire           pipe_rx07_valid
   ,input  wire           pipe_rx08_valid
   ,input  wire           pipe_rx09_valid
   ,input  wire           pipe_rx10_valid
   ,input  wire           pipe_rx11_valid
   ,input  wire           pipe_rx12_valid
   ,input  wire           pipe_rx13_valid
   ,input  wire           pipe_rx14_valid
   ,input  wire           pipe_rx15_valid
   ,input  wire [31:0]    pipe_rx00_data
   ,input  wire [31:0]    pipe_rx01_data
   ,input  wire [31:0]    pipe_rx02_data
   ,input  wire [31:0]    pipe_rx03_data
   ,input  wire [31:0]    pipe_rx04_data
   ,input  wire [31:0]    pipe_rx05_data
   ,input  wire [31:0]    pipe_rx06_data
   ,input  wire [31:0]    pipe_rx07_data
   ,input  wire [31:0]    pipe_rx08_data
   ,input  wire [31:0]    pipe_rx09_data
   ,input  wire [31:0]    pipe_rx10_data
   ,input  wire [31:0]    pipe_rx11_data
   ,input  wire [31:0]    pipe_rx12_data
   ,input  wire [31:0]    pipe_rx13_data
   ,input  wire [31:0]    pipe_rx14_data
   ,input  wire [31:0]    pipe_rx15_data
   ,output wire           pipe_rx00_polarity
   ,output wire           pipe_rx01_polarity
   ,output wire           pipe_rx02_polarity
   ,output wire           pipe_rx03_polarity
   ,output wire           pipe_rx04_polarity
   ,output wire           pipe_rx05_polarity
   ,output wire           pipe_rx06_polarity
   ,output wire           pipe_rx07_polarity
   ,output wire           pipe_rx08_polarity
   ,output wire           pipe_rx09_polarity
   ,output wire           pipe_rx10_polarity
   ,output wire           pipe_rx11_polarity
   ,output wire           pipe_rx12_polarity
   ,output wire           pipe_rx13_polarity
   ,output wire           pipe_rx14_polarity
   ,output wire           pipe_rx15_polarity
   ,input  wire [2:0]     pipe_rx00_status
   ,input  wire [2:0]     pipe_rx01_status
   ,input  wire [2:0]     pipe_rx02_status
   ,input  wire [2:0]     pipe_rx03_status
   ,input  wire [2:0]     pipe_rx04_status
   ,input  wire [2:0]     pipe_rx05_status
   ,input  wire [2:0]     pipe_rx06_status
   ,input  wire [2:0]     pipe_rx07_status
   ,input  wire [2:0]     pipe_rx08_status
   ,input  wire [2:0]     pipe_rx09_status
   ,input  wire [2:0]     pipe_rx10_status
   ,input  wire [2:0]     pipe_rx11_status
   ,input  wire [2:0]     pipe_rx12_status
   ,input  wire [2:0]     pipe_rx13_status
   ,input  wire [2:0]     pipe_rx14_status
   ,input  wire [2:0]     pipe_rx15_status
   ,input  wire           pipe_rx00_phy_status
   ,input  wire           pipe_rx01_phy_status
   ,input  wire           pipe_rx02_phy_status
   ,input  wire           pipe_rx03_phy_status
   ,input  wire           pipe_rx04_phy_status
   ,input  wire           pipe_rx05_phy_status
   ,input  wire           pipe_rx06_phy_status
   ,input  wire           pipe_rx07_phy_status
   ,input  wire           pipe_rx08_phy_status
   ,input  wire           pipe_rx09_phy_status
   ,input  wire           pipe_rx10_phy_status
   ,input  wire           pipe_rx11_phy_status
   ,input  wire           pipe_rx12_phy_status
   ,input  wire           pipe_rx13_phy_status
   ,input  wire           pipe_rx14_phy_status
   ,input  wire           pipe_rx15_phy_status
   ,input  wire           pipe_rx00_elec_idle
   ,input  wire           pipe_rx01_elec_idle
   ,input  wire           pipe_rx02_elec_idle
   ,input  wire           pipe_rx03_elec_idle
   ,input  wire           pipe_rx04_elec_idle
   ,input  wire           pipe_rx05_elec_idle
   ,input  wire           pipe_rx06_elec_idle
   ,input  wire           pipe_rx07_elec_idle
   ,input  wire           pipe_rx08_elec_idle
   ,input  wire           pipe_rx09_elec_idle
   ,input  wire           pipe_rx10_elec_idle
   ,input  wire           pipe_rx11_elec_idle
   ,input  wire           pipe_rx12_elec_idle
   ,input  wire           pipe_rx13_elec_idle
   ,input  wire           pipe_rx14_elec_idle
   ,input  wire           pipe_rx15_elec_idle
   ,input  wire           pipe_rx00_data_valid
   ,input  wire           pipe_rx01_data_valid
   ,input  wire           pipe_rx02_data_valid
   ,input  wire           pipe_rx03_data_valid
   ,input  wire           pipe_rx04_data_valid
   ,input  wire           pipe_rx05_data_valid
   ,input  wire           pipe_rx06_data_valid
   ,input  wire           pipe_rx07_data_valid
   ,input  wire           pipe_rx08_data_valid
   ,input  wire           pipe_rx09_data_valid
   ,input  wire           pipe_rx10_data_valid
   ,input  wire           pipe_rx11_data_valid
   ,input  wire           pipe_rx12_data_valid
   ,input  wire           pipe_rx13_data_valid
   ,input  wire           pipe_rx14_data_valid
   ,input  wire           pipe_rx15_data_valid
   ,input  wire [1:0]     pipe_rx00_start_block
   ,input  wire [1:0]     pipe_rx01_start_block
   ,input  wire [1:0]     pipe_rx02_start_block
   ,input  wire [1:0]     pipe_rx03_start_block
   ,input  wire [1:0]     pipe_rx04_start_block
   ,input  wire [1:0]     pipe_rx05_start_block
   ,input  wire [1:0]     pipe_rx06_start_block
   ,input  wire [1:0]     pipe_rx07_start_block
   ,input  wire [1:0]     pipe_rx08_start_block
   ,input  wire [1:0]     pipe_rx09_start_block
   ,input  wire [1:0]     pipe_rx10_start_block
   ,input  wire [1:0]     pipe_rx11_start_block
   ,input  wire [1:0]     pipe_rx12_start_block
   ,input  wire [1:0]     pipe_rx13_start_block
   ,input  wire [1:0]     pipe_rx14_start_block
   ,input  wire [1:0]     pipe_rx15_start_block
   ,input  wire [1:0]     pipe_rx00_sync_header
   ,input  wire [1:0]     pipe_rx01_sync_header
   ,input  wire [1:0]     pipe_rx02_sync_header
   ,input  wire [1:0]     pipe_rx03_sync_header
   ,input  wire [1:0]     pipe_rx04_sync_header
   ,input  wire [1:0]     pipe_rx05_sync_header
   ,input  wire [1:0]     pipe_rx06_sync_header
   ,input  wire [1:0]     pipe_rx07_sync_header
   ,input  wire [1:0]     pipe_rx08_sync_header
   ,input  wire [1:0]     pipe_rx09_sync_header
   ,input  wire [1:0]     pipe_rx10_sync_header
   ,input  wire [1:0]     pipe_rx11_sync_header
   ,input  wire [1:0]     pipe_rx12_sync_header
   ,input  wire [1:0]     pipe_rx13_sync_header
   ,input  wire [1:0]     pipe_rx14_sync_header
   ,input  wire [1:0]     pipe_rx15_sync_header
   ,output wire           pipe_tx00_compliance
   ,output wire           pipe_tx01_compliance
   ,output wire           pipe_tx02_compliance
   ,output wire           pipe_tx03_compliance
   ,output wire           pipe_tx04_compliance
   ,output wire           pipe_tx05_compliance
   ,output wire           pipe_tx06_compliance
   ,output wire           pipe_tx07_compliance
   ,output wire           pipe_tx08_compliance
   ,output wire           pipe_tx09_compliance
   ,output wire           pipe_tx10_compliance
   ,output wire           pipe_tx11_compliance
   ,output wire           pipe_tx12_compliance
   ,output wire           pipe_tx13_compliance
   ,output wire           pipe_tx14_compliance
   ,output wire           pipe_tx15_compliance
   ,output wire [1:0]     pipe_tx00_char_is_k
   ,output wire [1:0]     pipe_tx01_char_is_k
   ,output wire [1:0]     pipe_tx02_char_is_k
   ,output wire [1:0]     pipe_tx03_char_is_k
   ,output wire [1:0]     pipe_tx04_char_is_k
   ,output wire [1:0]     pipe_tx05_char_is_k
   ,output wire [1:0]     pipe_tx06_char_is_k
   ,output wire [1:0]     pipe_tx07_char_is_k
   ,output wire [1:0]     pipe_tx08_char_is_k
   ,output wire [1:0]     pipe_tx09_char_is_k
   ,output wire [1:0]     pipe_tx10_char_is_k
   ,output wire [1:0]     pipe_tx11_char_is_k
   ,output wire [1:0]     pipe_tx12_char_is_k
   ,output wire [1:0]     pipe_tx13_char_is_k
   ,output wire [1:0]     pipe_tx14_char_is_k
   ,output wire [1:0]     pipe_tx15_char_is_k
   ,output wire [31:0]    pipe_tx00_data
   ,output wire [31:0]    pipe_tx01_data
   ,output wire [31:0]    pipe_tx02_data
   ,output wire [31:0]    pipe_tx03_data
   ,output wire [31:0]    pipe_tx04_data
   ,output wire [31:0]    pipe_tx05_data
   ,output wire [31:0]    pipe_tx06_data
   ,output wire [31:0]    pipe_tx07_data
   ,output wire [31:0]    pipe_tx08_data
   ,output wire [31:0]    pipe_tx09_data
   ,output wire [31:0]    pipe_tx10_data
   ,output wire [31:0]    pipe_tx11_data
   ,output wire [31:0]    pipe_tx12_data
   ,output wire [31:0]    pipe_tx13_data
   ,output wire [31:0]    pipe_tx14_data
   ,output wire [31:0]    pipe_tx15_data
   ,output wire           pipe_tx00_elec_idle
   ,output wire           pipe_tx01_elec_idle
   ,output wire           pipe_tx02_elec_idle
   ,output wire           pipe_tx03_elec_idle
   ,output wire           pipe_tx04_elec_idle
   ,output wire           pipe_tx05_elec_idle
   ,output wire           pipe_tx06_elec_idle
   ,output wire           pipe_tx07_elec_idle
   ,output wire           pipe_tx08_elec_idle
   ,output wire           pipe_tx09_elec_idle
   ,output wire           pipe_tx10_elec_idle
   ,output wire           pipe_tx11_elec_idle
   ,output wire           pipe_tx12_elec_idle
   ,output wire           pipe_tx13_elec_idle
   ,output wire           pipe_tx14_elec_idle
   ,output wire           pipe_tx15_elec_idle
   ,output wire [1:0]     pipe_tx00_powerdown
   ,output wire [1:0]     pipe_tx01_powerdown
   ,output wire [1:0]     pipe_tx02_powerdown
   ,output wire [1:0]     pipe_tx03_powerdown
   ,output wire [1:0]     pipe_tx04_powerdown
   ,output wire [1:0]     pipe_tx05_powerdown
   ,output wire [1:0]     pipe_tx06_powerdown
   ,output wire [1:0]     pipe_tx07_powerdown
   ,output wire [1:0]     pipe_tx08_powerdown
   ,output wire [1:0]     pipe_tx09_powerdown
   ,output wire [1:0]     pipe_tx10_powerdown
   ,output wire [1:0]     pipe_tx11_powerdown
   ,output wire [1:0]     pipe_tx12_powerdown
   ,output wire [1:0]     pipe_tx13_powerdown
   ,output wire [1:0]     pipe_tx14_powerdown
   ,output wire [1:0]     pipe_tx15_powerdown
   ,output wire           pipe_tx00_data_valid
   ,output wire           pipe_tx01_data_valid
   ,output wire           pipe_tx02_data_valid
   ,output wire           pipe_tx03_data_valid
   ,output wire           pipe_tx04_data_valid
   ,output wire           pipe_tx05_data_valid
   ,output wire           pipe_tx06_data_valid
   ,output wire           pipe_tx07_data_valid
   ,output wire           pipe_tx08_data_valid
   ,output wire           pipe_tx09_data_valid
   ,output wire           pipe_tx10_data_valid
   ,output wire           pipe_tx11_data_valid
   ,output wire           pipe_tx12_data_valid
   ,output wire           pipe_tx13_data_valid
   ,output wire           pipe_tx14_data_valid
   ,output wire           pipe_tx15_data_valid
   ,output wire           pipe_tx00_start_block
   ,output wire           pipe_tx01_start_block
   ,output wire           pipe_tx02_start_block
   ,output wire           pipe_tx03_start_block
   ,output wire           pipe_tx04_start_block
   ,output wire           pipe_tx05_start_block
   ,output wire           pipe_tx06_start_block
   ,output wire           pipe_tx07_start_block
   ,output wire           pipe_tx08_start_block
   ,output wire           pipe_tx09_start_block
   ,output wire           pipe_tx10_start_block
   ,output wire           pipe_tx11_start_block
   ,output wire           pipe_tx12_start_block
   ,output wire           pipe_tx13_start_block
   ,output wire           pipe_tx14_start_block
   ,output wire           pipe_tx15_start_block
   ,output wire [1:0]     pipe_tx00_sync_header
   ,output wire [1:0]     pipe_tx01_sync_header
   ,output wire [1:0]     pipe_tx02_sync_header
   ,output wire [1:0]     pipe_tx03_sync_header
   ,output wire [1:0]     pipe_tx04_sync_header
   ,output wire [1:0]     pipe_tx05_sync_header
   ,output wire [1:0]     pipe_tx06_sync_header
   ,output wire [1:0]     pipe_tx07_sync_header
   ,output wire [1:0]     pipe_tx08_sync_header
   ,output wire [1:0]     pipe_tx09_sync_header
   ,output wire [1:0]     pipe_tx10_sync_header
   ,output wire [1:0]     pipe_tx11_sync_header
   ,output wire [1:0]     pipe_tx12_sync_header
   ,output wire [1:0]     pipe_tx13_sync_header
   ,output wire [1:0]     pipe_tx14_sync_header
   ,output wire [1:0]     pipe_tx15_sync_header
   ,output wire [1:0]     pipe_rx00_eq_control
   ,output wire [1:0]     pipe_rx01_eq_control
   ,output wire [1:0]     pipe_rx02_eq_control
   ,output wire [1:0]     pipe_rx03_eq_control
   ,output wire [1:0]     pipe_rx04_eq_control
   ,output wire [1:0]     pipe_rx05_eq_control
   ,output wire [1:0]     pipe_rx06_eq_control
   ,output wire [1:0]     pipe_rx07_eq_control
   ,output wire [1:0]     pipe_rx08_eq_control
   ,output wire [1:0]     pipe_rx09_eq_control
   ,output wire [1:0]     pipe_rx10_eq_control
   ,output wire [1:0]     pipe_rx11_eq_control
   ,output wire [1:0]     pipe_rx12_eq_control
   ,output wire [1:0]     pipe_rx13_eq_control
   ,output wire [1:0]     pipe_rx14_eq_control
   ,output wire [1:0]     pipe_rx15_eq_control
   ,input  wire           pipe_rx00_eq_lp_lf_fs_sel
   ,input  wire           pipe_rx01_eq_lp_lf_fs_sel
   ,input  wire           pipe_rx02_eq_lp_lf_fs_sel
   ,input  wire           pipe_rx03_eq_lp_lf_fs_sel
   ,input  wire           pipe_rx04_eq_lp_lf_fs_sel
   ,input  wire           pipe_rx05_eq_lp_lf_fs_sel
   ,input  wire           pipe_rx06_eq_lp_lf_fs_sel
   ,input  wire           pipe_rx07_eq_lp_lf_fs_sel
   ,input  wire           pipe_rx08_eq_lp_lf_fs_sel
   ,input  wire           pipe_rx09_eq_lp_lf_fs_sel
   ,input  wire           pipe_rx10_eq_lp_lf_fs_sel
   ,input  wire           pipe_rx11_eq_lp_lf_fs_sel
   ,input  wire           pipe_rx12_eq_lp_lf_fs_sel
   ,input  wire           pipe_rx13_eq_lp_lf_fs_sel
   ,input  wire           pipe_rx14_eq_lp_lf_fs_sel
   ,input  wire           pipe_rx15_eq_lp_lf_fs_sel
   ,input  wire [17:0]    pipe_rx00_eq_lp_new_tx_coeff_or_preset
   ,input  wire [17:0]    pipe_rx01_eq_lp_new_tx_coeff_or_preset
   ,input  wire [17:0]    pipe_rx02_eq_lp_new_tx_coeff_or_preset
   ,input  wire [17:0]    pipe_rx03_eq_lp_new_tx_coeff_or_preset
   ,input  wire [17:0]    pipe_rx04_eq_lp_new_tx_coeff_or_preset
   ,input  wire [17:0]    pipe_rx05_eq_lp_new_tx_coeff_or_preset
   ,input  wire [17:0]    pipe_rx06_eq_lp_new_tx_coeff_or_preset
   ,input  wire [17:0]    pipe_rx07_eq_lp_new_tx_coeff_or_preset
   ,input  wire [17:0]    pipe_rx08_eq_lp_new_tx_coeff_or_preset
   ,input  wire [17:0]    pipe_rx09_eq_lp_new_tx_coeff_or_preset
   ,input  wire [17:0]    pipe_rx10_eq_lp_new_tx_coeff_or_preset
   ,input  wire [17:0]    pipe_rx11_eq_lp_new_tx_coeff_or_preset
   ,input  wire [17:0]    pipe_rx12_eq_lp_new_tx_coeff_or_preset
   ,input  wire [17:0]    pipe_rx13_eq_lp_new_tx_coeff_or_preset
   ,input  wire [17:0]    pipe_rx14_eq_lp_new_tx_coeff_or_preset
   ,input  wire [17:0]    pipe_rx15_eq_lp_new_tx_coeff_or_preset
   ,input  wire           pipe_rx00_eq_lp_adapt_done
   ,input  wire           pipe_rx01_eq_lp_adapt_done
   ,input  wire           pipe_rx02_eq_lp_adapt_done
   ,input  wire           pipe_rx03_eq_lp_adapt_done
   ,input  wire           pipe_rx04_eq_lp_adapt_done
   ,input  wire           pipe_rx05_eq_lp_adapt_done
   ,input  wire           pipe_rx06_eq_lp_adapt_done
   ,input  wire           pipe_rx07_eq_lp_adapt_done
   ,input  wire           pipe_rx08_eq_lp_adapt_done
   ,input  wire           pipe_rx09_eq_lp_adapt_done
   ,input  wire           pipe_rx10_eq_lp_adapt_done
   ,input  wire           pipe_rx11_eq_lp_adapt_done
   ,input  wire           pipe_rx12_eq_lp_adapt_done
   ,input  wire           pipe_rx13_eq_lp_adapt_done
   ,input  wire           pipe_rx14_eq_lp_adapt_done
   ,input  wire           pipe_rx15_eq_lp_adapt_done
   ,input  wire           pipe_rx00_eq_done
   ,input  wire           pipe_rx01_eq_done
   ,input  wire           pipe_rx02_eq_done
   ,input  wire           pipe_rx03_eq_done
   ,input  wire           pipe_rx04_eq_done
   ,input  wire           pipe_rx05_eq_done
   ,input  wire           pipe_rx06_eq_done
   ,input  wire           pipe_rx07_eq_done
   ,input  wire           pipe_rx08_eq_done
   ,input  wire           pipe_rx09_eq_done
   ,input  wire           pipe_rx10_eq_done
   ,input  wire           pipe_rx11_eq_done
   ,input  wire           pipe_rx12_eq_done
   ,input  wire           pipe_rx13_eq_done
   ,input  wire           pipe_rx14_eq_done
   ,input  wire           pipe_rx15_eq_done
   ,output wire [1:0]     pipe_tx00_eq_control
   ,output wire [1:0]     pipe_tx01_eq_control
   ,output wire [1:0]     pipe_tx02_eq_control
   ,output wire [1:0]     pipe_tx03_eq_control
   ,output wire [1:0]     pipe_tx04_eq_control
   ,output wire [1:0]     pipe_tx05_eq_control
   ,output wire [1:0]     pipe_tx06_eq_control
   ,output wire [1:0]     pipe_tx07_eq_control
   ,output wire [1:0]     pipe_tx08_eq_control
   ,output wire [1:0]     pipe_tx09_eq_control
   ,output wire [1:0]     pipe_tx10_eq_control
   ,output wire [1:0]     pipe_tx11_eq_control
   ,output wire [1:0]     pipe_tx12_eq_control
   ,output wire [1:0]     pipe_tx13_eq_control
   ,output wire [1:0]     pipe_tx14_eq_control
   ,output wire [1:0]     pipe_tx15_eq_control
   ,output wire [5:0]     pipe_tx00_eq_deemph
   ,output wire [5:0]     pipe_tx01_eq_deemph
   ,output wire [5:0]     pipe_tx02_eq_deemph
   ,output wire [5:0]     pipe_tx03_eq_deemph
   ,output wire [5:0]     pipe_tx04_eq_deemph
   ,output wire [5:0]     pipe_tx05_eq_deemph
   ,output wire [5:0]     pipe_tx06_eq_deemph
   ,output wire [5:0]     pipe_tx07_eq_deemph
   ,output wire [5:0]     pipe_tx08_eq_deemph
   ,output wire [5:0]     pipe_tx09_eq_deemph
   ,output wire [5:0]     pipe_tx10_eq_deemph
   ,output wire [5:0]     pipe_tx11_eq_deemph
   ,output wire [5:0]     pipe_tx12_eq_deemph
   ,output wire [5:0]     pipe_tx13_eq_deemph
   ,output wire [5:0]     pipe_tx14_eq_deemph
   ,output wire [5:0]     pipe_tx15_eq_deemph
   ,input  wire [17:0]    pipe_tx00_eq_coeff
   ,input  wire [17:0]    pipe_tx01_eq_coeff
   ,input  wire [17:0]    pipe_tx02_eq_coeff
   ,input  wire [17:0]    pipe_tx03_eq_coeff
   ,input  wire [17:0]    pipe_tx04_eq_coeff
   ,input  wire [17:0]    pipe_tx05_eq_coeff
   ,input  wire [17:0]    pipe_tx06_eq_coeff
   ,input  wire [17:0]    pipe_tx07_eq_coeff
   ,input  wire [17:0]    pipe_tx08_eq_coeff
   ,input  wire [17:0]    pipe_tx09_eq_coeff
   ,input  wire [17:0]    pipe_tx10_eq_coeff
   ,input  wire [17:0]    pipe_tx11_eq_coeff
   ,input  wire [17:0]    pipe_tx12_eq_coeff
   ,input  wire [17:0]    pipe_tx13_eq_coeff
   ,input  wire [17:0]    pipe_tx14_eq_coeff
   ,input  wire [17:0]    pipe_tx15_eq_coeff
   ,input  wire           pipe_tx00_eq_done
   ,input  wire           pipe_tx01_eq_done
   ,input  wire           pipe_tx02_eq_done
   ,input  wire           pipe_tx03_eq_done
   ,input  wire           pipe_tx04_eq_done
   ,input  wire           pipe_tx05_eq_done
   ,input  wire           pipe_tx06_eq_done
   ,input  wire           pipe_tx07_eq_done
   ,input  wire           pipe_tx08_eq_done
   ,input  wire           pipe_tx09_eq_done
   ,input  wire           pipe_tx10_eq_done
   ,input  wire           pipe_tx11_eq_done
   ,input  wire           pipe_tx12_eq_done
   ,input  wire           pipe_tx13_eq_done
   ,input  wire           pipe_tx14_eq_done
   ,input  wire           pipe_tx15_eq_done
   ,output wire [3:0]     pipe_rx_eq_lp_tx_preset
   ,output wire [5:0]     pipe_rx_eq_lp_lf_fs
   ,output wire           pipe_tx_rcvr_det
   ,output wire [1:0]     pipe_tx_rate
   ,output wire           pipe_tx_deemph
   ,output wire [2:0]     pipe_tx_margin
   ,output wire           pipe_tx_swing
   ,output wire           pipe_tx_reset
   ,input  wire [5:0]     pipe_eq_fs
   ,input  wire [5:0]     pipe_eq_lf
   ,input  wire           pl_gen2_upstream_prefer_deemph
   ,output wire           pl_eq_in_progress
   ,output wire [1:0]     pl_eq_phase
   ,input  wire           pl_eq_reset_eieos_count
   ,input  wire           pl_redo_eq
   ,input  wire           pl_redo_eq_speed
   ,output wire           pl_eq_mismatch
   ,output wire           pl_redo_eq_pending
   ,output wire [AXI4_DATA_WIDTH-1:0] m_axis_cq_tdata
   ,input  wire [AXI4_DATA_WIDTH-1:0] s_axis_cc_tdata
   ,input  wire [AXI4_DATA_WIDTH-1:0] s_axis_rq_tdata
   ,output wire [AXI4_DATA_WIDTH-1:0] m_axis_rc_tdata
   ,output wire [AXI4_CQ_TUSER_WIDTH-1:0] m_axis_cq_tuser
   ,input  wire [AXI4_CC_TUSER_WIDTH-1:0] s_axis_cc_tuser
   ,output wire           m_axis_cq_tlast
   ,input  wire           s_axis_rq_tlast
   ,output wire           m_axis_rc_tlast
   ,input  wire           s_axis_cc_tlast
   ,input  wire [1:0]     pcie_cq_np_req
   ,output wire [5:0]     pcie_cq_np_req_count
   ,input  wire [AXI4_RQ_TUSER_WIDTH-1:0] s_axis_rq_tuser
   ,output wire [AXI4_RC_TUSER_WIDTH-1:0] m_axis_rc_tuser
   ,output wire [AXI4_TKEEP_WIDTH-1:0] m_axis_cq_tkeep
   ,input  wire [AXI4_TKEEP_WIDTH-1:0] s_axis_cc_tkeep
   ,input  wire [AXI4_TKEEP_WIDTH-1:0] s_axis_rq_tkeep
   ,output wire [AXI4_TKEEP_WIDTH-1:0] m_axis_rc_tkeep
   ,output wire           m_axis_cq_tvalid
   ,input  wire           s_axis_cc_tvalid
   ,input  wire           s_axis_rq_tvalid
   ,output wire           m_axis_rc_tvalid
   ,input  wire [AXI4_CQ_TREADY_WIDTH-1:0] m_axis_cq_tready
   ,output wire [AXI4_CC_TREADY_WIDTH-1:0] s_axis_cc_tready
   ,output wire [AXI4_RQ_TREADY_WIDTH-1:0] s_axis_rq_tready
   ,input  wire [AXI4_RC_TREADY_WIDTH-1:0] m_axis_rc_tready
   ,output wire [5:0]     pcie_rq_seq_num0
   ,output wire           pcie_rq_seq_num_vld0
   ,output wire [5:0]     pcie_rq_seq_num1
   ,output wire           pcie_rq_seq_num_vld1
   ,output wire [7:0]     pcie_rq_tag0
   ,output wire           pcie_rq_tag_vld0
   ,output wire [7:0]     pcie_rq_tag1
   ,output wire           pcie_rq_tag_vld1
   ,output wire [3:0]     pcie_tfc_nph_av
   ,output wire [3:0]     pcie_tfc_npd_av
   ,output wire [3:0]     pcie_rq_tag_av
   ,output wire [7:0]     axi_user_out
   ,input  wire [7:0]     axi_user_in
   ,input  wire [9:0]     cfg_mgmt_addr
   ,input  wire [7:0]     cfg_mgmt_function_number
   ,input  wire           cfg_mgmt_write
   ,input  wire [31:0]    cfg_mgmt_write_data
   ,input  wire [3:0]     cfg_mgmt_byte_enable
   ,input  wire           cfg_mgmt_read
   ,output wire [31:0]    cfg_mgmt_read_data
   ,output wire           cfg_mgmt_read_write_done
   ,input  wire           cfg_mgmt_debug_access
   ,output wire           cfg_phy_link_down
   ,output wire [1:0]     cfg_phy_link_status
   ,output wire [2:0]     cfg_negotiated_width
   ,output wire [1:0]     cfg_current_speed
   ,output wire [1:0]     cfg_max_payload
   ,output wire [2:0]     cfg_max_read_req
   ,output wire [15:0]    cfg_function_status
   ,output wire [11:0]    cfg_function_power_state
   ,output wire [1:0]     cfg_link_power_state
   ,output wire           cfg_err_cor_out
   ,output wire           cfg_err_nonfatal_out
   ,output wire           cfg_err_fatal_out
   ,output wire           cfg_local_error_valid
   ,output wire [4:0]     cfg_local_error_out
   ,output wire           cfg_ltr_enable
   ,output wire [5:0]     cfg_ltssm_state
   ,output wire [1:0]     cfg_rx_pm_state
   ,output wire [1:0]     cfg_tx_pm_state
   ,output wire [3:0]     cfg_rcb_status
   ,output wire [1:0]     cfg_obff_enable
   ,output wire           cfg_pl_status_change
   ,output wire [3:0]     cfg_tph_requester_enable
   ,output wire [11:0]    cfg_tph_st_mode
   ,output wire           cfg_msg_received
   ,output wire [7:0]     cfg_msg_received_data
   ,output wire [4:0]     cfg_msg_received_type
   ,input  wire           cfg_msg_transmit
   ,input  wire [2:0]     cfg_msg_transmit_type
   ,input  wire [31:0]    cfg_msg_transmit_data
   ,output wire           cfg_msg_transmit_done
   ,output wire [7:0]     cfg_fc_ph
   ,output wire [11:0]    cfg_fc_pd
   ,output wire [7:0]     cfg_fc_nph
   ,output wire [11:0]    cfg_fc_npd
   ,output wire [7:0]     cfg_fc_cplh
   ,output wire [11:0]    cfg_fc_cpld
   ,input  wire [2:0]     cfg_fc_sel
   ,input  wire           cfg_hot_reset_in
   ,output wire           cfg_hot_reset_out
   ,input  wire           cfg_config_space_enable
   ,input  wire [63:0]    cfg_dsn
   ,input  wire [15:0]    cfg_dev_id_pf0
   ,input  wire [15:0]    cfg_dev_id_pf1
   ,input  wire [15:0]    cfg_dev_id_pf2
   ,input  wire [15:0]    cfg_dev_id_pf3
   ,input  wire [15:0]    cfg_vend_id
   ,input  wire [7:0]     cfg_rev_id_pf0
   ,input  wire [7:0]     cfg_rev_id_pf1
   ,input  wire [7:0]     cfg_rev_id_pf2
   ,input  wire [7:0]     cfg_rev_id_pf3
   ,input  wire [15:0]    cfg_subsys_id_pf0
   ,input  wire [15:0]    cfg_subsys_id_pf1
   ,input  wire [15:0]    cfg_subsys_id_pf2
   ,input  wire [15:0]    cfg_subsys_id_pf3
   ,input  wire [15:0]    cfg_subsys_vend_id
   ,input  wire [7:0]     cfg_ds_port_number
   ,input  wire [7:0]     cfg_ds_bus_number
   ,input  wire [4:0]     cfg_ds_device_number
   ,input  wire [2:0]     cfg_ds_function_number
   ,output wire [7:0]     cfg_bus_number
   ,input  wire           cfg_power_state_change_ack
   ,output wire           cfg_power_state_change_interrupt
   ,input  wire           cfg_err_cor_in
   ,input  wire           cfg_err_uncor_in
   ,input  wire [3:0]     cfg_flr_done
   ,output wire [3:0]     cfg_flr_in_process
   ,input  wire           cfg_req_pm_transition_l23_ready
   ,input  wire           cfg_link_training_enable
   ,input  wire [3:0]     cfg_interrupt_int
   ,output wire           cfg_interrupt_sent
   ,input  wire [3:0]     cfg_interrupt_pending
   ,output wire [3:0]     cfg_interrupt_msi_enable
   ,input  wire [31:0]    cfg_interrupt_msi_int
   ,output wire           cfg_interrupt_msi_sent
   ,output wire           cfg_interrupt_msi_fail
   ,output wire [11:0]    cfg_interrupt_msi_mmenable
   ,input  wire [31:0]    cfg_interrupt_msi_pending_status
   ,input  wire [1:0]     cfg_interrupt_msi_pending_status_function_num
   ,input  wire           cfg_interrupt_msi_pending_status_data_enable
   ,output wire           cfg_interrupt_msi_mask_update
   ,input  wire [1:0]     cfg_interrupt_msi_select
   ,output wire [31:0]    cfg_interrupt_msi_data
   ,output wire [3:0]     cfg_interrupt_msix_enable
   ,output wire [3:0]     cfg_interrupt_msix_mask
   ,input  wire [63:0]    cfg_interrupt_msix_address
   ,input  wire [31:0]    cfg_interrupt_msix_data
   ,input  wire           cfg_interrupt_msix_int
   ,input  wire [1:0]     cfg_interrupt_msix_vec_pending
   ,output wire           cfg_interrupt_msix_vec_pending_status
   ,input  wire [2:0]     cfg_interrupt_msi_attr
   ,input  wire           cfg_interrupt_msi_tph_present
   ,input  wire [1:0]     cfg_interrupt_msi_tph_type
   ,input  wire [7:0]     cfg_interrupt_msi_tph_st_tag
   ,input  wire [7:0]     cfg_interrupt_msi_function_number
   ,output wire           cfg_ext_read_received
   ,output wire           cfg_ext_write_received
   ,output wire [9:0]     cfg_ext_register_number
   ,output wire [7:0]     cfg_ext_function_number
   ,output wire [31:0]    cfg_ext_write_data
   ,output wire [3:0]     cfg_ext_write_byte_enable
   ,input  wire [31:0]    cfg_ext_read_data
   ,input  wire           cfg_ext_read_data_valid
   ,output wire [251:0]   cfg_vf_flr_in_process
   ,input  wire [7:0]     cfg_vf_flr_func_num
   ,input  wire           cfg_vf_flr_done
   ,output wire [503:0]   cfg_vf_status
   ,output wire [755:0]   cfg_vf_power_state
   ,output wire [251:0]   cfg_vf_tph_requester_enable
   ,output wire [755:0]   cfg_vf_tph_st_mode
   ,output wire [251:0]   cfg_interrupt_msix_vf_enable
   ,output wire [251:0]   cfg_interrupt_msix_vf_mask
   ,input  wire           cfg_pm_aspm_l1_entry_reject
   ,input  wire           cfg_pm_aspm_tx_l0s_entry_disable
   ,input  wire [7:0]     user_tph_stt_func_num
   ,input  wire [5:0]     user_tph_stt_index
   ,input  wire           user_tph_stt_rd_en
   ,output wire [7:0]     user_tph_stt_rd_data
   ,input  wire [1:0]     conf_req_type
   ,input  wire [3:0]     conf_req_reg_num
   ,input  wire [31:0]    conf_req_data
   ,input  wire           conf_req_valid
   ,output wire           conf_req_ready
   ,output wire [31:0]    conf_resp_rdata
   ,output wire           conf_resp_valid
   ,output wire           conf_mcap_design_switch
   ,output wire           conf_mcap_eos
   ,output wire           conf_mcap_in_use_by_pcie
   ,input  wire           conf_mcap_request_by_conf
   ,input  wire           drp_clk
   ,input  wire           drp_en
   ,input  wire           drp_we
   ,input  wire [9:0]     drp_addr
   ,input  wire [15:0]    drp_di
   ,output wire           drp_rdy
   ,output wire [15:0]    drp_do

   ,input  wire           pipe_clk
   ,input  wire           core_clk
   ,input  wire           user_clk
   ,input  wire           user_clk2
   ,output wire           user_clk_en
   ,input  wire           mcap_clk
   ,input  wire           mcap_rst_b
   ,output wire           pcie_perst0_b
   ,output wire           pcie_perst1_b
   ,input  wire           phy_rdy 
  );

  // localparams
  
  localparam [10:0]      MSIX_CAP_TABLE_SIZE = PF0_MSIX_CAP_TABLE_SIZE +
                                               PF1_MSIX_CAP_TABLE_SIZE +
                                               PF2_MSIX_CAP_TABLE_SIZE +
                                               PF3_MSIX_CAP_TABLE_SIZE +
                                               VFG0_MSIX_CAP_TABLE_SIZE +
                                               VFG1_MSIX_CAP_TABLE_SIZE +
                                               VFG2_MSIX_CAP_TABLE_SIZE +
                                               VFG3_MSIX_CAP_TABLE_SIZE;
  localparam             MSIX_TABLE_RAM_ENABLE = AXISTEN_IF_ENABLE_INTERNAL_MSIX_TABLE;


  // Resets
  
  wire                        reset_n;
  wire                        mgmt_reset_n;
  wire                        mgmt_sticky_reset_n;
  wire                        pipe_reset_n;
  wire                        user_clkgate_en;
  wire                        pipe_clkgate_en;
  wire                        user_clk_en_to_e4;
  wire                        user_clk_to_e4;
  wire                        user_clk2_to_e4;
  wire                        pipe_clk_to_e4;
  wire                        cfg_phy_link_down_wire;
  wire                        cfg_phy_link_down_user_clk;

  wire [31:0]                 pipe_tx00_data_out;
  wire [31:0]                 pipe_tx01_data_out;
  wire [31:0]                 pipe_tx02_data_out;
  wire [31:0]                 pipe_tx03_data_out;
  wire [31:0]                 pipe_tx04_data_out;
  wire [31:0]                 pipe_tx05_data_out;
  wire [31:0]                 pipe_tx06_data_out;
  wire [31:0]                 pipe_tx07_data_out;
  wire [31:0]                 pipe_tx08_data_out;
  wire [31:0]                 pipe_tx09_data_out;
  wire [31:0]                 pipe_tx10_data_out;
  wire [31:0]                 pipe_tx11_data_out;
  wire [31:0]                 pipe_tx12_data_out;
  wire [31:0]                 pipe_tx13_data_out;
  wire [31:0]                 pipe_tx14_data_out;
  wire [31:0]                 pipe_tx15_data_out;

  assign cfg_phy_link_down = cfg_phy_link_down_wire;

generate if (IMPL_TARGET=="SOFT" || IMPL_TARGET=="PROTO") begin

   // no clock gating case for soft or hard
   assign user_clk_en_to_e4  = user_clk_en;
   assign user_clk_to_e4     = user_clk;
   assign user_clk2_to_e4    = user_clk2;
   assign pipe_clk_to_e4     = pipe_clk;   

end else begin

   // clock gating case for soft or hard
   assign user_clk_en_to_e4  = user_clkgate_en;
   assign user_clk_to_e4     = 1'b0;
   assign user_clk2_to_e4    = 1'b0;
   assign pipe_clk_to_e4     = pipe_clk;   // pipe clock gating not yet included

end
endgenerate

    assign pipe_tx00_data = pipe_tx00_data_out; 
    assign pipe_tx01_data = pipe_tx01_data_out;
    assign pipe_tx02_data = pipe_tx02_data_out;
    assign pipe_tx03_data = pipe_tx03_data_out;
    assign pipe_tx04_data = pipe_tx04_data_out;
    assign pipe_tx05_data = pipe_tx05_data_out;
    assign pipe_tx06_data = pipe_tx06_data_out;
    assign pipe_tx07_data = pipe_tx07_data_out;
    assign pipe_tx08_data = pipe_tx08_data_out;
    assign pipe_tx09_data = pipe_tx09_data_out;
    assign pipe_tx10_data = pipe_tx10_data_out;
    assign pipe_tx11_data = pipe_tx11_data_out;
    assign pipe_tx12_data = pipe_tx12_data_out;
    assign pipe_tx13_data = pipe_tx13_data_out;
    assign pipe_tx14_data = pipe_tx14_data_out;
    assign pipe_tx15_data = pipe_tx15_data_out;
     
 
  // Memory Interfaces

  wire [8:0]                  mi_replay_ram_address0;
  wire [8:0]                  mi_replay_ram_address1;
  wire [127:0]                mi_replay_ram_write_data0;
  wire                        mi_replay_ram_write_enable0;
  wire [127:0]                mi_replay_ram_write_data1;
  wire                        mi_replay_ram_write_enable1;
  wire [127:0]                mi_replay_ram_read_data0;
  wire                        mi_replay_ram_read_enable0;
  wire [127:0]                mi_replay_ram_read_data1;
  wire                        mi_replay_ram_read_enable1;
  wire [5:0]                  mi_replay_ram_err_cor;
  wire [5:0]                  mi_replay_ram_err_uncor;
  wire [8:0]                  mi_rx_posted_request_ram_write_address0;
  wire [143:0]                mi_rx_posted_request_ram_write_data0;
  wire                        mi_rx_posted_request_ram_write_enable0;
  wire [8:0]                  mi_rx_posted_request_ram_write_address1;
  wire [143:0]                mi_rx_posted_request_ram_write_data1;
  wire                        mi_rx_posted_request_ram_write_enable1;
  wire [8:0]                  mi_rx_posted_request_ram_read_address0;
  wire [143:0]                mi_rx_posted_request_ram_read_data0;
  wire                        mi_rx_posted_request_ram_read_enable0;
  wire [8:0]                  mi_rx_posted_request_ram_read_address1;
  wire [143:0]                mi_rx_posted_request_ram_read_data1;
  wire                        mi_rx_posted_request_ram_read_enable1;
  wire [5:0]                  mi_rx_posted_request_ram_err_cor;
  wire [5:0]                  mi_rx_posted_request_ram_err_uncor;
  wire [8:0]                  mi_rx_completion_ram_write_address0;
  wire [143:0]                mi_rx_completion_ram_write_data0;
  wire [1:0]                  mi_rx_completion_ram_write_enable0;
  wire [8:0]                  mi_rx_completion_ram_write_address1;
  wire [143:0]                mi_rx_completion_ram_write_data1;
  wire [1:0]                  mi_rx_completion_ram_write_enable1;
  wire [8:0]                  mi_rx_completion_ram_read_address0;
  wire [143:0]                mi_rx_completion_ram_read_data0;
  wire [1:0]                  mi_rx_completion_ram_read_enable0;
  wire [8:0]                  mi_rx_completion_ram_read_address1;
  wire [143:0]                mi_rx_completion_ram_read_data1;
  wire [1:0]                  mi_rx_completion_ram_read_enable1;
  wire [11:0]                 mi_rx_completion_ram_err_cor;
  wire [11:0]                 mi_rx_completion_ram_err_uncor;
  wire [11:0]                 cfg_tph_ram_address;
  wire [35:0]                 cfg_tph_ram_write_data;
  wire [3:0]                  cfg_tph_ram_write_byte_enable;
  wire [35:0]                 cfg_tph_ram_read_data;
  wire                        cfg_tph_ram_read_enable;
  wire [12:0]                 cfg_msix_ram_address;
  wire [35:0]                 cfg_msix_ram_write_data;
  wire [3:0]                  cfg_msix_ram_write_byte_enable;
  wire [35:0]                 cfg_msix_ram_read_data;
  wire                        cfg_msix_ram_read_enable;
 
  // Driven by soft logic
  wire                        pcie_posted_req_delivered;
  wire                        pcie_cq_pipeline_empty;
  wire                        pcie_cq_np_user_credit_rcvd;
  wire [1:0]                  pcie_compl_delivered;
  wire [7:0]                  pcie_compl_delivered_tag0;
  wire [7:0]                  pcie_compl_delivered_tag1;

  // Wires from Hard Block AXI Stream Interface to Soft Bridge
  wire [255:0]                m_axis_cq_tdata_int;
  wire [87:0]                 m_axis_cq_tuser_int;
  wire                        m_axis_cq_tlast_int;
  wire [7:0]                  m_axis_cq_tkeep_int;
  wire                        m_axis_cq_tvalid_int;
        
  wire [255:0]                s_axis_cc_tdata_int;
  wire [32:0]                 s_axis_cc_tuser_int;
  wire                        s_axis_cc_tlast_int;
  wire [7:0]                  s_axis_cc_tkeep_int;
  wire                        s_axis_cc_tvalid_int;

  wire [255:0]                s_axis_rq_tdata_int;
  wire [61:0]                 s_axis_rq_tuser_int;
  wire                        s_axis_rq_tlast_int;
  wire [7:0]                  s_axis_rq_tkeep_int;
  wire                        s_axis_rq_tvalid_int;

  wire [255:0]                m_axis_rc_tdata_int;
  wire [74:0]                 m_axis_rc_tuser_int;
  wire                        m_axis_rc_tlast_int;
  wire [7:0]                  m_axis_rc_tkeep_int;
  wire                        m_axis_rc_tvalid_int;

  wire [255:0]                s_axis_cc_tdata_axi512;
  wire [32:0]                 s_axis_cc_tuser_axi512;
  wire                        s_axis_cc_tlast_axi512;
  wire [7:0]                  s_axis_cc_tkeep_axi512;
  wire                        s_axis_cc_tvalid_axi512;

  wire [255:0]                s_axis_rq_tdata_axi512;
  wire [61:0]                 s_axis_rq_tuser_axi512;
  wire                        s_axis_rq_tlast_axi512;
  wire [7:0]                  s_axis_rq_tkeep_axi512;
  wire                        s_axis_rq_tvalid_axi512;

  wire [21:0]                 m_axis_cq_tready_int;
  wire [21:0]                 m_axis_rc_tready_int;
  wire [21:0]                 m_axis_cq_tready_axi512;
  wire [21:0]                 m_axis_rc_tready_axi512;
  wire [3:0]                  s_axis_cc_tready_int;
  wire                        s_axis_cc_tready_axi512;
  wire [3:0]                  s_axis_rq_tready_int;
  wire                        s_axis_rq_tready_axi512;

  wire [5:0]                  pcie_cq_np_req_count_int;
  wire [5:0]                  pcie_cq_np_req_count_axi512;

  wire                        pl_gen34_redo_equalization;
  wire                        pl_gen34_redo_eq_speed;
  wire                        pl_gen34_eq_mismatch;

  wire [5:0]     pcie_rq_seq_num0_cc;
  wire           pcie_rq_seq_num_vld0_cc;




  PCIE40E4 #(

    .CRM_CORE_CLK_FREQ_500(CRM_CORE_CLK_FREQ_500)
   ,.CRM_USER_CLK_FREQ(CRM_USER_CLK_FREQ)
   ,.SIM_DEVICE(SIM_DEVICE)
   ,.AXISTEN_IF_WIDTH(AXISTEN_IF_WIDTH)
   ,.AXISTEN_IF_EXT_512(AXISTEN_IF_EXT_512)
   ,.AXISTEN_IF_EXT_512_CQ_STRADDLE(AXISTEN_IF_EXT_512_CQ_STRADDLE)
   ,.AXISTEN_IF_EXT_512_CC_STRADDLE(AXISTEN_IF_EXT_512_CC_STRADDLE)
   ,.AXISTEN_IF_EXT_512_RQ_STRADDLE(AXISTEN_IF_EXT_512_RQ_STRADDLE)
   ,.AXISTEN_IF_EXT_512_RC_STRADDLE(AXISTEN_IF_EXT_512_RC_STRADDLE)
   ,.AXISTEN_IF_CQ_ALIGNMENT_MODE(AXISTEN_IF_CQ_ALIGNMENT_MODE)
   ,.AXISTEN_IF_CC_ALIGNMENT_MODE(AXISTEN_IF_CC_ALIGNMENT_MODE)
   ,.AXISTEN_IF_RQ_ALIGNMENT_MODE(AXISTEN_IF_RQ_ALIGNMENT_MODE)
   ,.AXISTEN_IF_RC_ALIGNMENT_MODE(AXISTEN_IF_RC_ALIGNMENT_MODE)
   ,.AXISTEN_IF_RC_STRADDLE(AXISTEN_IF_RC_STRADDLE)
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
   ,.PL_EQ_BYPASS_PHASE23(PL_EQ_BYPASS_PHASE23)
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
   ,.PL_SIM_FAST_LINK_TRAINING(PL_SIM_FAST_LINK_TRAINING)
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
   ,.HEADER_TYPE_OVERRIDE(HEADER_TYPE_OVERRIDE)
   ,.PF0_LINK_CONTROL_RCB(PF0_LINK_CONTROL_RCB)
   ,.PF0_DEV_CAP_MAX_PAYLOAD_SIZE(PF0_DEV_CAP_MAX_PAYLOAD_SIZE)
   ,.PF1_DEV_CAP_MAX_PAYLOAD_SIZE(PF1_DEV_CAP_MAX_PAYLOAD_SIZE)
   ,.PF2_DEV_CAP_MAX_PAYLOAD_SIZE(PF2_DEV_CAP_MAX_PAYLOAD_SIZE)
   ,.PF3_DEV_CAP_MAX_PAYLOAD_SIZE(PF3_DEV_CAP_MAX_PAYLOAD_SIZE)
   ,.PF0_DEV_CAP_EXT_TAG_SUPPORTED(PF0_DEV_CAP_EXT_TAG_SUPPORTED)
   ,.PF0_DEV_CAP_ENDPOINT_L0S_LATENCY(PF0_DEV_CAP_ENDPOINT_L0S_LATENCY)
   ,.PF0_DEV_CAP_ENDPOINT_L1_LATENCY(PF0_DEV_CAP_ENDPOINT_L1_LATENCY)
   ,.PF0_DEV_CAP_FUNCTION_LEVEL_RESET_CAPABLE(PF0_DEV_CAP_FUNCTION_LEVEL_RESET_CAPABLE)
   ,.PF0_LINK_CAP_ASPM_SUPPORT(PF0_LINK_CAP_ASPM_SUPPORT)
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
   ,.PF0_MSIX_CAP_PBA_OFFSET(PF0_MSIX_CAP_PBA_OFFSET)
   ,.PF1_MSIX_CAP_PBA_OFFSET(PF1_MSIX_CAP_PBA_OFFSET)
   ,.PF2_MSIX_CAP_PBA_OFFSET(PF2_MSIX_CAP_PBA_OFFSET)
   ,.PF3_MSIX_CAP_PBA_OFFSET(PF3_MSIX_CAP_PBA_OFFSET)
   ,.VFG0_MSIX_CAP_PBA_OFFSET(VFG0_MSIX_CAP_PBA_OFFSET)
   ,.VFG1_MSIX_CAP_PBA_OFFSET(VFG1_MSIX_CAP_PBA_OFFSET)
   ,.VFG2_MSIX_CAP_PBA_OFFSET(VFG2_MSIX_CAP_PBA_OFFSET)
   ,.VFG3_MSIX_CAP_PBA_OFFSET(VFG3_MSIX_CAP_PBA_OFFSET)
   ,.PF0_MSIX_CAP_TABLE_BIR(PF0_MSIX_CAP_TABLE_BIR)
   ,.PF1_MSIX_CAP_TABLE_BIR(PF1_MSIX_CAP_TABLE_BIR)
   ,.PF2_MSIX_CAP_TABLE_BIR(PF2_MSIX_CAP_TABLE_BIR)
   ,.PF3_MSIX_CAP_TABLE_BIR(PF3_MSIX_CAP_TABLE_BIR)
   ,.VFG0_MSIX_CAP_TABLE_BIR(VFG0_MSIX_CAP_TABLE_BIR)
   ,.VFG1_MSIX_CAP_TABLE_BIR(VFG1_MSIX_CAP_TABLE_BIR)
   ,.VFG2_MSIX_CAP_TABLE_BIR(VFG2_MSIX_CAP_TABLE_BIR)
   ,.VFG3_MSIX_CAP_TABLE_BIR(VFG3_MSIX_CAP_TABLE_BIR)
   ,.PF0_MSIX_CAP_TABLE_OFFSET(PF0_MSIX_CAP_TABLE_OFFSET)
   ,.PF1_MSIX_CAP_TABLE_OFFSET(PF1_MSIX_CAP_TABLE_OFFSET)
   ,.PF2_MSIX_CAP_TABLE_OFFSET(PF2_MSIX_CAP_TABLE_OFFSET)
   ,.PF3_MSIX_CAP_TABLE_OFFSET(PF3_MSIX_CAP_TABLE_OFFSET)
   ,.VFG0_MSIX_CAP_TABLE_OFFSET(VFG0_MSIX_CAP_TABLE_OFFSET)
   ,.VFG1_MSIX_CAP_TABLE_OFFSET(VFG1_MSIX_CAP_TABLE_OFFSET)
   ,.VFG2_MSIX_CAP_TABLE_OFFSET(VFG2_MSIX_CAP_TABLE_OFFSET)
   ,.VFG3_MSIX_CAP_TABLE_OFFSET(VFG3_MSIX_CAP_TABLE_OFFSET)
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
   ,.SPARE_BIT0(AXISTEN_IF_RQ_CC_REGISTERED_TREADY)
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

  ) pcie_4_0_e4_inst ( 
//
// GEN4 SPEED Code
//
    .AXIUSERIN(axi_user_in[7:0])
   ,.AXIUSEROUT(axi_user_out[7:0])
   ,.CFGBUSNUMBER(cfg_bus_number[7:0])
   ,.CFGCONFIGSPACEENABLE(cfg_config_space_enable)
   ,.CFGCURRENTSPEED(cfg_current_speed[1:0])
   ,.CFGDEVIDPF0(cfg_dev_id_pf0[15:0])
   ,.CFGDEVIDPF1(cfg_dev_id_pf1[15:0])
   ,.CFGDEVIDPF2(cfg_dev_id_pf2[15:0])
   ,.CFGDEVIDPF3(cfg_dev_id_pf3[15:0])
   ,.CFGDSBUSNUMBER(cfg_ds_bus_number[7:0])
   ,.CFGDSDEVICENUMBER(cfg_ds_device_number[4:0])
   ,.CFGDSFUNCTIONNUMBER(cfg_ds_function_number[2:0])
   ,.CFGDSN(cfg_dsn[63:0])
   ,.CFGDSPORTNUMBER(cfg_ds_port_number[7:0])
   ,.CFGERRCORIN(cfg_err_cor_in)
   ,.CFGERRCOROUT(cfg_err_cor_out)
   ,.CFGERRFATALOUT(cfg_err_fatal_out)
   ,.CFGERRNONFATALOUT(cfg_err_nonfatal_out)
   ,.CFGERRUNCORIN(cfg_err_uncor_in)
   ,.CFGEXTFUNCTIONNUMBER(cfg_ext_function_number[7:0])
   ,.CFGEXTREADDATA(cfg_ext_read_data[31:0])
   ,.CFGEXTREADDATAVALID(cfg_ext_read_data_valid)
   ,.CFGEXTREADRECEIVED(cfg_ext_read_received)
   ,.CFGEXTREGISTERNUMBER(cfg_ext_register_number[9:0])
   ,.CFGEXTWRITEBYTEENABLE(cfg_ext_write_byte_enable[3:0])
   ,.CFGEXTWRITEDATA(cfg_ext_write_data[31:0])
   ,.CFGEXTWRITERECEIVED(cfg_ext_write_received)
   ,.CFGFCCPLD(cfg_fc_cpld[11:0])
   ,.CFGFCCPLH(cfg_fc_cplh[7:0])
   ,.CFGFCNPD(cfg_fc_npd[11:0])
   ,.CFGFCNPH(cfg_fc_nph[7:0])
   ,.CFGFCPD(cfg_fc_pd[11:0])
   ,.CFGFCPH(cfg_fc_ph[7:0])
   ,.CFGFCSEL(cfg_fc_sel[2:0])
   ,.CFGFLRDONE(cfg_flr_done[3:0])
   ,.CFGFLRINPROCESS(cfg_flr_in_process[3:0])
   ,.CFGFUNCTIONPOWERSTATE(cfg_function_power_state[11:0])
   ,.CFGFUNCTIONSTATUS(cfg_function_status[15:0])
   ,.CFGHOTRESETIN(cfg_hot_reset_in)
   ,.CFGHOTRESETOUT(cfg_hot_reset_out)
   ,.CFGINTERRUPTINT(cfg_interrupt_int[3:0])
   ,.CFGINTERRUPTMSIATTR(cfg_interrupt_msi_attr[2:0])
   ,.CFGINTERRUPTMSIDATA(cfg_interrupt_msi_data[31:0])
   ,.CFGINTERRUPTMSIENABLE(cfg_interrupt_msi_enable[3:0])
   ,.CFGINTERRUPTMSIFAIL(cfg_interrupt_msi_fail)
   ,.CFGINTERRUPTMSIFUNCTIONNUMBER(cfg_interrupt_msi_function_number[7:0])
   ,.CFGINTERRUPTMSIINT(cfg_interrupt_msi_int[31:0])
   ,.CFGINTERRUPTMSIMASKUPDATE(cfg_interrupt_msi_mask_update)
   ,.CFGINTERRUPTMSIMMENABLE(cfg_interrupt_msi_mmenable[11:0])
   ,.CFGINTERRUPTMSIPENDINGSTATUS(cfg_interrupt_msi_pending_status[31:0])
   ,.CFGINTERRUPTMSIPENDINGSTATUSDATAENABLE(cfg_interrupt_msi_pending_status_data_enable)
   ,.CFGINTERRUPTMSIPENDINGSTATUSFUNCTIONNUM(cfg_interrupt_msi_pending_status_function_num[1:0])
   ,.CFGINTERRUPTMSISELECT(cfg_interrupt_msi_select[1:0])
   ,.CFGINTERRUPTMSISENT(cfg_interrupt_msi_sent)
   ,.CFGINTERRUPTMSITPHPRESENT(cfg_interrupt_msi_tph_present)
   ,.CFGINTERRUPTMSITPHSTTAG(cfg_interrupt_msi_tph_st_tag[7:0])
   ,.CFGINTERRUPTMSITPHTYPE(cfg_interrupt_msi_tph_type[1:0])
   ,.CFGINTERRUPTMSIXADDRESS(cfg_interrupt_msix_address[63:0])
   ,.CFGINTERRUPTMSIXDATA(cfg_interrupt_msix_data[31:0])
   ,.CFGINTERRUPTMSIXENABLE(cfg_interrupt_msix_enable[3:0])
   ,.CFGINTERRUPTMSIXINT(cfg_interrupt_msix_int)
   ,.CFGINTERRUPTMSIXMASK(cfg_interrupt_msix_mask[3:0])
   ,.CFGINTERRUPTMSIXVECPENDING(cfg_interrupt_msix_vec_pending[1:0])
   ,.CFGINTERRUPTMSIXVECPENDINGSTATUS(cfg_interrupt_msix_vec_pending_status)
   ,.CFGINTERRUPTPENDING(cfg_interrupt_pending[3:0])
   ,.CFGINTERRUPTSENT(cfg_interrupt_sent)
   ,.CFGLINKPOWERSTATE(cfg_link_power_state[1:0])
   ,.CFGLINKTRAININGENABLE(cfg_link_training_enable)
   ,.CFGLOCALERROROUT(cfg_local_error_out[4:0])
   ,.CFGLOCALERRORVALID(cfg_local_error_valid)
   ,.CFGLTRENABLE(cfg_ltr_enable)
   ,.CFGLTSSMSTATE(cfg_ltssm_state[5:0])
   ,.CFGMAXPAYLOAD(cfg_max_payload[1:0])
   ,.CFGMAXREADREQ(cfg_max_read_req[2:0])
   ,.CFGMGMTADDR(cfg_mgmt_addr[9:0])
   ,.CFGMGMTBYTEENABLE(cfg_mgmt_byte_enable[3:0])
   ,.CFGMGMTDEBUGACCESS(cfg_mgmt_debug_access)
   ,.CFGMGMTFUNCTIONNUMBER(cfg_mgmt_function_number[7:0])
   ,.CFGMGMTREAD(cfg_mgmt_read)
   ,.CFGMGMTREADDATA(cfg_mgmt_read_data[31:0])
   ,.CFGMGMTREADWRITEDONE(cfg_mgmt_read_write_done)
   ,.CFGMGMTWRITE(cfg_mgmt_write)
   ,.CFGMGMTWRITEDATA(cfg_mgmt_write_data[31:0])
   ,.CFGMSGRECEIVED(cfg_msg_received)
   ,.CFGMSGRECEIVEDDATA(cfg_msg_received_data[7:0])
   ,.CFGMSGRECEIVEDTYPE(cfg_msg_received_type[4:0])
   ,.CFGMSGTRANSMIT(cfg_msg_transmit)
   ,.CFGMSGTRANSMITDATA(cfg_msg_transmit_data[31:0])
   ,.CFGMSGTRANSMITDONE(cfg_msg_transmit_done)
   ,.CFGMSGTRANSMITTYPE(cfg_msg_transmit_type[2:0])
   ,.CFGMSIXRAMADDRESS(cfg_msix_ram_address[12:0])
   ,.CFGMSIXRAMREADDATA(cfg_msix_ram_read_data[35:0])
   ,.CFGMSIXRAMREADENABLE(cfg_msix_ram_read_enable)
   ,.CFGMSIXRAMWRITEBYTEENABLE(cfg_msix_ram_write_byte_enable[3:0])
   ,.CFGMSIXRAMWRITEDATA(cfg_msix_ram_write_data[35:0])
   ,.CFGNEGOTIATEDWIDTH(cfg_negotiated_width[2:0])
   ,.CFGOBFFENABLE(cfg_obff_enable[1:0])
   ,.CFGPHYLINKDOWN(cfg_phy_link_down_wire)
   ,.CFGPHYLINKSTATUS(cfg_phy_link_status[1:0])
   ,.CFGPLSTATUSCHANGE(cfg_pl_status_change)
   ,.CFGPMASPML1ENTRYREJECT(cfg_pm_aspm_l1_entry_reject)
   ,.CFGPMASPMTXL0SENTRYDISABLE(cfg_pm_aspm_tx_l0s_entry_disable)
   ,.CFGPOWERSTATECHANGEACK(cfg_power_state_change_ack)
   ,.CFGPOWERSTATECHANGEINTERRUPT(cfg_power_state_change_interrupt)
   ,.CFGRCBSTATUS(cfg_rcb_status[3:0])
   ,.CFGREQPMTRANSITIONL23READY(cfg_req_pm_transition_l23_ready)
   ,.CFGREVIDPF0(cfg_rev_id_pf0[7:0])
   ,.CFGREVIDPF1(cfg_rev_id_pf1[7:0])
   ,.CFGREVIDPF2(cfg_rev_id_pf2[7:0])
   ,.CFGREVIDPF3(cfg_rev_id_pf3[7:0])
   ,.CFGRXPMSTATE(cfg_rx_pm_state[1:0])
   ,.CFGSUBSYSIDPF0(cfg_subsys_id_pf0[15:0])
   ,.CFGSUBSYSIDPF1(cfg_subsys_id_pf1[15:0])
   ,.CFGSUBSYSIDPF2(cfg_subsys_id_pf2[15:0])
   ,.CFGSUBSYSIDPF3(cfg_subsys_id_pf3[15:0])
   ,.CFGSUBSYSVENDID(cfg_subsys_vend_id[15:0])
   ,.CFGTPHRAMADDRESS(cfg_tph_ram_address[11:0])
   ,.CFGTPHRAMREADDATA(cfg_tph_ram_read_data[35:0])
   ,.CFGTPHRAMREADENABLE(cfg_tph_ram_read_enable)
   ,.CFGTPHRAMWRITEBYTEENABLE(cfg_tph_ram_write_byte_enable[3:0])
   ,.CFGTPHRAMWRITEDATA(cfg_tph_ram_write_data[35:0])
   ,.CFGTPHREQUESTERENABLE(cfg_tph_requester_enable[3:0])
   ,.CFGTPHSTMODE(cfg_tph_st_mode[11:0])
   ,.CFGTXPMSTATE(cfg_tx_pm_state[1:0])
   ,.CFGVENDID(cfg_vend_id[15:0])
   ,.CFGVFFLRDONE(cfg_vf_flr_done)
   ,.CFGVFFLRFUNCNUM(cfg_vf_flr_func_num[7:0])
   ,.CONFMCAPDESIGNSWITCH(conf_mcap_design_switch)
   ,.CONFMCAPEOS(conf_mcap_eos)
   ,.CONFMCAPINUSEBYPCIE(conf_mcap_in_use_by_pcie)
   ,.CONFMCAPREQUESTBYCONF(conf_mcap_request_by_conf)
   ,.CONFREQDATA(conf_req_data[31:0])
   ,.CONFREQREADY(conf_req_ready)
   ,.CONFREQREGNUM(conf_req_reg_num[3:0])
   ,.CONFREQTYPE(conf_req_type[1:0])
   ,.CONFREQVALID(conf_req_valid)
   ,.CONFRESPRDATA(conf_resp_rdata[31:0])
   ,.CONFRESPVALID(conf_resp_valid)
   ,.CORECLK(core_clk)
   ,.CORECLKMIREPLAYRAM0(core_clk)
   ,.CORECLKMIREPLAYRAM1(core_clk)
   ,.CORECLKMIRXCOMPLETIONRAM0(core_clk)
   ,.CORECLKMIRXCOMPLETIONRAM1(core_clk)
   ,.CORECLKMIRXPOSTEDREQUESTRAM0(core_clk)
   ,.CORECLKMIRXPOSTEDREQUESTRAM1(core_clk)
   ,.DBGCTRL0OUT( )
   ,.DBGCTRL1OUT( )
   ,.DBGDATA0OUT( )
   ,.DBGDATA1OUT( )
   ,.DBGSEL0(6'd0)
   ,.DBGSEL1(6'd0)
   ,.DRPADDR(drp_addr[9:0])
   ,.DRPCLK(drp_clk)
   ,.DRPDI(drp_di[15:0])
   ,.DRPDO(drp_do[15:0])
   ,.DRPEN(drp_en)
   ,.DRPRDY(drp_rdy)
   ,.DRPWE(drp_we)
   ,.MAXISCQTDATA(m_axis_cq_tdata_int[255:0])
   ,.MAXISCQTKEEP(m_axis_cq_tkeep_int[7:0])
   ,.MAXISCQTLAST(m_axis_cq_tlast_int)
   ,.MAXISCQTREADY(m_axis_cq_tready_int[21:0])
   ,.MAXISCQTUSER(m_axis_cq_tuser_int[87:0])
   ,.MAXISCQTVALID(m_axis_cq_tvalid_int)
   ,.MAXISRCTDATA(m_axis_rc_tdata_int[255:0])
   ,.MAXISRCTKEEP(m_axis_rc_tkeep_int[7:0])
   ,.MAXISRCTLAST(m_axis_rc_tlast_int)
   ,.MAXISRCTREADY(m_axis_rc_tready_int[21:0])
   ,.MAXISRCTUSER(m_axis_rc_tuser_int[74:0])
   ,.MAXISRCTVALID(m_axis_rc_tvalid_int)
   ,.MCAPCLK(mcap_clk)
   ,.MGMTRESETN(mgmt_reset_n)
   ,.MGMTSTICKYRESETN(mgmt_sticky_reset_n)
   ,.MIREPLAYRAMADDRESS0(mi_replay_ram_address0[8:0])
   ,.MIREPLAYRAMADDRESS1(mi_replay_ram_address1[8:0])
   ,.MIREPLAYRAMERRCOR(mi_replay_ram_err_cor[5:0])
   ,.MIREPLAYRAMERRUNCOR(mi_replay_ram_err_uncor[5:0])
   ,.MIREPLAYRAMREADDATA0(mi_replay_ram_read_data0[127:0])
   ,.MIREPLAYRAMREADDATA1(mi_replay_ram_read_data1[127:0])
   ,.MIREPLAYRAMREADENABLE0(mi_replay_ram_read_enable0)
   ,.MIREPLAYRAMREADENABLE1(mi_replay_ram_read_enable1)
   ,.MIREPLAYRAMWRITEDATA0(mi_replay_ram_write_data0[127:0])
   ,.MIREPLAYRAMWRITEDATA1(mi_replay_ram_write_data1[127:0])
   ,.MIREPLAYRAMWRITEENABLE0(mi_replay_ram_write_enable0)
   ,.MIREPLAYRAMWRITEENABLE1(mi_replay_ram_write_enable1)
   ,.MIRXCOMPLETIONRAMERRCOR(mi_rx_completion_ram_err_cor[11:0])
   ,.MIRXCOMPLETIONRAMERRUNCOR(mi_rx_completion_ram_err_uncor[11:0])
   ,.MIRXCOMPLETIONRAMREADADDRESS0(mi_rx_completion_ram_read_address0[8:0])
   ,.MIRXCOMPLETIONRAMREADADDRESS1(mi_rx_completion_ram_read_address1[8:0])
   ,.MIRXCOMPLETIONRAMREADDATA0(mi_rx_completion_ram_read_data0[143:0])
   ,.MIRXCOMPLETIONRAMREADDATA1(mi_rx_completion_ram_read_data1[143:0])
   ,.MIRXCOMPLETIONRAMREADENABLE0(mi_rx_completion_ram_read_enable0[1:0])
   ,.MIRXCOMPLETIONRAMREADENABLE1(mi_rx_completion_ram_read_enable1[1:0])
   ,.MIRXCOMPLETIONRAMWRITEADDRESS0(mi_rx_completion_ram_write_address0[8:0])
   ,.MIRXCOMPLETIONRAMWRITEADDRESS1(mi_rx_completion_ram_write_address1[8:0])
   ,.MIRXCOMPLETIONRAMWRITEDATA0(mi_rx_completion_ram_write_data0[143:0])
   ,.MIRXCOMPLETIONRAMWRITEDATA1(mi_rx_completion_ram_write_data1[143:0])
   ,.MIRXCOMPLETIONRAMWRITEENABLE0(mi_rx_completion_ram_write_enable0[1:0])
   ,.MIRXCOMPLETIONRAMWRITEENABLE1(mi_rx_completion_ram_write_enable1[1:0])
   ,.MIRXPOSTEDREQUESTRAMERRCOR(mi_rx_posted_request_ram_err_cor[5:0])
   ,.MIRXPOSTEDREQUESTRAMERRUNCOR(mi_rx_posted_request_ram_err_uncor[5:0])
   ,.MIRXPOSTEDREQUESTRAMREADADDRESS0(mi_rx_posted_request_ram_read_address0[8:0])
   ,.MIRXPOSTEDREQUESTRAMREADADDRESS1(mi_rx_posted_request_ram_read_address1[8:0])
   ,.MIRXPOSTEDREQUESTRAMREADDATA0(mi_rx_posted_request_ram_read_data0[143:0])
   ,.MIRXPOSTEDREQUESTRAMREADDATA1(mi_rx_posted_request_ram_read_data1[143:0])
   ,.MIRXPOSTEDREQUESTRAMREADENABLE0(mi_rx_posted_request_ram_read_enable0)
   ,.MIRXPOSTEDREQUESTRAMREADENABLE1(mi_rx_posted_request_ram_read_enable1)
   ,.MIRXPOSTEDREQUESTRAMWRITEADDRESS0(mi_rx_posted_request_ram_write_address0[8:0])
   ,.MIRXPOSTEDREQUESTRAMWRITEADDRESS1(mi_rx_posted_request_ram_write_address1[8:0])
   ,.MIRXPOSTEDREQUESTRAMWRITEDATA0(mi_rx_posted_request_ram_write_data0[143:0])
   ,.MIRXPOSTEDREQUESTRAMWRITEDATA1(mi_rx_posted_request_ram_write_data1[143:0])
   ,.MIRXPOSTEDREQUESTRAMWRITEENABLE0(mi_rx_posted_request_ram_write_enable0)
   ,.MIRXPOSTEDREQUESTRAMWRITEENABLE1(mi_rx_posted_request_ram_write_enable1)
   ,.PCIECOMPLDELIVERED(pcie_compl_delivered[1:0])
   ,.PCIECOMPLDELIVEREDTAG0(pcie_compl_delivered_tag0[7:0])
   ,.PCIECOMPLDELIVEREDTAG1(pcie_compl_delivered_tag1[7:0])
   ,.PCIECQNPREQ(pcie_cq_np_req[1:0])
   ,.PCIECQNPREQCOUNT(pcie_cq_np_req_count_int[5:0])
   ,.PCIECQNPUSERCREDITRCVD(pcie_cq_np_user_credit_rcvd)
   ,.PCIECQPIPELINEEMPTY(pcie_cq_pipeline_empty)
   ,.PCIEPERST0B(pcie_perst0_b)
   ,.PCIEPERST1B(pcie_perst1_b)
   ,.MCAPPERST0B(mcap_rst_b)
   ,.MCAPPERST1B(mcap_rst_b)
   ,.PCIEPOSTEDREQDELIVERED(pcie_posted_req_delivered)
   ,.PCIERQSEQNUM0(pcie_rq_seq_num0_cc[5:0])
   ,.PCIERQSEQNUM1(pcie_rq_seq_num1[5:0])
   ,.PCIERQSEQNUMVLD0(pcie_rq_seq_num_vld0_cc)
   ,.PCIERQSEQNUMVLD1(pcie_rq_seq_num_vld1)
   ,.PCIERQTAG0(pcie_rq_tag0[7:0])
   ,.PCIERQTAG1(pcie_rq_tag1[7:0])
   ,.PCIERQTAGAV(pcie_rq_tag_av[3:0])
   ,.PCIERQTAGVLD0(pcie_rq_tag_vld0)
   ,.PCIERQTAGVLD1(pcie_rq_tag_vld1)
   ,.PCIETFCNPDAV(pcie_tfc_npd_av[3:0])
   ,.PCIETFCNPHAV(pcie_tfc_nph_av[3:0])
   ,.PIPECLKEN(1'b1)
   ,.PIPECLK(pipe_clk_to_e4)
   ,.PIPEEQFS(pipe_eq_fs[5:0])
   ,.PIPEEQLF(pipe_eq_lf[5:0])
   ,.PIPERESETN(pipe_reset_n)
   ,.PIPERX00CHARISK(pipe_rx00_char_is_k[1:0])
   ,.PIPERX00DATA(pipe_rx00_data[31:0])
   ,.PIPERX00DATAVALID(pipe_rx00_data_valid)
   ,.PIPERX00ELECIDLE(pipe_rx00_elec_idle)
   ,.PIPERX00EQCONTROL(pipe_rx00_eq_control[1:0])
   ,.PIPERX00EQDONE(pipe_rx00_eq_done)
   ,.PIPERX00EQLPADAPTDONE(pipe_rx00_eq_lp_adapt_done)
   ,.PIPERX00EQLPLFFSSEL(pipe_rx00_eq_lp_lf_fs_sel)
   ,.PIPERX00EQLPNEWTXCOEFFORPRESET(pipe_rx00_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.PIPERX00PHYSTATUS(pipe_rx00_phy_status)
   ,.PIPERX00POLARITY(pipe_rx00_polarity)
   ,.PIPERX00STARTBLOCK(pipe_rx00_start_block[1:0])
   ,.PIPERX00STATUS(pipe_rx00_status[2:0])
   ,.PIPERX00SYNCHEADER(pipe_rx00_sync_header[1:0])
   ,.PIPERX00VALID(pipe_rx00_valid)
   ,.PIPERX01CHARISK(pipe_rx01_char_is_k[1:0])
   ,.PIPERX01DATA(pipe_rx01_data[31:0])
   ,.PIPERX01DATAVALID(pipe_rx01_data_valid)
   ,.PIPERX01ELECIDLE(pipe_rx01_elec_idle)
   ,.PIPERX01EQCONTROL(pipe_rx01_eq_control[1:0])
   ,.PIPERX01EQDONE(pipe_rx01_eq_done)
   ,.PIPERX01EQLPADAPTDONE(pipe_rx01_eq_lp_adapt_done)
   ,.PIPERX01EQLPLFFSSEL(pipe_rx01_eq_lp_lf_fs_sel)
   ,.PIPERX01EQLPNEWTXCOEFFORPRESET(pipe_rx01_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.PIPERX01PHYSTATUS(pipe_rx01_phy_status)
   ,.PIPERX01POLARITY(pipe_rx01_polarity)
   ,.PIPERX01STARTBLOCK(pipe_rx01_start_block[1:0])
   ,.PIPERX01STATUS(pipe_rx01_status[2:0])
   ,.PIPERX01SYNCHEADER(pipe_rx01_sync_header[1:0])
   ,.PIPERX01VALID(pipe_rx01_valid)
   ,.PIPERX02CHARISK(pipe_rx02_char_is_k[1:0])
   ,.PIPERX02DATA(pipe_rx02_data[31:0])
   ,.PIPERX02DATAVALID(pipe_rx02_data_valid)
   ,.PIPERX02ELECIDLE(pipe_rx02_elec_idle)
   ,.PIPERX02EQCONTROL(pipe_rx02_eq_control[1:0])
   ,.PIPERX02EQDONE(pipe_rx02_eq_done)
   ,.PIPERX02EQLPADAPTDONE(pipe_rx02_eq_lp_adapt_done)
   ,.PIPERX02EQLPLFFSSEL(pipe_rx02_eq_lp_lf_fs_sel)
   ,.PIPERX02EQLPNEWTXCOEFFORPRESET(pipe_rx02_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.PIPERX02PHYSTATUS(pipe_rx02_phy_status)
   ,.PIPERX02POLARITY(pipe_rx02_polarity)
   ,.PIPERX02STARTBLOCK(pipe_rx02_start_block[1:0])
   ,.PIPERX02STATUS(pipe_rx02_status[2:0])
   ,.PIPERX02SYNCHEADER(pipe_rx02_sync_header[1:0])
   ,.PIPERX02VALID(pipe_rx02_valid)
   ,.PIPERX03CHARISK(pipe_rx03_char_is_k[1:0])
   ,.PIPERX03DATA(pipe_rx03_data[31:0])
   ,.PIPERX03DATAVALID(pipe_rx03_data_valid)
   ,.PIPERX03ELECIDLE(pipe_rx03_elec_idle)
   ,.PIPERX03EQCONTROL(pipe_rx03_eq_control[1:0])
   ,.PIPERX03EQDONE(pipe_rx03_eq_done)
   ,.PIPERX03EQLPADAPTDONE(pipe_rx03_eq_lp_adapt_done)
   ,.PIPERX03EQLPLFFSSEL(pipe_rx03_eq_lp_lf_fs_sel)
   ,.PIPERX03EQLPNEWTXCOEFFORPRESET(pipe_rx03_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.PIPERX03PHYSTATUS(pipe_rx03_phy_status)
   ,.PIPERX03POLARITY(pipe_rx03_polarity)
   ,.PIPERX03STARTBLOCK(pipe_rx03_start_block[1:0])
   ,.PIPERX03STATUS(pipe_rx03_status[2:0])
   ,.PIPERX03SYNCHEADER(pipe_rx03_sync_header[1:0])
   ,.PIPERX03VALID(pipe_rx03_valid)
   ,.PIPERX04CHARISK(pipe_rx04_char_is_k[1:0])
   ,.PIPERX04DATA(pipe_rx04_data[31:0])
   ,.PIPERX04DATAVALID(pipe_rx04_data_valid)
   ,.PIPERX04ELECIDLE(pipe_rx04_elec_idle)
   ,.PIPERX04EQCONTROL(pipe_rx04_eq_control[1:0])
   ,.PIPERX04EQDONE(pipe_rx04_eq_done)
   ,.PIPERX04EQLPADAPTDONE(pipe_rx04_eq_lp_adapt_done)
   ,.PIPERX04EQLPLFFSSEL(pipe_rx04_eq_lp_lf_fs_sel)
   ,.PIPERX04EQLPNEWTXCOEFFORPRESET(pipe_rx04_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.PIPERX04PHYSTATUS(pipe_rx04_phy_status)
   ,.PIPERX04POLARITY(pipe_rx04_polarity)
   ,.PIPERX04STARTBLOCK(pipe_rx04_start_block[1:0])
   ,.PIPERX04STATUS(pipe_rx04_status[2:0])
   ,.PIPERX04SYNCHEADER(pipe_rx04_sync_header[1:0])
   ,.PIPERX04VALID(pipe_rx04_valid)
   ,.PIPERX05CHARISK(pipe_rx05_char_is_k[1:0])
   ,.PIPERX05DATA(pipe_rx05_data[31:0])
   ,.PIPERX05DATAVALID(pipe_rx05_data_valid)
   ,.PIPERX05ELECIDLE(pipe_rx05_elec_idle)
   ,.PIPERX05EQCONTROL(pipe_rx05_eq_control[1:0])
   ,.PIPERX05EQDONE(pipe_rx05_eq_done)
   ,.PIPERX05EQLPADAPTDONE(pipe_rx05_eq_lp_adapt_done)
   ,.PIPERX05EQLPLFFSSEL(pipe_rx05_eq_lp_lf_fs_sel)
   ,.PIPERX05EQLPNEWTXCOEFFORPRESET(pipe_rx05_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.PIPERX05PHYSTATUS(pipe_rx05_phy_status)
   ,.PIPERX05POLARITY(pipe_rx05_polarity)
   ,.PIPERX05STARTBLOCK(pipe_rx05_start_block[1:0])
   ,.PIPERX05STATUS(pipe_rx05_status[2:0])
   ,.PIPERX05SYNCHEADER(pipe_rx05_sync_header[1:0])
   ,.PIPERX05VALID(pipe_rx05_valid)
   ,.PIPERX06CHARISK(pipe_rx06_char_is_k[1:0])
   ,.PIPERX06DATA(pipe_rx06_data[31:0])
   ,.PIPERX06DATAVALID(pipe_rx06_data_valid)
   ,.PIPERX06ELECIDLE(pipe_rx06_elec_idle)
   ,.PIPERX06EQCONTROL(pipe_rx06_eq_control[1:0])
   ,.PIPERX06EQDONE(pipe_rx06_eq_done)
   ,.PIPERX06EQLPADAPTDONE(pipe_rx06_eq_lp_adapt_done)
   ,.PIPERX06EQLPLFFSSEL(pipe_rx06_eq_lp_lf_fs_sel)
   ,.PIPERX06EQLPNEWTXCOEFFORPRESET(pipe_rx06_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.PIPERX06PHYSTATUS(pipe_rx06_phy_status)
   ,.PIPERX06POLARITY(pipe_rx06_polarity)
   ,.PIPERX06STARTBLOCK(pipe_rx06_start_block[1:0])
   ,.PIPERX06STATUS(pipe_rx06_status[2:0])
   ,.PIPERX06SYNCHEADER(pipe_rx06_sync_header[1:0])
   ,.PIPERX06VALID(pipe_rx06_valid)
   ,.PIPERX07CHARISK(pipe_rx07_char_is_k[1:0])
   ,.PIPERX07DATA(pipe_rx07_data[31:0])
   ,.PIPERX07DATAVALID(pipe_rx07_data_valid)
   ,.PIPERX07ELECIDLE(pipe_rx07_elec_idle)
   ,.PIPERX07EQCONTROL(pipe_rx07_eq_control[1:0])
   ,.PIPERX07EQDONE(pipe_rx07_eq_done)
   ,.PIPERX07EQLPADAPTDONE(pipe_rx07_eq_lp_adapt_done)
   ,.PIPERX07EQLPLFFSSEL(pipe_rx07_eq_lp_lf_fs_sel)
   ,.PIPERX07EQLPNEWTXCOEFFORPRESET(pipe_rx07_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.PIPERX07PHYSTATUS(pipe_rx07_phy_status)
   ,.PIPERX07POLARITY(pipe_rx07_polarity)
   ,.PIPERX07STARTBLOCK(pipe_rx07_start_block[1:0])
   ,.PIPERX07STATUS(pipe_rx07_status[2:0])
   ,.PIPERX07SYNCHEADER(pipe_rx07_sync_header[1:0])
   ,.PIPERX07VALID(pipe_rx07_valid)
   ,.PIPERX08CHARISK(pipe_rx08_char_is_k[1:0])
   ,.PIPERX08DATA(pipe_rx08_data[31:0])
   ,.PIPERX08DATAVALID(pipe_rx08_data_valid)
   ,.PIPERX08ELECIDLE(pipe_rx08_elec_idle)
   ,.PIPERX08EQCONTROL(pipe_rx08_eq_control[1:0])
   ,.PIPERX08EQDONE(pipe_rx08_eq_done)
   ,.PIPERX08EQLPADAPTDONE(pipe_rx08_eq_lp_adapt_done)
   ,.PIPERX08EQLPLFFSSEL(pipe_rx08_eq_lp_lf_fs_sel)
   ,.PIPERX08EQLPNEWTXCOEFFORPRESET(pipe_rx08_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.PIPERX08PHYSTATUS(pipe_rx08_phy_status)
   ,.PIPERX08POLARITY(pipe_rx08_polarity)
   ,.PIPERX08STARTBLOCK(pipe_rx08_start_block[1:0])
   ,.PIPERX08STATUS(pipe_rx08_status[2:0])
   ,.PIPERX08SYNCHEADER(pipe_rx08_sync_header[1:0])
   ,.PIPERX08VALID(pipe_rx08_valid)
   ,.PIPERX09CHARISK(pipe_rx09_char_is_k[1:0])
   ,.PIPERX09DATA(pipe_rx09_data[31:0])
   ,.PIPERX09DATAVALID(pipe_rx09_data_valid)
   ,.PIPERX09ELECIDLE(pipe_rx09_elec_idle)
   ,.PIPERX09EQCONTROL(pipe_rx09_eq_control[1:0])
   ,.PIPERX09EQDONE(pipe_rx09_eq_done)
   ,.PIPERX09EQLPADAPTDONE(pipe_rx09_eq_lp_adapt_done)
   ,.PIPERX09EQLPLFFSSEL(pipe_rx09_eq_lp_lf_fs_sel)
   ,.PIPERX09EQLPNEWTXCOEFFORPRESET(pipe_rx09_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.PIPERX09PHYSTATUS(pipe_rx09_phy_status)
   ,.PIPERX09POLARITY(pipe_rx09_polarity)
   ,.PIPERX09STARTBLOCK(pipe_rx09_start_block[1:0])
   ,.PIPERX09STATUS(pipe_rx09_status[2:0])
   ,.PIPERX09SYNCHEADER(pipe_rx09_sync_header[1:0])
   ,.PIPERX09VALID(pipe_rx09_valid)
   ,.PIPERX10CHARISK(pipe_rx10_char_is_k[1:0])
   ,.PIPERX10DATA(pipe_rx10_data[31:0])
   ,.PIPERX10DATAVALID(pipe_rx10_data_valid)
   ,.PIPERX10ELECIDLE(pipe_rx10_elec_idle)
   ,.PIPERX10EQCONTROL(pipe_rx10_eq_control[1:0])
   ,.PIPERX10EQDONE(pipe_rx10_eq_done)
   ,.PIPERX10EQLPADAPTDONE(pipe_rx10_eq_lp_adapt_done)
   ,.PIPERX10EQLPLFFSSEL(pipe_rx10_eq_lp_lf_fs_sel)
   ,.PIPERX10EQLPNEWTXCOEFFORPRESET(pipe_rx10_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.PIPERX10PHYSTATUS(pipe_rx10_phy_status)
   ,.PIPERX10POLARITY(pipe_rx10_polarity)
   ,.PIPERX10STARTBLOCK(pipe_rx10_start_block[1:0])
   ,.PIPERX10STATUS(pipe_rx10_status[2:0])
   ,.PIPERX10SYNCHEADER(pipe_rx10_sync_header[1:0])
   ,.PIPERX10VALID(pipe_rx10_valid)
   ,.PIPERX11CHARISK(pipe_rx11_char_is_k[1:0])
   ,.PIPERX11DATA(pipe_rx11_data[31:0])
   ,.PIPERX11DATAVALID(pipe_rx11_data_valid)
   ,.PIPERX11ELECIDLE(pipe_rx11_elec_idle)
   ,.PIPERX11EQCONTROL(pipe_rx11_eq_control[1:0])
   ,.PIPERX11EQDONE(pipe_rx11_eq_done)
   ,.PIPERX11EQLPADAPTDONE(pipe_rx11_eq_lp_adapt_done)
   ,.PIPERX11EQLPLFFSSEL(pipe_rx11_eq_lp_lf_fs_sel)
   ,.PIPERX11EQLPNEWTXCOEFFORPRESET(pipe_rx11_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.PIPERX11PHYSTATUS(pipe_rx11_phy_status)
   ,.PIPERX11POLARITY(pipe_rx11_polarity)
   ,.PIPERX11STARTBLOCK(pipe_rx11_start_block[1:0])
   ,.PIPERX11STATUS(pipe_rx11_status[2:0])
   ,.PIPERX11SYNCHEADER(pipe_rx11_sync_header[1:0])
   ,.PIPERX11VALID(pipe_rx11_valid)
   ,.PIPERX12CHARISK(pipe_rx12_char_is_k[1:0])
   ,.PIPERX12DATA(pipe_rx12_data[31:0])
   ,.PIPERX12DATAVALID(pipe_rx12_data_valid)
   ,.PIPERX12ELECIDLE(pipe_rx12_elec_idle)
   ,.PIPERX12EQCONTROL(pipe_rx12_eq_control[1:0])
   ,.PIPERX12EQDONE(pipe_rx12_eq_done)
   ,.PIPERX12EQLPADAPTDONE(pipe_rx12_eq_lp_adapt_done)
   ,.PIPERX12EQLPLFFSSEL(pipe_rx12_eq_lp_lf_fs_sel)
   ,.PIPERX12EQLPNEWTXCOEFFORPRESET(pipe_rx12_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.PIPERX12PHYSTATUS(pipe_rx12_phy_status)
   ,.PIPERX12POLARITY(pipe_rx12_polarity)
   ,.PIPERX12STARTBLOCK(pipe_rx12_start_block[1:0])
   ,.PIPERX12STATUS(pipe_rx12_status[2:0])
   ,.PIPERX12SYNCHEADER(pipe_rx12_sync_header[1:0])
   ,.PIPERX12VALID(pipe_rx12_valid)
   ,.PIPERX13CHARISK(pipe_rx13_char_is_k[1:0])
   ,.PIPERX13DATA(pipe_rx13_data[31:0])
   ,.PIPERX13DATAVALID(pipe_rx13_data_valid)
   ,.PIPERX13ELECIDLE(pipe_rx13_elec_idle)
   ,.PIPERX13EQCONTROL(pipe_rx13_eq_control[1:0])
   ,.PIPERX13EQDONE(pipe_rx13_eq_done)
   ,.PIPERX13EQLPADAPTDONE(pipe_rx13_eq_lp_adapt_done)
   ,.PIPERX13EQLPLFFSSEL(pipe_rx13_eq_lp_lf_fs_sel)
   ,.PIPERX13EQLPNEWTXCOEFFORPRESET(pipe_rx13_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.PIPERX13PHYSTATUS(pipe_rx13_phy_status)
   ,.PIPERX13POLARITY(pipe_rx13_polarity)
   ,.PIPERX13STARTBLOCK(pipe_rx13_start_block[1:0])
   ,.PIPERX13STATUS(pipe_rx13_status[2:0])
   ,.PIPERX13SYNCHEADER(pipe_rx13_sync_header[1:0])
   ,.PIPERX13VALID(pipe_rx13_valid)
   ,.PIPERX14CHARISK(pipe_rx14_char_is_k[1:0])
   ,.PIPERX14DATA(pipe_rx14_data[31:0])
   ,.PIPERX14DATAVALID(pipe_rx14_data_valid)
   ,.PIPERX14ELECIDLE(pipe_rx14_elec_idle)
   ,.PIPERX14EQCONTROL(pipe_rx14_eq_control[1:0])
   ,.PIPERX14EQDONE(pipe_rx14_eq_done)
   ,.PIPERX14EQLPADAPTDONE(pipe_rx14_eq_lp_adapt_done)
   ,.PIPERX14EQLPLFFSSEL(pipe_rx14_eq_lp_lf_fs_sel)
   ,.PIPERX14EQLPNEWTXCOEFFORPRESET(pipe_rx14_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.PIPERX14PHYSTATUS(pipe_rx14_phy_status)
   ,.PIPERX14POLARITY(pipe_rx14_polarity)
   ,.PIPERX14STARTBLOCK(pipe_rx14_start_block[1:0])
   ,.PIPERX14STATUS(pipe_rx14_status[2:0])
   ,.PIPERX14SYNCHEADER(pipe_rx14_sync_header[1:0])
   ,.PIPERX14VALID(pipe_rx14_valid)
   ,.PIPERX15CHARISK(pipe_rx15_char_is_k[1:0])
   ,.PIPERX15DATA(pipe_rx15_data[31:0])
   ,.PIPERX15DATAVALID(pipe_rx15_data_valid)
   ,.PIPERX15ELECIDLE(pipe_rx15_elec_idle)
   ,.PIPERX15EQCONTROL(pipe_rx15_eq_control[1:0])
   ,.PIPERX15EQDONE(pipe_rx15_eq_done)
   ,.PIPERX15EQLPADAPTDONE(pipe_rx15_eq_lp_adapt_done)
   ,.PIPERX15EQLPLFFSSEL(pipe_rx15_eq_lp_lf_fs_sel)
   ,.PIPERX15EQLPNEWTXCOEFFORPRESET(pipe_rx15_eq_lp_new_tx_coeff_or_preset[17:0])
   ,.PIPERX15PHYSTATUS(pipe_rx15_phy_status)
   ,.PIPERX15POLARITY(pipe_rx15_polarity)
   ,.PIPERX15STARTBLOCK(pipe_rx15_start_block[1:0])
   ,.PIPERX15STATUS(pipe_rx15_status[2:0])
   ,.PIPERX15SYNCHEADER(pipe_rx15_sync_header[1:0])
   ,.PIPERX15VALID(pipe_rx15_valid)
   ,.PIPERXEQLPLFFS(pipe_rx_eq_lp_lf_fs[5:0])
   ,.PIPERXEQLPTXPRESET(pipe_rx_eq_lp_tx_preset[3:0])
   ,.PIPETX00CHARISK(pipe_tx00_char_is_k[1:0])
   ,.PIPETX00COMPLIANCE(pipe_tx00_compliance)
   ,.PIPETX00DATA(pipe_tx00_data_out[31:0])
   ,.PIPETX00DATAVALID(pipe_tx00_data_valid)
   ,.PIPETX00ELECIDLE(pipe_tx00_elec_idle)
   ,.PIPETX00EQCOEFF(pipe_tx00_eq_coeff[17:0])
   ,.PIPETX00EQCONTROL(pipe_tx00_eq_control[1:0])
   ,.PIPETX00EQDEEMPH(pipe_tx00_eq_deemph[5:0])
   ,.PIPETX00EQDONE(pipe_tx00_eq_done)
   ,.PIPETX00POWERDOWN(pipe_tx00_powerdown[1:0])
   ,.PIPETX00STARTBLOCK(pipe_tx00_start_block)
   ,.PIPETX00SYNCHEADER(pipe_tx00_sync_header[1:0])
   ,.PIPETX01CHARISK(pipe_tx01_char_is_k[1:0])
   ,.PIPETX01COMPLIANCE(pipe_tx01_compliance)
   ,.PIPETX01DATA(pipe_tx01_data_out[31:0])
   ,.PIPETX01DATAVALID(pipe_tx01_data_valid)
   ,.PIPETX01ELECIDLE(pipe_tx01_elec_idle)
   ,.PIPETX01EQCOEFF(pipe_tx01_eq_coeff[17:0])
   ,.PIPETX01EQCONTROL(pipe_tx01_eq_control[1:0])
   ,.PIPETX01EQDEEMPH(pipe_tx01_eq_deemph[5:0])
   ,.PIPETX01EQDONE(pipe_tx01_eq_done)
   ,.PIPETX01POWERDOWN(pipe_tx01_powerdown[1:0])
   ,.PIPETX01STARTBLOCK(pipe_tx01_start_block)
   ,.PIPETX01SYNCHEADER(pipe_tx01_sync_header[1:0])
   ,.PIPETX02CHARISK(pipe_tx02_char_is_k[1:0])
   ,.PIPETX02COMPLIANCE(pipe_tx02_compliance)
   ,.PIPETX02DATA(pipe_tx02_data_out[31:0])
   ,.PIPETX02DATAVALID(pipe_tx02_data_valid)
   ,.PIPETX02ELECIDLE(pipe_tx02_elec_idle)
   ,.PIPETX02EQCOEFF(pipe_tx02_eq_coeff[17:0])
   ,.PIPETX02EQCONTROL(pipe_tx02_eq_control[1:0])
   ,.PIPETX02EQDEEMPH(pipe_tx02_eq_deemph[5:0])
   ,.PIPETX02EQDONE(pipe_tx02_eq_done)
   ,.PIPETX02POWERDOWN(pipe_tx02_powerdown[1:0])
   ,.PIPETX02STARTBLOCK(pipe_tx02_start_block)
   ,.PIPETX02SYNCHEADER(pipe_tx02_sync_header[1:0])
   ,.PIPETX03CHARISK(pipe_tx03_char_is_k[1:0])
   ,.PIPETX03COMPLIANCE(pipe_tx03_compliance)
   ,.PIPETX03DATA(pipe_tx03_data_out[31:0])
   ,.PIPETX03DATAVALID(pipe_tx03_data_valid)
   ,.PIPETX03ELECIDLE(pipe_tx03_elec_idle)
   ,.PIPETX03EQCOEFF(pipe_tx03_eq_coeff[17:0])
   ,.PIPETX03EQCONTROL(pipe_tx03_eq_control[1:0])
   ,.PIPETX03EQDEEMPH(pipe_tx03_eq_deemph[5:0])
   ,.PIPETX03EQDONE(pipe_tx03_eq_done)
   ,.PIPETX03POWERDOWN(pipe_tx03_powerdown[1:0])
   ,.PIPETX03STARTBLOCK(pipe_tx03_start_block)
   ,.PIPETX03SYNCHEADER(pipe_tx03_sync_header[1:0])
   ,.PIPETX04CHARISK(pipe_tx04_char_is_k[1:0])
   ,.PIPETX04COMPLIANCE(pipe_tx04_compliance)
   ,.PIPETX04DATA(pipe_tx04_data_out[31:0])
   ,.PIPETX04DATAVALID(pipe_tx04_data_valid)
   ,.PIPETX04ELECIDLE(pipe_tx04_elec_idle)
   ,.PIPETX04EQCOEFF(pipe_tx04_eq_coeff[17:0])
   ,.PIPETX04EQCONTROL(pipe_tx04_eq_control[1:0])
   ,.PIPETX04EQDEEMPH(pipe_tx04_eq_deemph[5:0])
   ,.PIPETX04EQDONE(pipe_tx04_eq_done)
   ,.PIPETX04POWERDOWN(pipe_tx04_powerdown[1:0])
   ,.PIPETX04STARTBLOCK(pipe_tx04_start_block)
   ,.PIPETX04SYNCHEADER(pipe_tx04_sync_header[1:0])
   ,.PIPETX05CHARISK(pipe_tx05_char_is_k[1:0])
   ,.PIPETX05COMPLIANCE(pipe_tx05_compliance)
   ,.PIPETX05DATA(pipe_tx05_data_out[31:0])
   ,.PIPETX05DATAVALID(pipe_tx05_data_valid)
   ,.PIPETX05ELECIDLE(pipe_tx05_elec_idle)
   ,.PIPETX05EQCOEFF(pipe_tx05_eq_coeff[17:0])
   ,.PIPETX05EQCONTROL(pipe_tx05_eq_control[1:0])
   ,.PIPETX05EQDEEMPH(pipe_tx05_eq_deemph[5:0])
   ,.PIPETX05EQDONE(pipe_tx05_eq_done)
   ,.PIPETX05POWERDOWN(pipe_tx05_powerdown[1:0])
   ,.PIPETX05STARTBLOCK(pipe_tx05_start_block)
   ,.PIPETX05SYNCHEADER(pipe_tx05_sync_header[1:0])
   ,.PIPETX06CHARISK(pipe_tx06_char_is_k[1:0])
   ,.PIPETX06COMPLIANCE(pipe_tx06_compliance)
   ,.PIPETX06DATA(pipe_tx06_data_out[31:0])
   ,.PIPETX06DATAVALID(pipe_tx06_data_valid)
   ,.PIPETX06ELECIDLE(pipe_tx06_elec_idle)
   ,.PIPETX06EQCOEFF(pipe_tx06_eq_coeff[17:0])
   ,.PIPETX06EQCONTROL(pipe_tx06_eq_control[1:0])
   ,.PIPETX06EQDEEMPH(pipe_tx06_eq_deemph[5:0])
   ,.PIPETX06EQDONE(pipe_tx06_eq_done)
   ,.PIPETX06POWERDOWN(pipe_tx06_powerdown[1:0])
   ,.PIPETX06STARTBLOCK(pipe_tx06_start_block)
   ,.PIPETX06SYNCHEADER(pipe_tx06_sync_header[1:0])
   ,.PIPETX07CHARISK(pipe_tx07_char_is_k[1:0])
   ,.PIPETX07COMPLIANCE(pipe_tx07_compliance)
   ,.PIPETX07DATA(pipe_tx07_data_out[31:0])
   ,.PIPETX07DATAVALID(pipe_tx07_data_valid)
   ,.PIPETX07ELECIDLE(pipe_tx07_elec_idle)
   ,.PIPETX07EQCOEFF(pipe_tx07_eq_coeff[17:0])
   ,.PIPETX07EQCONTROL(pipe_tx07_eq_control[1:0])
   ,.PIPETX07EQDEEMPH(pipe_tx07_eq_deemph[5:0])
   ,.PIPETX07EQDONE(pipe_tx07_eq_done)
   ,.PIPETX07POWERDOWN(pipe_tx07_powerdown[1:0])
   ,.PIPETX07STARTBLOCK(pipe_tx07_start_block)
   ,.PIPETX07SYNCHEADER(pipe_tx07_sync_header[1:0])
   ,.PIPETX08CHARISK(pipe_tx08_char_is_k[1:0])
   ,.PIPETX08COMPLIANCE(pipe_tx08_compliance)
   ,.PIPETX08DATA(pipe_tx08_data_out[31:0])
   ,.PIPETX08DATAVALID(pipe_tx08_data_valid)
   ,.PIPETX08ELECIDLE(pipe_tx08_elec_idle)
   ,.PIPETX08EQCOEFF(pipe_tx08_eq_coeff[17:0])
   ,.PIPETX08EQCONTROL(pipe_tx08_eq_control[1:0])
   ,.PIPETX08EQDEEMPH(pipe_tx08_eq_deemph[5:0])
   ,.PIPETX08EQDONE(pipe_tx08_eq_done)
   ,.PIPETX08POWERDOWN(pipe_tx08_powerdown[1:0])
   ,.PIPETX08STARTBLOCK(pipe_tx08_start_block)
   ,.PIPETX08SYNCHEADER(pipe_tx08_sync_header[1:0])
   ,.PIPETX09CHARISK(pipe_tx09_char_is_k[1:0])
   ,.PIPETX09COMPLIANCE(pipe_tx09_compliance)
   ,.PIPETX09DATA(pipe_tx09_data_out[31:0])
   ,.PIPETX09DATAVALID(pipe_tx09_data_valid)
   ,.PIPETX09ELECIDLE(pipe_tx09_elec_idle)
   ,.PIPETX09EQCOEFF(pipe_tx09_eq_coeff[17:0])
   ,.PIPETX09EQCONTROL(pipe_tx09_eq_control[1:0])
   ,.PIPETX09EQDEEMPH(pipe_tx09_eq_deemph[5:0])
   ,.PIPETX09EQDONE(pipe_tx09_eq_done)
   ,.PIPETX09POWERDOWN(pipe_tx09_powerdown[1:0])
   ,.PIPETX09STARTBLOCK(pipe_tx09_start_block)
   ,.PIPETX09SYNCHEADER(pipe_tx09_sync_header[1:0])
   ,.PIPETX10CHARISK(pipe_tx10_char_is_k[1:0])
   ,.PIPETX10COMPLIANCE(pipe_tx10_compliance)
   ,.PIPETX10DATA(pipe_tx10_data_out[31:0])
   ,.PIPETX10DATAVALID(pipe_tx10_data_valid)
   ,.PIPETX10ELECIDLE(pipe_tx10_elec_idle)
   ,.PIPETX10EQCOEFF(pipe_tx10_eq_coeff[17:0])
   ,.PIPETX10EQCONTROL(pipe_tx10_eq_control[1:0])
   ,.PIPETX10EQDEEMPH(pipe_tx10_eq_deemph[5:0])
   ,.PIPETX10EQDONE(pipe_tx10_eq_done)
   ,.PIPETX10POWERDOWN(pipe_tx10_powerdown[1:0])
   ,.PIPETX10STARTBLOCK(pipe_tx10_start_block)
   ,.PIPETX10SYNCHEADER(pipe_tx10_sync_header[1:0])
   ,.PIPETX11CHARISK(pipe_tx11_char_is_k[1:0])
   ,.PIPETX11COMPLIANCE(pipe_tx11_compliance)
   ,.PIPETX11DATA(pipe_tx11_data_out[31:0])
   ,.PIPETX11DATAVALID(pipe_tx11_data_valid)
   ,.PIPETX11ELECIDLE(pipe_tx11_elec_idle)
   ,.PIPETX11EQCOEFF(pipe_tx11_eq_coeff[17:0])
   ,.PIPETX11EQCONTROL(pipe_tx11_eq_control[1:0])
   ,.PIPETX11EQDEEMPH(pipe_tx11_eq_deemph[5:0])
   ,.PIPETX11EQDONE(pipe_tx11_eq_done)
   ,.PIPETX11POWERDOWN(pipe_tx11_powerdown[1:0])
   ,.PIPETX11STARTBLOCK(pipe_tx11_start_block)
   ,.PIPETX11SYNCHEADER(pipe_tx11_sync_header[1:0])
   ,.PIPETX12CHARISK(pipe_tx12_char_is_k[1:0])
   ,.PIPETX12COMPLIANCE(pipe_tx12_compliance)
   ,.PIPETX12DATA(pipe_tx12_data_out[31:0])
   ,.PIPETX12DATAVALID(pipe_tx12_data_valid)
   ,.PIPETX12ELECIDLE(pipe_tx12_elec_idle)
   ,.PIPETX12EQCOEFF(pipe_tx12_eq_coeff[17:0])
   ,.PIPETX12EQCONTROL(pipe_tx12_eq_control[1:0])
   ,.PIPETX12EQDEEMPH(pipe_tx12_eq_deemph[5:0])
   ,.PIPETX12EQDONE(pipe_tx12_eq_done)
   ,.PIPETX12POWERDOWN(pipe_tx12_powerdown[1:0])
   ,.PIPETX12STARTBLOCK(pipe_tx12_start_block)
   ,.PIPETX12SYNCHEADER(pipe_tx12_sync_header[1:0])
   ,.PIPETX13CHARISK(pipe_tx13_char_is_k[1:0])
   ,.PIPETX13COMPLIANCE(pipe_tx13_compliance)
   ,.PIPETX13DATA(pipe_tx13_data_out[31:0])
   ,.PIPETX13DATAVALID(pipe_tx13_data_valid)
   ,.PIPETX13ELECIDLE(pipe_tx13_elec_idle)
   ,.PIPETX13EQCOEFF(pipe_tx13_eq_coeff[17:0])
   ,.PIPETX13EQCONTROL(pipe_tx13_eq_control[1:0])
   ,.PIPETX13EQDEEMPH(pipe_tx13_eq_deemph[5:0])
   ,.PIPETX13EQDONE(pipe_tx13_eq_done)
   ,.PIPETX13POWERDOWN(pipe_tx13_powerdown[1:0])
   ,.PIPETX13STARTBLOCK(pipe_tx13_start_block)
   ,.PIPETX13SYNCHEADER(pipe_tx13_sync_header[1:0])
   ,.PIPETX14CHARISK(pipe_tx14_char_is_k[1:0])
   ,.PIPETX14COMPLIANCE(pipe_tx14_compliance)
   ,.PIPETX14DATA(pipe_tx14_data_out[31:0])
   ,.PIPETX14DATAVALID(pipe_tx14_data_valid)
   ,.PIPETX14ELECIDLE(pipe_tx14_elec_idle)
   ,.PIPETX14EQCOEFF(pipe_tx14_eq_coeff[17:0])
   ,.PIPETX14EQCONTROL(pipe_tx14_eq_control[1:0])
   ,.PIPETX14EQDEEMPH(pipe_tx14_eq_deemph[5:0])
   ,.PIPETX14EQDONE(pipe_tx14_eq_done)
   ,.PIPETX14POWERDOWN(pipe_tx14_powerdown[1:0])
   ,.PIPETX14STARTBLOCK(pipe_tx14_start_block)
   ,.PIPETX14SYNCHEADER(pipe_tx14_sync_header[1:0])
   ,.PIPETX15CHARISK(pipe_tx15_char_is_k[1:0])
   ,.PIPETX15COMPLIANCE(pipe_tx15_compliance)
   ,.PIPETX15DATA(pipe_tx15_data_out[31:0])
   ,.PIPETX15DATAVALID(pipe_tx15_data_valid)
   ,.PIPETX15ELECIDLE(pipe_tx15_elec_idle)
   ,.PIPETX15EQCOEFF(pipe_tx15_eq_coeff[17:0])
   ,.PIPETX15EQCONTROL(pipe_tx15_eq_control[1:0])
   ,.PIPETX15EQDEEMPH(pipe_tx15_eq_deemph[5:0])
   ,.PIPETX15EQDONE(pipe_tx15_eq_done)
   ,.PIPETX15POWERDOWN(pipe_tx15_powerdown[1:0])
   ,.PIPETX15STARTBLOCK(pipe_tx15_start_block)
   ,.PIPETX15SYNCHEADER(pipe_tx15_sync_header[1:0])
   ,.PIPETXDEEMPH(pipe_tx_deemph)
   ,.PIPETXMARGIN(pipe_tx_margin[2:0])
   ,.PIPETXRATE(pipe_tx_rate[1:0])
   ,.PIPETXRCVRDET(pipe_tx_rcvr_det)
   ,.PIPETXRESET(pipe_tx_reset)
   ,.PIPETXSWING(pipe_tx_swing)
   ,.PLEQINPROGRESS(pl_eq_in_progress)
   ,.PLEQPHASE(pl_eq_phase[1:0])
   ,.PLEQRESETEIEOSCOUNT(pl_eq_reset_eieos_count)
   ,.PLGEN2UPSTREAMPREFERDEEMPH(pl_gen2_upstream_prefer_deemph)
   ,.PLGEN34EQMISMATCH(pl_gen34_eq_mismatch)
   ,.PLGEN34REDOEQSPEED(pl_gen34_redo_eq_speed)
   ,.PLGEN34REDOEQUALIZATION(pl_gen34_redo_equalization)
   ,.RESETN(reset_n)
   ,.SAXISCCTDATA(s_axis_cc_tdata_int[255:0])
   ,.SAXISCCTKEEP(s_axis_cc_tkeep_int[7:0])
   ,.SAXISCCTLAST(s_axis_cc_tlast_int)
   ,.SAXISCCTREADY(s_axis_cc_tready_int[3:0])
   ,.SAXISCCTUSER(s_axis_cc_tuser_int[32:0])
   ,.SAXISCCTVALID(s_axis_cc_tvalid_int)
   ,.SAXISRQTDATA(s_axis_rq_tdata_int[255:0])
   ,.SAXISRQTKEEP(s_axis_rq_tkeep_int[7:0])
   ,.SAXISRQTLAST(s_axis_rq_tlast_int)
   ,.SAXISRQTREADY(s_axis_rq_tready_int[3:0])
   ,.SAXISRQTUSER(s_axis_rq_tuser_int[61:0])
   ,.SAXISRQTVALID(s_axis_rq_tvalid_int)
   ,.USERCLK2(user_clk2_to_e4)
   ,.USERCLKEN(user_clk_en_to_e4)
   ,.USERCLK(user_clk_to_e4)
   ,.USERSPAREIN({32{1'b0}})
   ,.USERSPAREOUT( )

  );


  // BlockRAM Module

  pcie4_uscale_plus_0_bram 
 #(
   .TCQ(TCQ)
  ,.AXISTEN_IF_MSIX_TO_RAM_PIPELINE(AXISTEN_IF_MSIX_TO_RAM_PIPELINE)
  ,.AXISTEN_IF_MSIX_FROM_RAM_PIPELINE(AXISTEN_IF_MSIX_FROM_RAM_PIPELINE)
  ,.TPH_TO_RAM_PIPELINE(TPH_TO_RAM_PIPELINE)
  ,.TPH_FROM_RAM_PIPELINE(TPH_FROM_RAM_PIPELINE)
  ,.TL_COMPLETION_RAM_SIZE(TL_COMPLETION_RAM_SIZE)
  ,.TL_RX_COMPLETION_TO_RAM_WRITE_PIPELINE(TL_RX_COMPLETION_TO_RAM_WRITE_PIPELINE)
  ,.TL_RX_COMPLETION_TO_RAM_READ_PIPELINE(TL_RX_COMPLETION_TO_RAM_READ_PIPELINE)
  ,.TL_RX_COMPLETION_FROM_RAM_READ_PIPELINE(TL_RX_COMPLETION_FROM_RAM_READ_PIPELINE)
  ,.TL_RX_POSTED_TO_RAM_WRITE_PIPELINE(TL_RX_POSTED_TO_RAM_WRITE_PIPELINE)
  ,.TL_RX_POSTED_TO_RAM_READ_PIPELINE(TL_RX_POSTED_TO_RAM_READ_PIPELINE)
  ,.TL_RX_POSTED_FROM_RAM_READ_PIPELINE(TL_RX_POSTED_FROM_RAM_READ_PIPELINE)
  ,.LL_REPLAY_TO_RAM_PIPELINE(LL_REPLAY_TO_RAM_PIPELINE)
  ,.LL_REPLAY_FROM_RAM_PIPELINE(LL_REPLAY_FROM_RAM_PIPELINE)
  ,.TL_PF_ENABLE_REG(TL_PF_ENABLE_REG)
  ,.SRIOV_CAP_ENABLE(SRIOV_CAP_ENABLE)
  ,.PF0_SRIOV_CAP_TOTAL_VF(PF0_SRIOV_CAP_TOTAL_VF)
  ,.PF1_SRIOV_CAP_TOTAL_VF(PF1_SRIOV_CAP_TOTAL_VF)
  ,.PF2_SRIOV_CAP_TOTAL_VF(PF2_SRIOV_CAP_TOTAL_VF)
  ,.PF3_SRIOV_CAP_TOTAL_VF(PF3_SRIOV_CAP_TOTAL_VF)
  ,.PF0_TPHR_CAP_ENABLE(PF0_TPHR_CAP_ENABLE)
  ,.MSIX_CAP_TABLE_SIZE(MSIX_CAP_TABLE_SIZE)
  ,.MSIX_TABLE_RAM_ENABLE(MSIX_TABLE_RAM_ENABLE)


  ) pcie_4_0_bram_inst (

   .core_clk_i(core_clk)
  ,.user_clk_i(user_clk) 
  ,.reset_i(!reset_n)
  ,.mi_rep_addr_i(mi_replay_ram_address0[8:0])
  ,.mi_rep_wdata_i({mi_replay_ram_write_data1[127:0],mi_replay_ram_write_data0[127:0]})
  ,.mi_rep_wen_i(mi_replay_ram_write_enable0)
  ,.mi_rep_rdata_o({mi_replay_ram_read_data1[127:0],mi_replay_ram_read_data0[127:0]})
  ,.mi_rep_rden_i(mi_replay_ram_read_enable0)
  ,.mi_rep_err_cor_o(mi_replay_ram_err_cor[3:0])
  ,.mi_rep_err_uncor_o(mi_replay_ram_err_uncor[3:0])
  ,.mi_req_waddr0_i(mi_rx_posted_request_ram_write_address0[8:0])
  ,.mi_req_wdata0_i(mi_rx_posted_request_ram_write_data0[143:0])
  ,.mi_req_wen0_i(mi_rx_posted_request_ram_write_enable0)
  ,.mi_req_waddr1_i(mi_rx_posted_request_ram_write_address1[8:0])
  ,.mi_req_wdata1_i(mi_rx_posted_request_ram_write_data1[143:0])
  ,.mi_req_wen1_i(mi_rx_posted_request_ram_write_enable1)
  ,.mi_req_raddr0_i(mi_rx_posted_request_ram_read_address0[8:0])
  ,.mi_req_rdata0_o(mi_rx_posted_request_ram_read_data0[143:0])
  ,.mi_req_ren0_i(mi_rx_posted_request_ram_read_enable0)
  ,.mi_req_raddr1_i(mi_rx_posted_request_ram_read_address1[8:0])
  ,.mi_req_rdata1_o(mi_rx_posted_request_ram_read_data1[143:0])
  ,.mi_req_ren1_i(mi_rx_posted_request_ram_read_enable1)
  ,.mi_req_err_cor_o(mi_rx_posted_request_ram_err_cor[5:0])
  ,.mi_req_err_uncor_o(mi_rx_posted_request_ram_err_uncor[5:0])
  ,.mi_cpl_waddr0_i(mi_rx_completion_ram_write_address0[8:0])
  ,.mi_cpl_wdata0_i(mi_rx_completion_ram_write_data0[143:0])
  ,.mi_cpl_wen0_i(mi_rx_completion_ram_write_enable0[1:0])
  ,.mi_cpl_waddr1_i(mi_rx_completion_ram_write_address1[8:0])
  ,.mi_cpl_wdata1_i(mi_rx_completion_ram_write_data1[143:0])
  ,.mi_cpl_wen1_i(mi_rx_completion_ram_write_enable1[1:0])
  ,.mi_cpl_raddr0_i(mi_rx_completion_ram_read_address0[8:0])
  ,.mi_cpl_rdata0_o(mi_rx_completion_ram_read_data0[143:0])
  ,.mi_cpl_ren0_i(mi_rx_completion_ram_read_enable0[1:0])
  ,.mi_cpl_raddr1_i(mi_rx_completion_ram_read_address1[8:0])
  ,.mi_cpl_rdata1_o(mi_rx_completion_ram_read_data1[143:0])
  ,.mi_cpl_ren1_i(mi_rx_completion_ram_read_enable1[1:0])
  ,.mi_cpl_err_cor_o(mi_rx_completion_ram_err_cor[11:0])
  ,.mi_cpl_err_uncor_o(mi_rx_completion_ram_err_uncor[11:0])
  ,.cfg_msix_waddr_i(cfg_msix_ram_address[12:0])
  ,.cfg_msix_wdata_i(cfg_msix_ram_write_data[31:0])
  ,.cfg_msix_wdip_i(cfg_msix_ram_write_data[35:32])
  ,.cfg_msix_wen_i(cfg_msix_ram_write_byte_enable[3:0])
  ,.cfg_msix_rdata_o(cfg_msix_ram_read_data[31:0])
  ,.cfg_msix_rdop_o(cfg_msix_ram_read_data[35:32])
  ,.cfg_msix_ren_i(cfg_msix_ram_read_enable)
  ,.user_tph_stt_func_num_i(user_tph_stt_func_num[7:0])
  ,.user_tph_stt_index_i(user_tph_stt_index[5:0])
  ,.user_tph_stt_rd_en_i(user_tph_stt_rd_en)
  ,.user_tph_stt_rd_data_o(user_tph_stt_rd_data[7:0])
  ,.cfg_tph_waddr_i(cfg_tph_ram_address[11:0])
  ,.cfg_tph_wdata_i(cfg_tph_ram_write_data[31:0])
  ,.cfg_tph_wdip_i(cfg_tph_ram_write_data[35:32])
  ,.cfg_tph_wen_i(cfg_tph_ram_write_byte_enable[3:0])
  ,.cfg_tph_rdata_o(cfg_tph_ram_read_data[31:0])
  ,.cfg_tph_rdop_o(cfg_tph_ram_read_data[35:32])
  ,.cfg_tph_ren_i(cfg_tph_ram_read_enable)

  );

  assign mi_replay_ram_err_cor[5:4] = 2'b00;
  assign mi_replay_ram_err_uncor[5:4] = 2'b00;

  // Initialization Controller Module

  pcie4_uscale_plus_0_init_ctrl
 #(
    .TCQ(TCQ)
   ,.PL_UPSTREAM_FACING(PL_UPSTREAM_FACING)
   ,.IS_SWITCH_PORT(IS_SWITCH_PORT)
   ,.CRM_CORE_CLK_FREQ_500(CRM_CORE_CLK_FREQ_500)
   ,.CRM_USER_CLK_FREQ(CRM_USER_CLK_FREQ)

  ) pcie_4_0_init_ctrl_inst ( 

    .core_clk_i (core_clk)
   ,.user_clk_i (user_clk)
   ,.reset_n_o (reset_n)
   ,.pipe_reset_n_o (pipe_reset_n)
   ,.mgmt_reset_n_o (mgmt_reset_n)
   ,.mgmt_sticky_reset_n_o (mgmt_sticky_reset_n)
   ,.phy_rdy_i (phy_rdy)
   ,.cfg_hot_reset_in_i(cfg_hot_reset_in)
   ,.cfg_phy_link_down_i(cfg_phy_link_down_wire)
   ,.cfg_phy_link_down_user_clk_o(cfg_phy_link_down_user_clk)
   ,.state_o ()
   ,.user_clk_en_o(user_clk_en)
   ,.user_clkgate_en_o(user_clkgate_en)

  );

  // VF Decode Module
  
  pcie4_uscale_plus_0_vf_decode
 #(
    .TCQ(TCQ)
   ,.TL_PF_ENABLE_REG(TL_PF_ENABLE_REG)
   ,.PF0_SRIOV_CAP_TOTAL_VF(PF0_SRIOV_CAP_TOTAL_VF)
   ,.PF1_SRIOV_CAP_TOTAL_VF(PF1_SRIOV_CAP_TOTAL_VF)
   ,.PF2_SRIOV_CAP_TOTAL_VF(PF2_SRIOV_CAP_TOTAL_VF)
   ,.PF3_SRIOV_CAP_TOTAL_VF(PF3_SRIOV_CAP_TOTAL_VF)
   ,.PF0_SRIOV_FIRST_VF_OFFSET(PF0_SRIOV_FIRST_VF_OFFSET)
   ,.PF1_SRIOV_FIRST_VF_OFFSET(PF1_SRIOV_FIRST_VF_OFFSET)
   ,.PF2_SRIOV_FIRST_VF_OFFSET(PF2_SRIOV_FIRST_VF_OFFSET)
   ,.PF3_SRIOV_FIRST_VF_OFFSET(PF3_SRIOV_FIRST_VF_OFFSET)
   ,.SRIOV_CAP_ENABLE(SRIOV_CAP_ENABLE)
   ,.ARI_CAP_ENABLE(ARI_CAP_ENABLE)

  ) pcie_4_0_vf_decode_inst (

     .clk_i(user_clk)
    ,.reset_i(!reset_n)
    ,.link_down_i(cfg_phy_link_down_user_clk)
    ,.cfg_ext_write_received_i(cfg_ext_write_received)
    ,.cfg_ext_register_number_i(cfg_ext_register_number[9:0])
    ,.cfg_ext_function_number_i(cfg_ext_function_number[7:0])
    ,.cfg_ext_write_data_i(cfg_ext_write_data[31:0])
    ,.cfg_ext_write_byte_enable_i(cfg_ext_write_byte_enable[3:0])
    ,.cfg_flr_in_process_i(cfg_flr_in_process[3:0])

    ,.cfg_vf_flr_in_process_o(cfg_vf_flr_in_process[251:0])
    ,.cfg_vf_status_o(cfg_vf_status[503:0])
    ,.cfg_vf_power_state_o(cfg_vf_power_state[755:0])
    ,.cfg_vf_tph_requester_enable_o(cfg_vf_tph_requester_enable[251:0])
    ,.cfg_vf_tph_st_mode_o(cfg_vf_tph_st_mode[755:0])
    ,.cfg_interrupt_msix_vf_enable_o(cfg_interrupt_msix_vf_enable[251:0])
    ,.cfg_interrupt_msix_vf_mask_o(cfg_interrupt_msix_vf_mask[251:0])

  );

  // PL EQ Interface Module

  pcie4_uscale_plus_0_pl_eq
 #(
     .TCQ(TCQ)
    ,.IMPL_TARGET(IMPL_TARGET)
    ,.PL_UPSTREAM_FACING(PL_UPSTREAM_FACING)

  ) pcie_4_0_pl_eq_inst (

     .clk_i(user_clk)
    ,.reset_i(!reset_n)
    ,.link_down_reset_i(cfg_phy_link_down_user_clk)

    ,.cfg_ltssm_state_i(cfg_ltssm_state[5:0])     
    ,.pl_redo_eq_i(pl_redo_eq)
    ,.pl_redo_eq_speed_i(pl_redo_eq_speed)
    ,.pl_eq_mismatch_o(pl_eq_mismatch)
    ,.pl_redo_eq_pending_o(pl_redo_eq_pending)
    ,.pl_gen34_redo_equalization_o(pl_gen34_redo_equalization)
    ,.pl_gen34_redo_eq_speed_o(pl_gen34_redo_eq_speed)
    ,.pl_gen34_eq_mismatch_i(pl_gen34_eq_mismatch)

  );

  // AXI4ST 256b/512b Bridge Module
  pcie4_uscale_plus_0_512b_intfc
 #(
        .TCQ(TCQ),
        .IMPL_TARGET(IMPL_TARGET),
        .AXISTEN_IF_EXT_512_INTFC_RAM_STYLE(AXISTEN_IF_EXT_512_INTFC_RAM_STYLE),
        .AXI4_USER_DATA_WIDTH(AXI4_DATA_WIDTH),
        .AXI4_CORE_DATA_WIDTH(256),
        .AXI4_USER_CQ_TUSER_WIDTH(AXI4_CQ_TUSER_WIDTH),
        .AXI4_USER_CC_TUSER_WIDTH(AXI4_CC_TUSER_WIDTH),
        .AXI4_USER_RQ_TUSER_WIDTH(AXI4_RQ_TUSER_WIDTH),
        .AXI4_USER_RC_TUSER_WIDTH(AXI4_RC_TUSER_WIDTH),
        .AXI4_CORE_CQ_TUSER_WIDTH(88),
        .AXI4_CORE_CC_TUSER_WIDTH(33),
        .AXI4_CORE_RQ_TUSER_WIDTH(62),
        .AXI4_CORE_RC_TUSER_WIDTH(75),
        .AXI4_USER_CQ_TKEEP_WIDTH(AXI4_TKEEP_WIDTH),
        .AXI4_USER_CC_TKEEP_WIDTH(AXI4_TKEEP_WIDTH),
        .AXI4_USER_RQ_TKEEP_WIDTH(AXI4_TKEEP_WIDTH),
        .AXI4_USER_RC_TKEEP_WIDTH(AXI4_TKEEP_WIDTH),
        .AXI4_CORE_CQ_TKEEP_WIDTH(8),
        .AXI4_CORE_CC_TKEEP_WIDTH(8),
        .AXI4_CORE_RQ_TKEEP_WIDTH(8),
        .AXI4_CORE_RC_TKEEP_WIDTH(8),
        .AXI4_CORE_CQ_TREADY_WIDTH(22),
        .AXI4_CORE_RC_TREADY_WIDTH(22),

        .AXISTEN_IF_EXT_512_CQ_STRADDLE(AXISTEN_IF_EXT_512_CQ_STRADDLE),
        .AXISTEN_IF_EXT_512_CC_STRADDLE(AXISTEN_IF_EXT_512_CC_STRADDLE),
        .AXISTEN_IF_EXT_512_RQ_STRADDLE(AXISTEN_IF_EXT_512_RQ_STRADDLE),
        .AXISTEN_IF_EXT_512_RC_STRADDLE(AXISTEN_IF_EXT_512_RC_STRADDLE),
        .AXISTEN_IF_EXT_512_RC_4TLP_STRADDLE(AXISTEN_IF_EXT_512_RC_4TLP_STRADDLE),
        .AXISTEN_IF_CQ_ALIGNMENT_MODE(AXISTEN_IF_CQ_ALIGNMENT_MODE),
        .AXISTEN_IF_CC_ALIGNMENT_MODE(AXISTEN_IF_CC_ALIGNMENT_MODE),
        .AXISTEN_IF_RQ_ALIGNMENT_MODE(AXISTEN_IF_RQ_ALIGNMENT_MODE),
        .AXISTEN_IF_RC_ALIGNMENT_MODE(AXISTEN_IF_RC_ALIGNMENT_MODE),
        .AXISTEN_IF_RQ_CC_REGISTERED_TREADY(AXISTEN_IF_RQ_CC_REGISTERED_TREADY),
        .AXISTEN_IF_RX_PARITY_EN(AXISTEN_IF_RX_PARITY_EN),
        .AXISTEN_IF_TX_PARITY_EN(AXISTEN_IF_TX_PARITY_EN)

     ) pcie4_0_512b_intfc_mod (

        .user_clk_i         (user_clk),
        .user_clk2_i        (user_clk2),
        .user_clk_en_i      (user_clk_en),
        .reset_n_user_clk_i (reset_n),
        .reset_n_user_clk2_i(reset_n),
        .link_down_reset_i  (cfg_phy_link_down_user_clk),
        //-----------------------------------
        // Client-side signals
        //-----------------------------------
        // CQ Interface
        .m_axis_cq_tdata_o  (m_axis_cq_tdata),
        .m_axis_cq_tvalid_o (m_axis_cq_tvalid),
        .m_axis_cq_tuser_o  (m_axis_cq_tuser),
        .m_axis_cq_tlast_o  (m_axis_cq_tlast),
        .m_axis_cq_tkeep_o  (m_axis_cq_tkeep),
        .m_axis_cq_tready_i (m_axis_cq_tready[0]),
        .pcie_cq_np_req_i   (pcie_cq_np_req),
        .pcie_cq_np_req_count_o(pcie_cq_np_req_count_axi512),
        // CC Interface
        .s_axis_cc_tdata_i  (s_axis_cc_tdata),
        .s_axis_cc_tvalid_i (s_axis_cc_tvalid),
        .s_axis_cc_tuser_i  (s_axis_cc_tuser),
        .s_axis_cc_tlast_i  (s_axis_cc_tlast),
        .s_axis_cc_tkeep_i  (s_axis_cc_tkeep),
        .s_axis_cc_tready_o (s_axis_cc_tready_axi512),
        // RQ Interface
        .s_axis_rq_tdata_i  (s_axis_rq_tdata),
        .s_axis_rq_tvalid_i (s_axis_rq_tvalid),
        .s_axis_rq_tuser_i  (s_axis_rq_tuser),
        .s_axis_rq_tlast_i  (s_axis_rq_tlast),
        .s_axis_rq_tkeep_i  (s_axis_rq_tkeep),
        .s_axis_rq_tready_o (s_axis_rq_tready_axi512),
        // RC Interface
        .m_axis_rc_tdata_o  (m_axis_rc_tdata),
        .m_axis_rc_tvalid_o (m_axis_rc_tvalid),
        .m_axis_rc_tuser_o  (m_axis_rc_tuser),
        .m_axis_rc_tlast_o  (m_axis_rc_tlast),
        .m_axis_rc_tkeep_o  (m_axis_rc_tkeep),
        .m_axis_rc_tready_i (m_axis_rc_tready[0]),
        //-----------------------------------
        // Core-side signals
        //-----------------------------------
        // CQ Interface
        .core_cq_tdata_i    (m_axis_cq_tdata_int),
        .core_cq_tvalid_i   (m_axis_cq_tvalid_int),
        .core_cq_tuser_i    (m_axis_cq_tuser_int),
        .core_cq_tlast_i    (m_axis_cq_tlast_int),
        .core_cq_tkeep_i    (m_axis_cq_tkeep_int),
        .core_cq_tready_o   (m_axis_cq_tready_axi512),
        .posted_req_delivered_o(pcie_posted_req_delivered),
        .cq_pipeline_empty_o(pcie_cq_pipeline_empty),
        .cq_np_user_credit_rcvd_o(pcie_cq_np_user_credit_rcvd),
        // CC Interface
        .core_cc_tdata_o    (s_axis_cc_tdata_axi512),
        .core_cc_tvalid_o   (s_axis_cc_tvalid_axi512),
        .core_cc_tuser_o    (s_axis_cc_tuser_axi512),
        .core_cc_tlast_o    (s_axis_cc_tlast_axi512),
        .core_cc_tkeep_o    (s_axis_cc_tkeep_axi512),
        .core_cc_tready_i   (s_axis_cc_tready_int),
        // RQ Interface
        .core_rq_tdata_o    (s_axis_rq_tdata_axi512),
        .core_rq_tvalid_o   (s_axis_rq_tvalid_axi512),
        .core_rq_tuser_o    (s_axis_rq_tuser_axi512),
        .core_rq_tlast_o    (s_axis_rq_tlast_axi512),
        .core_rq_tkeep_o    (s_axis_rq_tkeep_axi512),
        .core_rq_tready_i   (s_axis_rq_tready_int),
        // RC Interface
        .core_rc_tdata_i    (m_axis_rc_tdata_int),
        .core_rc_tvalid_i   (m_axis_rc_tvalid_int),
        .core_rc_tuser_i    (m_axis_rc_tuser_int),
        .core_rc_tlast_i    (m_axis_rc_tlast_int),
        .core_rc_tkeep_i    (m_axis_rc_tkeep_int),
        .core_rc_tready_o   (m_axis_rc_tready_axi512),
        .compl_delivered_o  (pcie_compl_delivered),
        .compl_delivered_tag0_o(pcie_compl_delivered_tag0),
        .compl_delivered_tag1_o(pcie_compl_delivered_tag1)
        );

      assign s_axis_cc_tdata_int = s_axis_cc_tdata_axi512;
      assign s_axis_cc_tvalid_int = s_axis_cc_tvalid_axi512;
      assign s_axis_cc_tuser_int = s_axis_cc_tuser_axi512;
      assign s_axis_cc_tlast_int = s_axis_cc_tlast_axi512;
      assign s_axis_cc_tkeep_int = s_axis_cc_tkeep_axi512;
      
      assign s_axis_rq_tdata_int = s_axis_rq_tdata_axi512;
      assign s_axis_rq_tvalid_int = s_axis_rq_tvalid_axi512;
      assign s_axis_rq_tuser_int = s_axis_rq_tuser_axi512;
      assign s_axis_rq_tlast_int = s_axis_rq_tlast_axi512;
      assign s_axis_rq_tkeep_int = s_axis_rq_tkeep_axi512;

    
   assign m_axis_cq_tready_int[21:0] = (AXISTEN_IF_EXT_512 == "TRUE") ? 
                                                           m_axis_cq_tready_axi512 :
                                                           m_axis_cq_tready;

   assign m_axis_rc_tready_int[21:0] = (AXISTEN_IF_EXT_512 == "TRUE") ? 
                                                           m_axis_rc_tready_axi512 :
                                                           m_axis_rc_tready;

   assign s_axis_cc_tready = (AXISTEN_IF_EXT_512 == "TRUE") ? {4{s_axis_cc_tready_axi512}} :
                                                              s_axis_cc_tready_int;

   assign s_axis_rq_tready = (AXISTEN_IF_EXT_512 == "TRUE") ? {4{s_axis_rq_tready_axi512}} :
                                                              s_axis_rq_tready_int;

   assign pcie_cq_np_req_count = (AXISTEN_IF_EXT_512 == "TRUE") ? pcie_cq_np_req_count_axi512:
                                                                  pcie_cq_np_req_count_int;



  generate if ((TL_USER_SPARE[1]) ||
               ((CRM_CORE_CLK_FREQ_500 == "TRUE") && (CRM_USER_CLK_FREQ[1:0] == 2'b11)) ||
               ((CRM_CORE_CLK_FREQ_500 == "FALSE") && (CRM_USER_CLK_FREQ[1:0] == 2'b10))) begin: seqnum_fifo_bypass
  
    assign pcie_rq_seq_num0[5:0] = pcie_rq_seq_num0_cc[5:0];
    assign pcie_rq_seq_num_vld0 = pcie_rq_seq_num_vld0_cc;
  
  end else begin: seqnum_fifo
  
     //
     // Sequence Number FIFOs
     //

  pcie4_uscale_plus_0_seqnum_fifo #(
     .RAM_WIDTH(7), 
     .RAM_DEPTH(16), 
     .FIFO_FULL_HIGH_THRESHOLD(16),
     .ADDR_WIDTH(4)
   ) seq_fifo_0 (
     .core_reset_n_i(reset_n),
     .core_clk_i(core_clk),
     .user_reset_n_i(reset_n),
     .user_clk_i(user_clk),
     .data_i({pcie_rq_seq_num_vld0_cc, pcie_rq_seq_num0_cc[5:0]}),
     .data_o({pcie_rq_seq_num_vld0, pcie_rq_seq_num0[5:0]})
   );

  end
  endgenerate


endmodule
