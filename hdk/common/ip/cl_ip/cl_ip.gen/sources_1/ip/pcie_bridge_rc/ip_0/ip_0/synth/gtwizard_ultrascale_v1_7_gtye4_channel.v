// (c) Copyright 2013-2015, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and international copyright
// and other intellectual property laws.
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
////////////////////////////////////////////////////////////

// ***************************
// * DO NOT MODIFY THIS FILE *
// ***************************

`timescale 1ps/1ps

module gtwizard_ultrascale_v1_7_18_gtye4_channel #(


  // -------------------------------------------------------------------------------------------------------------------
  // Parameters controlling primitive wrapper HDL generation
  // -------------------------------------------------------------------------------------------------------------------
  parameter         NUM_CHANNELS = 4,


  // -------------------------------------------------------------------------------------------------------------------
  // Parameters relating to GTYE4_CHANNEL primitive
  // -------------------------------------------------------------------------------------------------------------------

  // primitive wrapper parameters which override corresponding GTYE4_CHANNEL primitive parameters
  parameter   [0:0] GTYE4_CHANNEL_ACJTAG_DEBUG_MODE = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_ACJTAG_MODE = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_ACJTAG_RESET = 1'b0,
  parameter  [15:0] GTYE4_CHANNEL_ADAPT_CFG0 = 16'h9200,
  parameter  [15:0] GTYE4_CHANNEL_ADAPT_CFG1 = 16'h801C,
  parameter  [15:0] GTYE4_CHANNEL_ADAPT_CFG2 = 16'h0000,
  parameter         GTYE4_CHANNEL_ALIGN_COMMA_DOUBLE = "FALSE",
  parameter   [9:0] GTYE4_CHANNEL_ALIGN_COMMA_ENABLE = 10'b0001111111,
  parameter integer GTYE4_CHANNEL_ALIGN_COMMA_WORD = 1,
  parameter         GTYE4_CHANNEL_ALIGN_MCOMMA_DET = "TRUE",
  parameter   [9:0] GTYE4_CHANNEL_ALIGN_MCOMMA_VALUE = 10'b1010000011,
  parameter         GTYE4_CHANNEL_ALIGN_PCOMMA_DET = "TRUE",
  parameter   [9:0] GTYE4_CHANNEL_ALIGN_PCOMMA_VALUE = 10'b0101111100,
  parameter   [0:0] GTYE4_CHANNEL_A_RXOSCALRESET = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_A_RXPROGDIVRESET = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_A_RXTERMINATION = 1'b1,
  parameter   [4:0] GTYE4_CHANNEL_A_TXDIFFCTRL = 5'b01100,
  parameter   [0:0] GTYE4_CHANNEL_A_TXPROGDIVRESET = 1'b0,
  parameter         GTYE4_CHANNEL_CBCC_DATA_SOURCE_SEL = "DECODED",
  parameter   [0:0] GTYE4_CHANNEL_CDR_SWAP_MODE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_CFOK_PWRSVE_EN = 1'b1,
  parameter         GTYE4_CHANNEL_CHAN_BOND_KEEP_ALIGN = "FALSE",
  parameter integer GTYE4_CHANNEL_CHAN_BOND_MAX_SKEW = 7,
  parameter   [9:0] GTYE4_CHANNEL_CHAN_BOND_SEQ_1_1 = 10'b0101111100,
  parameter   [9:0] GTYE4_CHANNEL_CHAN_BOND_SEQ_1_2 = 10'b0000000000,
  parameter   [9:0] GTYE4_CHANNEL_CHAN_BOND_SEQ_1_3 = 10'b0000000000,
  parameter   [9:0] GTYE4_CHANNEL_CHAN_BOND_SEQ_1_4 = 10'b0000000000,
  parameter   [3:0] GTYE4_CHANNEL_CHAN_BOND_SEQ_1_ENABLE = 4'b1111,
  parameter   [9:0] GTYE4_CHANNEL_CHAN_BOND_SEQ_2_1 = 10'b0100000000,
  parameter   [9:0] GTYE4_CHANNEL_CHAN_BOND_SEQ_2_2 = 10'b0100000000,
  parameter   [9:0] GTYE4_CHANNEL_CHAN_BOND_SEQ_2_3 = 10'b0100000000,
  parameter   [9:0] GTYE4_CHANNEL_CHAN_BOND_SEQ_2_4 = 10'b0100000000,
  parameter   [3:0] GTYE4_CHANNEL_CHAN_BOND_SEQ_2_ENABLE = 4'b1111,
  parameter         GTYE4_CHANNEL_CHAN_BOND_SEQ_2_USE = "FALSE",
  parameter integer GTYE4_CHANNEL_CHAN_BOND_SEQ_LEN = 2,
  parameter  [15:0] GTYE4_CHANNEL_CH_HSPMUX = 16'h2424,
  parameter  [15:0] GTYE4_CHANNEL_CKCAL1_CFG_0 = 16'b1100000011000000,
  parameter  [15:0] GTYE4_CHANNEL_CKCAL1_CFG_1 = 16'b0101000011000000,
  parameter  [15:0] GTYE4_CHANNEL_CKCAL1_CFG_2 = 16'b0000000000000000,
  parameter  [15:0] GTYE4_CHANNEL_CKCAL1_CFG_3 = 16'b0000000000000000,
  parameter  [15:0] GTYE4_CHANNEL_CKCAL2_CFG_0 = 16'b1100000011000000,
  parameter  [15:0] GTYE4_CHANNEL_CKCAL2_CFG_1 = 16'b1000000011000000,
  parameter  [15:0] GTYE4_CHANNEL_CKCAL2_CFG_2 = 16'b0000000000000000,
  parameter  [15:0] GTYE4_CHANNEL_CKCAL2_CFG_3 = 16'b0000000000000000,
  parameter  [15:0] GTYE4_CHANNEL_CKCAL2_CFG_4 = 16'b0000000000000000,
  parameter         GTYE4_CHANNEL_CLK_CORRECT_USE = "TRUE",
  parameter         GTYE4_CHANNEL_CLK_COR_KEEP_IDLE = "FALSE",
  parameter integer GTYE4_CHANNEL_CLK_COR_MAX_LAT = 20,
  parameter integer GTYE4_CHANNEL_CLK_COR_MIN_LAT = 18,
  parameter         GTYE4_CHANNEL_CLK_COR_PRECEDENCE = "TRUE",
  parameter integer GTYE4_CHANNEL_CLK_COR_REPEAT_WAIT = 0,
  parameter   [9:0] GTYE4_CHANNEL_CLK_COR_SEQ_1_1 = 10'b0100011100,
  parameter   [9:0] GTYE4_CHANNEL_CLK_COR_SEQ_1_2 = 10'b0000000000,
  parameter   [9:0] GTYE4_CHANNEL_CLK_COR_SEQ_1_3 = 10'b0000000000,
  parameter   [9:0] GTYE4_CHANNEL_CLK_COR_SEQ_1_4 = 10'b0000000000,
  parameter   [3:0] GTYE4_CHANNEL_CLK_COR_SEQ_1_ENABLE = 4'b1111,
  parameter   [9:0] GTYE4_CHANNEL_CLK_COR_SEQ_2_1 = 10'b0100000000,
  parameter   [9:0] GTYE4_CHANNEL_CLK_COR_SEQ_2_2 = 10'b0100000000,
  parameter   [9:0] GTYE4_CHANNEL_CLK_COR_SEQ_2_3 = 10'b0100000000,
  parameter   [9:0] GTYE4_CHANNEL_CLK_COR_SEQ_2_4 = 10'b0100000000,
  parameter   [3:0] GTYE4_CHANNEL_CLK_COR_SEQ_2_ENABLE = 4'b1111,
  parameter         GTYE4_CHANNEL_CLK_COR_SEQ_2_USE = "FALSE",
  parameter integer GTYE4_CHANNEL_CLK_COR_SEQ_LEN = 2,
  parameter  [15:0] GTYE4_CHANNEL_CPLL_CFG0 = 16'h01FA,
  parameter  [15:0] GTYE4_CHANNEL_CPLL_CFG1 = 16'h24A9,
  parameter  [15:0] GTYE4_CHANNEL_CPLL_CFG2 = 16'h6807,
  parameter  [15:0] GTYE4_CHANNEL_CPLL_CFG3 = 16'h0000,
  parameter integer GTYE4_CHANNEL_CPLL_FBDIV = 4,
  parameter integer GTYE4_CHANNEL_CPLL_FBDIV_45 = 4,
  parameter  [15:0] GTYE4_CHANNEL_CPLL_INIT_CFG0 = 16'h001E,
  parameter  [15:0] GTYE4_CHANNEL_CPLL_LOCK_CFG = 16'h01E8,
  parameter integer GTYE4_CHANNEL_CPLL_REFCLK_DIV = 1,
  parameter   [2:0] GTYE4_CHANNEL_CTLE3_OCAP_EXT_CTRL = 3'b000,
  parameter   [0:0] GTYE4_CHANNEL_CTLE3_OCAP_EXT_EN = 1'b0,
  parameter   [1:0] GTYE4_CHANNEL_DDI_CTRL = 2'b00,
  parameter integer GTYE4_CHANNEL_DDI_REALIGN_WAIT = 15,
  parameter         GTYE4_CHANNEL_DEC_MCOMMA_DETECT = "TRUE",
  parameter         GTYE4_CHANNEL_DEC_PCOMMA_DETECT = "TRUE",
  parameter         GTYE4_CHANNEL_DEC_VALID_COMMA_ONLY = "TRUE",
  parameter   [0:0] GTYE4_CHANNEL_DELAY_ELEC = 1'b0,
  parameter   [9:0] GTYE4_CHANNEL_DMONITOR_CFG0 = 10'h000,
  parameter   [7:0] GTYE4_CHANNEL_DMONITOR_CFG1 = 8'h00,
  parameter   [0:0] GTYE4_CHANNEL_ES_CLK_PHASE_SEL = 1'b0,
  parameter   [5:0] GTYE4_CHANNEL_ES_CONTROL = 6'b000000,
  parameter         GTYE4_CHANNEL_ES_ERRDET_EN = "FALSE",
  parameter         GTYE4_CHANNEL_ES_EYE_SCAN_EN = "FALSE",
  parameter  [11:0] GTYE4_CHANNEL_ES_HORZ_OFFSET = 12'h800,
  parameter   [4:0] GTYE4_CHANNEL_ES_PRESCALE = 5'b00000,
  parameter  [15:0] GTYE4_CHANNEL_ES_QUALIFIER0 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_ES_QUALIFIER1 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_ES_QUALIFIER2 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_ES_QUALIFIER3 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_ES_QUALIFIER4 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_ES_QUALIFIER5 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_ES_QUALIFIER6 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_ES_QUALIFIER7 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_ES_QUALIFIER8 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_ES_QUALIFIER9 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_ES_QUAL_MASK0 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_ES_QUAL_MASK1 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_ES_QUAL_MASK2 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_ES_QUAL_MASK3 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_ES_QUAL_MASK4 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_ES_QUAL_MASK5 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_ES_QUAL_MASK6 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_ES_QUAL_MASK7 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_ES_QUAL_MASK8 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_ES_QUAL_MASK9 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_ES_SDATA_MASK0 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_ES_SDATA_MASK1 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_ES_SDATA_MASK2 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_ES_SDATA_MASK3 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_ES_SDATA_MASK4 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_ES_SDATA_MASK5 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_ES_SDATA_MASK6 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_ES_SDATA_MASK7 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_ES_SDATA_MASK8 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_ES_SDATA_MASK9 = 16'h0000,
  parameter integer GTYE4_CHANNEL_EYESCAN_VP_RANGE = 0,
  parameter   [0:0] GTYE4_CHANNEL_EYE_SCAN_SWAP_EN = 1'b0,
  parameter   [3:0] GTYE4_CHANNEL_FTS_DESKEW_SEQ_ENABLE = 4'b1111,
  parameter   [3:0] GTYE4_CHANNEL_FTS_LANE_DESKEW_CFG = 4'b1111,
  parameter         GTYE4_CHANNEL_FTS_LANE_DESKEW_EN = "FALSE",
  parameter   [4:0] GTYE4_CHANNEL_GEARBOX_MODE = 5'b00000,
  parameter   [0:0] GTYE4_CHANNEL_ISCAN_CK_PH_SEL2 = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_LOCAL_MASTER = 1'b0,
  parameter integer GTYE4_CHANNEL_LPBK_BIAS_CTRL = 4,
  parameter   [0:0] GTYE4_CHANNEL_LPBK_EN_RCAL_B = 1'b0,
  parameter   [3:0] GTYE4_CHANNEL_LPBK_EXT_RCAL = 4'b0000,
  parameter integer GTYE4_CHANNEL_LPBK_IND_CTRL0 = 5,
  parameter integer GTYE4_CHANNEL_LPBK_IND_CTRL1 = 5,
  parameter integer GTYE4_CHANNEL_LPBK_IND_CTRL2 = 5,
  parameter integer GTYE4_CHANNEL_LPBK_RG_CTRL = 2,
  parameter   [1:0] GTYE4_CHANNEL_OOBDIVCTL = 2'b00,
  parameter   [0:0] GTYE4_CHANNEL_OOB_PWRUP = 1'b0,
  parameter         GTYE4_CHANNEL_PCI3_AUTO_REALIGN = "FRST_SMPL",
  parameter   [0:0] GTYE4_CHANNEL_PCI3_PIPE_RX_ELECIDLE = 1'b1,
  parameter   [1:0] GTYE4_CHANNEL_PCI3_RX_ASYNC_EBUF_BYPASS = 2'b00,
  parameter   [0:0] GTYE4_CHANNEL_PCI3_RX_ELECIDLE_EI2_ENABLE = 1'b0,
  parameter   [5:0] GTYE4_CHANNEL_PCI3_RX_ELECIDLE_H2L_COUNT = 6'b000000,
  parameter   [2:0] GTYE4_CHANNEL_PCI3_RX_ELECIDLE_H2L_DISABLE = 3'b000,
  parameter   [5:0] GTYE4_CHANNEL_PCI3_RX_ELECIDLE_HI_COUNT = 6'b000000,
  parameter   [0:0] GTYE4_CHANNEL_PCI3_RX_ELECIDLE_LP4_DISABLE = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_PCI3_RX_FIFO_DISABLE = 1'b0,
  parameter   [4:0] GTYE4_CHANNEL_PCIE3_CLK_COR_EMPTY_THRSH = 5'b00000,
  parameter   [5:0] GTYE4_CHANNEL_PCIE3_CLK_COR_FULL_THRSH = 6'b010000,
  parameter   [4:0] GTYE4_CHANNEL_PCIE3_CLK_COR_MAX_LAT = 5'b01000,
  parameter   [4:0] GTYE4_CHANNEL_PCIE3_CLK_COR_MIN_LAT = 5'b00100,
  parameter   [5:0] GTYE4_CHANNEL_PCIE3_CLK_COR_THRSH_TIMER = 6'b001000,
  parameter         GTYE4_CHANNEL_PCIE_64B_DYN_CLKSW_DIS = "FALSE",
  parameter  [15:0] GTYE4_CHANNEL_PCIE_BUFG_DIV_CTRL = 16'h0000,
  parameter         GTYE4_CHANNEL_PCIE_GEN4_64BIT_INT_EN = "FALSE",
  parameter   [1:0] GTYE4_CHANNEL_PCIE_PLL_SEL_MODE_GEN12 = 2'h0,
  parameter   [1:0] GTYE4_CHANNEL_PCIE_PLL_SEL_MODE_GEN3 = 2'h0,
  parameter   [1:0] GTYE4_CHANNEL_PCIE_PLL_SEL_MODE_GEN4 = 2'h0,
  parameter  [15:0] GTYE4_CHANNEL_PCIE_RXPCS_CFG_GEN3 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_PCIE_RXPMA_CFG = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_PCIE_TXPCS_CFG_GEN3 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_PCIE_TXPMA_CFG = 16'h0000,
  parameter         GTYE4_CHANNEL_PCS_PCIE_EN = "FALSE",
  parameter  [15:0] GTYE4_CHANNEL_PCS_RSVD0 = 16'h0000,
  parameter  [11:0] GTYE4_CHANNEL_PD_TRANS_TIME_FROM_P2 = 12'h03C,
  parameter   [7:0] GTYE4_CHANNEL_PD_TRANS_TIME_NONE_P2 = 8'h19,
  parameter   [7:0] GTYE4_CHANNEL_PD_TRANS_TIME_TO_P2 = 8'h64,
  parameter integer GTYE4_CHANNEL_PREIQ_FREQ_BST = 0,
  parameter   [0:0] GTYE4_CHANNEL_RATE_SW_USE_DRP = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RCLK_SIPO_DLY_ENB = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RCLK_SIPO_INV_EN = 1'b0,
  parameter   [2:0] GTYE4_CHANNEL_RTX_BUF_CML_CTRL = 3'b010,
  parameter   [1:0] GTYE4_CHANNEL_RTX_BUF_TERM_CTRL = 2'b00,
  parameter   [4:0] GTYE4_CHANNEL_RXBUFRESET_TIME = 5'b00001,
  parameter         GTYE4_CHANNEL_RXBUF_ADDR_MODE = "FULL",
  parameter   [3:0] GTYE4_CHANNEL_RXBUF_EIDLE_HI_CNT = 4'b1000,
  parameter   [3:0] GTYE4_CHANNEL_RXBUF_EIDLE_LO_CNT = 4'b0000,
  parameter         GTYE4_CHANNEL_RXBUF_EN = "TRUE",
  parameter         GTYE4_CHANNEL_RXBUF_RESET_ON_CB_CHANGE = "TRUE",
  parameter         GTYE4_CHANNEL_RXBUF_RESET_ON_COMMAALIGN = "FALSE",
  parameter         GTYE4_CHANNEL_RXBUF_RESET_ON_EIDLE = "FALSE",
  parameter         GTYE4_CHANNEL_RXBUF_RESET_ON_RATE_CHANGE = "TRUE",
  parameter integer GTYE4_CHANNEL_RXBUF_THRESH_OVFLW = 0,
  parameter         GTYE4_CHANNEL_RXBUF_THRESH_OVRD = "FALSE",
  parameter integer GTYE4_CHANNEL_RXBUF_THRESH_UNDFLW = 4,
  parameter   [4:0] GTYE4_CHANNEL_RXCDRFREQRESET_TIME = 5'b10000,
  parameter   [4:0] GTYE4_CHANNEL_RXCDRPHRESET_TIME = 5'b00001,
  parameter  [15:0] GTYE4_CHANNEL_RXCDR_CFG0 = 16'h0003,
  parameter  [15:0] GTYE4_CHANNEL_RXCDR_CFG0_GEN3 = 16'h0003,
  parameter  [15:0] GTYE4_CHANNEL_RXCDR_CFG1 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXCDR_CFG1_GEN3 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXCDR_CFG2 = 16'h0164,
  parameter   [9:0] GTYE4_CHANNEL_RXCDR_CFG2_GEN2 = 10'h164,
  parameter  [15:0] GTYE4_CHANNEL_RXCDR_CFG2_GEN3 = 16'h0034,
  parameter  [15:0] GTYE4_CHANNEL_RXCDR_CFG2_GEN4 = 16'h0034,
  parameter  [15:0] GTYE4_CHANNEL_RXCDR_CFG3 = 16'h0024,
  parameter   [5:0] GTYE4_CHANNEL_RXCDR_CFG3_GEN2 = 6'h24,
  parameter  [15:0] GTYE4_CHANNEL_RXCDR_CFG3_GEN3 = 16'h0024,
  parameter  [15:0] GTYE4_CHANNEL_RXCDR_CFG3_GEN4 = 16'h0024,
  parameter  [15:0] GTYE4_CHANNEL_RXCDR_CFG4 = 16'h5CF6,
  parameter  [15:0] GTYE4_CHANNEL_RXCDR_CFG4_GEN3 = 16'h5CF6,
  parameter  [15:0] GTYE4_CHANNEL_RXCDR_CFG5 = 16'hB46B,
  parameter  [15:0] GTYE4_CHANNEL_RXCDR_CFG5_GEN3 = 16'h146B,
  parameter   [0:0] GTYE4_CHANNEL_RXCDR_FR_RESET_ON_EIDLE = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXCDR_HOLD_DURING_EIDLE = 1'b0,
  parameter  [15:0] GTYE4_CHANNEL_RXCDR_LOCK_CFG0 = 16'h0040,
  parameter  [15:0] GTYE4_CHANNEL_RXCDR_LOCK_CFG1 = 16'h8000,
  parameter  [15:0] GTYE4_CHANNEL_RXCDR_LOCK_CFG2 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXCDR_LOCK_CFG3 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXCDR_LOCK_CFG4 = 16'h0000,
  parameter   [0:0] GTYE4_CHANNEL_RXCDR_PH_RESET_ON_EIDLE = 1'b0,
  parameter  [15:0] GTYE4_CHANNEL_RXCFOK_CFG0 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXCFOK_CFG1 = 16'h0002,
  parameter  [15:0] GTYE4_CHANNEL_RXCFOK_CFG2 = 16'h002D,
  parameter  [15:0] GTYE4_CHANNEL_RXCKCAL1_IQ_LOOP_RST_CFG = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXCKCAL1_I_LOOP_RST_CFG = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXCKCAL1_Q_LOOP_RST_CFG = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXCKCAL2_DX_LOOP_RST_CFG = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXCKCAL2_D_LOOP_RST_CFG = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXCKCAL2_S_LOOP_RST_CFG = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXCKCAL2_X_LOOP_RST_CFG = 16'h0000,
  parameter   [6:0] GTYE4_CHANNEL_RXDFELPMRESET_TIME = 7'b0001111,
  parameter  [15:0] GTYE4_CHANNEL_RXDFELPM_KL_CFG0 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXDFELPM_KL_CFG1 = 16'h0022,
  parameter  [15:0] GTYE4_CHANNEL_RXDFELPM_KL_CFG2 = 16'h0100,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_CFG0 = 16'h4000,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_CFG1 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_GC_CFG0 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_GC_CFG1 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_GC_CFG2 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_H2_CFG0 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_H2_CFG1 = 16'h0002,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_H3_CFG0 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_H3_CFG1 = 16'h0002,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_H4_CFG0 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_H4_CFG1 = 16'h0003,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_H5_CFG0 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_H5_CFG1 = 16'h0002,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_H6_CFG0 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_H6_CFG1 = 16'h0002,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_H7_CFG0 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_H7_CFG1 = 16'h0002,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_H8_CFG0 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_H8_CFG1 = 16'h0002,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_H9_CFG0 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_H9_CFG1 = 16'h0002,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_HA_CFG0 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_HA_CFG1 = 16'h0002,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_HB_CFG0 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_HB_CFG1 = 16'h0002,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_HC_CFG0 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_HC_CFG1 = 16'h0002,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_HD_CFG0 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_HD_CFG1 = 16'h0002,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_HE_CFG0 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_HE_CFG1 = 16'h0002,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_HF_CFG0 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_HF_CFG1 = 16'h0002,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_KH_CFG0 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_KH_CFG1 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_KH_CFG2 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_KH_CFG3 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_OS_CFG0 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_OS_CFG1 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_UT_CFG0 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_UT_CFG1 = 16'h0002,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_UT_CFG2 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_VP_CFG0 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXDFE_VP_CFG1 = 16'h0022,
  parameter  [15:0] GTYE4_CHANNEL_RXDLY_CFG = 16'h0010,
  parameter  [15:0] GTYE4_CHANNEL_RXDLY_LCFG = 16'h0030,
  parameter         GTYE4_CHANNEL_RXELECIDLE_CFG = "SIGCFG_4",
  parameter integer GTYE4_CHANNEL_RXGBOX_FIFO_INIT_RD_ADDR = 4,
  parameter         GTYE4_CHANNEL_RXGEARBOX_EN = "FALSE",
  parameter   [4:0] GTYE4_CHANNEL_RXISCANRESET_TIME = 5'b00001,
  parameter  [15:0] GTYE4_CHANNEL_RXLPM_CFG = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXLPM_GC_CFG = 16'h1000,
  parameter  [15:0] GTYE4_CHANNEL_RXLPM_KH_CFG0 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXLPM_KH_CFG1 = 16'h0002,
  parameter  [15:0] GTYE4_CHANNEL_RXLPM_OS_CFG0 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXLPM_OS_CFG1 = 16'h0000,
  parameter   [8:0] GTYE4_CHANNEL_RXOOB_CFG = 9'b000110000,
  parameter         GTYE4_CHANNEL_RXOOB_CLK_CFG = "PMA",
  parameter   [4:0] GTYE4_CHANNEL_RXOSCALRESET_TIME = 5'b00011,
  parameter integer GTYE4_CHANNEL_RXOUT_DIV = 4,
  parameter   [4:0] GTYE4_CHANNEL_RXPCSRESET_TIME = 5'b00001,
  parameter  [15:0] GTYE4_CHANNEL_RXPHBEACON_CFG = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_RXPHDLY_CFG = 16'h2020,
  parameter  [15:0] GTYE4_CHANNEL_RXPHSAMP_CFG = 16'h2100,
  parameter  [15:0] GTYE4_CHANNEL_RXPHSLIP_CFG = 16'h9933,
  parameter   [4:0] GTYE4_CHANNEL_RXPH_MONITOR_SEL = 5'b00000,
  parameter  [15:0] GTYE4_CHANNEL_RXPI_CFG0 = 16'h0102,
  parameter  [15:0] GTYE4_CHANNEL_RXPI_CFG1 = 16'b0000000001010100,
  parameter         GTYE4_CHANNEL_RXPMACLK_SEL = "DATA",
  parameter   [4:0] GTYE4_CHANNEL_RXPMARESET_TIME = 5'b00001,
  parameter   [0:0] GTYE4_CHANNEL_RXPRBS_ERR_LOOPBACK = 1'b0,
  parameter integer GTYE4_CHANNEL_RXPRBS_LINKACQ_CNT = 15,
  parameter   [0:0] GTYE4_CHANNEL_RXREFCLKDIV2_SEL = 1'b0,
  parameter integer GTYE4_CHANNEL_RXSLIDE_AUTO_WAIT = 7,
  parameter         GTYE4_CHANNEL_RXSLIDE_MODE = "OFF",
  parameter   [0:0] GTYE4_CHANNEL_RXSYNC_MULTILANE = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXSYNC_OVRD = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXSYNC_SKIP_DA = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RX_AFE_CM_EN = 1'b0,
  parameter  [15:0] GTYE4_CHANNEL_RX_BIAS_CFG0 = 16'h12B0,
  parameter   [5:0] GTYE4_CHANNEL_RX_BUFFER_CFG = 6'b000000,
  parameter   [0:0] GTYE4_CHANNEL_RX_CAPFF_SARC_ENB = 1'b0,
  parameter integer GTYE4_CHANNEL_RX_CLK25_DIV = 8,
  parameter   [0:0] GTYE4_CHANNEL_RX_CLKMUX_EN = 1'b1,
  parameter   [4:0] GTYE4_CHANNEL_RX_CLK_SLIP_OVRD = 5'b00000,
  parameter   [3:0] GTYE4_CHANNEL_RX_CM_BUF_CFG = 4'b1010,
  parameter   [0:0] GTYE4_CHANNEL_RX_CM_BUF_PD = 1'b0,
  parameter integer GTYE4_CHANNEL_RX_CM_SEL = 3,
  parameter integer GTYE4_CHANNEL_RX_CM_TRIM = 12,
  parameter   [0:0] GTYE4_CHANNEL_RX_CTLE_PWR_SAVING = 1'b0,
  parameter   [3:0] GTYE4_CHANNEL_RX_CTLE_RES_CTRL = 4'b0000,
  parameter integer GTYE4_CHANNEL_RX_DATA_WIDTH = 20,
  parameter   [5:0] GTYE4_CHANNEL_RX_DDI_SEL = 6'b000000,
  parameter         GTYE4_CHANNEL_RX_DEFER_RESET_BUF_EN = "TRUE",
  parameter   [2:0] GTYE4_CHANNEL_RX_DEGEN_CTRL = 3'b100,
  parameter integer GTYE4_CHANNEL_RX_DFELPM_CFG0 = 0,
  parameter   [0:0] GTYE4_CHANNEL_RX_DFELPM_CFG1 = 1'b1,
  parameter   [0:0] GTYE4_CHANNEL_RX_DFELPM_KLKH_AGC_STUP_EN = 1'b1,
  parameter integer GTYE4_CHANNEL_RX_DFE_AGC_CFG1 = 4,
  parameter integer GTYE4_CHANNEL_RX_DFE_KL_LPM_KH_CFG0 = 1,
  parameter integer GTYE4_CHANNEL_RX_DFE_KL_LPM_KH_CFG1 = 4,
  parameter   [1:0] GTYE4_CHANNEL_RX_DFE_KL_LPM_KL_CFG0 = 2'b01,
  parameter integer GTYE4_CHANNEL_RX_DFE_KL_LPM_KL_CFG1 = 4,
  parameter   [0:0] GTYE4_CHANNEL_RX_DFE_LPM_HOLD_DURING_EIDLE = 1'b0,
  parameter         GTYE4_CHANNEL_RX_DISPERR_SEQ_MATCH = "TRUE",
  parameter   [4:0] GTYE4_CHANNEL_RX_DIVRESET_TIME = 5'b00001,
  parameter   [0:0] GTYE4_CHANNEL_RX_EN_CTLE_RCAL_B = 1'b0,
  parameter integer GTYE4_CHANNEL_RX_EN_SUM_RCAL_B = 0,
  parameter   [6:0] GTYE4_CHANNEL_RX_EYESCAN_VS_CODE = 7'b0000000,
  parameter   [0:0] GTYE4_CHANNEL_RX_EYESCAN_VS_NEG_DIR = 1'b0,
  parameter   [1:0] GTYE4_CHANNEL_RX_EYESCAN_VS_RANGE = 2'b10,
  parameter   [0:0] GTYE4_CHANNEL_RX_EYESCAN_VS_UT_SIGN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RX_FABINT_USRCLK_FLOP = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RX_I2V_FILTER_EN = 1'b1,
  parameter integer GTYE4_CHANNEL_RX_INT_DATAWIDTH = 1,
  parameter   [0:0] GTYE4_CHANNEL_RX_PMA_POWER_SAVE = 1'b0,
  parameter  [15:0] GTYE4_CHANNEL_RX_PMA_RSV0 = 16'h000F,
  parameter    real GTYE4_CHANNEL_RX_PROGDIV_CFG = 0.0,
  parameter  [15:0] GTYE4_CHANNEL_RX_PROGDIV_RATE = 16'h0001,
  parameter   [3:0] GTYE4_CHANNEL_RX_RESLOAD_CTRL = 4'b0000,
  parameter   [0:0] GTYE4_CHANNEL_RX_RESLOAD_OVRD = 1'b0,
  parameter   [2:0] GTYE4_CHANNEL_RX_SAMPLE_PERIOD = 3'b101,
  parameter integer GTYE4_CHANNEL_RX_SIG_VALID_DLY = 11,
  parameter integer GTYE4_CHANNEL_RX_SUM_DEGEN_AVTT_OVERITE = 0,
  parameter   [0:0] GTYE4_CHANNEL_RX_SUM_DFETAPREP_EN = 1'b0,
  parameter   [3:0] GTYE4_CHANNEL_RX_SUM_IREF_TUNE = 4'b0000,
  parameter integer GTYE4_CHANNEL_RX_SUM_PWR_SAVING = 0,
  parameter   [3:0] GTYE4_CHANNEL_RX_SUM_RES_CTRL = 4'b0000,
  parameter   [3:0] GTYE4_CHANNEL_RX_SUM_VCMTUNE = 4'b0011,
  parameter   [0:0] GTYE4_CHANNEL_RX_SUM_VCM_BIAS_TUNE_EN = 1'b1,
  parameter   [0:0] GTYE4_CHANNEL_RX_SUM_VCM_OVWR = 1'b0,
  parameter   [2:0] GTYE4_CHANNEL_RX_SUM_VREF_TUNE = 3'b100,
  parameter   [1:0] GTYE4_CHANNEL_RX_TUNE_AFE_OS = 2'b00,
  parameter   [2:0] GTYE4_CHANNEL_RX_VREG_CTRL = 3'b010,
  parameter   [0:0] GTYE4_CHANNEL_RX_VREG_PDB = 1'b1,
  parameter   [1:0] GTYE4_CHANNEL_RX_WIDEMODE_CDR = 2'b01,
  parameter   [1:0] GTYE4_CHANNEL_RX_WIDEMODE_CDR_GEN3 = 2'b01,
  parameter   [1:0] GTYE4_CHANNEL_RX_WIDEMODE_CDR_GEN4 = 2'b01,
  parameter         GTYE4_CHANNEL_RX_XCLK_SEL = "RXDES",
  parameter   [0:0] GTYE4_CHANNEL_RX_XMODE_SEL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_SAMPLE_CLK_PHASE = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_SAS_12G_MODE = 1'b0,
  parameter   [3:0] GTYE4_CHANNEL_SATA_BURST_SEQ_LEN = 4'b1111,
  parameter   [2:0] GTYE4_CHANNEL_SATA_BURST_VAL = 3'b100,
  parameter         GTYE4_CHANNEL_SATA_CPLL_CFG = "VCO_3000MHZ",
  parameter   [2:0] GTYE4_CHANNEL_SATA_EIDLE_VAL = 3'b100,
  parameter         GTYE4_CHANNEL_SHOW_REALIGN_COMMA = "TRUE",
  parameter         GTYE4_CHANNEL_SIM_MODE = "FAST",
  parameter         GTYE4_CHANNEL_SIM_RECEIVER_DETECT_PASS = "TRUE",
  parameter         GTYE4_CHANNEL_SIM_RESET_SPEEDUP = "TRUE",
  parameter         GTYE4_CHANNEL_SIM_TX_EIDLE_DRIVE_LEVEL = "Z",
  parameter         GTYE4_CHANNEL_SIM_DEVICE  = "ULTRASCALE_PLUS",
  parameter   [0:0] GTYE4_CHANNEL_SRSTMODE = 1'b0,
  parameter   [1:0] GTYE4_CHANNEL_TAPDLY_SET_TX = 2'h0,
  parameter  [14:0] GTYE4_CHANNEL_TERM_RCAL_CFG = 15'b100001000010000,
  parameter   [2:0] GTYE4_CHANNEL_TERM_RCAL_OVRD = 3'b000,
  parameter   [7:0] GTYE4_CHANNEL_TRANS_TIME_RATE = 8'h0E,
  parameter   [7:0] GTYE4_CHANNEL_TST_RSV0 = 8'h00,
  parameter   [7:0] GTYE4_CHANNEL_TST_RSV1 = 8'h00,
  parameter         GTYE4_CHANNEL_TXBUF_EN = "TRUE",
  parameter         GTYE4_CHANNEL_TXBUF_RESET_ON_RATE_CHANGE = "FALSE",
  parameter  [15:0] GTYE4_CHANNEL_TXDLY_CFG = 16'h0010,
  parameter  [15:0] GTYE4_CHANNEL_TXDLY_LCFG = 16'h0030,
  parameter integer GTYE4_CHANNEL_TXDRV_FREQBAND = 0,
  parameter  [15:0] GTYE4_CHANNEL_TXFE_CFG0 = 16'b0000000000000000,
  parameter  [15:0] GTYE4_CHANNEL_TXFE_CFG1 = 16'b0000000000000000,
  parameter  [15:0] GTYE4_CHANNEL_TXFE_CFG2 = 16'b0000000000000000,
  parameter  [15:0] GTYE4_CHANNEL_TXFE_CFG3 = 16'b0000000000000000,
  parameter         GTYE4_CHANNEL_TXFIFO_ADDR_CFG = "LOW",
  parameter integer GTYE4_CHANNEL_TXGBOX_FIFO_INIT_RD_ADDR = 4,
  parameter         GTYE4_CHANNEL_TXGEARBOX_EN = "FALSE",
  parameter integer GTYE4_CHANNEL_TXOUT_DIV = 4,
  parameter   [4:0] GTYE4_CHANNEL_TXPCSRESET_TIME = 5'b00001,
  parameter  [15:0] GTYE4_CHANNEL_TXPHDLY_CFG0 = 16'h6020,
  parameter  [15:0] GTYE4_CHANNEL_TXPHDLY_CFG1 = 16'h0002,
  parameter  [15:0] GTYE4_CHANNEL_TXPH_CFG = 16'h0123,
  parameter  [15:0] GTYE4_CHANNEL_TXPH_CFG2 = 16'h0000,
  parameter   [4:0] GTYE4_CHANNEL_TXPH_MONITOR_SEL = 5'b00000,
  parameter  [15:0] GTYE4_CHANNEL_TXPI_CFG0 = 16'b0000000100000000,
  parameter  [15:0] GTYE4_CHANNEL_TXPI_CFG1 = 16'b0000000000000000,
  parameter   [0:0] GTYE4_CHANNEL_TXPI_GRAY_SEL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPI_INVSTROBE_SEL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPI_PPM = 1'b0,
  parameter   [7:0] GTYE4_CHANNEL_TXPI_PPM_CFG = 8'b00000000,
  parameter   [2:0] GTYE4_CHANNEL_TXPI_SYNFREQ_PPM = 3'b000,
  parameter   [4:0] GTYE4_CHANNEL_TXPMARESET_TIME = 5'b00001,
  parameter   [0:0] GTYE4_CHANNEL_TXREFCLKDIV2_SEL = 1'b0,
  parameter integer GTYE4_CHANNEL_TXSWBST_BST = 1,
  parameter integer GTYE4_CHANNEL_TXSWBST_EN = 0,
  parameter integer GTYE4_CHANNEL_TXSWBST_MAG = 6,
  parameter   [0:0] GTYE4_CHANNEL_TXSYNC_MULTILANE = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXSYNC_OVRD = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXSYNC_SKIP_DA = 1'b0,
  parameter integer GTYE4_CHANNEL_TX_CLK25_DIV = 8,
  parameter   [0:0] GTYE4_CHANNEL_TX_CLKMUX_EN = 1'b1,
  parameter integer GTYE4_CHANNEL_TX_DATA_WIDTH = 20,
  parameter  [15:0] GTYE4_CHANNEL_TX_DCC_LOOP_RST_CFG = 16'h0000,
  parameter   [5:0] GTYE4_CHANNEL_TX_DEEMPH0 = 6'b000000,
  parameter   [5:0] GTYE4_CHANNEL_TX_DEEMPH1 = 6'b000000,
  parameter   [5:0] GTYE4_CHANNEL_TX_DEEMPH2 = 6'b000000,
  parameter   [5:0] GTYE4_CHANNEL_TX_DEEMPH3 = 6'b000000,
  parameter   [4:0] GTYE4_CHANNEL_TX_DIVRESET_TIME = 5'b00001,
  parameter         GTYE4_CHANNEL_TX_DRIVE_MODE = "DIRECT",
  parameter   [2:0] GTYE4_CHANNEL_TX_EIDLE_ASSERT_DELAY = 3'b110,
  parameter   [2:0] GTYE4_CHANNEL_TX_EIDLE_DEASSERT_DELAY = 3'b100,
  parameter   [0:0] GTYE4_CHANNEL_TX_FABINT_USRCLK_FLOP = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TX_FIFO_BYP_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TX_IDLE_DATA_ZERO = 1'b0,
  parameter integer GTYE4_CHANNEL_TX_INT_DATAWIDTH = 1,
  parameter         GTYE4_CHANNEL_TX_LOOPBACK_DRIVE_HIZ = "FALSE",
  parameter   [0:0] GTYE4_CHANNEL_TX_MAINCURSOR_SEL = 1'b0,
  parameter   [6:0] GTYE4_CHANNEL_TX_MARGIN_FULL_0 = 7'b1001110,
  parameter   [6:0] GTYE4_CHANNEL_TX_MARGIN_FULL_1 = 7'b1001001,
  parameter   [6:0] GTYE4_CHANNEL_TX_MARGIN_FULL_2 = 7'b1000101,
  parameter   [6:0] GTYE4_CHANNEL_TX_MARGIN_FULL_3 = 7'b1000010,
  parameter   [6:0] GTYE4_CHANNEL_TX_MARGIN_FULL_4 = 7'b1000000,
  parameter   [6:0] GTYE4_CHANNEL_TX_MARGIN_LOW_0 = 7'b1000110,
  parameter   [6:0] GTYE4_CHANNEL_TX_MARGIN_LOW_1 = 7'b1000100,
  parameter   [6:0] GTYE4_CHANNEL_TX_MARGIN_LOW_2 = 7'b1000010,
  parameter   [6:0] GTYE4_CHANNEL_TX_MARGIN_LOW_3 = 7'b1000000,
  parameter   [6:0] GTYE4_CHANNEL_TX_MARGIN_LOW_4 = 7'b1000000,
  parameter  [15:0] GTYE4_CHANNEL_TX_PHICAL_CFG0 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_TX_PHICAL_CFG1 = 16'h003F,
  parameter integer GTYE4_CHANNEL_TX_PI_BIASSET = 0,
  parameter   [0:0] GTYE4_CHANNEL_TX_PMADATA_OPT = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TX_PMA_POWER_SAVE = 1'b0,
  parameter  [15:0] GTYE4_CHANNEL_TX_PMA_RSV0 = 16'h0000,
  parameter  [15:0] GTYE4_CHANNEL_TX_PMA_RSV1 = 16'h0000,
  parameter         GTYE4_CHANNEL_TX_PROGCLK_SEL = "POSTPI",
  parameter    real GTYE4_CHANNEL_TX_PROGDIV_CFG = 0.0,
  parameter  [15:0] GTYE4_CHANNEL_TX_PROGDIV_RATE = 16'h0001,
  parameter  [13:0] GTYE4_CHANNEL_TX_RXDETECT_CFG = 14'h0032,
  parameter integer GTYE4_CHANNEL_TX_RXDETECT_REF = 3,
  parameter   [2:0] GTYE4_CHANNEL_TX_SAMPLE_PERIOD = 3'b101,
  parameter   [1:0] GTYE4_CHANNEL_TX_SW_MEAS = 2'b00,
  parameter   [2:0] GTYE4_CHANNEL_TX_VREG_CTRL = 3'b000,
  parameter   [0:0] GTYE4_CHANNEL_TX_VREG_PDB = 1'b0,
  parameter   [1:0] GTYE4_CHANNEL_TX_VREG_VREFSEL = 2'b00,
  parameter         GTYE4_CHANNEL_TX_XCLK_SEL = "TXOUT",
  parameter   [0:0] GTYE4_CHANNEL_USB_BOTH_BURST_IDLE = 1'b0,
  parameter   [6:0] GTYE4_CHANNEL_USB_BURSTMAX_U3WAKE = 7'b1111111,
  parameter   [6:0] GTYE4_CHANNEL_USB_BURSTMIN_U3WAKE = 7'b1100011,
  parameter   [0:0] GTYE4_CHANNEL_USB_CLK_COR_EQ_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_USB_EXT_CNTL = 1'b1,
  parameter   [9:0] GTYE4_CHANNEL_USB_IDLEMAX_POLLING = 10'b1010111011,
  parameter   [9:0] GTYE4_CHANNEL_USB_IDLEMIN_POLLING = 10'b0100101011,
  parameter   [8:0] GTYE4_CHANNEL_USB_LFPSPING_BURST = 9'b000000101,
  parameter   [8:0] GTYE4_CHANNEL_USB_LFPSPOLLING_BURST = 9'b000110001,
  parameter   [8:0] GTYE4_CHANNEL_USB_LFPSPOLLING_IDLE_MS = 9'b000000100,
  parameter   [8:0] GTYE4_CHANNEL_USB_LFPSU1EXIT_BURST = 9'b000011101,
  parameter   [8:0] GTYE4_CHANNEL_USB_LFPSU2LPEXIT_BURST_MS = 9'b001100011,
  parameter   [8:0] GTYE4_CHANNEL_USB_LFPSU3WAKE_BURST_MS = 9'b111110011,
  parameter   [3:0] GTYE4_CHANNEL_USB_LFPS_TPERIOD = 4'b0011,
  parameter   [0:0] GTYE4_CHANNEL_USB_LFPS_TPERIOD_ACCURATE = 1'b1,
  parameter   [0:0] GTYE4_CHANNEL_USB_MODE = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_USB_PCIE_ERR_REP_DIS = 1'b0,
  parameter integer GTYE4_CHANNEL_USB_PING_SATA_MAX_INIT = 21,
  parameter integer GTYE4_CHANNEL_USB_PING_SATA_MIN_INIT = 12,
  parameter integer GTYE4_CHANNEL_USB_POLL_SATA_MAX_BURST = 8,
  parameter integer GTYE4_CHANNEL_USB_POLL_SATA_MIN_BURST = 4,
  parameter   [0:0] GTYE4_CHANNEL_USB_RAW_ELEC = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_USB_RXIDLE_P0_CTRL = 1'b1,
  parameter   [0:0] GTYE4_CHANNEL_USB_TXIDLE_TUNE_ENABLE = 1'b1,
  parameter integer GTYE4_CHANNEL_USB_U1_SATA_MAX_WAKE = 7,
  parameter integer GTYE4_CHANNEL_USB_U1_SATA_MIN_WAKE = 4,
  parameter integer GTYE4_CHANNEL_USB_U2_SAS_MAX_COM = 64,
  parameter integer GTYE4_CHANNEL_USB_U2_SAS_MIN_COM = 36,
  parameter   [0:0] GTYE4_CHANNEL_USE_PCS_CLK_PHASE_SEL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_Y_ALL_MODE = 1'b0,

  // primitive wrapper parameters which specify GTYE4_CHANNEL primitive input port default driver values
  parameter   [0:0] GTYE4_CHANNEL_CDRSTEPDIR_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_CDRSTEPSQ_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_CDRSTEPSX_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_CFGRESET_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_CLKRSVD0_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_CLKRSVD1_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_CPLLFREQLOCK_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_CPLLLOCKDETCLK_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_CPLLLOCKEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_CPLLPD_VAL = 1'b0,
  parameter   [2:0] GTYE4_CHANNEL_CPLLREFCLKSEL_VAL = 3'b0,
  parameter   [0:0] GTYE4_CHANNEL_CPLLRESET_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_DMONFIFORESET_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_DMONITORCLK_VAL = 1'b0,
  parameter   [9:0] GTYE4_CHANNEL_DRPADDR_VAL = 10'b0,
  parameter   [0:0] GTYE4_CHANNEL_DRPCLK_VAL = 1'b0,
  parameter  [15:0] GTYE4_CHANNEL_DRPDI_VAL = 16'b0,
  parameter   [0:0] GTYE4_CHANNEL_DRPEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_DRPRST_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_DRPWE_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_EYESCANRESET_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_EYESCANTRIGGER_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_FREQOS_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_GTGREFCLK_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_GTNORTHREFCLK0_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_GTNORTHREFCLK1_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_GTREFCLK0_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_GTREFCLK1_VAL = 1'b0,
  parameter  [15:0] GTYE4_CHANNEL_GTRSVD_VAL = 16'b0,
  parameter   [0:0] GTYE4_CHANNEL_GTRXRESET_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_GTRXRESETSEL_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_GTSOUTHREFCLK0_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_GTSOUTHREFCLK1_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_GTTXRESET_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_GTTXRESETSEL_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_GTYRXN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_GTYRXP_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_INCPCTRL_VAL = 1'b0,
  parameter   [2:0] GTYE4_CHANNEL_LOOPBACK_VAL = 3'b0,
  parameter   [0:0] GTYE4_CHANNEL_PCIEEQRXEQADAPTDONE_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_PCIERSTIDLE_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_PCIERSTTXSYNCSTART_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_PCIEUSERRATEDONE_VAL = 1'b0,
  parameter  [15:0] GTYE4_CHANNEL_PCSRSVDIN_VAL = 16'b0,
  parameter   [0:0] GTYE4_CHANNEL_QPLL0CLK_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_QPLL0FREQLOCK_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_QPLL0REFCLK_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_QPLL1CLK_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_QPLL1FREQLOCK_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_QPLL1REFCLK_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RESETOVRD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RX8B10BEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXAFECFOKEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXBUFRESET_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXCDRFREQRESET_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXCDRHOLD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXCDROVRDEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXCDRRESET_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXCHBONDEN_VAL = 1'b0,
  parameter   [4:0] GTYE4_CHANNEL_RXCHBONDI_VAL = 5'b0,
  parameter   [2:0] GTYE4_CHANNEL_RXCHBONDLEVEL_VAL = 3'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXCHBONDMASTER_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXCHBONDSLAVE_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXCKCALRESET_VAL = 1'b0,
  parameter   [6:0] GTYE4_CHANNEL_RXCKCALSTART_VAL = 7'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXCOMMADETEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFEAGCHOLD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFEAGCOVRDEN_VAL = 1'b0,
  parameter   [3:0] GTYE4_CHANNEL_RXDFECFOKFCNUM_VAL = 4'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFECFOKFEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFECFOKFPULSE_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFECFOKHOLD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFECFOKOVREN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFEKHHOLD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFEKHOVRDEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFELFHOLD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFELFOVRDEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFELPMRESET_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP10HOLD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP10OVRDEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP11HOLD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP11OVRDEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP12HOLD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP12OVRDEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP13HOLD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP13OVRDEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP14HOLD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP14OVRDEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP15HOLD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP15OVRDEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP2HOLD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP2OVRDEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP3HOLD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP3OVRDEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP4HOLD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP4OVRDEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP5HOLD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP5OVRDEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP6HOLD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP6OVRDEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP7HOLD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP7OVRDEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP8HOLD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP8OVRDEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP9HOLD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP9OVRDEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFEUTHOLD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFEUTOVRDEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFEVPHOLD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFEVPOVRDEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFEXYDEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDLYBYPASS_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDLYEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDLYOVRDEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDLYSRESET_VAL = 1'b0,
  parameter   [1:0] GTYE4_CHANNEL_RXELECIDLEMODE_VAL = 2'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXEQTRAINING_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXGEARBOXSLIP_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXLATCLK_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXLPMEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXLPMGCHOLD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXLPMGCOVRDEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXLPMHFHOLD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXLPMHFOVRDEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXLPMLFHOLD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXLPMLFKLOVRDEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXLPMOSHOLD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXLPMOSOVRDEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXMCOMMAALIGNEN_VAL = 1'b0,
  parameter   [1:0] GTYE4_CHANNEL_RXMONITORSEL_VAL = 2'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXOOBRESET_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXOSCALRESET_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXOSHOLD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXOSOVRDEN_VAL = 1'b0,
  parameter   [2:0] GTYE4_CHANNEL_RXOUTCLKSEL_VAL = 3'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXPCOMMAALIGNEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXPCSRESET_VAL = 1'b0,
  parameter   [1:0] GTYE4_CHANNEL_RXPD_VAL = 2'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXPHALIGN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXPHALIGNEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXPHDLYPD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXPHDLYRESET_VAL = 1'b0,
  parameter   [1:0] GTYE4_CHANNEL_RXPLLCLKSEL_VAL = 2'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXPMARESET_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXPOLARITY_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXPRBSCNTRESET_VAL = 1'b0,
  parameter   [3:0] GTYE4_CHANNEL_RXPRBSSEL_VAL = 4'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXPROGDIVRESET_VAL = 1'b0,
  parameter   [2:0] GTYE4_CHANNEL_RXRATE_VAL = 3'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXRATEMODE_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXSLIDE_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXSLIPOUTCLK_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXSLIPPMA_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXSYNCALLIN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXSYNCIN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXSYNCMODE_VAL = 1'b0,
  parameter   [1:0] GTYE4_CHANNEL_RXSYSCLKSEL_VAL = 2'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXTERMINATION_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXUSERRDY_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXUSRCLK_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXUSRCLK2_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_SIGVALIDCLK_VAL = 1'b0,
  parameter  [19:0] GTYE4_CHANNEL_TSTIN_VAL = 20'b0,
  parameter   [7:0] GTYE4_CHANNEL_TX8B10BBYPASS_VAL = 8'b0,
  parameter   [0:0] GTYE4_CHANNEL_TX8B10BEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXCOMINIT_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXCOMSAS_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXCOMWAKE_VAL = 1'b0,
  parameter  [15:0] GTYE4_CHANNEL_TXCTRL0_VAL = 16'b0,
  parameter  [15:0] GTYE4_CHANNEL_TXCTRL1_VAL = 16'b0,
  parameter   [7:0] GTYE4_CHANNEL_TXCTRL2_VAL = 8'b0,
  parameter [127:0] GTYE4_CHANNEL_TXDATA_VAL = 128'b0,
  parameter   [7:0] GTYE4_CHANNEL_TXDATAEXTENDRSVD_VAL = 8'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXDCCFORCESTART_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXDCCRESET_VAL = 1'b0,
  parameter   [1:0] GTYE4_CHANNEL_TXDEEMPH_VAL = 2'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXDETECTRX_VAL = 1'b0,
  parameter   [4:0] GTYE4_CHANNEL_TXDIFFCTRL_VAL = 5'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXDLYBYPASS_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXDLYEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXDLYHOLD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXDLYOVRDEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXDLYSRESET_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXDLYUPDOWN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXELECIDLE_VAL = 1'b0,
  parameter   [5:0] GTYE4_CHANNEL_TXHEADER_VAL = 6'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXINHIBIT_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXLATCLK_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXLFPSTRESET_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXLFPSU2LPEXIT_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXLFPSU3WAKE_VAL = 1'b0,
  parameter   [6:0] GTYE4_CHANNEL_TXMAINCURSOR_VAL = 7'b0,
  parameter   [2:0] GTYE4_CHANNEL_TXMARGIN_VAL = 3'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXMUXDCDEXHOLD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXMUXDCDORWREN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXONESZEROS_VAL = 1'b0,
  parameter   [2:0] GTYE4_CHANNEL_TXOUTCLKSEL_VAL = 3'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPCSRESET_VAL = 1'b0,
  parameter   [1:0] GTYE4_CHANNEL_TXPD_VAL = 2'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPDELECIDLEMODE_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPHALIGN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPHALIGNEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPHDLYPD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPHDLYRESET_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPHDLYTSTCLK_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPHINIT_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPHOVRDEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPIPPMEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPIPPMOVRDEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPIPPMPD_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPIPPMSEL_VAL = 1'b0,
  parameter   [4:0] GTYE4_CHANNEL_TXPIPPMSTEPSIZE_VAL = 5'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPISOPD_VAL = 1'b0,
  parameter   [1:0] GTYE4_CHANNEL_TXPLLCLKSEL_VAL = 2'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPMARESET_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPOLARITY_VAL = 1'b0,
  parameter   [4:0] GTYE4_CHANNEL_TXPOSTCURSOR_VAL = 5'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPRBSFORCEERR_VAL = 1'b0,
  parameter   [3:0] GTYE4_CHANNEL_TXPRBSSEL_VAL = 4'b0,
  parameter   [4:0] GTYE4_CHANNEL_TXPRECURSOR_VAL = 5'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPROGDIVRESET_VAL = 1'b0,
  parameter   [2:0] GTYE4_CHANNEL_TXRATE_VAL = 3'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXRATEMODE_VAL = 1'b0,
  parameter   [6:0] GTYE4_CHANNEL_TXSEQUENCE_VAL = 7'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXSWING_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXSYNCALLIN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXSYNCIN_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXSYNCMODE_VAL = 1'b0,
  parameter   [1:0] GTYE4_CHANNEL_TXSYSCLKSEL_VAL = 2'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXUSERRDY_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXUSRCLK_VAL = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXUSRCLK2_VAL = 1'b0,

  // primitive wrapper parameters which control GTYE4_CHANNEL primitive input port tie-off enablement
  parameter   [0:0] GTYE4_CHANNEL_CDRSTEPDIR_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_CDRSTEPSQ_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_CDRSTEPSX_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_CFGRESET_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_CLKRSVD0_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_CLKRSVD1_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_CPLLFREQLOCK_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_CPLLLOCKDETCLK_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_CPLLLOCKEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_CPLLPD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_CPLLREFCLKSEL_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_CPLLRESET_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_DMONFIFORESET_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_DMONITORCLK_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_DRPADDR_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_DRPCLK_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_DRPDI_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_DRPEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_DRPRST_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_DRPWE_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_EYESCANRESET_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_EYESCANTRIGGER_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_FREQOS_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_GTGREFCLK_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_GTNORTHREFCLK0_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_GTNORTHREFCLK1_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_GTREFCLK0_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_GTREFCLK1_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_GTRSVD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_GTRXRESET_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_GTRXRESETSEL_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_GTSOUTHREFCLK0_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_GTSOUTHREFCLK1_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_GTTXRESET_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_GTTXRESETSEL_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_GTYRXN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_GTYRXP_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_INCPCTRL_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_LOOPBACK_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_PCIEEQRXEQADAPTDONE_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_PCIERSTIDLE_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_PCIERSTTXSYNCSTART_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_PCIEUSERRATEDONE_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_PCSRSVDIN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_QPLL0CLK_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_QPLL0FREQLOCK_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_QPLL0REFCLK_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_QPLL1CLK_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_QPLL1FREQLOCK_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_QPLL1REFCLK_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RESETOVRD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RX8B10BEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXAFECFOKEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXBUFRESET_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXCDRFREQRESET_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXCDRHOLD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXCDROVRDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXCDRRESET_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXCHBONDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXCHBONDI_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXCHBONDLEVEL_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXCHBONDMASTER_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXCHBONDSLAVE_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXCKCALRESET_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXCKCALSTART_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXCOMMADETEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFEAGCHOLD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFEAGCOVRDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFECFOKFCNUM_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFECFOKFEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFECFOKFPULSE_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFECFOKHOLD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFECFOKOVREN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFEKHHOLD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFEKHOVRDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFELFHOLD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFELFOVRDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFELPMRESET_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP10HOLD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP10OVRDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP11HOLD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP11OVRDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP12HOLD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP12OVRDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP13HOLD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP13OVRDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP14HOLD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP14OVRDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP15HOLD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP15OVRDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP2HOLD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP2OVRDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP3HOLD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP3OVRDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP4HOLD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP4OVRDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP5HOLD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP5OVRDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP6HOLD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP6OVRDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP7HOLD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP7OVRDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP8HOLD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP8OVRDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP9HOLD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFETAP9OVRDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFEUTHOLD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFEUTOVRDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFEVPHOLD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFEVPOVRDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDFEXYDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDLYBYPASS_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDLYEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDLYOVRDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXDLYSRESET_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXELECIDLEMODE_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXEQTRAINING_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXGEARBOXSLIP_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXLATCLK_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXLPMEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXLPMGCHOLD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXLPMGCOVRDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXLPMHFHOLD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXLPMHFOVRDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXLPMLFHOLD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXLPMLFKLOVRDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXLPMOSHOLD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXLPMOSOVRDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXMCOMMAALIGNEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXMONITORSEL_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXOOBRESET_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXOSCALRESET_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXOSHOLD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXOSOVRDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXOUTCLKSEL_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXPCOMMAALIGNEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXPCSRESET_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXPD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXPHALIGN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXPHALIGNEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXPHDLYPD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXPHDLYRESET_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXPLLCLKSEL_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXPMARESET_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXPOLARITY_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXPRBSCNTRESET_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXPRBSSEL_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXPROGDIVRESET_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXRATE_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXRATEMODE_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXSLIDE_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXSLIPOUTCLK_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXSLIPPMA_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXSYNCALLIN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXSYNCIN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXSYNCMODE_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXSYSCLKSEL_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXTERMINATION_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXUSERRDY_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXUSRCLK_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_RXUSRCLK2_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_SIGVALIDCLK_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TSTIN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TX8B10BBYPASS_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TX8B10BEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXCOMINIT_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXCOMSAS_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXCOMWAKE_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXCTRL0_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXCTRL1_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXCTRL2_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXDATA_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXDATAEXTENDRSVD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXDCCFORCESTART_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXDCCRESET_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXDEEMPH_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXDETECTRX_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXDIFFCTRL_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXDLYBYPASS_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXDLYEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXDLYHOLD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXDLYOVRDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXDLYSRESET_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXDLYUPDOWN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXELECIDLE_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXHEADER_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXINHIBIT_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXLATCLK_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXLFPSTRESET_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXLFPSU2LPEXIT_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXLFPSU3WAKE_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXMAINCURSOR_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXMARGIN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXMUXDCDEXHOLD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXMUXDCDORWREN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXONESZEROS_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXOUTCLKSEL_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPCSRESET_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPDELECIDLEMODE_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPHALIGN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPHALIGNEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPHDLYPD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPHDLYRESET_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPHDLYTSTCLK_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPHINIT_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPHOVRDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPIPPMEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPIPPMOVRDEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPIPPMPD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPIPPMSEL_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPIPPMSTEPSIZE_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPISOPD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPLLCLKSEL_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPMARESET_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPOLARITY_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPOSTCURSOR_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPRBSFORCEERR_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPRBSSEL_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPRECURSOR_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXPROGDIVRESET_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXRATE_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXRATEMODE_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXSEQUENCE_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXSWING_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXSYNCALLIN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXSYNCIN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXSYNCMODE_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXSYSCLKSEL_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXUSERRDY_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXUSRCLK_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_CHANNEL_TXUSRCLK2_TIE_EN = 1'b0

)(


  // -------------------------------------------------------------------------------------------------------------------
  // Ports relating to GTYE4_CHANNEL primitive
  // -------------------------------------------------------------------------------------------------------------------

  // primitive wrapper input ports which can drive corresponding GTYE4_CHANNEL primitive input ports
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_CDRSTEPDIR,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_CDRSTEPSQ,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_CDRSTEPSX,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_CFGRESET,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_CLKRSVD0,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_CLKRSVD1,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_CPLLFREQLOCK,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_CPLLLOCKDETCLK,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_CPLLLOCKEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_CPLLPD,
  input  wire [(NUM_CHANNELS*  3)-1:0] GTYE4_CHANNEL_CPLLREFCLKSEL,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_CPLLRESET,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_DMONFIFORESET,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_DMONITORCLK,
  input  wire [(NUM_CHANNELS* 10)-1:0] GTYE4_CHANNEL_DRPADDR,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_DRPCLK,
  input  wire [(NUM_CHANNELS* 16)-1:0] GTYE4_CHANNEL_DRPDI,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_DRPEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_DRPRST,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_DRPWE,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_EYESCANRESET,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_EYESCANTRIGGER,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_FREQOS,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_GTGREFCLK,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_GTNORTHREFCLK0,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_GTNORTHREFCLK1,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_GTREFCLK0,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_GTREFCLK1,
  input  wire [(NUM_CHANNELS* 16)-1:0] GTYE4_CHANNEL_GTRSVD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_GTRXRESET,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_GTRXRESETSEL,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_GTYRXN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_GTYRXP,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_GTSOUTHREFCLK0,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_GTSOUTHREFCLK1,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_GTTXRESET,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_GTTXRESETSEL,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_INCPCTRL,
  input  wire [(NUM_CHANNELS*  3)-1:0] GTYE4_CHANNEL_LOOPBACK,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_PCIEEQRXEQADAPTDONE,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_PCIERSTIDLE,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_PCIERSTTXSYNCSTART,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_PCIEUSERRATEDONE,
  input  wire [(NUM_CHANNELS* 16)-1:0] GTYE4_CHANNEL_PCSRSVDIN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_QPLL0CLK,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_QPLL0FREQLOCK,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_QPLL0REFCLK,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_QPLL1CLK,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_QPLL1FREQLOCK,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_QPLL1REFCLK,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RESETOVRD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RX8B10BEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXAFECFOKEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXBUFRESET,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXCDRFREQRESET,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXCDRHOLD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXCDROVRDEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXCDRRESET,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXCHBONDEN,
  input  wire [(NUM_CHANNELS*  5)-1:0] GTYE4_CHANNEL_RXCHBONDI,
  input  wire [(NUM_CHANNELS*  3)-1:0] GTYE4_CHANNEL_RXCHBONDLEVEL,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXCHBONDMASTER,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXCHBONDSLAVE,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXCKCALRESET,
  input  wire [(NUM_CHANNELS*  7)-1:0] GTYE4_CHANNEL_RXCKCALSTART,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXCOMMADETEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFEAGCHOLD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFEAGCOVRDEN,
  input  wire [(NUM_CHANNELS*  4)-1:0] GTYE4_CHANNEL_RXDFECFOKFCNUM,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFECFOKFEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFECFOKFPULSE,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFECFOKHOLD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFECFOKOVREN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFEKHHOLD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFEKHOVRDEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFELFHOLD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFELFOVRDEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFELPMRESET,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP10HOLD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP10OVRDEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP11HOLD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP11OVRDEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP12HOLD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP12OVRDEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP13HOLD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP13OVRDEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP14HOLD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP14OVRDEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP15HOLD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP15OVRDEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP2HOLD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP2OVRDEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP3HOLD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP3OVRDEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP4HOLD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP4OVRDEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP5HOLD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP5OVRDEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP6HOLD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP6OVRDEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP7HOLD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP7OVRDEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP8HOLD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP8OVRDEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP9HOLD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP9OVRDEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFEUTHOLD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFEUTOVRDEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFEVPHOLD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFEVPOVRDEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFEXYDEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDLYBYPASS,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDLYEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDLYOVRDEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDLYSRESET,
  input  wire [(NUM_CHANNELS*  2)-1:0] GTYE4_CHANNEL_RXELECIDLEMODE,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXEQTRAINING,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXGEARBOXSLIP,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXLATCLK,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXLPMEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXLPMGCHOLD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXLPMGCOVRDEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXLPMHFHOLD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXLPMHFOVRDEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXLPMLFHOLD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXLPMLFKLOVRDEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXLPMOSHOLD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXLPMOSOVRDEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXMCOMMAALIGNEN,
  input  wire [(NUM_CHANNELS*  2)-1:0] GTYE4_CHANNEL_RXMONITORSEL,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXOOBRESET,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXOSCALRESET,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXOSHOLD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXOSOVRDEN,
  input  wire [(NUM_CHANNELS*  3)-1:0] GTYE4_CHANNEL_RXOUTCLKSEL,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXPCOMMAALIGNEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXPCSRESET,
  input  wire [(NUM_CHANNELS*  2)-1:0] GTYE4_CHANNEL_RXPD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXPHALIGN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXPHALIGNEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXPHDLYPD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXPHDLYRESET,
  input  wire [(NUM_CHANNELS*  2)-1:0] GTYE4_CHANNEL_RXPLLCLKSEL,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXPMARESET,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXPOLARITY,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXPRBSCNTRESET,
  input  wire [(NUM_CHANNELS*  4)-1:0] GTYE4_CHANNEL_RXPRBSSEL,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXPROGDIVRESET,
  input  wire [(NUM_CHANNELS*  3)-1:0] GTYE4_CHANNEL_RXRATE,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXRATEMODE,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXSLIDE,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXSLIPOUTCLK,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXSLIPPMA,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXSYNCALLIN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXSYNCIN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXSYNCMODE,
  input  wire [(NUM_CHANNELS*  2)-1:0] GTYE4_CHANNEL_RXSYSCLKSEL,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXTERMINATION,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXUSERRDY,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXUSRCLK,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXUSRCLK2,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_SIGVALIDCLK,
  input  wire [(NUM_CHANNELS* 20)-1:0] GTYE4_CHANNEL_TSTIN,
  input  wire [(NUM_CHANNELS*  8)-1:0] GTYE4_CHANNEL_TX8B10BBYPASS,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TX8B10BEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXCOMINIT,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXCOMSAS,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXCOMWAKE,
  input  wire [(NUM_CHANNELS* 16)-1:0] GTYE4_CHANNEL_TXCTRL0,
  input  wire [(NUM_CHANNELS* 16)-1:0] GTYE4_CHANNEL_TXCTRL1,
  input  wire [(NUM_CHANNELS*  8)-1:0] GTYE4_CHANNEL_TXCTRL2,
  input  wire [(NUM_CHANNELS*128)-1:0] GTYE4_CHANNEL_TXDATA,
  input  wire [(NUM_CHANNELS*  8)-1:0] GTYE4_CHANNEL_TXDATAEXTENDRSVD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXDCCFORCESTART,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXDCCRESET,
  input  wire [(NUM_CHANNELS*  2)-1:0] GTYE4_CHANNEL_TXDEEMPH,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXDETECTRX,
  input  wire [(NUM_CHANNELS*  5)-1:0] GTYE4_CHANNEL_TXDIFFCTRL,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXDLYBYPASS,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXDLYEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXDLYHOLD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXDLYOVRDEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXDLYSRESET,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXDLYUPDOWN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXELECIDLE,
  input  wire [(NUM_CHANNELS*  6)-1:0] GTYE4_CHANNEL_TXHEADER,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXINHIBIT,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXLATCLK,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXLFPSTRESET,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXLFPSU2LPEXIT,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXLFPSU3WAKE,
  input  wire [(NUM_CHANNELS*  7)-1:0] GTYE4_CHANNEL_TXMAINCURSOR,
  input  wire [(NUM_CHANNELS*  3)-1:0] GTYE4_CHANNEL_TXMARGIN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXMUXDCDEXHOLD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXMUXDCDORWREN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXONESZEROS,
  input  wire [(NUM_CHANNELS*  3)-1:0] GTYE4_CHANNEL_TXOUTCLKSEL,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPCSRESET,
  input  wire [(NUM_CHANNELS*  2)-1:0] GTYE4_CHANNEL_TXPD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPDELECIDLEMODE,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPHALIGN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPHALIGNEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPHDLYPD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPHDLYRESET,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPHDLYTSTCLK,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPHINIT,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPHOVRDEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPIPPMEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPIPPMOVRDEN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPIPPMPD,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPIPPMSEL,
  input  wire [(NUM_CHANNELS*  5)-1:0] GTYE4_CHANNEL_TXPIPPMSTEPSIZE,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPISOPD,
  input  wire [(NUM_CHANNELS*  2)-1:0] GTYE4_CHANNEL_TXPLLCLKSEL,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPMARESET,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPOLARITY,
  input  wire [(NUM_CHANNELS*  5)-1:0] GTYE4_CHANNEL_TXPOSTCURSOR,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPRBSFORCEERR,
  input  wire [(NUM_CHANNELS*  4)-1:0] GTYE4_CHANNEL_TXPRBSSEL,
  input  wire [(NUM_CHANNELS*  5)-1:0] GTYE4_CHANNEL_TXPRECURSOR,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPROGDIVRESET,
  input  wire [(NUM_CHANNELS*  3)-1:0] GTYE4_CHANNEL_TXRATE,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXRATEMODE,
  input  wire [(NUM_CHANNELS*  7)-1:0] GTYE4_CHANNEL_TXSEQUENCE,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXSWING,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXSYNCALLIN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXSYNCIN,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXSYNCMODE,
  input  wire [(NUM_CHANNELS*  2)-1:0] GTYE4_CHANNEL_TXSYSCLKSEL,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXUSERRDY,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXUSRCLK,
  input  wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXUSRCLK2,

  // primitive wrapper output ports which are driven by corresponding GTYE4_CHANNEL primitive output ports
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_BUFGTCE,
  output wire [(NUM_CHANNELS*  3)-1:0] GTYE4_CHANNEL_BUFGTCEMASK,
  output wire [(NUM_CHANNELS*  9)-1:0] GTYE4_CHANNEL_BUFGTDIV,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_BUFGTRESET,
  output wire [(NUM_CHANNELS*  3)-1:0] GTYE4_CHANNEL_BUFGTRSTMASK,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_CPLLFBCLKLOST,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_CPLLLOCK,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_CPLLREFCLKLOST,
  output wire [(NUM_CHANNELS* 16)-1:0] GTYE4_CHANNEL_DMONITOROUT,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_DMONITOROUTCLK,
  output wire [(NUM_CHANNELS* 16)-1:0] GTYE4_CHANNEL_DRPDO,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_DRPRDY,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_EYESCANDATAERROR,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_GTPOWERGOOD,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_GTREFCLKMONITOR,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_GTYTXN,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_GTYTXP,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_PCIERATEGEN3,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_PCIERATEIDLE,
  output wire [(NUM_CHANNELS*  2)-1:0] GTYE4_CHANNEL_PCIERATEQPLLPD,
  output wire [(NUM_CHANNELS*  2)-1:0] GTYE4_CHANNEL_PCIERATEQPLLRESET,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_PCIESYNCTXSYNCDONE,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_PCIEUSERGEN3RDY,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_PCIEUSERPHYSTATUSRST,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_PCIEUSERRATESTART,
  output wire [(NUM_CHANNELS* 16)-1:0] GTYE4_CHANNEL_PCSRSVDOUT,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_PHYSTATUS,
  output wire [(NUM_CHANNELS* 16)-1:0] GTYE4_CHANNEL_PINRSRVDAS,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_POWERPRESENT,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RESETEXCEPTION,
  output wire [(NUM_CHANNELS*  3)-1:0] GTYE4_CHANNEL_RXBUFSTATUS,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXBYTEISALIGNED,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXBYTEREALIGN,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXCDRLOCK,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXCDRPHDONE,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXCHANBONDSEQ,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXCHANISALIGNED,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXCHANREALIGN,
  output wire [(NUM_CHANNELS*  5)-1:0] GTYE4_CHANNEL_RXCHBONDO,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXCKCALDONE,
  output wire [(NUM_CHANNELS*  2)-1:0] GTYE4_CHANNEL_RXCLKCORCNT,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXCOMINITDET,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXCOMMADET,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXCOMSASDET,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXCOMWAKEDET,
  output wire [(NUM_CHANNELS* 16)-1:0] GTYE4_CHANNEL_RXCTRL0,
  output wire [(NUM_CHANNELS* 16)-1:0] GTYE4_CHANNEL_RXCTRL1,
  output wire [(NUM_CHANNELS*  8)-1:0] GTYE4_CHANNEL_RXCTRL2,
  output wire [(NUM_CHANNELS*  8)-1:0] GTYE4_CHANNEL_RXCTRL3,
  output wire [(NUM_CHANNELS*128)-1:0] GTYE4_CHANNEL_RXDATA,
  output wire [(NUM_CHANNELS*  8)-1:0] GTYE4_CHANNEL_RXDATAEXTENDRSVD,
  output wire [(NUM_CHANNELS*  2)-1:0] GTYE4_CHANNEL_RXDATAVALID,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDLYSRESETDONE,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXELECIDLE,
  output wire [(NUM_CHANNELS*  6)-1:0] GTYE4_CHANNEL_RXHEADER,
  output wire [(NUM_CHANNELS*  2)-1:0] GTYE4_CHANNEL_RXHEADERVALID,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXLFPSTRESETDET,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXLFPSU2LPEXITDET,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXLFPSU3WAKEDET,
  output wire [(NUM_CHANNELS*  8)-1:0] GTYE4_CHANNEL_RXMONITOROUT,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXOSINTDONE,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXOSINTSTARTED,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXOSINTSTROBEDONE,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXOSINTSTROBESTARTED,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXOUTCLK,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXOUTCLKFABRIC,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXOUTCLKPCS,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXPHALIGNDONE,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXPHALIGNERR,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXPMARESETDONE,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXPRBSERR,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXPRBSLOCKED,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXPRGDIVRESETDONE,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXRATEDONE,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXRECCLKOUT,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXRESETDONE,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXSLIDERDY,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXSLIPDONE,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXSLIPOUTCLKRDY,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXSLIPPMARDY,
  output wire [(NUM_CHANNELS*  2)-1:0] GTYE4_CHANNEL_RXSTARTOFSEQ,
  output wire [(NUM_CHANNELS*  3)-1:0] GTYE4_CHANNEL_RXSTATUS,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXSYNCDONE,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXSYNCOUT,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXVALID,
  output wire [(NUM_CHANNELS*  2)-1:0] GTYE4_CHANNEL_TXBUFSTATUS,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXCOMFINISH,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXDCCDONE,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXDLYSRESETDONE,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXOUTCLK,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXOUTCLKFABRIC,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXOUTCLKPCS,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPHALIGNDONE,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPHINITDONE,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPMARESETDONE,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPRGDIVRESETDONE,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXRATEDONE,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXRESETDONE,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXSYNCDONE,
  output wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXSYNCOUT

);


  // -------------------------------------------------------------------------------------------------------------------
  // HDL generation of wiring and instances relating to GTYE4_CHANNEL primitive
  // -------------------------------------------------------------------------------------------------------------------

  generate if (NUM_CHANNELS > 0) begin : gtye4_channel_gen

    // for each GTYE4_CHANNEL primitive input port, declare a vector scaled to drive all generated instances
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_CDRSTEPDIR_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_CDRSTEPSQ_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_CDRSTEPSX_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_CFGRESET_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_CLKRSVD0_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_CLKRSVD1_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_CPLLFREQLOCK_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_CPLLLOCKDETCLK_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_CPLLLOCKEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_CPLLPD_int;
    wire [(NUM_CHANNELS*  3)-1:0] GTYE4_CHANNEL_CPLLREFCLKSEL_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_CPLLRESET_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_DMONFIFORESET_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_DMONITORCLK_int;
    wire [(NUM_CHANNELS* 10)-1:0] GTYE4_CHANNEL_DRPADDR_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_DRPCLK_int;
    wire [(NUM_CHANNELS* 16)-1:0] GTYE4_CHANNEL_DRPDI_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_DRPEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_DRPRST_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_DRPWE_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_EYESCANRESET_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_EYESCANTRIGGER_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_FREQOS_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_GTGREFCLK_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_GTNORTHREFCLK0_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_GTNORTHREFCLK1_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_GTREFCLK0_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_GTREFCLK1_int;
    wire [(NUM_CHANNELS* 16)-1:0] GTYE4_CHANNEL_GTRSVD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_GTRXRESET_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_GTRXRESETSEL_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_GTSOUTHREFCLK0_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_GTSOUTHREFCLK1_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_GTTXRESET_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_GTTXRESETSEL_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_GTYRXN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_GTYRXP_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_INCPCTRL_int;
    wire [(NUM_CHANNELS*  3)-1:0] GTYE4_CHANNEL_LOOPBACK_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_PCIEEQRXEQADAPTDONE_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_PCIERSTIDLE_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_PCIERSTTXSYNCSTART_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_PCIEUSERRATEDONE_int;
    wire [(NUM_CHANNELS* 16)-1:0] GTYE4_CHANNEL_PCSRSVDIN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_QPLL0CLK_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_QPLL0FREQLOCK_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_QPLL0REFCLK_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_QPLL1CLK_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_QPLL1FREQLOCK_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_QPLL1REFCLK_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RESETOVRD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RX8B10BEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXAFECFOKEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXBUFRESET_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXCDRFREQRESET_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXCDRHOLD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXCDROVRDEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXCDRRESET_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXCHBONDEN_int;
    wire [(NUM_CHANNELS*  5)-1:0] GTYE4_CHANNEL_RXCHBONDI_int;
    wire [(NUM_CHANNELS*  3)-1:0] GTYE4_CHANNEL_RXCHBONDLEVEL_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXCHBONDMASTER_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXCHBONDSLAVE_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXCKCALRESET_int;
    wire [(NUM_CHANNELS*  7)-1:0] GTYE4_CHANNEL_RXCKCALSTART_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXCOMMADETEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFEAGCHOLD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFEAGCOVRDEN_int;
    wire [(NUM_CHANNELS*  4)-1:0] GTYE4_CHANNEL_RXDFECFOKFCNUM_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFECFOKFEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFECFOKFPULSE_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFECFOKHOLD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFECFOKOVREN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFEKHHOLD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFEKHOVRDEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFELFHOLD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFELFOVRDEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFELPMRESET_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP10HOLD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP10OVRDEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP11HOLD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP11OVRDEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP12HOLD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP12OVRDEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP13HOLD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP13OVRDEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP14HOLD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP14OVRDEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP15HOLD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP15OVRDEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP2HOLD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP2OVRDEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP3HOLD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP3OVRDEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP4HOLD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP4OVRDEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP5HOLD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP5OVRDEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP6HOLD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP6OVRDEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP7HOLD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP7OVRDEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP8HOLD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP8OVRDEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP9HOLD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFETAP9OVRDEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFEUTHOLD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFEUTOVRDEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFEVPHOLD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFEVPOVRDEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDFEXYDEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDLYBYPASS_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDLYEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDLYOVRDEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXDLYSRESET_int;
    wire [(NUM_CHANNELS*  2)-1:0] GTYE4_CHANNEL_RXELECIDLEMODE_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXEQTRAINING_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXGEARBOXSLIP_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXLATCLK_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXLPMEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXLPMGCHOLD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXLPMGCOVRDEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXLPMHFHOLD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXLPMHFOVRDEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXLPMLFHOLD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXLPMLFKLOVRDEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXLPMOSHOLD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXLPMOSOVRDEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXMCOMMAALIGNEN_int;
    wire [(NUM_CHANNELS*  2)-1:0] GTYE4_CHANNEL_RXMONITORSEL_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXOOBRESET_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXOSCALRESET_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXOSHOLD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXOSOVRDEN_int;
    wire [(NUM_CHANNELS*  3)-1:0] GTYE4_CHANNEL_RXOUTCLKSEL_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXPCOMMAALIGNEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXPCSRESET_int;
    wire [(NUM_CHANNELS*  2)-1:0] GTYE4_CHANNEL_RXPD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXPHALIGN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXPHALIGNEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXPHDLYPD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXPHDLYRESET_int;
    wire [(NUM_CHANNELS*  2)-1:0] GTYE4_CHANNEL_RXPLLCLKSEL_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXPMARESET_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXPOLARITY_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXPRBSCNTRESET_int;
    wire [(NUM_CHANNELS*  4)-1:0] GTYE4_CHANNEL_RXPRBSSEL_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXPROGDIVRESET_int;
    wire [(NUM_CHANNELS*  3)-1:0] GTYE4_CHANNEL_RXRATE_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXRATEMODE_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXSLIDE_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXSLIPOUTCLK_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXSLIPPMA_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXSYNCALLIN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXSYNCIN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXSYNCMODE_int;
    wire [(NUM_CHANNELS*  2)-1:0] GTYE4_CHANNEL_RXSYSCLKSEL_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXTERMINATION_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXUSERRDY_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXUSRCLK_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_RXUSRCLK2_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_SIGVALIDCLK_int;
    wire [(NUM_CHANNELS* 20)-1:0] GTYE4_CHANNEL_TSTIN_int;
    wire [(NUM_CHANNELS*  8)-1:0] GTYE4_CHANNEL_TX8B10BBYPASS_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TX8B10BEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXCOMINIT_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXCOMSAS_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXCOMWAKE_int;
    wire [(NUM_CHANNELS* 16)-1:0] GTYE4_CHANNEL_TXCTRL0_int;
    wire [(NUM_CHANNELS* 16)-1:0] GTYE4_CHANNEL_TXCTRL1_int;
    wire [(NUM_CHANNELS*  8)-1:0] GTYE4_CHANNEL_TXCTRL2_int;
    wire [(NUM_CHANNELS*128)-1:0] GTYE4_CHANNEL_TXDATA_int;
    wire [(NUM_CHANNELS*  8)-1:0] GTYE4_CHANNEL_TXDATAEXTENDRSVD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXDCCFORCESTART_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXDCCRESET_int;
    wire [(NUM_CHANNELS*  2)-1:0] GTYE4_CHANNEL_TXDEEMPH_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXDETECTRX_int;
    wire [(NUM_CHANNELS*  5)-1:0] GTYE4_CHANNEL_TXDIFFCTRL_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXDLYBYPASS_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXDLYEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXDLYHOLD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXDLYOVRDEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXDLYSRESET_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXDLYUPDOWN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXELECIDLE_int;
    wire [(NUM_CHANNELS*  6)-1:0] GTYE4_CHANNEL_TXHEADER_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXINHIBIT_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXLATCLK_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXLFPSTRESET_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXLFPSU2LPEXIT_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXLFPSU3WAKE_int;
    wire [(NUM_CHANNELS*  7)-1:0] GTYE4_CHANNEL_TXMAINCURSOR_int;
    wire [(NUM_CHANNELS*  3)-1:0] GTYE4_CHANNEL_TXMARGIN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXMUXDCDEXHOLD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXMUXDCDORWREN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXONESZEROS_int;
    wire [(NUM_CHANNELS*  3)-1:0] GTYE4_CHANNEL_TXOUTCLKSEL_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPCSRESET_int;
    wire [(NUM_CHANNELS*  2)-1:0] GTYE4_CHANNEL_TXPD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPDELECIDLEMODE_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPHALIGN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPHALIGNEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPHDLYPD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPHDLYRESET_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPHDLYTSTCLK_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPHINIT_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPHOVRDEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPIPPMEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPIPPMOVRDEN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPIPPMPD_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPIPPMSEL_int;
    wire [(NUM_CHANNELS*  5)-1:0] GTYE4_CHANNEL_TXPIPPMSTEPSIZE_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPISOPD_int;
    wire [(NUM_CHANNELS*  2)-1:0] GTYE4_CHANNEL_TXPLLCLKSEL_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPMARESET_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPOLARITY_int;
    wire [(NUM_CHANNELS*  5)-1:0] GTYE4_CHANNEL_TXPOSTCURSOR_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPRBSFORCEERR_int;
    wire [(NUM_CHANNELS*  4)-1:0] GTYE4_CHANNEL_TXPRBSSEL_int;
    wire [(NUM_CHANNELS*  5)-1:0] GTYE4_CHANNEL_TXPRECURSOR_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXPROGDIVRESET_int;
    wire [(NUM_CHANNELS*  3)-1:0] GTYE4_CHANNEL_TXRATE_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXRATEMODE_int;
    wire [(NUM_CHANNELS*  7)-1:0] GTYE4_CHANNEL_TXSEQUENCE_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXSWING_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXSYNCALLIN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXSYNCIN_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXSYNCMODE_int;
    wire [(NUM_CHANNELS*  2)-1:0] GTYE4_CHANNEL_TXSYSCLKSEL_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXUSERRDY_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXUSRCLK_int;
    wire [(NUM_CHANNELS*  1)-1:0] GTYE4_CHANNEL_TXUSRCLK2_int;

    // assign each vector either the corresponding tie-off value or the corresponding input port, scaled appropriately
    if (GTYE4_CHANNEL_CDRSTEPDIR_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_CDRSTEPDIR_int = {NUM_CHANNELS{GTYE4_CHANNEL_CDRSTEPDIR_VAL}};
    else
      assign GTYE4_CHANNEL_CDRSTEPDIR_int = {NUM_CHANNELS{GTYE4_CHANNEL_CDRSTEPDIR}};

    if (GTYE4_CHANNEL_CDRSTEPSQ_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_CDRSTEPSQ_int = {NUM_CHANNELS{GTYE4_CHANNEL_CDRSTEPSQ_VAL}};
    else
      assign GTYE4_CHANNEL_CDRSTEPSQ_int = {NUM_CHANNELS{GTYE4_CHANNEL_CDRSTEPSQ}};

    if (GTYE4_CHANNEL_CDRSTEPSX_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_CDRSTEPSX_int = {NUM_CHANNELS{GTYE4_CHANNEL_CDRSTEPSX_VAL}};
    else
      assign GTYE4_CHANNEL_CDRSTEPSX_int = {NUM_CHANNELS{GTYE4_CHANNEL_CDRSTEPSX}};

    if (GTYE4_CHANNEL_CFGRESET_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_CFGRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_CFGRESET_VAL}};
    else
      assign GTYE4_CHANNEL_CFGRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_CFGRESET}};

    if (GTYE4_CHANNEL_CLKRSVD0_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_CLKRSVD0_int = {NUM_CHANNELS{GTYE4_CHANNEL_CLKRSVD0_VAL}};
    else
      assign GTYE4_CHANNEL_CLKRSVD0_int = {NUM_CHANNELS{GTYE4_CHANNEL_CLKRSVD0}};

    if (GTYE4_CHANNEL_CLKRSVD1_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_CLKRSVD1_int = {NUM_CHANNELS{GTYE4_CHANNEL_CLKRSVD1_VAL}};
    else
      assign GTYE4_CHANNEL_CLKRSVD1_int = {NUM_CHANNELS{GTYE4_CHANNEL_CLKRSVD1}};

    if (GTYE4_CHANNEL_CPLLFREQLOCK_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_CPLLFREQLOCK_int = {NUM_CHANNELS{GTYE4_CHANNEL_CPLLFREQLOCK_VAL}};
    else
      assign GTYE4_CHANNEL_CPLLFREQLOCK_int = {NUM_CHANNELS{GTYE4_CHANNEL_CPLLFREQLOCK}};

    if (GTYE4_CHANNEL_CPLLLOCKDETCLK_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_CPLLLOCKDETCLK_int = {NUM_CHANNELS{GTYE4_CHANNEL_CPLLLOCKDETCLK_VAL}};
    else
      assign GTYE4_CHANNEL_CPLLLOCKDETCLK_int = {NUM_CHANNELS{GTYE4_CHANNEL_CPLLLOCKDETCLK}};

    if (GTYE4_CHANNEL_CPLLLOCKEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_CPLLLOCKEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_CPLLLOCKEN_VAL}};
    else
      assign GTYE4_CHANNEL_CPLLLOCKEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_CPLLLOCKEN}};

    if (GTYE4_CHANNEL_CPLLPD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_CPLLPD_int = {NUM_CHANNELS{GTYE4_CHANNEL_CPLLPD_VAL}};
    else
      assign GTYE4_CHANNEL_CPLLPD_int = {NUM_CHANNELS{GTYE4_CHANNEL_CPLLPD}};

    if (GTYE4_CHANNEL_CPLLREFCLKSEL_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_CPLLREFCLKSEL_int = {NUM_CHANNELS{GTYE4_CHANNEL_CPLLREFCLKSEL_VAL}};
    else
      assign GTYE4_CHANNEL_CPLLREFCLKSEL_int = {NUM_CHANNELS{GTYE4_CHANNEL_CPLLREFCLKSEL}};

    if (GTYE4_CHANNEL_CPLLRESET_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_CPLLRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_CPLLRESET_VAL}};
    else
      assign GTYE4_CHANNEL_CPLLRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_CPLLRESET}};

    if (GTYE4_CHANNEL_DMONFIFORESET_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_DMONFIFORESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_DMONFIFORESET_VAL}};
    else
      assign GTYE4_CHANNEL_DMONFIFORESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_DMONFIFORESET}};

    if (GTYE4_CHANNEL_DMONITORCLK_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_DMONITORCLK_int = {NUM_CHANNELS{GTYE4_CHANNEL_DMONITORCLK_VAL}};
    else
      assign GTYE4_CHANNEL_DMONITORCLK_int = {NUM_CHANNELS{GTYE4_CHANNEL_DMONITORCLK}};

    if (GTYE4_CHANNEL_DRPADDR_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_DRPADDR_int = {NUM_CHANNELS{GTYE4_CHANNEL_DRPADDR_VAL}};
    else
      assign GTYE4_CHANNEL_DRPADDR_int = {NUM_CHANNELS{GTYE4_CHANNEL_DRPADDR}};

    if (GTYE4_CHANNEL_DRPCLK_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_DRPCLK_int = {NUM_CHANNELS{GTYE4_CHANNEL_DRPCLK_VAL}};
    else
      assign GTYE4_CHANNEL_DRPCLK_int = {NUM_CHANNELS{GTYE4_CHANNEL_DRPCLK}};

    if (GTYE4_CHANNEL_DRPDI_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_DRPDI_int = {NUM_CHANNELS{GTYE4_CHANNEL_DRPDI_VAL}};
    else
      assign GTYE4_CHANNEL_DRPDI_int = {NUM_CHANNELS{GTYE4_CHANNEL_DRPDI}};

    if (GTYE4_CHANNEL_DRPEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_DRPEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_DRPEN_VAL}};
    else
      assign GTYE4_CHANNEL_DRPEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_DRPEN}};

    if (GTYE4_CHANNEL_DRPRST_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_DRPRST_int = {NUM_CHANNELS{GTYE4_CHANNEL_DRPRST_VAL}};
    else
      assign GTYE4_CHANNEL_DRPRST_int = {NUM_CHANNELS{GTYE4_CHANNEL_DRPRST}};

    if (GTYE4_CHANNEL_DRPWE_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_DRPWE_int = {NUM_CHANNELS{GTYE4_CHANNEL_DRPWE_VAL}};
    else
      assign GTYE4_CHANNEL_DRPWE_int = {NUM_CHANNELS{GTYE4_CHANNEL_DRPWE}};

    if (GTYE4_CHANNEL_EYESCANRESET_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_EYESCANRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_EYESCANRESET_VAL}};
    else
      assign GTYE4_CHANNEL_EYESCANRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_EYESCANRESET}};

    if (GTYE4_CHANNEL_EYESCANTRIGGER_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_EYESCANTRIGGER_int = {NUM_CHANNELS{GTYE4_CHANNEL_EYESCANTRIGGER_VAL}};
    else
      assign GTYE4_CHANNEL_EYESCANTRIGGER_int = {NUM_CHANNELS{GTYE4_CHANNEL_EYESCANTRIGGER}};

    if (GTYE4_CHANNEL_FREQOS_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_FREQOS_int = {NUM_CHANNELS{GTYE4_CHANNEL_FREQOS_VAL}};
    else
      assign GTYE4_CHANNEL_FREQOS_int = {NUM_CHANNELS{GTYE4_CHANNEL_FREQOS}};

    if (GTYE4_CHANNEL_GTGREFCLK_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_GTGREFCLK_int = {NUM_CHANNELS{GTYE4_CHANNEL_GTGREFCLK_VAL}};
    else
      assign GTYE4_CHANNEL_GTGREFCLK_int = {NUM_CHANNELS{GTYE4_CHANNEL_GTGREFCLK}};

    if (GTYE4_CHANNEL_GTNORTHREFCLK0_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_GTNORTHREFCLK0_int = {NUM_CHANNELS{GTYE4_CHANNEL_GTNORTHREFCLK0_VAL}};
    else
      assign GTYE4_CHANNEL_GTNORTHREFCLK0_int = {NUM_CHANNELS{GTYE4_CHANNEL_GTNORTHREFCLK0}};

    if (GTYE4_CHANNEL_GTNORTHREFCLK1_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_GTNORTHREFCLK1_int = {NUM_CHANNELS{GTYE4_CHANNEL_GTNORTHREFCLK1_VAL}};
    else
      assign GTYE4_CHANNEL_GTNORTHREFCLK1_int = {NUM_CHANNELS{GTYE4_CHANNEL_GTNORTHREFCLK1}};

    if (GTYE4_CHANNEL_GTREFCLK0_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_GTREFCLK0_int = {NUM_CHANNELS{GTYE4_CHANNEL_GTREFCLK0_VAL}};
    else
      assign GTYE4_CHANNEL_GTREFCLK0_int = {NUM_CHANNELS{GTYE4_CHANNEL_GTREFCLK0}};

    if (GTYE4_CHANNEL_GTREFCLK1_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_GTREFCLK1_int = {NUM_CHANNELS{GTYE4_CHANNEL_GTREFCLK1_VAL}};
    else
      assign GTYE4_CHANNEL_GTREFCLK1_int = {NUM_CHANNELS{GTYE4_CHANNEL_GTREFCLK1}};

    if (GTYE4_CHANNEL_GTRSVD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_GTRSVD_int = {NUM_CHANNELS{GTYE4_CHANNEL_GTRSVD_VAL}};
    else
      assign GTYE4_CHANNEL_GTRSVD_int = {NUM_CHANNELS{GTYE4_CHANNEL_GTRSVD}};

    if (GTYE4_CHANNEL_GTRXRESET_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_GTRXRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_GTRXRESET_VAL}};
    else
      assign GTYE4_CHANNEL_GTRXRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_GTRXRESET}};

    if (GTYE4_CHANNEL_GTRXRESETSEL_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_GTRXRESETSEL_int = {NUM_CHANNELS{GTYE4_CHANNEL_GTRXRESETSEL_VAL}};
    else
      assign GTYE4_CHANNEL_GTRXRESETSEL_int = {NUM_CHANNELS{GTYE4_CHANNEL_GTRXRESETSEL}};

    if (GTYE4_CHANNEL_GTSOUTHREFCLK0_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_GTSOUTHREFCLK0_int = {NUM_CHANNELS{GTYE4_CHANNEL_GTSOUTHREFCLK0_VAL}};
    else
      assign GTYE4_CHANNEL_GTSOUTHREFCLK0_int = {NUM_CHANNELS{GTYE4_CHANNEL_GTSOUTHREFCLK0}};

    if (GTYE4_CHANNEL_GTSOUTHREFCLK1_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_GTSOUTHREFCLK1_int = {NUM_CHANNELS{GTYE4_CHANNEL_GTSOUTHREFCLK1_VAL}};
    else
      assign GTYE4_CHANNEL_GTSOUTHREFCLK1_int = {NUM_CHANNELS{GTYE4_CHANNEL_GTSOUTHREFCLK1}};

    if (GTYE4_CHANNEL_GTTXRESET_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_GTTXRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_GTTXRESET_VAL}};
    else
      assign GTYE4_CHANNEL_GTTXRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_GTTXRESET}};

    if (GTYE4_CHANNEL_GTTXRESETSEL_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_GTTXRESETSEL_int = {NUM_CHANNELS{GTYE4_CHANNEL_GTTXRESETSEL_VAL}};
    else
      assign GTYE4_CHANNEL_GTTXRESETSEL_int = {NUM_CHANNELS{GTYE4_CHANNEL_GTTXRESETSEL}};

    if (GTYE4_CHANNEL_GTYRXN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_GTYRXN_int = {NUM_CHANNELS{GTYE4_CHANNEL_GTYRXN_VAL}};
    else
      assign GTYE4_CHANNEL_GTYRXN_int = {NUM_CHANNELS{GTYE4_CHANNEL_GTYRXN}};

    if (GTYE4_CHANNEL_GTYRXP_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_GTYRXP_int = {NUM_CHANNELS{GTYE4_CHANNEL_GTYRXP_VAL}};
    else
      assign GTYE4_CHANNEL_GTYRXP_int = {NUM_CHANNELS{GTYE4_CHANNEL_GTYRXP}};

    if (GTYE4_CHANNEL_INCPCTRL_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_INCPCTRL_int = {NUM_CHANNELS{GTYE4_CHANNEL_INCPCTRL_VAL}};
    else
      assign GTYE4_CHANNEL_INCPCTRL_int = {NUM_CHANNELS{GTYE4_CHANNEL_INCPCTRL}};

    if (GTYE4_CHANNEL_LOOPBACK_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_LOOPBACK_int = {NUM_CHANNELS{GTYE4_CHANNEL_LOOPBACK_VAL}};
    else
      assign GTYE4_CHANNEL_LOOPBACK_int = {NUM_CHANNELS{GTYE4_CHANNEL_LOOPBACK}};

    if (GTYE4_CHANNEL_PCIEEQRXEQADAPTDONE_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_PCIEEQRXEQADAPTDONE_int = {NUM_CHANNELS{GTYE4_CHANNEL_PCIEEQRXEQADAPTDONE_VAL}};
    else
      assign GTYE4_CHANNEL_PCIEEQRXEQADAPTDONE_int = {NUM_CHANNELS{GTYE4_CHANNEL_PCIEEQRXEQADAPTDONE}};

    if (GTYE4_CHANNEL_PCIERSTIDLE_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_PCIERSTIDLE_int = {NUM_CHANNELS{GTYE4_CHANNEL_PCIERSTIDLE_VAL}};
    else
      assign GTYE4_CHANNEL_PCIERSTIDLE_int = {NUM_CHANNELS{GTYE4_CHANNEL_PCIERSTIDLE}};

    if (GTYE4_CHANNEL_PCIERSTTXSYNCSTART_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_PCIERSTTXSYNCSTART_int = {NUM_CHANNELS{GTYE4_CHANNEL_PCIERSTTXSYNCSTART_VAL}};
    else
      assign GTYE4_CHANNEL_PCIERSTTXSYNCSTART_int = {NUM_CHANNELS{GTYE4_CHANNEL_PCIERSTTXSYNCSTART}};

    if (GTYE4_CHANNEL_PCIEUSERRATEDONE_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_PCIEUSERRATEDONE_int = {NUM_CHANNELS{GTYE4_CHANNEL_PCIEUSERRATEDONE_VAL}};
    else
      assign GTYE4_CHANNEL_PCIEUSERRATEDONE_int = {NUM_CHANNELS{GTYE4_CHANNEL_PCIEUSERRATEDONE}};

    if (GTYE4_CHANNEL_PCSRSVDIN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_PCSRSVDIN_int = {NUM_CHANNELS{GTYE4_CHANNEL_PCSRSVDIN_VAL}};
    else
      assign GTYE4_CHANNEL_PCSRSVDIN_int = {NUM_CHANNELS{GTYE4_CHANNEL_PCSRSVDIN}};

    if (GTYE4_CHANNEL_QPLL0CLK_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_QPLL0CLK_int = {NUM_CHANNELS{GTYE4_CHANNEL_QPLL0CLK_VAL}};
    else
      assign GTYE4_CHANNEL_QPLL0CLK_int = {NUM_CHANNELS{GTYE4_CHANNEL_QPLL0CLK}};

    if (GTYE4_CHANNEL_QPLL0FREQLOCK_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_QPLL0FREQLOCK_int = {NUM_CHANNELS{GTYE4_CHANNEL_QPLL0FREQLOCK_VAL}};
    else
      assign GTYE4_CHANNEL_QPLL0FREQLOCK_int = {NUM_CHANNELS{GTYE4_CHANNEL_QPLL0FREQLOCK}};

    if (GTYE4_CHANNEL_QPLL0REFCLK_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_QPLL0REFCLK_int = {NUM_CHANNELS{GTYE4_CHANNEL_QPLL0REFCLK_VAL}};
    else
      assign GTYE4_CHANNEL_QPLL0REFCLK_int = {NUM_CHANNELS{GTYE4_CHANNEL_QPLL0REFCLK}};

    if (GTYE4_CHANNEL_QPLL1CLK_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_QPLL1CLK_int = {NUM_CHANNELS{GTYE4_CHANNEL_QPLL1CLK_VAL}};
    else
      assign GTYE4_CHANNEL_QPLL1CLK_int = {NUM_CHANNELS{GTYE4_CHANNEL_QPLL1CLK}};

    if (GTYE4_CHANNEL_QPLL1FREQLOCK_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_QPLL1FREQLOCK_int = {NUM_CHANNELS{GTYE4_CHANNEL_QPLL1FREQLOCK_VAL}};
    else
      assign GTYE4_CHANNEL_QPLL1FREQLOCK_int = {NUM_CHANNELS{GTYE4_CHANNEL_QPLL1FREQLOCK}};

    if (GTYE4_CHANNEL_QPLL1REFCLK_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_QPLL1REFCLK_int = {NUM_CHANNELS{GTYE4_CHANNEL_QPLL1REFCLK_VAL}};
    else
      assign GTYE4_CHANNEL_QPLL1REFCLK_int = {NUM_CHANNELS{GTYE4_CHANNEL_QPLL1REFCLK}};

    if (GTYE4_CHANNEL_RESETOVRD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RESETOVRD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RESETOVRD_VAL}};
    else
      assign GTYE4_CHANNEL_RESETOVRD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RESETOVRD}};

    if (GTYE4_CHANNEL_RX8B10BEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RX8B10BEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RX8B10BEN_VAL}};
    else
      assign GTYE4_CHANNEL_RX8B10BEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RX8B10BEN}};

    if (GTYE4_CHANNEL_RXAFECFOKEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXAFECFOKEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXAFECFOKEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXAFECFOKEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXAFECFOKEN}};

    if (GTYE4_CHANNEL_RXBUFRESET_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXBUFRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXBUFRESET_VAL}};
    else
      assign GTYE4_CHANNEL_RXBUFRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXBUFRESET}};

    if (GTYE4_CHANNEL_RXCDRFREQRESET_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXCDRFREQRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXCDRFREQRESET_VAL}};
    else
      assign GTYE4_CHANNEL_RXCDRFREQRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXCDRFREQRESET}};

    if (GTYE4_CHANNEL_RXCDRHOLD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXCDRHOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXCDRHOLD_VAL}};
    else
      assign GTYE4_CHANNEL_RXCDRHOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXCDRHOLD}};

    if (GTYE4_CHANNEL_RXCDROVRDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXCDROVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXCDROVRDEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXCDROVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXCDROVRDEN}};

    if (GTYE4_CHANNEL_RXCDRRESET_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXCDRRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXCDRRESET_VAL}};
    else
      assign GTYE4_CHANNEL_RXCDRRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXCDRRESET}};

    if (GTYE4_CHANNEL_RXCHBONDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXCHBONDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXCHBONDEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXCHBONDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXCHBONDEN}};

    if (GTYE4_CHANNEL_RXCHBONDI_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXCHBONDI_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXCHBONDI_VAL}};
    else
      assign GTYE4_CHANNEL_RXCHBONDI_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXCHBONDI}};

    if (GTYE4_CHANNEL_RXCHBONDLEVEL_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXCHBONDLEVEL_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXCHBONDLEVEL_VAL}};
    else
      assign GTYE4_CHANNEL_RXCHBONDLEVEL_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXCHBONDLEVEL}};

    if (GTYE4_CHANNEL_RXCHBONDMASTER_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXCHBONDMASTER_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXCHBONDMASTER_VAL}};
    else
      assign GTYE4_CHANNEL_RXCHBONDMASTER_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXCHBONDMASTER}};

    if (GTYE4_CHANNEL_RXCHBONDSLAVE_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXCHBONDSLAVE_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXCHBONDSLAVE_VAL}};
    else
      assign GTYE4_CHANNEL_RXCHBONDSLAVE_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXCHBONDSLAVE}};

    if (GTYE4_CHANNEL_RXCKCALRESET_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXCKCALRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXCKCALRESET_VAL}};
    else
      assign GTYE4_CHANNEL_RXCKCALRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXCKCALRESET}};

    if (GTYE4_CHANNEL_RXCKCALSTART_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXCKCALSTART_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXCKCALSTART_VAL}};
    else
      assign GTYE4_CHANNEL_RXCKCALSTART_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXCKCALSTART}};

    if (GTYE4_CHANNEL_RXCOMMADETEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXCOMMADETEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXCOMMADETEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXCOMMADETEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXCOMMADETEN}};

    if (GTYE4_CHANNEL_RXDFEAGCHOLD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFEAGCHOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFEAGCHOLD_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFEAGCHOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFEAGCHOLD}};

    if (GTYE4_CHANNEL_RXDFEAGCOVRDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFEAGCOVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFEAGCOVRDEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFEAGCOVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFEAGCOVRDEN}};

    if (GTYE4_CHANNEL_RXDFECFOKFCNUM_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFECFOKFCNUM_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFECFOKFCNUM_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFECFOKFCNUM_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFECFOKFCNUM}};

    if (GTYE4_CHANNEL_RXDFECFOKFEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFECFOKFEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFECFOKFEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFECFOKFEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFECFOKFEN}};

    if (GTYE4_CHANNEL_RXDFECFOKFPULSE_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFECFOKFPULSE_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFECFOKFPULSE_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFECFOKFPULSE_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFECFOKFPULSE}};

    if (GTYE4_CHANNEL_RXDFECFOKHOLD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFECFOKHOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFECFOKHOLD_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFECFOKHOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFECFOKHOLD}};

    if (GTYE4_CHANNEL_RXDFECFOKOVREN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFECFOKOVREN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFECFOKOVREN_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFECFOKOVREN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFECFOKOVREN}};

    if (GTYE4_CHANNEL_RXDFEKHHOLD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFEKHHOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFEKHHOLD_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFEKHHOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFEKHHOLD}};

    if (GTYE4_CHANNEL_RXDFEKHOVRDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFEKHOVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFEKHOVRDEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFEKHOVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFEKHOVRDEN}};

    if (GTYE4_CHANNEL_RXDFELFHOLD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFELFHOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFELFHOLD_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFELFHOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFELFHOLD}};

    if (GTYE4_CHANNEL_RXDFELFOVRDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFELFOVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFELFOVRDEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFELFOVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFELFOVRDEN}};

    if (GTYE4_CHANNEL_RXDFELPMRESET_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFELPMRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFELPMRESET_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFELPMRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFELPMRESET}};

    if (GTYE4_CHANNEL_RXDFETAP10HOLD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFETAP10HOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP10HOLD_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFETAP10HOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP10HOLD}};

    if (GTYE4_CHANNEL_RXDFETAP10OVRDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFETAP10OVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP10OVRDEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFETAP10OVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP10OVRDEN}};

    if (GTYE4_CHANNEL_RXDFETAP11HOLD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFETAP11HOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP11HOLD_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFETAP11HOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP11HOLD}};

    if (GTYE4_CHANNEL_RXDFETAP11OVRDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFETAP11OVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP11OVRDEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFETAP11OVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP11OVRDEN}};

    if (GTYE4_CHANNEL_RXDFETAP12HOLD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFETAP12HOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP12HOLD_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFETAP12HOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP12HOLD}};

    if (GTYE4_CHANNEL_RXDFETAP12OVRDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFETAP12OVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP12OVRDEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFETAP12OVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP12OVRDEN}};

    if (GTYE4_CHANNEL_RXDFETAP13HOLD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFETAP13HOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP13HOLD_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFETAP13HOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP13HOLD}};

    if (GTYE4_CHANNEL_RXDFETAP13OVRDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFETAP13OVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP13OVRDEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFETAP13OVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP13OVRDEN}};

    if (GTYE4_CHANNEL_RXDFETAP14HOLD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFETAP14HOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP14HOLD_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFETAP14HOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP14HOLD}};

    if (GTYE4_CHANNEL_RXDFETAP14OVRDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFETAP14OVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP14OVRDEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFETAP14OVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP14OVRDEN}};

    if (GTYE4_CHANNEL_RXDFETAP15HOLD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFETAP15HOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP15HOLD_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFETAP15HOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP15HOLD}};

    if (GTYE4_CHANNEL_RXDFETAP15OVRDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFETAP15OVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP15OVRDEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFETAP15OVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP15OVRDEN}};

    if (GTYE4_CHANNEL_RXDFETAP2HOLD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFETAP2HOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP2HOLD_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFETAP2HOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP2HOLD}};

    if (GTYE4_CHANNEL_RXDFETAP2OVRDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFETAP2OVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP2OVRDEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFETAP2OVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP2OVRDEN}};

    if (GTYE4_CHANNEL_RXDFETAP3HOLD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFETAP3HOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP3HOLD_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFETAP3HOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP3HOLD}};

    if (GTYE4_CHANNEL_RXDFETAP3OVRDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFETAP3OVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP3OVRDEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFETAP3OVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP3OVRDEN}};

    if (GTYE4_CHANNEL_RXDFETAP4HOLD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFETAP4HOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP4HOLD_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFETAP4HOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP4HOLD}};

    if (GTYE4_CHANNEL_RXDFETAP4OVRDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFETAP4OVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP4OVRDEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFETAP4OVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP4OVRDEN}};

    if (GTYE4_CHANNEL_RXDFETAP5HOLD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFETAP5HOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP5HOLD_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFETAP5HOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP5HOLD}};

    if (GTYE4_CHANNEL_RXDFETAP5OVRDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFETAP5OVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP5OVRDEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFETAP5OVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP5OVRDEN}};

    if (GTYE4_CHANNEL_RXDFETAP6HOLD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFETAP6HOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP6HOLD_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFETAP6HOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP6HOLD}};

    if (GTYE4_CHANNEL_RXDFETAP6OVRDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFETAP6OVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP6OVRDEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFETAP6OVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP6OVRDEN}};

    if (GTYE4_CHANNEL_RXDFETAP7HOLD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFETAP7HOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP7HOLD_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFETAP7HOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP7HOLD}};

    if (GTYE4_CHANNEL_RXDFETAP7OVRDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFETAP7OVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP7OVRDEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFETAP7OVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP7OVRDEN}};

    if (GTYE4_CHANNEL_RXDFETAP8HOLD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFETAP8HOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP8HOLD_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFETAP8HOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP8HOLD}};

    if (GTYE4_CHANNEL_RXDFETAP8OVRDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFETAP8OVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP8OVRDEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFETAP8OVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP8OVRDEN}};

    if (GTYE4_CHANNEL_RXDFETAP9HOLD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFETAP9HOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP9HOLD_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFETAP9HOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP9HOLD}};

    if (GTYE4_CHANNEL_RXDFETAP9OVRDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFETAP9OVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP9OVRDEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFETAP9OVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFETAP9OVRDEN}};

    if (GTYE4_CHANNEL_RXDFEUTHOLD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFEUTHOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFEUTHOLD_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFEUTHOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFEUTHOLD}};

    if (GTYE4_CHANNEL_RXDFEUTOVRDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFEUTOVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFEUTOVRDEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFEUTOVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFEUTOVRDEN}};

    if (GTYE4_CHANNEL_RXDFEVPHOLD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFEVPHOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFEVPHOLD_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFEVPHOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFEVPHOLD}};

    if (GTYE4_CHANNEL_RXDFEVPOVRDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFEVPOVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFEVPOVRDEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFEVPOVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFEVPOVRDEN}};

    if (GTYE4_CHANNEL_RXDFEXYDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDFEXYDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFEXYDEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXDFEXYDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDFEXYDEN}};

    if (GTYE4_CHANNEL_RXDLYBYPASS_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDLYBYPASS_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDLYBYPASS_VAL}};
    else
      assign GTYE4_CHANNEL_RXDLYBYPASS_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDLYBYPASS}};

    if (GTYE4_CHANNEL_RXDLYEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDLYEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDLYEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXDLYEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDLYEN}};

    if (GTYE4_CHANNEL_RXDLYOVRDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDLYOVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDLYOVRDEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXDLYOVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDLYOVRDEN}};

    if (GTYE4_CHANNEL_RXDLYSRESET_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXDLYSRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDLYSRESET_VAL}};
    else
      assign GTYE4_CHANNEL_RXDLYSRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXDLYSRESET}};

    if (GTYE4_CHANNEL_RXELECIDLEMODE_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXELECIDLEMODE_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXELECIDLEMODE_VAL}};
    else
      assign GTYE4_CHANNEL_RXELECIDLEMODE_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXELECIDLEMODE}};

    if (GTYE4_CHANNEL_RXEQTRAINING_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXEQTRAINING_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXEQTRAINING_VAL}};
    else
      assign GTYE4_CHANNEL_RXEQTRAINING_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXEQTRAINING}};

    if (GTYE4_CHANNEL_RXGEARBOXSLIP_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXGEARBOXSLIP_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXGEARBOXSLIP_VAL}};
    else
      assign GTYE4_CHANNEL_RXGEARBOXSLIP_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXGEARBOXSLIP}};

    if (GTYE4_CHANNEL_RXLATCLK_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXLATCLK_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXLATCLK_VAL}};
    else
      assign GTYE4_CHANNEL_RXLATCLK_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXLATCLK}};

    if (GTYE4_CHANNEL_RXLPMEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXLPMEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXLPMEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXLPMEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXLPMEN}};

    if (GTYE4_CHANNEL_RXLPMGCHOLD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXLPMGCHOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXLPMGCHOLD_VAL}};
    else
      assign GTYE4_CHANNEL_RXLPMGCHOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXLPMGCHOLD}};

    if (GTYE4_CHANNEL_RXLPMGCOVRDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXLPMGCOVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXLPMGCOVRDEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXLPMGCOVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXLPMGCOVRDEN}};

    if (GTYE4_CHANNEL_RXLPMHFHOLD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXLPMHFHOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXLPMHFHOLD_VAL}};
    else
      assign GTYE4_CHANNEL_RXLPMHFHOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXLPMHFHOLD}};

    if (GTYE4_CHANNEL_RXLPMHFOVRDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXLPMHFOVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXLPMHFOVRDEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXLPMHFOVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXLPMHFOVRDEN}};

    if (GTYE4_CHANNEL_RXLPMLFHOLD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXLPMLFHOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXLPMLFHOLD_VAL}};
    else
      assign GTYE4_CHANNEL_RXLPMLFHOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXLPMLFHOLD}};

    if (GTYE4_CHANNEL_RXLPMLFKLOVRDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXLPMLFKLOVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXLPMLFKLOVRDEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXLPMLFKLOVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXLPMLFKLOVRDEN}};

    if (GTYE4_CHANNEL_RXLPMOSHOLD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXLPMOSHOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXLPMOSHOLD_VAL}};
    else
      assign GTYE4_CHANNEL_RXLPMOSHOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXLPMOSHOLD}};

    if (GTYE4_CHANNEL_RXLPMOSOVRDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXLPMOSOVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXLPMOSOVRDEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXLPMOSOVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXLPMOSOVRDEN}};

    if (GTYE4_CHANNEL_RXMCOMMAALIGNEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXMCOMMAALIGNEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXMCOMMAALIGNEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXMCOMMAALIGNEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXMCOMMAALIGNEN}};

    if (GTYE4_CHANNEL_RXMONITORSEL_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXMONITORSEL_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXMONITORSEL_VAL}};
    else
      assign GTYE4_CHANNEL_RXMONITORSEL_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXMONITORSEL}};

    if (GTYE4_CHANNEL_RXOOBRESET_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXOOBRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXOOBRESET_VAL}};
    else
      assign GTYE4_CHANNEL_RXOOBRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXOOBRESET}};

    if (GTYE4_CHANNEL_RXOSCALRESET_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXOSCALRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXOSCALRESET_VAL}};
    else
      assign GTYE4_CHANNEL_RXOSCALRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXOSCALRESET}};

    if (GTYE4_CHANNEL_RXOSHOLD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXOSHOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXOSHOLD_VAL}};
    else
      assign GTYE4_CHANNEL_RXOSHOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXOSHOLD}};

    if (GTYE4_CHANNEL_RXOSOVRDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXOSOVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXOSOVRDEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXOSOVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXOSOVRDEN}};

    if (GTYE4_CHANNEL_RXOUTCLKSEL_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXOUTCLKSEL_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXOUTCLKSEL_VAL}};
    else
      assign GTYE4_CHANNEL_RXOUTCLKSEL_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXOUTCLKSEL}};

    if (GTYE4_CHANNEL_RXPCOMMAALIGNEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXPCOMMAALIGNEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXPCOMMAALIGNEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXPCOMMAALIGNEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXPCOMMAALIGNEN}};

    if (GTYE4_CHANNEL_RXPCSRESET_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXPCSRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXPCSRESET_VAL}};
    else
      assign GTYE4_CHANNEL_RXPCSRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXPCSRESET}};

    if (GTYE4_CHANNEL_RXPD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXPD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXPD_VAL}};
    else
      assign GTYE4_CHANNEL_RXPD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXPD}};

    if (GTYE4_CHANNEL_RXPHALIGN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXPHALIGN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXPHALIGN_VAL}};
    else
      assign GTYE4_CHANNEL_RXPHALIGN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXPHALIGN}};

    if (GTYE4_CHANNEL_RXPHALIGNEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXPHALIGNEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXPHALIGNEN_VAL}};
    else
      assign GTYE4_CHANNEL_RXPHALIGNEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXPHALIGNEN}};

    if (GTYE4_CHANNEL_RXPHDLYPD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXPHDLYPD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXPHDLYPD_VAL}};
    else
      assign GTYE4_CHANNEL_RXPHDLYPD_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXPHDLYPD}};

    if (GTYE4_CHANNEL_RXPHDLYRESET_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXPHDLYRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXPHDLYRESET_VAL}};
    else
      assign GTYE4_CHANNEL_RXPHDLYRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXPHDLYRESET}};

    if (GTYE4_CHANNEL_RXPLLCLKSEL_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXPLLCLKSEL_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXPLLCLKSEL_VAL}};
    else
      assign GTYE4_CHANNEL_RXPLLCLKSEL_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXPLLCLKSEL}};

    if (GTYE4_CHANNEL_RXPMARESET_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXPMARESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXPMARESET_VAL}};
    else
      assign GTYE4_CHANNEL_RXPMARESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXPMARESET}};

    if (GTYE4_CHANNEL_RXPOLARITY_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXPOLARITY_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXPOLARITY_VAL}};
    else
      assign GTYE4_CHANNEL_RXPOLARITY_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXPOLARITY}};

    if (GTYE4_CHANNEL_RXPRBSCNTRESET_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXPRBSCNTRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXPRBSCNTRESET_VAL}};
    else
      assign GTYE4_CHANNEL_RXPRBSCNTRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXPRBSCNTRESET}};

    if (GTYE4_CHANNEL_RXPRBSSEL_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXPRBSSEL_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXPRBSSEL_VAL}};
    else
      assign GTYE4_CHANNEL_RXPRBSSEL_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXPRBSSEL}};

    if (GTYE4_CHANNEL_RXPROGDIVRESET_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXPROGDIVRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXPROGDIVRESET_VAL}};
    else
      assign GTYE4_CHANNEL_RXPROGDIVRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXPROGDIVRESET}};

    if (GTYE4_CHANNEL_RXRATE_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXRATE_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXRATE_VAL}};
    else
      assign GTYE4_CHANNEL_RXRATE_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXRATE}};

    if (GTYE4_CHANNEL_RXRATEMODE_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXRATEMODE_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXRATEMODE_VAL}};
    else
      assign GTYE4_CHANNEL_RXRATEMODE_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXRATEMODE}};

    if (GTYE4_CHANNEL_RXSLIDE_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXSLIDE_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXSLIDE_VAL}};
    else
      assign GTYE4_CHANNEL_RXSLIDE_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXSLIDE}};

    if (GTYE4_CHANNEL_RXSLIPOUTCLK_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXSLIPOUTCLK_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXSLIPOUTCLK_VAL}};
    else
      assign GTYE4_CHANNEL_RXSLIPOUTCLK_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXSLIPOUTCLK}};

    if (GTYE4_CHANNEL_RXSLIPPMA_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXSLIPPMA_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXSLIPPMA_VAL}};
    else
      assign GTYE4_CHANNEL_RXSLIPPMA_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXSLIPPMA}};

    if (GTYE4_CHANNEL_RXSYNCALLIN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXSYNCALLIN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXSYNCALLIN_VAL}};
    else
      assign GTYE4_CHANNEL_RXSYNCALLIN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXSYNCALLIN}};

    if (GTYE4_CHANNEL_RXSYNCIN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXSYNCIN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXSYNCIN_VAL}};
    else
      assign GTYE4_CHANNEL_RXSYNCIN_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXSYNCIN}};

    if (GTYE4_CHANNEL_RXSYNCMODE_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXSYNCMODE_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXSYNCMODE_VAL}};
    else
      assign GTYE4_CHANNEL_RXSYNCMODE_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXSYNCMODE}};

    if (GTYE4_CHANNEL_RXSYSCLKSEL_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXSYSCLKSEL_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXSYSCLKSEL_VAL}};
    else
      assign GTYE4_CHANNEL_RXSYSCLKSEL_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXSYSCLKSEL}};

    if (GTYE4_CHANNEL_RXTERMINATION_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXTERMINATION_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXTERMINATION_VAL}};
    else
      assign GTYE4_CHANNEL_RXTERMINATION_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXTERMINATION}};

    if (GTYE4_CHANNEL_RXUSERRDY_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXUSERRDY_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXUSERRDY_VAL}};
    else
      assign GTYE4_CHANNEL_RXUSERRDY_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXUSERRDY}};

    if (GTYE4_CHANNEL_RXUSRCLK_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXUSRCLK_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXUSRCLK_VAL}};
    else
      assign GTYE4_CHANNEL_RXUSRCLK_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXUSRCLK}};

    if (GTYE4_CHANNEL_RXUSRCLK2_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_RXUSRCLK2_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXUSRCLK2_VAL}};
    else
      assign GTYE4_CHANNEL_RXUSRCLK2_int = {NUM_CHANNELS{GTYE4_CHANNEL_RXUSRCLK2}};

    if (GTYE4_CHANNEL_SIGVALIDCLK_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_SIGVALIDCLK_int = {NUM_CHANNELS{GTYE4_CHANNEL_SIGVALIDCLK_VAL}};
    else
      assign GTYE4_CHANNEL_SIGVALIDCLK_int = {NUM_CHANNELS{GTYE4_CHANNEL_SIGVALIDCLK}};

    if (GTYE4_CHANNEL_TSTIN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TSTIN_int = {NUM_CHANNELS{GTYE4_CHANNEL_TSTIN_VAL}};
    else
      assign GTYE4_CHANNEL_TSTIN_int = {NUM_CHANNELS{GTYE4_CHANNEL_TSTIN}};

    if (GTYE4_CHANNEL_TX8B10BBYPASS_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TX8B10BBYPASS_int = {NUM_CHANNELS{GTYE4_CHANNEL_TX8B10BBYPASS_VAL}};
    else
      assign GTYE4_CHANNEL_TX8B10BBYPASS_int = {NUM_CHANNELS{GTYE4_CHANNEL_TX8B10BBYPASS}};

    if (GTYE4_CHANNEL_TX8B10BEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TX8B10BEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_TX8B10BEN_VAL}};
    else
      assign GTYE4_CHANNEL_TX8B10BEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_TX8B10BEN}};

    if (GTYE4_CHANNEL_TXCOMINIT_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXCOMINIT_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXCOMINIT_VAL}};
    else
      assign GTYE4_CHANNEL_TXCOMINIT_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXCOMINIT}};

    if (GTYE4_CHANNEL_TXCOMSAS_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXCOMSAS_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXCOMSAS_VAL}};
    else
      assign GTYE4_CHANNEL_TXCOMSAS_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXCOMSAS}};

    if (GTYE4_CHANNEL_TXCOMWAKE_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXCOMWAKE_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXCOMWAKE_VAL}};
    else
      assign GTYE4_CHANNEL_TXCOMWAKE_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXCOMWAKE}};

    if (GTYE4_CHANNEL_TXCTRL0_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXCTRL0_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXCTRL0_VAL}};
    else
      assign GTYE4_CHANNEL_TXCTRL0_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXCTRL0}};

    if (GTYE4_CHANNEL_TXCTRL1_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXCTRL1_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXCTRL1_VAL}};
    else
      assign GTYE4_CHANNEL_TXCTRL1_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXCTRL1}};

    if (GTYE4_CHANNEL_TXCTRL2_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXCTRL2_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXCTRL2_VAL}};
    else
      assign GTYE4_CHANNEL_TXCTRL2_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXCTRL2}};

    if (GTYE4_CHANNEL_TXDATA_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXDATA_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXDATA_VAL}};
    else
      assign GTYE4_CHANNEL_TXDATA_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXDATA}};

    if (GTYE4_CHANNEL_TXDATAEXTENDRSVD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXDATAEXTENDRSVD_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXDATAEXTENDRSVD_VAL}};
    else
      assign GTYE4_CHANNEL_TXDATAEXTENDRSVD_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXDATAEXTENDRSVD}};

    if (GTYE4_CHANNEL_TXDCCFORCESTART_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXDCCFORCESTART_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXDCCFORCESTART_VAL}};
    else
      assign GTYE4_CHANNEL_TXDCCFORCESTART_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXDCCFORCESTART}};

    if (GTYE4_CHANNEL_TXDCCRESET_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXDCCRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXDCCRESET_VAL}};
    else
      assign GTYE4_CHANNEL_TXDCCRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXDCCRESET}};

    if (GTYE4_CHANNEL_TXDEEMPH_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXDEEMPH_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXDEEMPH_VAL}};
    else
      assign GTYE4_CHANNEL_TXDEEMPH_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXDEEMPH}};

    if (GTYE4_CHANNEL_TXDETECTRX_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXDETECTRX_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXDETECTRX_VAL}};
    else
      assign GTYE4_CHANNEL_TXDETECTRX_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXDETECTRX}};

    if (GTYE4_CHANNEL_TXDIFFCTRL_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXDIFFCTRL_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXDIFFCTRL_VAL}};
    else
      assign GTYE4_CHANNEL_TXDIFFCTRL_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXDIFFCTRL}};

    if (GTYE4_CHANNEL_TXDLYBYPASS_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXDLYBYPASS_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXDLYBYPASS_VAL}};
    else
      assign GTYE4_CHANNEL_TXDLYBYPASS_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXDLYBYPASS}};

    if (GTYE4_CHANNEL_TXDLYEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXDLYEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXDLYEN_VAL}};
    else
      assign GTYE4_CHANNEL_TXDLYEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXDLYEN}};

    if (GTYE4_CHANNEL_TXDLYHOLD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXDLYHOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXDLYHOLD_VAL}};
    else
      assign GTYE4_CHANNEL_TXDLYHOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXDLYHOLD}};

    if (GTYE4_CHANNEL_TXDLYOVRDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXDLYOVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXDLYOVRDEN_VAL}};
    else
      assign GTYE4_CHANNEL_TXDLYOVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXDLYOVRDEN}};

    if (GTYE4_CHANNEL_TXDLYSRESET_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXDLYSRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXDLYSRESET_VAL}};
    else
      assign GTYE4_CHANNEL_TXDLYSRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXDLYSRESET}};

    if (GTYE4_CHANNEL_TXDLYUPDOWN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXDLYUPDOWN_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXDLYUPDOWN_VAL}};
    else
      assign GTYE4_CHANNEL_TXDLYUPDOWN_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXDLYUPDOWN}};

    if (GTYE4_CHANNEL_TXELECIDLE_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXELECIDLE_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXELECIDLE_VAL}};
    else
      assign GTYE4_CHANNEL_TXELECIDLE_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXELECIDLE}};

    if (GTYE4_CHANNEL_TXHEADER_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXHEADER_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXHEADER_VAL}};
    else
      assign GTYE4_CHANNEL_TXHEADER_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXHEADER}};

    if (GTYE4_CHANNEL_TXINHIBIT_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXINHIBIT_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXINHIBIT_VAL}};
    else
      assign GTYE4_CHANNEL_TXINHIBIT_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXINHIBIT}};

    if (GTYE4_CHANNEL_TXLATCLK_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXLATCLK_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXLATCLK_VAL}};
    else
      assign GTYE4_CHANNEL_TXLATCLK_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXLATCLK}};

    if (GTYE4_CHANNEL_TXLFPSTRESET_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXLFPSTRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXLFPSTRESET_VAL}};
    else
      assign GTYE4_CHANNEL_TXLFPSTRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXLFPSTRESET}};

    if (GTYE4_CHANNEL_TXLFPSU2LPEXIT_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXLFPSU2LPEXIT_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXLFPSU2LPEXIT_VAL}};
    else
      assign GTYE4_CHANNEL_TXLFPSU2LPEXIT_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXLFPSU2LPEXIT}};

    if (GTYE4_CHANNEL_TXLFPSU3WAKE_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXLFPSU3WAKE_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXLFPSU3WAKE_VAL}};
    else
      assign GTYE4_CHANNEL_TXLFPSU3WAKE_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXLFPSU3WAKE}};

    if (GTYE4_CHANNEL_TXMAINCURSOR_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXMAINCURSOR_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXMAINCURSOR_VAL}};
    else
      assign GTYE4_CHANNEL_TXMAINCURSOR_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXMAINCURSOR}};

    if (GTYE4_CHANNEL_TXMARGIN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXMARGIN_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXMARGIN_VAL}};
    else
      assign GTYE4_CHANNEL_TXMARGIN_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXMARGIN}};

    if (GTYE4_CHANNEL_TXMUXDCDEXHOLD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXMUXDCDEXHOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXMUXDCDEXHOLD_VAL}};
    else
      assign GTYE4_CHANNEL_TXMUXDCDEXHOLD_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXMUXDCDEXHOLD}};

    if (GTYE4_CHANNEL_TXMUXDCDORWREN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXMUXDCDORWREN_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXMUXDCDORWREN_VAL}};
    else
      assign GTYE4_CHANNEL_TXMUXDCDORWREN_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXMUXDCDORWREN}};

    if (GTYE4_CHANNEL_TXONESZEROS_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXONESZEROS_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXONESZEROS_VAL}};
    else
      assign GTYE4_CHANNEL_TXONESZEROS_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXONESZEROS}};

    if (GTYE4_CHANNEL_TXOUTCLKSEL_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXOUTCLKSEL_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXOUTCLKSEL_VAL}};
    else
      assign GTYE4_CHANNEL_TXOUTCLKSEL_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXOUTCLKSEL}};

    if (GTYE4_CHANNEL_TXPCSRESET_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXPCSRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPCSRESET_VAL}};
    else
      assign GTYE4_CHANNEL_TXPCSRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPCSRESET}};

    if (GTYE4_CHANNEL_TXPD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXPD_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPD_VAL}};
    else
      assign GTYE4_CHANNEL_TXPD_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPD}};

    if (GTYE4_CHANNEL_TXPDELECIDLEMODE_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXPDELECIDLEMODE_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPDELECIDLEMODE_VAL}};
    else
      assign GTYE4_CHANNEL_TXPDELECIDLEMODE_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPDELECIDLEMODE}};

    if (GTYE4_CHANNEL_TXPHALIGN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXPHALIGN_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPHALIGN_VAL}};
    else
      assign GTYE4_CHANNEL_TXPHALIGN_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPHALIGN}};

    if (GTYE4_CHANNEL_TXPHALIGNEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXPHALIGNEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPHALIGNEN_VAL}};
    else
      assign GTYE4_CHANNEL_TXPHALIGNEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPHALIGNEN}};

    if (GTYE4_CHANNEL_TXPHDLYPD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXPHDLYPD_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPHDLYPD_VAL}};
    else
      assign GTYE4_CHANNEL_TXPHDLYPD_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPHDLYPD}};

    if (GTYE4_CHANNEL_TXPHDLYRESET_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXPHDLYRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPHDLYRESET_VAL}};
    else
      assign GTYE4_CHANNEL_TXPHDLYRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPHDLYRESET}};

    if (GTYE4_CHANNEL_TXPHDLYTSTCLK_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXPHDLYTSTCLK_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPHDLYTSTCLK_VAL}};
    else
      assign GTYE4_CHANNEL_TXPHDLYTSTCLK_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPHDLYTSTCLK}};

    if (GTYE4_CHANNEL_TXPHINIT_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXPHINIT_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPHINIT_VAL}};
    else
      assign GTYE4_CHANNEL_TXPHINIT_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPHINIT}};

    if (GTYE4_CHANNEL_TXPHOVRDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXPHOVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPHOVRDEN_VAL}};
    else
      assign GTYE4_CHANNEL_TXPHOVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPHOVRDEN}};

    if (GTYE4_CHANNEL_TXPIPPMEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXPIPPMEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPIPPMEN_VAL}};
    else
      assign GTYE4_CHANNEL_TXPIPPMEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPIPPMEN}};

    if (GTYE4_CHANNEL_TXPIPPMOVRDEN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXPIPPMOVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPIPPMOVRDEN_VAL}};
    else
      assign GTYE4_CHANNEL_TXPIPPMOVRDEN_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPIPPMOVRDEN}};

    if (GTYE4_CHANNEL_TXPIPPMPD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXPIPPMPD_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPIPPMPD_VAL}};
    else
      assign GTYE4_CHANNEL_TXPIPPMPD_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPIPPMPD}};

    if (GTYE4_CHANNEL_TXPIPPMSEL_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXPIPPMSEL_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPIPPMSEL_VAL}};
    else
      assign GTYE4_CHANNEL_TXPIPPMSEL_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPIPPMSEL}};

    if (GTYE4_CHANNEL_TXPIPPMSTEPSIZE_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXPIPPMSTEPSIZE_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPIPPMSTEPSIZE_VAL}};
    else
      assign GTYE4_CHANNEL_TXPIPPMSTEPSIZE_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPIPPMSTEPSIZE}};

    if (GTYE4_CHANNEL_TXPISOPD_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXPISOPD_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPISOPD_VAL}};
    else
      assign GTYE4_CHANNEL_TXPISOPD_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPISOPD}};

    if (GTYE4_CHANNEL_TXPLLCLKSEL_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXPLLCLKSEL_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPLLCLKSEL_VAL}};
    else
      assign GTYE4_CHANNEL_TXPLLCLKSEL_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPLLCLKSEL}};

    if (GTYE4_CHANNEL_TXPMARESET_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXPMARESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPMARESET_VAL}};
    else
      assign GTYE4_CHANNEL_TXPMARESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPMARESET}};

    if (GTYE4_CHANNEL_TXPOLARITY_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXPOLARITY_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPOLARITY_VAL}};
    else
      assign GTYE4_CHANNEL_TXPOLARITY_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPOLARITY}};

    if (GTYE4_CHANNEL_TXPOSTCURSOR_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXPOSTCURSOR_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPOSTCURSOR_VAL}};
    else
      assign GTYE4_CHANNEL_TXPOSTCURSOR_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPOSTCURSOR}};

    if (GTYE4_CHANNEL_TXPRBSFORCEERR_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXPRBSFORCEERR_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPRBSFORCEERR_VAL}};
    else
      assign GTYE4_CHANNEL_TXPRBSFORCEERR_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPRBSFORCEERR}};

    if (GTYE4_CHANNEL_TXPRBSSEL_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXPRBSSEL_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPRBSSEL_VAL}};
    else
      assign GTYE4_CHANNEL_TXPRBSSEL_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPRBSSEL}};

    if (GTYE4_CHANNEL_TXPRECURSOR_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXPRECURSOR_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPRECURSOR_VAL}};
    else
      assign GTYE4_CHANNEL_TXPRECURSOR_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPRECURSOR}};

    if (GTYE4_CHANNEL_TXPROGDIVRESET_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXPROGDIVRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPROGDIVRESET_VAL}};
    else
      assign GTYE4_CHANNEL_TXPROGDIVRESET_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXPROGDIVRESET}};

    if (GTYE4_CHANNEL_TXRATE_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXRATE_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXRATE_VAL}};
    else
      assign GTYE4_CHANNEL_TXRATE_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXRATE}};

    if (GTYE4_CHANNEL_TXRATEMODE_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXRATEMODE_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXRATEMODE_VAL}};
    else
      assign GTYE4_CHANNEL_TXRATEMODE_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXRATEMODE}};

    if (GTYE4_CHANNEL_TXSEQUENCE_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXSEQUENCE_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXSEQUENCE_VAL}};
    else
      assign GTYE4_CHANNEL_TXSEQUENCE_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXSEQUENCE}};

    if (GTYE4_CHANNEL_TXSWING_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXSWING_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXSWING_VAL}};
    else
      assign GTYE4_CHANNEL_TXSWING_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXSWING}};

    if (GTYE4_CHANNEL_TXSYNCALLIN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXSYNCALLIN_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXSYNCALLIN_VAL}};
    else
      assign GTYE4_CHANNEL_TXSYNCALLIN_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXSYNCALLIN}};

    if (GTYE4_CHANNEL_TXSYNCIN_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXSYNCIN_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXSYNCIN_VAL}};
    else
      assign GTYE4_CHANNEL_TXSYNCIN_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXSYNCIN}};

    if (GTYE4_CHANNEL_TXSYNCMODE_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXSYNCMODE_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXSYNCMODE_VAL}};
    else
      assign GTYE4_CHANNEL_TXSYNCMODE_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXSYNCMODE}};

    if (GTYE4_CHANNEL_TXSYSCLKSEL_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXSYSCLKSEL_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXSYSCLKSEL_VAL}};
    else
      assign GTYE4_CHANNEL_TXSYSCLKSEL_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXSYSCLKSEL}};

    if (GTYE4_CHANNEL_TXUSERRDY_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXUSERRDY_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXUSERRDY_VAL}};
    else
      assign GTYE4_CHANNEL_TXUSERRDY_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXUSERRDY}};

    if (GTYE4_CHANNEL_TXUSRCLK_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXUSRCLK_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXUSRCLK_VAL}};
    else
      assign GTYE4_CHANNEL_TXUSRCLK_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXUSRCLK}};

    if (GTYE4_CHANNEL_TXUSRCLK2_TIE_EN == 1'b1)
      assign GTYE4_CHANNEL_TXUSRCLK2_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXUSRCLK2_VAL}};
    else
      assign GTYE4_CHANNEL_TXUSRCLK2_int = {NUM_CHANNELS{GTYE4_CHANNEL_TXUSRCLK2}};

    // generate the appropriate number of GTYE4_CHANNEL primitive instances, mapping parameters and ports
    genvar ch;
    for (ch = 0; ch < NUM_CHANNELS; ch = ch + 1) begin : gen_gtye4_channel_inst

      GTYE4_CHANNEL #(
        .ACJTAG_DEBUG_MODE            (GTYE4_CHANNEL_ACJTAG_DEBUG_MODE           ),
        .ACJTAG_MODE                  (GTYE4_CHANNEL_ACJTAG_MODE                 ),
        .ACJTAG_RESET                 (GTYE4_CHANNEL_ACJTAG_RESET                ),
        .ADAPT_CFG0                   (GTYE4_CHANNEL_ADAPT_CFG0                  ),
        .ADAPT_CFG1                   (GTYE4_CHANNEL_ADAPT_CFG1                  ),
        .ADAPT_CFG2                   (GTYE4_CHANNEL_ADAPT_CFG2                  ),
        .ALIGN_COMMA_DOUBLE           (GTYE4_CHANNEL_ALIGN_COMMA_DOUBLE          ),
        .ALIGN_COMMA_ENABLE           (GTYE4_CHANNEL_ALIGN_COMMA_ENABLE          ),
        .ALIGN_COMMA_WORD             (GTYE4_CHANNEL_ALIGN_COMMA_WORD            ),
        .ALIGN_MCOMMA_DET             (GTYE4_CHANNEL_ALIGN_MCOMMA_DET            ),
        .ALIGN_MCOMMA_VALUE           (GTYE4_CHANNEL_ALIGN_MCOMMA_VALUE          ),
        .ALIGN_PCOMMA_DET             (GTYE4_CHANNEL_ALIGN_PCOMMA_DET            ),
        .ALIGN_PCOMMA_VALUE           (GTYE4_CHANNEL_ALIGN_PCOMMA_VALUE          ),
        .A_RXOSCALRESET               (GTYE4_CHANNEL_A_RXOSCALRESET              ),
        .A_RXPROGDIVRESET             (GTYE4_CHANNEL_A_RXPROGDIVRESET            ),
        .A_RXTERMINATION              (GTYE4_CHANNEL_A_RXTERMINATION             ),
        .A_TXDIFFCTRL                 (GTYE4_CHANNEL_A_TXDIFFCTRL                ),
        .A_TXPROGDIVRESET             (GTYE4_CHANNEL_A_TXPROGDIVRESET            ),
        .CBCC_DATA_SOURCE_SEL         (GTYE4_CHANNEL_CBCC_DATA_SOURCE_SEL        ),
        .CDR_SWAP_MODE_EN             (GTYE4_CHANNEL_CDR_SWAP_MODE_EN            ),
        .CFOK_PWRSVE_EN               (GTYE4_CHANNEL_CFOK_PWRSVE_EN              ),
        .CHAN_BOND_KEEP_ALIGN         (GTYE4_CHANNEL_CHAN_BOND_KEEP_ALIGN        ),
        .CHAN_BOND_MAX_SKEW           (GTYE4_CHANNEL_CHAN_BOND_MAX_SKEW          ),
        .CHAN_BOND_SEQ_1_1            (GTYE4_CHANNEL_CHAN_BOND_SEQ_1_1           ),
        .CHAN_BOND_SEQ_1_2            (GTYE4_CHANNEL_CHAN_BOND_SEQ_1_2           ),
        .CHAN_BOND_SEQ_1_3            (GTYE4_CHANNEL_CHAN_BOND_SEQ_1_3           ),
        .CHAN_BOND_SEQ_1_4            (GTYE4_CHANNEL_CHAN_BOND_SEQ_1_4           ),
        .CHAN_BOND_SEQ_1_ENABLE       (GTYE4_CHANNEL_CHAN_BOND_SEQ_1_ENABLE      ),
        .CHAN_BOND_SEQ_2_1            (GTYE4_CHANNEL_CHAN_BOND_SEQ_2_1           ),
        .CHAN_BOND_SEQ_2_2            (GTYE4_CHANNEL_CHAN_BOND_SEQ_2_2           ),
        .CHAN_BOND_SEQ_2_3            (GTYE4_CHANNEL_CHAN_BOND_SEQ_2_3           ),
        .CHAN_BOND_SEQ_2_4            (GTYE4_CHANNEL_CHAN_BOND_SEQ_2_4           ),
        .CHAN_BOND_SEQ_2_ENABLE       (GTYE4_CHANNEL_CHAN_BOND_SEQ_2_ENABLE      ),
        .CHAN_BOND_SEQ_2_USE          (GTYE4_CHANNEL_CHAN_BOND_SEQ_2_USE         ),
        .CHAN_BOND_SEQ_LEN            (GTYE4_CHANNEL_CHAN_BOND_SEQ_LEN           ),
        .CH_HSPMUX                    (GTYE4_CHANNEL_CH_HSPMUX                   ),
        .CKCAL1_CFG_0                 (GTYE4_CHANNEL_CKCAL1_CFG_0                ),
        .CKCAL1_CFG_1                 (GTYE4_CHANNEL_CKCAL1_CFG_1                ),
        .CKCAL1_CFG_2                 (GTYE4_CHANNEL_CKCAL1_CFG_2                ),
        .CKCAL1_CFG_3                 (GTYE4_CHANNEL_CKCAL1_CFG_3                ),
        .CKCAL2_CFG_0                 (GTYE4_CHANNEL_CKCAL2_CFG_0                ),
        .CKCAL2_CFG_1                 (GTYE4_CHANNEL_CKCAL2_CFG_1                ),
        .CKCAL2_CFG_2                 (GTYE4_CHANNEL_CKCAL2_CFG_2                ),
        .CKCAL2_CFG_3                 (GTYE4_CHANNEL_CKCAL2_CFG_3                ),
        .CKCAL2_CFG_4                 (GTYE4_CHANNEL_CKCAL2_CFG_4                ),
        .CLK_CORRECT_USE              (GTYE4_CHANNEL_CLK_CORRECT_USE             ),
        .CLK_COR_KEEP_IDLE            (GTYE4_CHANNEL_CLK_COR_KEEP_IDLE           ),
        .CLK_COR_MAX_LAT              (GTYE4_CHANNEL_CLK_COR_MAX_LAT             ),
        .CLK_COR_MIN_LAT              (GTYE4_CHANNEL_CLK_COR_MIN_LAT             ),
        .CLK_COR_PRECEDENCE           (GTYE4_CHANNEL_CLK_COR_PRECEDENCE          ),
        .CLK_COR_REPEAT_WAIT          (GTYE4_CHANNEL_CLK_COR_REPEAT_WAIT         ),
        .CLK_COR_SEQ_1_1              (GTYE4_CHANNEL_CLK_COR_SEQ_1_1             ),
        .CLK_COR_SEQ_1_2              (GTYE4_CHANNEL_CLK_COR_SEQ_1_2             ),
        .CLK_COR_SEQ_1_3              (GTYE4_CHANNEL_CLK_COR_SEQ_1_3             ),
        .CLK_COR_SEQ_1_4              (GTYE4_CHANNEL_CLK_COR_SEQ_1_4             ),
        .CLK_COR_SEQ_1_ENABLE         (GTYE4_CHANNEL_CLK_COR_SEQ_1_ENABLE        ),
        .CLK_COR_SEQ_2_1              (GTYE4_CHANNEL_CLK_COR_SEQ_2_1             ),
        .CLK_COR_SEQ_2_2              (GTYE4_CHANNEL_CLK_COR_SEQ_2_2             ),
        .CLK_COR_SEQ_2_3              (GTYE4_CHANNEL_CLK_COR_SEQ_2_3             ),
        .CLK_COR_SEQ_2_4              (GTYE4_CHANNEL_CLK_COR_SEQ_2_4             ),
        .CLK_COR_SEQ_2_ENABLE         (GTYE4_CHANNEL_CLK_COR_SEQ_2_ENABLE        ),
        .CLK_COR_SEQ_2_USE            (GTYE4_CHANNEL_CLK_COR_SEQ_2_USE           ),
        .CLK_COR_SEQ_LEN              (GTYE4_CHANNEL_CLK_COR_SEQ_LEN             ),
        .CPLL_CFG0                    (GTYE4_CHANNEL_CPLL_CFG0                   ),
        .CPLL_CFG1                    (GTYE4_CHANNEL_CPLL_CFG1                   ),
        .CPLL_CFG2                    (GTYE4_CHANNEL_CPLL_CFG2                   ),
        .CPLL_CFG3                    (GTYE4_CHANNEL_CPLL_CFG3                   ),
        .CPLL_FBDIV                   (GTYE4_CHANNEL_CPLL_FBDIV                  ),
        .CPLL_FBDIV_45                (GTYE4_CHANNEL_CPLL_FBDIV_45               ),
        .CPLL_INIT_CFG0               (GTYE4_CHANNEL_CPLL_INIT_CFG0              ),
        .CPLL_LOCK_CFG                (GTYE4_CHANNEL_CPLL_LOCK_CFG               ),
        .CPLL_REFCLK_DIV              (GTYE4_CHANNEL_CPLL_REFCLK_DIV             ),
        .CTLE3_OCAP_EXT_CTRL          (GTYE4_CHANNEL_CTLE3_OCAP_EXT_CTRL         ),
        .CTLE3_OCAP_EXT_EN            (GTYE4_CHANNEL_CTLE3_OCAP_EXT_EN           ),
        .DDI_CTRL                     (GTYE4_CHANNEL_DDI_CTRL                    ),
        .DDI_REALIGN_WAIT             (GTYE4_CHANNEL_DDI_REALIGN_WAIT            ),
        .DEC_MCOMMA_DETECT            (GTYE4_CHANNEL_DEC_MCOMMA_DETECT           ),
        .DEC_PCOMMA_DETECT            (GTYE4_CHANNEL_DEC_PCOMMA_DETECT           ),
        .DEC_VALID_COMMA_ONLY         (GTYE4_CHANNEL_DEC_VALID_COMMA_ONLY        ),
        .DELAY_ELEC                   (GTYE4_CHANNEL_DELAY_ELEC                  ),
        .DMONITOR_CFG0                (GTYE4_CHANNEL_DMONITOR_CFG0               ),
        .DMONITOR_CFG1                (GTYE4_CHANNEL_DMONITOR_CFG1               ),
        .ES_CLK_PHASE_SEL             (GTYE4_CHANNEL_ES_CLK_PHASE_SEL            ),
        .ES_CONTROL                   (GTYE4_CHANNEL_ES_CONTROL                  ),
        .ES_ERRDET_EN                 (GTYE4_CHANNEL_ES_ERRDET_EN                ),
        .ES_EYE_SCAN_EN               (GTYE4_CHANNEL_ES_EYE_SCAN_EN              ),
        .ES_HORZ_OFFSET               (GTYE4_CHANNEL_ES_HORZ_OFFSET              ),
        .ES_PRESCALE                  (GTYE4_CHANNEL_ES_PRESCALE                 ),
        .ES_QUALIFIER0                (GTYE4_CHANNEL_ES_QUALIFIER0               ),
        .ES_QUALIFIER1                (GTYE4_CHANNEL_ES_QUALIFIER1               ),
        .ES_QUALIFIER2                (GTYE4_CHANNEL_ES_QUALIFIER2               ),
        .ES_QUALIFIER3                (GTYE4_CHANNEL_ES_QUALIFIER3               ),
        .ES_QUALIFIER4                (GTYE4_CHANNEL_ES_QUALIFIER4               ),
        .ES_QUALIFIER5                (GTYE4_CHANNEL_ES_QUALIFIER5               ),
        .ES_QUALIFIER6                (GTYE4_CHANNEL_ES_QUALIFIER6               ),
        .ES_QUALIFIER7                (GTYE4_CHANNEL_ES_QUALIFIER7               ),
        .ES_QUALIFIER8                (GTYE4_CHANNEL_ES_QUALIFIER8               ),
        .ES_QUALIFIER9                (GTYE4_CHANNEL_ES_QUALIFIER9               ),
        .ES_QUAL_MASK0                (GTYE4_CHANNEL_ES_QUAL_MASK0               ),
        .ES_QUAL_MASK1                (GTYE4_CHANNEL_ES_QUAL_MASK1               ),
        .ES_QUAL_MASK2                (GTYE4_CHANNEL_ES_QUAL_MASK2               ),
        .ES_QUAL_MASK3                (GTYE4_CHANNEL_ES_QUAL_MASK3               ),
        .ES_QUAL_MASK4                (GTYE4_CHANNEL_ES_QUAL_MASK4               ),
        .ES_QUAL_MASK5                (GTYE4_CHANNEL_ES_QUAL_MASK5               ),
        .ES_QUAL_MASK6                (GTYE4_CHANNEL_ES_QUAL_MASK6               ),
        .ES_QUAL_MASK7                (GTYE4_CHANNEL_ES_QUAL_MASK7               ),
        .ES_QUAL_MASK8                (GTYE4_CHANNEL_ES_QUAL_MASK8               ),
        .ES_QUAL_MASK9                (GTYE4_CHANNEL_ES_QUAL_MASK9               ),
        .ES_SDATA_MASK0               (GTYE4_CHANNEL_ES_SDATA_MASK0              ),
        .ES_SDATA_MASK1               (GTYE4_CHANNEL_ES_SDATA_MASK1              ),
        .ES_SDATA_MASK2               (GTYE4_CHANNEL_ES_SDATA_MASK2              ),
        .ES_SDATA_MASK3               (GTYE4_CHANNEL_ES_SDATA_MASK3              ),
        .ES_SDATA_MASK4               (GTYE4_CHANNEL_ES_SDATA_MASK4              ),
        .ES_SDATA_MASK5               (GTYE4_CHANNEL_ES_SDATA_MASK5              ),
        .ES_SDATA_MASK6               (GTYE4_CHANNEL_ES_SDATA_MASK6              ),
        .ES_SDATA_MASK7               (GTYE4_CHANNEL_ES_SDATA_MASK7              ),
        .ES_SDATA_MASK8               (GTYE4_CHANNEL_ES_SDATA_MASK8              ),
        .ES_SDATA_MASK9               (GTYE4_CHANNEL_ES_SDATA_MASK9              ),
        .EYESCAN_VP_RANGE             (GTYE4_CHANNEL_EYESCAN_VP_RANGE            ),
        .EYE_SCAN_SWAP_EN             (GTYE4_CHANNEL_EYE_SCAN_SWAP_EN            ),
        .FTS_DESKEW_SEQ_ENABLE        (GTYE4_CHANNEL_FTS_DESKEW_SEQ_ENABLE       ),
        .FTS_LANE_DESKEW_CFG          (GTYE4_CHANNEL_FTS_LANE_DESKEW_CFG         ),
        .FTS_LANE_DESKEW_EN           (GTYE4_CHANNEL_FTS_LANE_DESKEW_EN          ),
        .GEARBOX_MODE                 (GTYE4_CHANNEL_GEARBOX_MODE                ),
        .ISCAN_CK_PH_SEL2             (GTYE4_CHANNEL_ISCAN_CK_PH_SEL2            ),
        .LOCAL_MASTER                 (GTYE4_CHANNEL_LOCAL_MASTER                ),
        .LPBK_BIAS_CTRL               (GTYE4_CHANNEL_LPBK_BIAS_CTRL              ),
        .LPBK_EN_RCAL_B               (GTYE4_CHANNEL_LPBK_EN_RCAL_B              ),
        .LPBK_EXT_RCAL                (GTYE4_CHANNEL_LPBK_EXT_RCAL               ),
        .LPBK_IND_CTRL0               (GTYE4_CHANNEL_LPBK_IND_CTRL0              ),
        .LPBK_IND_CTRL1               (GTYE4_CHANNEL_LPBK_IND_CTRL1              ),
        .LPBK_IND_CTRL2               (GTYE4_CHANNEL_LPBK_IND_CTRL2              ),
        .LPBK_RG_CTRL                 (GTYE4_CHANNEL_LPBK_RG_CTRL                ),
        .OOBDIVCTL                    (GTYE4_CHANNEL_OOBDIVCTL                   ),
        .OOB_PWRUP                    (GTYE4_CHANNEL_OOB_PWRUP                   ),
        .PCI3_AUTO_REALIGN            (GTYE4_CHANNEL_PCI3_AUTO_REALIGN           ),
        .PCI3_PIPE_RX_ELECIDLE        (GTYE4_CHANNEL_PCI3_PIPE_RX_ELECIDLE       ),
        .PCI3_RX_ASYNC_EBUF_BYPASS    (GTYE4_CHANNEL_PCI3_RX_ASYNC_EBUF_BYPASS   ),
        .PCI3_RX_ELECIDLE_EI2_ENABLE  (GTYE4_CHANNEL_PCI3_RX_ELECIDLE_EI2_ENABLE ),
        .PCI3_RX_ELECIDLE_H2L_COUNT   (GTYE4_CHANNEL_PCI3_RX_ELECIDLE_H2L_COUNT  ),
        .PCI3_RX_ELECIDLE_H2L_DISABLE (GTYE4_CHANNEL_PCI3_RX_ELECIDLE_H2L_DISABLE),
        .PCI3_RX_ELECIDLE_HI_COUNT    (GTYE4_CHANNEL_PCI3_RX_ELECIDLE_HI_COUNT   ),
        .PCI3_RX_ELECIDLE_LP4_DISABLE (GTYE4_CHANNEL_PCI3_RX_ELECIDLE_LP4_DISABLE),
        .PCI3_RX_FIFO_DISABLE         (GTYE4_CHANNEL_PCI3_RX_FIFO_DISABLE        ),
        .PCIE3_CLK_COR_EMPTY_THRSH    (GTYE4_CHANNEL_PCIE3_CLK_COR_EMPTY_THRSH   ),
        .PCIE3_CLK_COR_FULL_THRSH     (GTYE4_CHANNEL_PCIE3_CLK_COR_FULL_THRSH    ),
        .PCIE3_CLK_COR_MAX_LAT        (GTYE4_CHANNEL_PCIE3_CLK_COR_MAX_LAT       ),
        .PCIE3_CLK_COR_MIN_LAT        (GTYE4_CHANNEL_PCIE3_CLK_COR_MIN_LAT       ),
        .PCIE3_CLK_COR_THRSH_TIMER    (GTYE4_CHANNEL_PCIE3_CLK_COR_THRSH_TIMER   ),
        .PCIE_64B_DYN_CLKSW_DIS       (GTYE4_CHANNEL_PCIE_64B_DYN_CLKSW_DIS      ),
        .PCIE_BUFG_DIV_CTRL           (GTYE4_CHANNEL_PCIE_BUFG_DIV_CTRL          ),
        .PCIE_GEN4_64BIT_INT_EN       (GTYE4_CHANNEL_PCIE_GEN4_64BIT_INT_EN      ),
        .PCIE_PLL_SEL_MODE_GEN12      (GTYE4_CHANNEL_PCIE_PLL_SEL_MODE_GEN12     ),
        .PCIE_PLL_SEL_MODE_GEN3       (GTYE4_CHANNEL_PCIE_PLL_SEL_MODE_GEN3      ),
        .PCIE_PLL_SEL_MODE_GEN4       (GTYE4_CHANNEL_PCIE_PLL_SEL_MODE_GEN4      ),
        .PCIE_RXPCS_CFG_GEN3          (GTYE4_CHANNEL_PCIE_RXPCS_CFG_GEN3         ),
        .PCIE_RXPMA_CFG               (GTYE4_CHANNEL_PCIE_RXPMA_CFG              ),
        .PCIE_TXPCS_CFG_GEN3          (GTYE4_CHANNEL_PCIE_TXPCS_CFG_GEN3         ),
        .PCIE_TXPMA_CFG               (GTYE4_CHANNEL_PCIE_TXPMA_CFG              ),
        .PCS_PCIE_EN                  (GTYE4_CHANNEL_PCS_PCIE_EN                 ),
        .PCS_RSVD0                    (GTYE4_CHANNEL_PCS_RSVD0                   ),
        .PD_TRANS_TIME_FROM_P2        (GTYE4_CHANNEL_PD_TRANS_TIME_FROM_P2       ),
        .PD_TRANS_TIME_NONE_P2        (GTYE4_CHANNEL_PD_TRANS_TIME_NONE_P2       ),
        .PD_TRANS_TIME_TO_P2          (GTYE4_CHANNEL_PD_TRANS_TIME_TO_P2         ),
        .PREIQ_FREQ_BST               (GTYE4_CHANNEL_PREIQ_FREQ_BST              ),
        .RATE_SW_USE_DRP              (GTYE4_CHANNEL_RATE_SW_USE_DRP             ),
        .RCLK_SIPO_DLY_ENB            (GTYE4_CHANNEL_RCLK_SIPO_DLY_ENB           ),
        .RCLK_SIPO_INV_EN             (GTYE4_CHANNEL_RCLK_SIPO_INV_EN            ),
        .RTX_BUF_CML_CTRL             (GTYE4_CHANNEL_RTX_BUF_CML_CTRL            ),
        .RTX_BUF_TERM_CTRL            (GTYE4_CHANNEL_RTX_BUF_TERM_CTRL           ),
        .RXBUFRESET_TIME              (GTYE4_CHANNEL_RXBUFRESET_TIME             ),
        .RXBUF_ADDR_MODE              (GTYE4_CHANNEL_RXBUF_ADDR_MODE             ),
        .RXBUF_EIDLE_HI_CNT           (GTYE4_CHANNEL_RXBUF_EIDLE_HI_CNT          ),
        .RXBUF_EIDLE_LO_CNT           (GTYE4_CHANNEL_RXBUF_EIDLE_LO_CNT          ),
        .RXBUF_EN                     (GTYE4_CHANNEL_RXBUF_EN                    ),
        .RXBUF_RESET_ON_CB_CHANGE     (GTYE4_CHANNEL_RXBUF_RESET_ON_CB_CHANGE    ),
        .RXBUF_RESET_ON_COMMAALIGN    (GTYE4_CHANNEL_RXBUF_RESET_ON_COMMAALIGN   ),
        .RXBUF_RESET_ON_EIDLE         (GTYE4_CHANNEL_RXBUF_RESET_ON_EIDLE        ),
        .RXBUF_RESET_ON_RATE_CHANGE   (GTYE4_CHANNEL_RXBUF_RESET_ON_RATE_CHANGE  ),
        .RXBUF_THRESH_OVFLW           (GTYE4_CHANNEL_RXBUF_THRESH_OVFLW          ),
        .RXBUF_THRESH_OVRD            (GTYE4_CHANNEL_RXBUF_THRESH_OVRD           ),
        .RXBUF_THRESH_UNDFLW          (GTYE4_CHANNEL_RXBUF_THRESH_UNDFLW         ),
        .RXCDRFREQRESET_TIME          (GTYE4_CHANNEL_RXCDRFREQRESET_TIME         ),
        .RXCDRPHRESET_TIME            (GTYE4_CHANNEL_RXCDRPHRESET_TIME           ),
        .RXCDR_CFG0                   (GTYE4_CHANNEL_RXCDR_CFG0                  ),
        .RXCDR_CFG0_GEN3              (GTYE4_CHANNEL_RXCDR_CFG0_GEN3             ),
        .RXCDR_CFG1                   (GTYE4_CHANNEL_RXCDR_CFG1                  ),
        .RXCDR_CFG1_GEN3              (GTYE4_CHANNEL_RXCDR_CFG1_GEN3             ),
        .RXCDR_CFG2                   (GTYE4_CHANNEL_RXCDR_CFG2                  ),
        .RXCDR_CFG2_GEN2              (GTYE4_CHANNEL_RXCDR_CFG2_GEN2             ),
        .RXCDR_CFG2_GEN3              (GTYE4_CHANNEL_RXCDR_CFG2_GEN3             ),
        .RXCDR_CFG2_GEN4              (GTYE4_CHANNEL_RXCDR_CFG2_GEN4             ),
        .RXCDR_CFG3                   (GTYE4_CHANNEL_RXCDR_CFG3                  ),
        .RXCDR_CFG3_GEN2              (GTYE4_CHANNEL_RXCDR_CFG3_GEN2             ),
        .RXCDR_CFG3_GEN3              (GTYE4_CHANNEL_RXCDR_CFG3_GEN3             ),
        .RXCDR_CFG3_GEN4              (GTYE4_CHANNEL_RXCDR_CFG3_GEN4             ),
        .RXCDR_CFG4                   (GTYE4_CHANNEL_RXCDR_CFG4                  ),
        .RXCDR_CFG4_GEN3              (GTYE4_CHANNEL_RXCDR_CFG4_GEN3             ),
        .RXCDR_CFG5                   (GTYE4_CHANNEL_RXCDR_CFG5                  ),
        .RXCDR_CFG5_GEN3              (GTYE4_CHANNEL_RXCDR_CFG5_GEN3             ),
        .RXCDR_FR_RESET_ON_EIDLE      (GTYE4_CHANNEL_RXCDR_FR_RESET_ON_EIDLE     ),
        .RXCDR_HOLD_DURING_EIDLE      (GTYE4_CHANNEL_RXCDR_HOLD_DURING_EIDLE     ),
        .RXCDR_LOCK_CFG0              (GTYE4_CHANNEL_RXCDR_LOCK_CFG0             ),
        .RXCDR_LOCK_CFG1              (GTYE4_CHANNEL_RXCDR_LOCK_CFG1             ),
        .RXCDR_LOCK_CFG2              (GTYE4_CHANNEL_RXCDR_LOCK_CFG2             ),
        .RXCDR_LOCK_CFG3              (GTYE4_CHANNEL_RXCDR_LOCK_CFG3             ),
        .RXCDR_LOCK_CFG4              (GTYE4_CHANNEL_RXCDR_LOCK_CFG4             ),
        .RXCDR_PH_RESET_ON_EIDLE      (GTYE4_CHANNEL_RXCDR_PH_RESET_ON_EIDLE     ),
        .RXCFOK_CFG0                  (GTYE4_CHANNEL_RXCFOK_CFG0                 ),
        .RXCFOK_CFG1                  (GTYE4_CHANNEL_RXCFOK_CFG1                 ),
        .RXCFOK_CFG2                  (GTYE4_CHANNEL_RXCFOK_CFG2                 ),
        .RXCKCAL1_IQ_LOOP_RST_CFG     (GTYE4_CHANNEL_RXCKCAL1_IQ_LOOP_RST_CFG    ),
        .RXCKCAL1_I_LOOP_RST_CFG      (GTYE4_CHANNEL_RXCKCAL1_I_LOOP_RST_CFG     ),
        .RXCKCAL1_Q_LOOP_RST_CFG      (GTYE4_CHANNEL_RXCKCAL1_Q_LOOP_RST_CFG     ),
        .RXCKCAL2_DX_LOOP_RST_CFG     (GTYE4_CHANNEL_RXCKCAL2_DX_LOOP_RST_CFG    ),
        .RXCKCAL2_D_LOOP_RST_CFG      (GTYE4_CHANNEL_RXCKCAL2_D_LOOP_RST_CFG     ),
        .RXCKCAL2_S_LOOP_RST_CFG      (GTYE4_CHANNEL_RXCKCAL2_S_LOOP_RST_CFG     ),
        .RXCKCAL2_X_LOOP_RST_CFG      (GTYE4_CHANNEL_RXCKCAL2_X_LOOP_RST_CFG     ),
        .RXDFELPMRESET_TIME           (GTYE4_CHANNEL_RXDFELPMRESET_TIME          ),
        .RXDFELPM_KL_CFG0             (GTYE4_CHANNEL_RXDFELPM_KL_CFG0            ),
        .RXDFELPM_KL_CFG1             (GTYE4_CHANNEL_RXDFELPM_KL_CFG1            ),
        .RXDFELPM_KL_CFG2             (GTYE4_CHANNEL_RXDFELPM_KL_CFG2            ),
        .RXDFE_CFG0                   (GTYE4_CHANNEL_RXDFE_CFG0                  ),
        .RXDFE_CFG1                   (GTYE4_CHANNEL_RXDFE_CFG1                  ),
        .RXDFE_GC_CFG0                (GTYE4_CHANNEL_RXDFE_GC_CFG0               ),
        .RXDFE_GC_CFG1                (GTYE4_CHANNEL_RXDFE_GC_CFG1               ),
        .RXDFE_GC_CFG2                (GTYE4_CHANNEL_RXDFE_GC_CFG2               ),
        .RXDFE_H2_CFG0                (GTYE4_CHANNEL_RXDFE_H2_CFG0               ),
        .RXDFE_H2_CFG1                (GTYE4_CHANNEL_RXDFE_H2_CFG1               ),
        .RXDFE_H3_CFG0                (GTYE4_CHANNEL_RXDFE_H3_CFG0               ),
        .RXDFE_H3_CFG1                (GTYE4_CHANNEL_RXDFE_H3_CFG1               ),
        .RXDFE_H4_CFG0                (GTYE4_CHANNEL_RXDFE_H4_CFG0               ),
        .RXDFE_H4_CFG1                (GTYE4_CHANNEL_RXDFE_H4_CFG1               ),
        .RXDFE_H5_CFG0                (GTYE4_CHANNEL_RXDFE_H5_CFG0               ),
        .RXDFE_H5_CFG1                (GTYE4_CHANNEL_RXDFE_H5_CFG1               ),
        .RXDFE_H6_CFG0                (GTYE4_CHANNEL_RXDFE_H6_CFG0               ),
        .RXDFE_H6_CFG1                (GTYE4_CHANNEL_RXDFE_H6_CFG1               ),
        .RXDFE_H7_CFG0                (GTYE4_CHANNEL_RXDFE_H7_CFG0               ),
        .RXDFE_H7_CFG1                (GTYE4_CHANNEL_RXDFE_H7_CFG1               ),
        .RXDFE_H8_CFG0                (GTYE4_CHANNEL_RXDFE_H8_CFG0               ),
        .RXDFE_H8_CFG1                (GTYE4_CHANNEL_RXDFE_H8_CFG1               ),
        .RXDFE_H9_CFG0                (GTYE4_CHANNEL_RXDFE_H9_CFG0               ),
        .RXDFE_H9_CFG1                (GTYE4_CHANNEL_RXDFE_H9_CFG1               ),
        .RXDFE_HA_CFG0                (GTYE4_CHANNEL_RXDFE_HA_CFG0               ),
        .RXDFE_HA_CFG1                (GTYE4_CHANNEL_RXDFE_HA_CFG1               ),
        .RXDFE_HB_CFG0                (GTYE4_CHANNEL_RXDFE_HB_CFG0               ),
        .RXDFE_HB_CFG1                (GTYE4_CHANNEL_RXDFE_HB_CFG1               ),
        .RXDFE_HC_CFG0                (GTYE4_CHANNEL_RXDFE_HC_CFG0               ),
        .RXDFE_HC_CFG1                (GTYE4_CHANNEL_RXDFE_HC_CFG1               ),
        .RXDFE_HD_CFG0                (GTYE4_CHANNEL_RXDFE_HD_CFG0               ),
        .RXDFE_HD_CFG1                (GTYE4_CHANNEL_RXDFE_HD_CFG1               ),
        .RXDFE_HE_CFG0                (GTYE4_CHANNEL_RXDFE_HE_CFG0               ),
        .RXDFE_HE_CFG1                (GTYE4_CHANNEL_RXDFE_HE_CFG1               ),
        .RXDFE_HF_CFG0                (GTYE4_CHANNEL_RXDFE_HF_CFG0               ),
        .RXDFE_HF_CFG1                (GTYE4_CHANNEL_RXDFE_HF_CFG1               ),
        .RXDFE_KH_CFG0                (GTYE4_CHANNEL_RXDFE_KH_CFG0               ),
        .RXDFE_KH_CFG1                (GTYE4_CHANNEL_RXDFE_KH_CFG1               ),
        .RXDFE_KH_CFG2                (GTYE4_CHANNEL_RXDFE_KH_CFG2               ),
        .RXDFE_KH_CFG3                (GTYE4_CHANNEL_RXDFE_KH_CFG3               ),
        .RXDFE_OS_CFG0                (GTYE4_CHANNEL_RXDFE_OS_CFG0               ),
        .RXDFE_OS_CFG1                (GTYE4_CHANNEL_RXDFE_OS_CFG1               ),
        .RXDFE_UT_CFG0                (GTYE4_CHANNEL_RXDFE_UT_CFG0               ),
        .RXDFE_UT_CFG1                (GTYE4_CHANNEL_RXDFE_UT_CFG1               ),
        .RXDFE_UT_CFG2                (GTYE4_CHANNEL_RXDFE_UT_CFG2               ),
        .RXDFE_VP_CFG0                (GTYE4_CHANNEL_RXDFE_VP_CFG0               ),
        .RXDFE_VP_CFG1                (GTYE4_CHANNEL_RXDFE_VP_CFG1               ),
        .RXDLY_CFG                    (GTYE4_CHANNEL_RXDLY_CFG                   ),
        .RXDLY_LCFG                   (GTYE4_CHANNEL_RXDLY_LCFG                  ),
        .RXELECIDLE_CFG               (GTYE4_CHANNEL_RXELECIDLE_CFG              ),
        .RXGBOX_FIFO_INIT_RD_ADDR     (GTYE4_CHANNEL_RXGBOX_FIFO_INIT_RD_ADDR    ),
        .RXGEARBOX_EN                 (GTYE4_CHANNEL_RXGEARBOX_EN                ),
        .RXISCANRESET_TIME            (GTYE4_CHANNEL_RXISCANRESET_TIME           ),
        .RXLPM_CFG                    (GTYE4_CHANNEL_RXLPM_CFG                   ),
        .RXLPM_GC_CFG                 (GTYE4_CHANNEL_RXLPM_GC_CFG                ),
        .RXLPM_KH_CFG0                (GTYE4_CHANNEL_RXLPM_KH_CFG0               ),
        .RXLPM_KH_CFG1                (GTYE4_CHANNEL_RXLPM_KH_CFG1               ),
        .RXLPM_OS_CFG0                (GTYE4_CHANNEL_RXLPM_OS_CFG0               ),
        .RXLPM_OS_CFG1                (GTYE4_CHANNEL_RXLPM_OS_CFG1               ),
        .RXOOB_CFG                    (GTYE4_CHANNEL_RXOOB_CFG                   ),
        .RXOOB_CLK_CFG                (GTYE4_CHANNEL_RXOOB_CLK_CFG               ),
        .RXOSCALRESET_TIME            (GTYE4_CHANNEL_RXOSCALRESET_TIME           ),
        .RXOUT_DIV                    (GTYE4_CHANNEL_RXOUT_DIV                   ),
        .RXPCSRESET_TIME              (GTYE4_CHANNEL_RXPCSRESET_TIME             ),
        .RXPHBEACON_CFG               (GTYE4_CHANNEL_RXPHBEACON_CFG              ),
        .RXPHDLY_CFG                  (GTYE4_CHANNEL_RXPHDLY_CFG                 ),
        .RXPHSAMP_CFG                 (GTYE4_CHANNEL_RXPHSAMP_CFG                ),
        .RXPHSLIP_CFG                 (GTYE4_CHANNEL_RXPHSLIP_CFG                ),
        .RXPH_MONITOR_SEL             (GTYE4_CHANNEL_RXPH_MONITOR_SEL            ),
        .RXPI_CFG0                    (GTYE4_CHANNEL_RXPI_CFG0                   ),
        .RXPI_CFG1                    (GTYE4_CHANNEL_RXPI_CFG1                   ),
        .RXPMACLK_SEL                 (GTYE4_CHANNEL_RXPMACLK_SEL                ),
        .RXPMARESET_TIME              (GTYE4_CHANNEL_RXPMARESET_TIME             ),
        .RXPRBS_ERR_LOOPBACK          (GTYE4_CHANNEL_RXPRBS_ERR_LOOPBACK         ),
        .RXPRBS_LINKACQ_CNT           (GTYE4_CHANNEL_RXPRBS_LINKACQ_CNT          ),
        .RXREFCLKDIV2_SEL             (GTYE4_CHANNEL_RXREFCLKDIV2_SEL            ),
        .RXSLIDE_AUTO_WAIT            (GTYE4_CHANNEL_RXSLIDE_AUTO_WAIT           ),
        .RXSLIDE_MODE                 (GTYE4_CHANNEL_RXSLIDE_MODE                ),
        .RXSYNC_MULTILANE             (GTYE4_CHANNEL_RXSYNC_MULTILANE            ),
        .RXSYNC_OVRD                  (GTYE4_CHANNEL_RXSYNC_OVRD                 ),
        .RXSYNC_SKIP_DA               (GTYE4_CHANNEL_RXSYNC_SKIP_DA              ),
        .RX_AFE_CM_EN                 (GTYE4_CHANNEL_RX_AFE_CM_EN                ),
        .RX_BIAS_CFG0                 (GTYE4_CHANNEL_RX_BIAS_CFG0                ),
        .RX_BUFFER_CFG                (GTYE4_CHANNEL_RX_BUFFER_CFG               ),
        .RX_CAPFF_SARC_ENB            (GTYE4_CHANNEL_RX_CAPFF_SARC_ENB           ),
        .RX_CLK25_DIV                 (GTYE4_CHANNEL_RX_CLK25_DIV                ),
        .RX_CLKMUX_EN                 (GTYE4_CHANNEL_RX_CLKMUX_EN                ),
        .RX_CLK_SLIP_OVRD             (GTYE4_CHANNEL_RX_CLK_SLIP_OVRD            ),
        .RX_CM_BUF_CFG                (GTYE4_CHANNEL_RX_CM_BUF_CFG               ),
        .RX_CM_BUF_PD                 (GTYE4_CHANNEL_RX_CM_BUF_PD                ),
        .RX_CM_SEL                    (GTYE4_CHANNEL_RX_CM_SEL                   ),
        .RX_CM_TRIM                   (GTYE4_CHANNEL_RX_CM_TRIM                  ),
        .RX_CTLE_PWR_SAVING           (GTYE4_CHANNEL_RX_CTLE_PWR_SAVING          ),
        .RX_CTLE_RES_CTRL             (GTYE4_CHANNEL_RX_CTLE_RES_CTRL            ),
        .RX_DATA_WIDTH                (GTYE4_CHANNEL_RX_DATA_WIDTH               ),
        .RX_DDI_SEL                   (GTYE4_CHANNEL_RX_DDI_SEL                  ),
        .RX_DEFER_RESET_BUF_EN        (GTYE4_CHANNEL_RX_DEFER_RESET_BUF_EN       ),
        .RX_DEGEN_CTRL                (GTYE4_CHANNEL_RX_DEGEN_CTRL               ),
        .RX_DFELPM_CFG0               (GTYE4_CHANNEL_RX_DFELPM_CFG0              ),
        .RX_DFELPM_CFG1               (GTYE4_CHANNEL_RX_DFELPM_CFG1              ),
        .RX_DFELPM_KLKH_AGC_STUP_EN   (GTYE4_CHANNEL_RX_DFELPM_KLKH_AGC_STUP_EN  ),
        .RX_DFE_AGC_CFG1              (GTYE4_CHANNEL_RX_DFE_AGC_CFG1             ),
        .RX_DFE_KL_LPM_KH_CFG0        (GTYE4_CHANNEL_RX_DFE_KL_LPM_KH_CFG0       ),
        .RX_DFE_KL_LPM_KH_CFG1        (GTYE4_CHANNEL_RX_DFE_KL_LPM_KH_CFG1       ),
        .RX_DFE_KL_LPM_KL_CFG0        (GTYE4_CHANNEL_RX_DFE_KL_LPM_KL_CFG0       ),
        .RX_DFE_KL_LPM_KL_CFG1        (GTYE4_CHANNEL_RX_DFE_KL_LPM_KL_CFG1       ),
        .RX_DFE_LPM_HOLD_DURING_EIDLE (GTYE4_CHANNEL_RX_DFE_LPM_HOLD_DURING_EIDLE),
        .RX_DISPERR_SEQ_MATCH         (GTYE4_CHANNEL_RX_DISPERR_SEQ_MATCH        ),
        .RX_DIVRESET_TIME             (GTYE4_CHANNEL_RX_DIVRESET_TIME            ),
        .RX_EN_CTLE_RCAL_B            (GTYE4_CHANNEL_RX_EN_CTLE_RCAL_B           ),
        .RX_EN_SUM_RCAL_B             (GTYE4_CHANNEL_RX_EN_SUM_RCAL_B            ),
        .RX_EYESCAN_VS_CODE           (GTYE4_CHANNEL_RX_EYESCAN_VS_CODE          ),
        .RX_EYESCAN_VS_NEG_DIR        (GTYE4_CHANNEL_RX_EYESCAN_VS_NEG_DIR       ),
        .RX_EYESCAN_VS_RANGE          (GTYE4_CHANNEL_RX_EYESCAN_VS_RANGE         ),
        .RX_EYESCAN_VS_UT_SIGN        (GTYE4_CHANNEL_RX_EYESCAN_VS_UT_SIGN       ),
        .RX_FABINT_USRCLK_FLOP        (GTYE4_CHANNEL_RX_FABINT_USRCLK_FLOP       ),
        .RX_I2V_FILTER_EN             (GTYE4_CHANNEL_RX_I2V_FILTER_EN            ),
        .RX_INT_DATAWIDTH             (GTYE4_CHANNEL_RX_INT_DATAWIDTH            ),
        .RX_PMA_POWER_SAVE            (GTYE4_CHANNEL_RX_PMA_POWER_SAVE           ),
        .RX_PMA_RSV0                  (GTYE4_CHANNEL_RX_PMA_RSV0                 ),
        .RX_PROGDIV_CFG               (GTYE4_CHANNEL_RX_PROGDIV_CFG              ),
        .RX_PROGDIV_RATE              (GTYE4_CHANNEL_RX_PROGDIV_RATE             ),
        .RX_RESLOAD_CTRL              (GTYE4_CHANNEL_RX_RESLOAD_CTRL             ),
        .RX_RESLOAD_OVRD              (GTYE4_CHANNEL_RX_RESLOAD_OVRD             ),
        .RX_SAMPLE_PERIOD             (GTYE4_CHANNEL_RX_SAMPLE_PERIOD            ),
        .RX_SIG_VALID_DLY             (GTYE4_CHANNEL_RX_SIG_VALID_DLY            ),
        .RX_SUM_DEGEN_AVTT_OVERITE    (GTYE4_CHANNEL_RX_SUM_DEGEN_AVTT_OVERITE   ),
        .RX_SUM_DFETAPREP_EN          (GTYE4_CHANNEL_RX_SUM_DFETAPREP_EN         ),
        .RX_SUM_IREF_TUNE             (GTYE4_CHANNEL_RX_SUM_IREF_TUNE            ),
        .RX_SUM_PWR_SAVING            (GTYE4_CHANNEL_RX_SUM_PWR_SAVING           ),
        .RX_SUM_RES_CTRL              (GTYE4_CHANNEL_RX_SUM_RES_CTRL             ),
        .RX_SUM_VCMTUNE               (GTYE4_CHANNEL_RX_SUM_VCMTUNE              ),
        .RX_SUM_VCM_BIAS_TUNE_EN      (GTYE4_CHANNEL_RX_SUM_VCM_BIAS_TUNE_EN     ),
        .RX_SUM_VCM_OVWR              (GTYE4_CHANNEL_RX_SUM_VCM_OVWR             ),
        .RX_SUM_VREF_TUNE             (GTYE4_CHANNEL_RX_SUM_VREF_TUNE            ),
        .RX_TUNE_AFE_OS               (GTYE4_CHANNEL_RX_TUNE_AFE_OS              ),
        .RX_VREG_CTRL                 (GTYE4_CHANNEL_RX_VREG_CTRL                ),
        .RX_VREG_PDB                  (GTYE4_CHANNEL_RX_VREG_PDB                 ),
        .RX_WIDEMODE_CDR              (GTYE4_CHANNEL_RX_WIDEMODE_CDR             ),
        .RX_WIDEMODE_CDR_GEN3         (GTYE4_CHANNEL_RX_WIDEMODE_CDR_GEN3        ),
        .RX_WIDEMODE_CDR_GEN4         (GTYE4_CHANNEL_RX_WIDEMODE_CDR_GEN4        ),
        .RX_XCLK_SEL                  (GTYE4_CHANNEL_RX_XCLK_SEL                 ),
        .RX_XMODE_SEL                 (GTYE4_CHANNEL_RX_XMODE_SEL                ),
        .SAMPLE_CLK_PHASE             (GTYE4_CHANNEL_SAMPLE_CLK_PHASE            ),
        .SAS_12G_MODE                 (GTYE4_CHANNEL_SAS_12G_MODE                ),
        .SATA_BURST_SEQ_LEN           (GTYE4_CHANNEL_SATA_BURST_SEQ_LEN          ),
        .SATA_BURST_VAL               (GTYE4_CHANNEL_SATA_BURST_VAL              ),
        .SATA_CPLL_CFG                (GTYE4_CHANNEL_SATA_CPLL_CFG               ),
        .SATA_EIDLE_VAL               (GTYE4_CHANNEL_SATA_EIDLE_VAL              ),
        .SHOW_REALIGN_COMMA           (GTYE4_CHANNEL_SHOW_REALIGN_COMMA          ),
        .SIM_MODE                     (GTYE4_CHANNEL_SIM_MODE                    ),
        .SIM_RECEIVER_DETECT_PASS     (GTYE4_CHANNEL_SIM_RECEIVER_DETECT_PASS    ),
        .SIM_RESET_SPEEDUP            (GTYE4_CHANNEL_SIM_RESET_SPEEDUP           ),
        .SIM_TX_EIDLE_DRIVE_LEVEL     (GTYE4_CHANNEL_SIM_TX_EIDLE_DRIVE_LEVEL    ),
        .SIM_DEVICE                   (GTYE4_CHANNEL_SIM_DEVICE                  ),
        .SRSTMODE                     (GTYE4_CHANNEL_SRSTMODE                    ),
        .TAPDLY_SET_TX                (GTYE4_CHANNEL_TAPDLY_SET_TX               ),
        .TERM_RCAL_CFG                (GTYE4_CHANNEL_TERM_RCAL_CFG               ),
        .TERM_RCAL_OVRD               (GTYE4_CHANNEL_TERM_RCAL_OVRD              ),
        .TRANS_TIME_RATE              (GTYE4_CHANNEL_TRANS_TIME_RATE             ),
        .TST_RSV0                     (GTYE4_CHANNEL_TST_RSV0                    ),
        .TST_RSV1                     (GTYE4_CHANNEL_TST_RSV1                    ),
        .TXBUF_EN                     (GTYE4_CHANNEL_TXBUF_EN                    ),
        .TXBUF_RESET_ON_RATE_CHANGE   (GTYE4_CHANNEL_TXBUF_RESET_ON_RATE_CHANGE  ),
        .TXDLY_CFG                    (GTYE4_CHANNEL_TXDLY_CFG                   ),
        .TXDLY_LCFG                   (GTYE4_CHANNEL_TXDLY_LCFG                  ),
        .TXDRV_FREQBAND               (GTYE4_CHANNEL_TXDRV_FREQBAND              ),
        .TXFE_CFG0                    (GTYE4_CHANNEL_TXFE_CFG0                   ),
        .TXFE_CFG1                    (GTYE4_CHANNEL_TXFE_CFG1                   ),
        .TXFE_CFG2                    (GTYE4_CHANNEL_TXFE_CFG2                   ),
        .TXFE_CFG3                    (GTYE4_CHANNEL_TXFE_CFG3                   ),
        .TXFIFO_ADDR_CFG              (GTYE4_CHANNEL_TXFIFO_ADDR_CFG             ),
        .TXGBOX_FIFO_INIT_RD_ADDR     (GTYE4_CHANNEL_TXGBOX_FIFO_INIT_RD_ADDR    ),
        .TXGEARBOX_EN                 (GTYE4_CHANNEL_TXGEARBOX_EN                ),
        .TXOUT_DIV                    (GTYE4_CHANNEL_TXOUT_DIV                   ),
        .TXPCSRESET_TIME              (GTYE4_CHANNEL_TXPCSRESET_TIME             ),
        .TXPHDLY_CFG0                 (GTYE4_CHANNEL_TXPHDLY_CFG0                ),
        .TXPHDLY_CFG1                 (GTYE4_CHANNEL_TXPHDLY_CFG1                ),
        .TXPH_CFG                     (GTYE4_CHANNEL_TXPH_CFG                    ),
        .TXPH_CFG2                    (GTYE4_CHANNEL_TXPH_CFG2                   ),
        .TXPH_MONITOR_SEL             (GTYE4_CHANNEL_TXPH_MONITOR_SEL            ),
        .TXPI_CFG0                    (GTYE4_CHANNEL_TXPI_CFG0                   ),
        .TXPI_CFG1                    (GTYE4_CHANNEL_TXPI_CFG1                   ),
        .TXPI_GRAY_SEL                (GTYE4_CHANNEL_TXPI_GRAY_SEL               ),
        .TXPI_INVSTROBE_SEL           (GTYE4_CHANNEL_TXPI_INVSTROBE_SEL          ),
        .TXPI_PPM                     (GTYE4_CHANNEL_TXPI_PPM                    ),
        .TXPI_PPM_CFG                 (GTYE4_CHANNEL_TXPI_PPM_CFG                ),
        .TXPI_SYNFREQ_PPM             (GTYE4_CHANNEL_TXPI_SYNFREQ_PPM            ),
        .TXPMARESET_TIME              (GTYE4_CHANNEL_TXPMARESET_TIME             ),
        .TXREFCLKDIV2_SEL             (GTYE4_CHANNEL_TXREFCLKDIV2_SEL            ),
        .TXSWBST_BST                  (GTYE4_CHANNEL_TXSWBST_BST                 ),
        .TXSWBST_EN                   (GTYE4_CHANNEL_TXSWBST_EN                  ),
        .TXSWBST_MAG                  (GTYE4_CHANNEL_TXSWBST_MAG                 ),
        .TXSYNC_MULTILANE             (GTYE4_CHANNEL_TXSYNC_MULTILANE            ),
        .TXSYNC_OVRD                  (GTYE4_CHANNEL_TXSYNC_OVRD                 ),
        .TXSYNC_SKIP_DA               (GTYE4_CHANNEL_TXSYNC_SKIP_DA              ),
        .TX_CLK25_DIV                 (GTYE4_CHANNEL_TX_CLK25_DIV                ),
        .TX_CLKMUX_EN                 (GTYE4_CHANNEL_TX_CLKMUX_EN                ),
        .TX_DATA_WIDTH                (GTYE4_CHANNEL_TX_DATA_WIDTH               ),
        .TX_DCC_LOOP_RST_CFG          (GTYE4_CHANNEL_TX_DCC_LOOP_RST_CFG         ),
        .TX_DEEMPH0                   (GTYE4_CHANNEL_TX_DEEMPH0                  ),
        .TX_DEEMPH1                   (GTYE4_CHANNEL_TX_DEEMPH1                  ),
        .TX_DEEMPH2                   (GTYE4_CHANNEL_TX_DEEMPH2                  ),
        .TX_DEEMPH3                   (GTYE4_CHANNEL_TX_DEEMPH3                  ),
        .TX_DIVRESET_TIME             (GTYE4_CHANNEL_TX_DIVRESET_TIME            ),
        .TX_DRIVE_MODE                (GTYE4_CHANNEL_TX_DRIVE_MODE               ),
        .TX_EIDLE_ASSERT_DELAY        (GTYE4_CHANNEL_TX_EIDLE_ASSERT_DELAY       ),
        .TX_EIDLE_DEASSERT_DELAY      (GTYE4_CHANNEL_TX_EIDLE_DEASSERT_DELAY     ),
        .TX_FABINT_USRCLK_FLOP        (GTYE4_CHANNEL_TX_FABINT_USRCLK_FLOP       ),
        .TX_FIFO_BYP_EN               (GTYE4_CHANNEL_TX_FIFO_BYP_EN              ),
        .TX_IDLE_DATA_ZERO            (GTYE4_CHANNEL_TX_IDLE_DATA_ZERO           ),
        .TX_INT_DATAWIDTH             (GTYE4_CHANNEL_TX_INT_DATAWIDTH            ),
        .TX_LOOPBACK_DRIVE_HIZ        (GTYE4_CHANNEL_TX_LOOPBACK_DRIVE_HIZ       ),
        .TX_MAINCURSOR_SEL            (GTYE4_CHANNEL_TX_MAINCURSOR_SEL           ),
        .TX_MARGIN_FULL_0             (GTYE4_CHANNEL_TX_MARGIN_FULL_0            ),
        .TX_MARGIN_FULL_1             (GTYE4_CHANNEL_TX_MARGIN_FULL_1            ),
        .TX_MARGIN_FULL_2             (GTYE4_CHANNEL_TX_MARGIN_FULL_2            ),
        .TX_MARGIN_FULL_3             (GTYE4_CHANNEL_TX_MARGIN_FULL_3            ),
        .TX_MARGIN_FULL_4             (GTYE4_CHANNEL_TX_MARGIN_FULL_4            ),
        .TX_MARGIN_LOW_0              (GTYE4_CHANNEL_TX_MARGIN_LOW_0             ),
        .TX_MARGIN_LOW_1              (GTYE4_CHANNEL_TX_MARGIN_LOW_1             ),
        .TX_MARGIN_LOW_2              (GTYE4_CHANNEL_TX_MARGIN_LOW_2             ),
        .TX_MARGIN_LOW_3              (GTYE4_CHANNEL_TX_MARGIN_LOW_3             ),
        .TX_MARGIN_LOW_4              (GTYE4_CHANNEL_TX_MARGIN_LOW_4             ),
        .TX_PHICAL_CFG0               (GTYE4_CHANNEL_TX_PHICAL_CFG0              ),
        .TX_PHICAL_CFG1               (GTYE4_CHANNEL_TX_PHICAL_CFG1              ),
        .TX_PI_BIASSET                (GTYE4_CHANNEL_TX_PI_BIASSET               ),
        .TX_PMADATA_OPT               (GTYE4_CHANNEL_TX_PMADATA_OPT              ),
        .TX_PMA_POWER_SAVE            (GTYE4_CHANNEL_TX_PMA_POWER_SAVE           ),
        .TX_PMA_RSV0                  (GTYE4_CHANNEL_TX_PMA_RSV0                 ),
        .TX_PMA_RSV1                  (GTYE4_CHANNEL_TX_PMA_RSV1                 ),
        .TX_PROGCLK_SEL               (GTYE4_CHANNEL_TX_PROGCLK_SEL              ),
        .TX_PROGDIV_CFG               (GTYE4_CHANNEL_TX_PROGDIV_CFG              ),
        .TX_PROGDIV_RATE              (GTYE4_CHANNEL_TX_PROGDIV_RATE             ),
        .TX_RXDETECT_CFG              (GTYE4_CHANNEL_TX_RXDETECT_CFG             ),
        .TX_RXDETECT_REF              (GTYE4_CHANNEL_TX_RXDETECT_REF             ),
        .TX_SAMPLE_PERIOD             (GTYE4_CHANNEL_TX_SAMPLE_PERIOD            ),
        .TX_SW_MEAS                   (GTYE4_CHANNEL_TX_SW_MEAS                  ),
        .TX_VREG_CTRL                 (GTYE4_CHANNEL_TX_VREG_CTRL                ),
        .TX_VREG_PDB                  (GTYE4_CHANNEL_TX_VREG_PDB                 ),
        .TX_VREG_VREFSEL              (GTYE4_CHANNEL_TX_VREG_VREFSEL             ),
        .TX_XCLK_SEL                  (GTYE4_CHANNEL_TX_XCLK_SEL                 ),
        .USB_BOTH_BURST_IDLE          (GTYE4_CHANNEL_USB_BOTH_BURST_IDLE         ),
        .USB_BURSTMAX_U3WAKE          (GTYE4_CHANNEL_USB_BURSTMAX_U3WAKE         ),
        .USB_BURSTMIN_U3WAKE          (GTYE4_CHANNEL_USB_BURSTMIN_U3WAKE         ),
        .USB_CLK_COR_EQ_EN            (GTYE4_CHANNEL_USB_CLK_COR_EQ_EN           ),
        .USB_EXT_CNTL                 (GTYE4_CHANNEL_USB_EXT_CNTL                ),
        .USB_IDLEMAX_POLLING          (GTYE4_CHANNEL_USB_IDLEMAX_POLLING         ),
        .USB_IDLEMIN_POLLING          (GTYE4_CHANNEL_USB_IDLEMIN_POLLING         ),
        .USB_LFPSPING_BURST           (GTYE4_CHANNEL_USB_LFPSPING_BURST          ),
        .USB_LFPSPOLLING_BURST        (GTYE4_CHANNEL_USB_LFPSPOLLING_BURST       ),
        .USB_LFPSPOLLING_IDLE_MS      (GTYE4_CHANNEL_USB_LFPSPOLLING_IDLE_MS     ),
        .USB_LFPSU1EXIT_BURST         (GTYE4_CHANNEL_USB_LFPSU1EXIT_BURST        ),
        .USB_LFPSU2LPEXIT_BURST_MS    (GTYE4_CHANNEL_USB_LFPSU2LPEXIT_BURST_MS   ),
        .USB_LFPSU3WAKE_BURST_MS      (GTYE4_CHANNEL_USB_LFPSU3WAKE_BURST_MS     ),
        .USB_LFPS_TPERIOD             (GTYE4_CHANNEL_USB_LFPS_TPERIOD            ),
        .USB_LFPS_TPERIOD_ACCURATE    (GTYE4_CHANNEL_USB_LFPS_TPERIOD_ACCURATE   ),
        .USB_MODE                     (GTYE4_CHANNEL_USB_MODE                    ),
        .USB_PCIE_ERR_REP_DIS         (GTYE4_CHANNEL_USB_PCIE_ERR_REP_DIS        ),
        .USB_PING_SATA_MAX_INIT       (GTYE4_CHANNEL_USB_PING_SATA_MAX_INIT      ),
        .USB_PING_SATA_MIN_INIT       (GTYE4_CHANNEL_USB_PING_SATA_MIN_INIT      ),
        .USB_POLL_SATA_MAX_BURST      (GTYE4_CHANNEL_USB_POLL_SATA_MAX_BURST     ),
        .USB_POLL_SATA_MIN_BURST      (GTYE4_CHANNEL_USB_POLL_SATA_MIN_BURST     ),
        .USB_RAW_ELEC                 (GTYE4_CHANNEL_USB_RAW_ELEC                ),
        .USB_RXIDLE_P0_CTRL           (GTYE4_CHANNEL_USB_RXIDLE_P0_CTRL          ),
        .USB_TXIDLE_TUNE_ENABLE       (GTYE4_CHANNEL_USB_TXIDLE_TUNE_ENABLE      ),
        .USB_U1_SATA_MAX_WAKE         (GTYE4_CHANNEL_USB_U1_SATA_MAX_WAKE        ),
        .USB_U1_SATA_MIN_WAKE         (GTYE4_CHANNEL_USB_U1_SATA_MIN_WAKE        ),
        .USB_U2_SAS_MAX_COM           (GTYE4_CHANNEL_USB_U2_SAS_MAX_COM          ),
        .USB_U2_SAS_MIN_COM           (GTYE4_CHANNEL_USB_U2_SAS_MIN_COM          ),
        .USE_PCS_CLK_PHASE_SEL        (GTYE4_CHANNEL_USE_PCS_CLK_PHASE_SEL       ),
        .Y_ALL_MODE                   (GTYE4_CHANNEL_Y_ALL_MODE                  )
      ) GTYE4_CHANNEL_PRIM_INST (
        .CDRSTEPDIR                   (GTYE4_CHANNEL_CDRSTEPDIR_int          [((ch+1)*  1)-1:(ch*  1)]),
        .CDRSTEPSQ                    (GTYE4_CHANNEL_CDRSTEPSQ_int           [((ch+1)*  1)-1:(ch*  1)]),
        .CDRSTEPSX                    (GTYE4_CHANNEL_CDRSTEPSX_int           [((ch+1)*  1)-1:(ch*  1)]),
        .CFGRESET                     (GTYE4_CHANNEL_CFGRESET_int            [((ch+1)*  1)-1:(ch*  1)]),
        .CLKRSVD0                     (GTYE4_CHANNEL_CLKRSVD0_int            [((ch+1)*  1)-1:(ch*  1)]),
        .CLKRSVD1                     (GTYE4_CHANNEL_CLKRSVD1_int            [((ch+1)*  1)-1:(ch*  1)]),
        .CPLLFREQLOCK                 (GTYE4_CHANNEL_CPLLFREQLOCK_int        [((ch+1)*  1)-1:(ch*  1)]),
        .CPLLLOCKDETCLK               (GTYE4_CHANNEL_CPLLLOCKDETCLK_int      [((ch+1)*  1)-1:(ch*  1)]),
        .CPLLLOCKEN                   (GTYE4_CHANNEL_CPLLLOCKEN_int          [((ch+1)*  1)-1:(ch*  1)]),
        .CPLLPD                       (GTYE4_CHANNEL_CPLLPD_int              [((ch+1)*  1)-1:(ch*  1)]),
        .CPLLREFCLKSEL                (GTYE4_CHANNEL_CPLLREFCLKSEL_int       [((ch+1)*  3)-1:(ch*  3)]),
        .CPLLRESET                    (GTYE4_CHANNEL_CPLLRESET_int           [((ch+1)*  1)-1:(ch*  1)]),
        .DMONFIFORESET                (GTYE4_CHANNEL_DMONFIFORESET_int       [((ch+1)*  1)-1:(ch*  1)]),
        .DMONITORCLK                  (GTYE4_CHANNEL_DMONITORCLK_int         [((ch+1)*  1)-1:(ch*  1)]),
        .DRPADDR                      (GTYE4_CHANNEL_DRPADDR_int             [((ch+1)* 10)-1:(ch* 10)]),
        .DRPCLK                       (GTYE4_CHANNEL_DRPCLK_int              [((ch+1)*  1)-1:(ch*  1)]),
        .DRPDI                        (GTYE4_CHANNEL_DRPDI_int               [((ch+1)* 16)-1:(ch* 16)]),
        .DRPEN                        (GTYE4_CHANNEL_DRPEN_int               [((ch+1)*  1)-1:(ch*  1)]),
        .DRPRST                       (GTYE4_CHANNEL_DRPRST_int              [((ch+1)*  1)-1:(ch*  1)]),
        .DRPWE                        (GTYE4_CHANNEL_DRPWE_int               [((ch+1)*  1)-1:(ch*  1)]),
        .EYESCANRESET                 (GTYE4_CHANNEL_EYESCANRESET_int        [((ch+1)*  1)-1:(ch*  1)]),
        .EYESCANTRIGGER               (GTYE4_CHANNEL_EYESCANTRIGGER_int      [((ch+1)*  1)-1:(ch*  1)]),
        .FREQOS                       (GTYE4_CHANNEL_FREQOS_int              [((ch+1)*  1)-1:(ch*  1)]),
        .GTGREFCLK                    (GTYE4_CHANNEL_GTGREFCLK_int           [((ch+1)*  1)-1:(ch*  1)]),
        .GTNORTHREFCLK0               (GTYE4_CHANNEL_GTNORTHREFCLK0_int      [((ch+1)*  1)-1:(ch*  1)]),
        .GTNORTHREFCLK1               (GTYE4_CHANNEL_GTNORTHREFCLK1_int      [((ch+1)*  1)-1:(ch*  1)]),
        .GTREFCLK0                    (GTYE4_CHANNEL_GTREFCLK0_int           [((ch+1)*  1)-1:(ch*  1)]),
        .GTREFCLK1                    (GTYE4_CHANNEL_GTREFCLK1_int           [((ch+1)*  1)-1:(ch*  1)]),
        .GTRSVD                       (GTYE4_CHANNEL_GTRSVD_int              [((ch+1)* 16)-1:(ch* 16)]),
        .GTRXRESET                    (GTYE4_CHANNEL_GTRXRESET_int           [((ch+1)*  1)-1:(ch*  1)]),
        .GTRXRESETSEL                 (GTYE4_CHANNEL_GTRXRESETSEL_int        [((ch+1)*  1)-1:(ch*  1)]),
        .GTSOUTHREFCLK0               (GTYE4_CHANNEL_GTSOUTHREFCLK0_int      [((ch+1)*  1)-1:(ch*  1)]),
        .GTSOUTHREFCLK1               (GTYE4_CHANNEL_GTSOUTHREFCLK1_int      [((ch+1)*  1)-1:(ch*  1)]),
        .GTTXRESET                    (GTYE4_CHANNEL_GTTXRESET_int           [((ch+1)*  1)-1:(ch*  1)]),
        .GTTXRESETSEL                 (GTYE4_CHANNEL_GTTXRESETSEL_int        [((ch+1)*  1)-1:(ch*  1)]),
        .GTYRXN                       (GTYE4_CHANNEL_GTYRXN_int              [((ch+1)*  1)-1:(ch*  1)]),
        .GTYRXP                       (GTYE4_CHANNEL_GTYRXP_int              [((ch+1)*  1)-1:(ch*  1)]),
        .INCPCTRL                     (GTYE4_CHANNEL_INCPCTRL_int            [((ch+1)*  1)-1:(ch*  1)]),
        .LOOPBACK                     (GTYE4_CHANNEL_LOOPBACK_int            [((ch+1)*  3)-1:(ch*  3)]),
        .PCIEEQRXEQADAPTDONE          (GTYE4_CHANNEL_PCIEEQRXEQADAPTDONE_int [((ch+1)*  1)-1:(ch*  1)]),
        .PCIERSTIDLE                  (GTYE4_CHANNEL_PCIERSTIDLE_int         [((ch+1)*  1)-1:(ch*  1)]),
        .PCIERSTTXSYNCSTART           (GTYE4_CHANNEL_PCIERSTTXSYNCSTART_int  [((ch+1)*  1)-1:(ch*  1)]),
        .PCIEUSERRATEDONE             (GTYE4_CHANNEL_PCIEUSERRATEDONE_int    [((ch+1)*  1)-1:(ch*  1)]),
        .PCSRSVDIN                    (GTYE4_CHANNEL_PCSRSVDIN_int           [((ch+1)* 16)-1:(ch* 16)]),
        .QPLL0CLK                     (GTYE4_CHANNEL_QPLL0CLK_int            [((ch+1)*  1)-1:(ch*  1)]),
        .QPLL0FREQLOCK                (GTYE4_CHANNEL_QPLL0FREQLOCK_int       [((ch+1)*  1)-1:(ch*  1)]),
        .QPLL0REFCLK                  (GTYE4_CHANNEL_QPLL0REFCLK_int         [((ch+1)*  1)-1:(ch*  1)]),
        .QPLL1CLK                     (GTYE4_CHANNEL_QPLL1CLK_int            [((ch+1)*  1)-1:(ch*  1)]),
        .QPLL1FREQLOCK                (GTYE4_CHANNEL_QPLL1FREQLOCK_int       [((ch+1)*  1)-1:(ch*  1)]),
        .QPLL1REFCLK                  (GTYE4_CHANNEL_QPLL1REFCLK_int         [((ch+1)*  1)-1:(ch*  1)]),
        .RESETOVRD                    (GTYE4_CHANNEL_RESETOVRD_int           [((ch+1)*  1)-1:(ch*  1)]),
        .RX8B10BEN                    (GTYE4_CHANNEL_RX8B10BEN_int           [((ch+1)*  1)-1:(ch*  1)]),
        .RXAFECFOKEN                  (GTYE4_CHANNEL_RXAFECFOKEN_int         [((ch+1)*  1)-1:(ch*  1)]),
        .RXBUFRESET                   (GTYE4_CHANNEL_RXBUFRESET_int          [((ch+1)*  1)-1:(ch*  1)]),
        .RXCDRFREQRESET               (GTYE4_CHANNEL_RXCDRFREQRESET_int      [((ch+1)*  1)-1:(ch*  1)]),
        .RXCDRHOLD                    (GTYE4_CHANNEL_RXCDRHOLD_int           [((ch+1)*  1)-1:(ch*  1)]),
        .RXCDROVRDEN                  (GTYE4_CHANNEL_RXCDROVRDEN_int         [((ch+1)*  1)-1:(ch*  1)]),
        .RXCDRRESET                   (GTYE4_CHANNEL_RXCDRRESET_int          [((ch+1)*  1)-1:(ch*  1)]),
        .RXCHBONDEN                   (GTYE4_CHANNEL_RXCHBONDEN_int          [((ch+1)*  1)-1:(ch*  1)]),
        .RXCHBONDI                    (GTYE4_CHANNEL_RXCHBONDI_int           [((ch+1)*  5)-1:(ch*  5)]),
        .RXCHBONDLEVEL                (GTYE4_CHANNEL_RXCHBONDLEVEL_int       [((ch+1)*  3)-1:(ch*  3)]),
        .RXCHBONDMASTER               (GTYE4_CHANNEL_RXCHBONDMASTER_int      [((ch+1)*  1)-1:(ch*  1)]),
        .RXCHBONDSLAVE                (GTYE4_CHANNEL_RXCHBONDSLAVE_int       [((ch+1)*  1)-1:(ch*  1)]),
        .RXCKCALRESET                 (GTYE4_CHANNEL_RXCKCALRESET_int        [((ch+1)*  1)-1:(ch*  1)]),
        .RXCKCALSTART                 (GTYE4_CHANNEL_RXCKCALSTART_int        [((ch+1)*  7)-1:(ch*  7)]),
        .RXCOMMADETEN                 (GTYE4_CHANNEL_RXCOMMADETEN_int        [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFEAGCHOLD                 (GTYE4_CHANNEL_RXDFEAGCHOLD_int        [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFEAGCOVRDEN               (GTYE4_CHANNEL_RXDFEAGCOVRDEN_int      [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFECFOKFCNUM               (GTYE4_CHANNEL_RXDFECFOKFCNUM_int      [((ch+1)*  4)-1:(ch*  4)]),
        .RXDFECFOKFEN                 (GTYE4_CHANNEL_RXDFECFOKFEN_int        [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFECFOKFPULSE              (GTYE4_CHANNEL_RXDFECFOKFPULSE_int     [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFECFOKHOLD                (GTYE4_CHANNEL_RXDFECFOKHOLD_int       [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFECFOKOVREN               (GTYE4_CHANNEL_RXDFECFOKOVREN_int      [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFEKHHOLD                  (GTYE4_CHANNEL_RXDFEKHHOLD_int         [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFEKHOVRDEN                (GTYE4_CHANNEL_RXDFEKHOVRDEN_int       [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFELFHOLD                  (GTYE4_CHANNEL_RXDFELFHOLD_int         [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFELFOVRDEN                (GTYE4_CHANNEL_RXDFELFOVRDEN_int       [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFELPMRESET                (GTYE4_CHANNEL_RXDFELPMRESET_int       [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFETAP10HOLD               (GTYE4_CHANNEL_RXDFETAP10HOLD_int      [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFETAP10OVRDEN             (GTYE4_CHANNEL_RXDFETAP10OVRDEN_int    [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFETAP11HOLD               (GTYE4_CHANNEL_RXDFETAP11HOLD_int      [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFETAP11OVRDEN             (GTYE4_CHANNEL_RXDFETAP11OVRDEN_int    [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFETAP12HOLD               (GTYE4_CHANNEL_RXDFETAP12HOLD_int      [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFETAP12OVRDEN             (GTYE4_CHANNEL_RXDFETAP12OVRDEN_int    [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFETAP13HOLD               (GTYE4_CHANNEL_RXDFETAP13HOLD_int      [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFETAP13OVRDEN             (GTYE4_CHANNEL_RXDFETAP13OVRDEN_int    [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFETAP14HOLD               (GTYE4_CHANNEL_RXDFETAP14HOLD_int      [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFETAP14OVRDEN             (GTYE4_CHANNEL_RXDFETAP14OVRDEN_int    [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFETAP15HOLD               (GTYE4_CHANNEL_RXDFETAP15HOLD_int      [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFETAP15OVRDEN             (GTYE4_CHANNEL_RXDFETAP15OVRDEN_int    [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFETAP2HOLD                (GTYE4_CHANNEL_RXDFETAP2HOLD_int       [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFETAP2OVRDEN              (GTYE4_CHANNEL_RXDFETAP2OVRDEN_int     [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFETAP3HOLD                (GTYE4_CHANNEL_RXDFETAP3HOLD_int       [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFETAP3OVRDEN              (GTYE4_CHANNEL_RXDFETAP3OVRDEN_int     [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFETAP4HOLD                (GTYE4_CHANNEL_RXDFETAP4HOLD_int       [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFETAP4OVRDEN              (GTYE4_CHANNEL_RXDFETAP4OVRDEN_int     [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFETAP5HOLD                (GTYE4_CHANNEL_RXDFETAP5HOLD_int       [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFETAP5OVRDEN              (GTYE4_CHANNEL_RXDFETAP5OVRDEN_int     [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFETAP6HOLD                (GTYE4_CHANNEL_RXDFETAP6HOLD_int       [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFETAP6OVRDEN              (GTYE4_CHANNEL_RXDFETAP6OVRDEN_int     [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFETAP7HOLD                (GTYE4_CHANNEL_RXDFETAP7HOLD_int       [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFETAP7OVRDEN              (GTYE4_CHANNEL_RXDFETAP7OVRDEN_int     [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFETAP8HOLD                (GTYE4_CHANNEL_RXDFETAP8HOLD_int       [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFETAP8OVRDEN              (GTYE4_CHANNEL_RXDFETAP8OVRDEN_int     [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFETAP9HOLD                (GTYE4_CHANNEL_RXDFETAP9HOLD_int       [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFETAP9OVRDEN              (GTYE4_CHANNEL_RXDFETAP9OVRDEN_int     [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFEUTHOLD                  (GTYE4_CHANNEL_RXDFEUTHOLD_int         [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFEUTOVRDEN                (GTYE4_CHANNEL_RXDFEUTOVRDEN_int       [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFEVPHOLD                  (GTYE4_CHANNEL_RXDFEVPHOLD_int         [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFEVPOVRDEN                (GTYE4_CHANNEL_RXDFEVPOVRDEN_int       [((ch+1)*  1)-1:(ch*  1)]),
        .RXDFEXYDEN                   (GTYE4_CHANNEL_RXDFEXYDEN_int          [((ch+1)*  1)-1:(ch*  1)]),
        .RXDLYBYPASS                  (GTYE4_CHANNEL_RXDLYBYPASS_int         [((ch+1)*  1)-1:(ch*  1)]),
        .RXDLYEN                      (GTYE4_CHANNEL_RXDLYEN_int             [((ch+1)*  1)-1:(ch*  1)]),
        .RXDLYOVRDEN                  (GTYE4_CHANNEL_RXDLYOVRDEN_int         [((ch+1)*  1)-1:(ch*  1)]),
        .RXDLYSRESET                  (GTYE4_CHANNEL_RXDLYSRESET_int         [((ch+1)*  1)-1:(ch*  1)]),
        .RXELECIDLEMODE               (GTYE4_CHANNEL_RXELECIDLEMODE_int      [((ch+1)*  2)-1:(ch*  2)]),
        .RXEQTRAINING                 (GTYE4_CHANNEL_RXEQTRAINING_int        [((ch+1)*  1)-1:(ch*  1)]),
        .RXGEARBOXSLIP                (GTYE4_CHANNEL_RXGEARBOXSLIP_int       [((ch+1)*  1)-1:(ch*  1)]),
        .RXLATCLK                     (GTYE4_CHANNEL_RXLATCLK_int            [((ch+1)*  1)-1:(ch*  1)]),
        .RXLPMEN                      (GTYE4_CHANNEL_RXLPMEN_int             [((ch+1)*  1)-1:(ch*  1)]),
        .RXLPMGCHOLD                  (GTYE4_CHANNEL_RXLPMGCHOLD_int         [((ch+1)*  1)-1:(ch*  1)]),
        .RXLPMGCOVRDEN                (GTYE4_CHANNEL_RXLPMGCOVRDEN_int       [((ch+1)*  1)-1:(ch*  1)]),
        .RXLPMHFHOLD                  (GTYE4_CHANNEL_RXLPMHFHOLD_int         [((ch+1)*  1)-1:(ch*  1)]),
        .RXLPMHFOVRDEN                (GTYE4_CHANNEL_RXLPMHFOVRDEN_int       [((ch+1)*  1)-1:(ch*  1)]),
        .RXLPMLFHOLD                  (GTYE4_CHANNEL_RXLPMLFHOLD_int         [((ch+1)*  1)-1:(ch*  1)]),
        .RXLPMLFKLOVRDEN              (GTYE4_CHANNEL_RXLPMLFKLOVRDEN_int     [((ch+1)*  1)-1:(ch*  1)]),
        .RXLPMOSHOLD                  (GTYE4_CHANNEL_RXLPMOSHOLD_int         [((ch+1)*  1)-1:(ch*  1)]),
        .RXLPMOSOVRDEN                (GTYE4_CHANNEL_RXLPMOSOVRDEN_int       [((ch+1)*  1)-1:(ch*  1)]),
        .RXMCOMMAALIGNEN              (GTYE4_CHANNEL_RXMCOMMAALIGNEN_int     [((ch+1)*  1)-1:(ch*  1)]),
        .RXMONITORSEL                 (GTYE4_CHANNEL_RXMONITORSEL_int        [((ch+1)*  2)-1:(ch*  2)]),
        .RXOOBRESET                   (GTYE4_CHANNEL_RXOOBRESET_int          [((ch+1)*  1)-1:(ch*  1)]),
        .RXOSCALRESET                 (GTYE4_CHANNEL_RXOSCALRESET_int        [((ch+1)*  1)-1:(ch*  1)]),
        .RXOSHOLD                     (GTYE4_CHANNEL_RXOSHOLD_int            [((ch+1)*  1)-1:(ch*  1)]),
        .RXOSOVRDEN                   (GTYE4_CHANNEL_RXOSOVRDEN_int          [((ch+1)*  1)-1:(ch*  1)]),
        .RXOUTCLKSEL                  (GTYE4_CHANNEL_RXOUTCLKSEL_int         [((ch+1)*  3)-1:(ch*  3)]),
        .RXPCOMMAALIGNEN              (GTYE4_CHANNEL_RXPCOMMAALIGNEN_int     [((ch+1)*  1)-1:(ch*  1)]),
        .RXPCSRESET                   (GTYE4_CHANNEL_RXPCSRESET_int          [((ch+1)*  1)-1:(ch*  1)]),
        .RXPD                         (GTYE4_CHANNEL_RXPD_int                [((ch+1)*  2)-1:(ch*  2)]),
        .RXPHALIGN                    (GTYE4_CHANNEL_RXPHALIGN_int           [((ch+1)*  1)-1:(ch*  1)]),
        .RXPHALIGNEN                  (GTYE4_CHANNEL_RXPHALIGNEN_int         [((ch+1)*  1)-1:(ch*  1)]),
        .RXPHDLYPD                    (GTYE4_CHANNEL_RXPHDLYPD_int           [((ch+1)*  1)-1:(ch*  1)]),
        .RXPHDLYRESET                 (GTYE4_CHANNEL_RXPHDLYRESET_int        [((ch+1)*  1)-1:(ch*  1)]),
        .RXPLLCLKSEL                  (GTYE4_CHANNEL_RXPLLCLKSEL_int         [((ch+1)*  2)-1:(ch*  2)]),
        .RXPMARESET                   (GTYE4_CHANNEL_RXPMARESET_int          [((ch+1)*  1)-1:(ch*  1)]),
        .RXPOLARITY                   (GTYE4_CHANNEL_RXPOLARITY_int          [((ch+1)*  1)-1:(ch*  1)]),
        .RXPRBSCNTRESET               (GTYE4_CHANNEL_RXPRBSCNTRESET_int      [((ch+1)*  1)-1:(ch*  1)]),
        .RXPRBSSEL                    (GTYE4_CHANNEL_RXPRBSSEL_int           [((ch+1)*  4)-1:(ch*  4)]),
        .RXPROGDIVRESET               (GTYE4_CHANNEL_RXPROGDIVRESET_int      [((ch+1)*  1)-1:(ch*  1)]),
        .RXRATE                       (GTYE4_CHANNEL_RXRATE_int              [((ch+1)*  3)-1:(ch*  3)]),
        .RXRATEMODE                   (GTYE4_CHANNEL_RXRATEMODE_int          [((ch+1)*  1)-1:(ch*  1)]),
        .RXSLIDE                      (GTYE4_CHANNEL_RXSLIDE_int             [((ch+1)*  1)-1:(ch*  1)]),
        .RXSLIPOUTCLK                 (GTYE4_CHANNEL_RXSLIPOUTCLK_int        [((ch+1)*  1)-1:(ch*  1)]),
        .RXSLIPPMA                    (GTYE4_CHANNEL_RXSLIPPMA_int           [((ch+1)*  1)-1:(ch*  1)]),
        .RXSYNCALLIN                  (GTYE4_CHANNEL_RXSYNCALLIN_int         [((ch+1)*  1)-1:(ch*  1)]),
        .RXSYNCIN                     (GTYE4_CHANNEL_RXSYNCIN_int            [((ch+1)*  1)-1:(ch*  1)]),
        .RXSYNCMODE                   (GTYE4_CHANNEL_RXSYNCMODE_int          [((ch+1)*  1)-1:(ch*  1)]),
        .RXSYSCLKSEL                  (GTYE4_CHANNEL_RXSYSCLKSEL_int         [((ch+1)*  2)-1:(ch*  2)]),
        .RXTERMINATION                (GTYE4_CHANNEL_RXTERMINATION_int       [((ch+1)*  1)-1:(ch*  1)]),
        .RXUSERRDY                    (GTYE4_CHANNEL_RXUSERRDY_int           [((ch+1)*  1)-1:(ch*  1)]),
        .RXUSRCLK                     (GTYE4_CHANNEL_RXUSRCLK_int            [((ch+1)*  1)-1:(ch*  1)]),
        .RXUSRCLK2                    (GTYE4_CHANNEL_RXUSRCLK2_int           [((ch+1)*  1)-1:(ch*  1)]),
        .SIGVALIDCLK                  (GTYE4_CHANNEL_SIGVALIDCLK_int         [((ch+1)*  1)-1:(ch*  1)]),
        .TSTIN                        (GTYE4_CHANNEL_TSTIN_int               [((ch+1)* 20)-1:(ch* 20)]),
        .TX8B10BBYPASS                (GTYE4_CHANNEL_TX8B10BBYPASS_int       [((ch+1)*  8)-1:(ch*  8)]),
        .TX8B10BEN                    (GTYE4_CHANNEL_TX8B10BEN_int           [((ch+1)*  1)-1:(ch*  1)]),
        .TXCOMINIT                    (GTYE4_CHANNEL_TXCOMINIT_int           [((ch+1)*  1)-1:(ch*  1)]),
        .TXCOMSAS                     (GTYE4_CHANNEL_TXCOMSAS_int            [((ch+1)*  1)-1:(ch*  1)]),
        .TXCOMWAKE                    (GTYE4_CHANNEL_TXCOMWAKE_int           [((ch+1)*  1)-1:(ch*  1)]),
        .TXCTRL0                      (GTYE4_CHANNEL_TXCTRL0_int             [((ch+1)* 16)-1:(ch* 16)]),
        .TXCTRL1                      (GTYE4_CHANNEL_TXCTRL1_int             [((ch+1)* 16)-1:(ch* 16)]),
        .TXCTRL2                      (GTYE4_CHANNEL_TXCTRL2_int             [((ch+1)*  8)-1:(ch*  8)]),
        .TXDATA                       (GTYE4_CHANNEL_TXDATA_int              [((ch+1)*128)-1:(ch*128)]),
        .TXDATAEXTENDRSVD             (GTYE4_CHANNEL_TXDATAEXTENDRSVD_int    [((ch+1)*  8)-1:(ch*  8)]),
        .TXDCCFORCESTART              (GTYE4_CHANNEL_TXDCCFORCESTART_int     [((ch+1)*  1)-1:(ch*  1)]),
        .TXDCCRESET                   (GTYE4_CHANNEL_TXDCCRESET_int          [((ch+1)*  1)-1:(ch*  1)]),
        .TXDEEMPH                     (GTYE4_CHANNEL_TXDEEMPH_int            [((ch+1)*  2)-1:(ch*  2)]),
        .TXDETECTRX                   (GTYE4_CHANNEL_TXDETECTRX_int          [((ch+1)*  1)-1:(ch*  1)]),
        .TXDIFFCTRL                   (GTYE4_CHANNEL_TXDIFFCTRL_int          [((ch+1)*  5)-1:(ch*  5)]),
        .TXDLYBYPASS                  (GTYE4_CHANNEL_TXDLYBYPASS_int         [((ch+1)*  1)-1:(ch*  1)]),
        .TXDLYEN                      (GTYE4_CHANNEL_TXDLYEN_int             [((ch+1)*  1)-1:(ch*  1)]),
        .TXDLYHOLD                    (GTYE4_CHANNEL_TXDLYHOLD_int           [((ch+1)*  1)-1:(ch*  1)]),
        .TXDLYOVRDEN                  (GTYE4_CHANNEL_TXDLYOVRDEN_int         [((ch+1)*  1)-1:(ch*  1)]),
        .TXDLYSRESET                  (GTYE4_CHANNEL_TXDLYSRESET_int         [((ch+1)*  1)-1:(ch*  1)]),
        .TXDLYUPDOWN                  (GTYE4_CHANNEL_TXDLYUPDOWN_int         [((ch+1)*  1)-1:(ch*  1)]),
        .TXELECIDLE                   (GTYE4_CHANNEL_TXELECIDLE_int          [((ch+1)*  1)-1:(ch*  1)]),
        .TXHEADER                     (GTYE4_CHANNEL_TXHEADER_int            [((ch+1)*  6)-1:(ch*  6)]),
        .TXINHIBIT                    (GTYE4_CHANNEL_TXINHIBIT_int           [((ch+1)*  1)-1:(ch*  1)]),
        .TXLATCLK                     (GTYE4_CHANNEL_TXLATCLK_int            [((ch+1)*  1)-1:(ch*  1)]),
        .TXLFPSTRESET                 (GTYE4_CHANNEL_TXLFPSTRESET_int        [((ch+1)*  1)-1:(ch*  1)]),
        .TXLFPSU2LPEXIT               (GTYE4_CHANNEL_TXLFPSU2LPEXIT_int      [((ch+1)*  1)-1:(ch*  1)]),
        .TXLFPSU3WAKE                 (GTYE4_CHANNEL_TXLFPSU3WAKE_int        [((ch+1)*  1)-1:(ch*  1)]),
        .TXMAINCURSOR                 (GTYE4_CHANNEL_TXMAINCURSOR_int        [((ch+1)*  7)-1:(ch*  7)]),
        .TXMARGIN                     (GTYE4_CHANNEL_TXMARGIN_int            [((ch+1)*  3)-1:(ch*  3)]),
        .TXMUXDCDEXHOLD               (GTYE4_CHANNEL_TXMUXDCDEXHOLD_int      [((ch+1)*  1)-1:(ch*  1)]),
        .TXMUXDCDORWREN               (GTYE4_CHANNEL_TXMUXDCDORWREN_int      [((ch+1)*  1)-1:(ch*  1)]),
        .TXONESZEROS                  (GTYE4_CHANNEL_TXONESZEROS_int         [((ch+1)*  1)-1:(ch*  1)]),
        .TXOUTCLKSEL                  (GTYE4_CHANNEL_TXOUTCLKSEL_int         [((ch+1)*  3)-1:(ch*  3)]),
        .TXPCSRESET                   (GTYE4_CHANNEL_TXPCSRESET_int          [((ch+1)*  1)-1:(ch*  1)]),
        .TXPD                         (GTYE4_CHANNEL_TXPD_int                [((ch+1)*  2)-1:(ch*  2)]),
        .TXPDELECIDLEMODE             (GTYE4_CHANNEL_TXPDELECIDLEMODE_int    [((ch+1)*  1)-1:(ch*  1)]),
        .TXPHALIGN                    (GTYE4_CHANNEL_TXPHALIGN_int           [((ch+1)*  1)-1:(ch*  1)]),
        .TXPHALIGNEN                  (GTYE4_CHANNEL_TXPHALIGNEN_int         [((ch+1)*  1)-1:(ch*  1)]),
        .TXPHDLYPD                    (GTYE4_CHANNEL_TXPHDLYPD_int           [((ch+1)*  1)-1:(ch*  1)]),
        .TXPHDLYRESET                 (GTYE4_CHANNEL_TXPHDLYRESET_int        [((ch+1)*  1)-1:(ch*  1)]),
        .TXPHDLYTSTCLK                (GTYE4_CHANNEL_TXPHDLYTSTCLK_int       [((ch+1)*  1)-1:(ch*  1)]),
        .TXPHINIT                     (GTYE4_CHANNEL_TXPHINIT_int            [((ch+1)*  1)-1:(ch*  1)]),
        .TXPHOVRDEN                   (GTYE4_CHANNEL_TXPHOVRDEN_int          [((ch+1)*  1)-1:(ch*  1)]),
        .TXPIPPMEN                    (GTYE4_CHANNEL_TXPIPPMEN_int           [((ch+1)*  1)-1:(ch*  1)]),
        .TXPIPPMOVRDEN                (GTYE4_CHANNEL_TXPIPPMOVRDEN_int       [((ch+1)*  1)-1:(ch*  1)]),
        .TXPIPPMPD                    (GTYE4_CHANNEL_TXPIPPMPD_int           [((ch+1)*  1)-1:(ch*  1)]),
        .TXPIPPMSEL                   (GTYE4_CHANNEL_TXPIPPMSEL_int          [((ch+1)*  1)-1:(ch*  1)]),
        .TXPIPPMSTEPSIZE              (GTYE4_CHANNEL_TXPIPPMSTEPSIZE_int     [((ch+1)*  5)-1:(ch*  5)]),
        .TXPISOPD                     (GTYE4_CHANNEL_TXPISOPD_int            [((ch+1)*  1)-1:(ch*  1)]),
        .TXPLLCLKSEL                  (GTYE4_CHANNEL_TXPLLCLKSEL_int         [((ch+1)*  2)-1:(ch*  2)]),
        .TXPMARESET                   (GTYE4_CHANNEL_TXPMARESET_int          [((ch+1)*  1)-1:(ch*  1)]),
        .TXPOLARITY                   (GTYE4_CHANNEL_TXPOLARITY_int          [((ch+1)*  1)-1:(ch*  1)]),
        .TXPOSTCURSOR                 (GTYE4_CHANNEL_TXPOSTCURSOR_int        [((ch+1)*  5)-1:(ch*  5)]),
        .TXPRBSFORCEERR               (GTYE4_CHANNEL_TXPRBSFORCEERR_int      [((ch+1)*  1)-1:(ch*  1)]),
        .TXPRBSSEL                    (GTYE4_CHANNEL_TXPRBSSEL_int           [((ch+1)*  4)-1:(ch*  4)]),
        .TXPRECURSOR                  (GTYE4_CHANNEL_TXPRECURSOR_int         [((ch+1)*  5)-1:(ch*  5)]),
        .TXPROGDIVRESET               (GTYE4_CHANNEL_TXPROGDIVRESET_int      [((ch+1)*  1)-1:(ch*  1)]),
        .TXRATE                       (GTYE4_CHANNEL_TXRATE_int              [((ch+1)*  3)-1:(ch*  3)]),
        .TXRATEMODE                   (GTYE4_CHANNEL_TXRATEMODE_int          [((ch+1)*  1)-1:(ch*  1)]),
        .TXSEQUENCE                   (GTYE4_CHANNEL_TXSEQUENCE_int          [((ch+1)*  7)-1:(ch*  7)]),
        .TXSWING                      (GTYE4_CHANNEL_TXSWING_int             [((ch+1)*  1)-1:(ch*  1)]),
        .TXSYNCALLIN                  (GTYE4_CHANNEL_TXSYNCALLIN_int         [((ch+1)*  1)-1:(ch*  1)]),
        .TXSYNCIN                     (GTYE4_CHANNEL_TXSYNCIN_int            [((ch+1)*  1)-1:(ch*  1)]),
        .TXSYNCMODE                   (GTYE4_CHANNEL_TXSYNCMODE_int          [((ch+1)*  1)-1:(ch*  1)]),
        .TXSYSCLKSEL                  (GTYE4_CHANNEL_TXSYSCLKSEL_int         [((ch+1)*  2)-1:(ch*  2)]),
        .TXUSERRDY                    (GTYE4_CHANNEL_TXUSERRDY_int           [((ch+1)*  1)-1:(ch*  1)]),
        .TXUSRCLK                     (GTYE4_CHANNEL_TXUSRCLK_int            [((ch+1)*  1)-1:(ch*  1)]),
        .TXUSRCLK2                    (GTYE4_CHANNEL_TXUSRCLK2_int           [((ch+1)*  1)-1:(ch*  1)]),

        .BUFGTCE                      (GTYE4_CHANNEL_BUFGTCE                 [((ch+1)*  1)-1:(ch*  1)]),
        .BUFGTCEMASK                  (GTYE4_CHANNEL_BUFGTCEMASK             [((ch+1)*  3)-1:(ch*  3)]),
        .BUFGTDIV                     (GTYE4_CHANNEL_BUFGTDIV                [((ch+1)*  9)-1:(ch*  9)]),
        .BUFGTRESET                   (GTYE4_CHANNEL_BUFGTRESET              [((ch+1)*  1)-1:(ch*  1)]),
        .BUFGTRSTMASK                 (GTYE4_CHANNEL_BUFGTRSTMASK            [((ch+1)*  3)-1:(ch*  3)]),
        .CPLLFBCLKLOST                (GTYE4_CHANNEL_CPLLFBCLKLOST           [((ch+1)*  1)-1:(ch*  1)]),
        .CPLLLOCK                     (GTYE4_CHANNEL_CPLLLOCK                [((ch+1)*  1)-1:(ch*  1)]),
        .CPLLREFCLKLOST               (GTYE4_CHANNEL_CPLLREFCLKLOST          [((ch+1)*  1)-1:(ch*  1)]),
        .DMONITOROUT                  (GTYE4_CHANNEL_DMONITOROUT             [((ch+1)* 16)-1:(ch* 16)]),
        .DMONITOROUTCLK               (GTYE4_CHANNEL_DMONITOROUTCLK          [((ch+1)*  1)-1:(ch*  1)]),
        .DRPDO                        (GTYE4_CHANNEL_DRPDO                   [((ch+1)* 16)-1:(ch* 16)]),
        .DRPRDY                       (GTYE4_CHANNEL_DRPRDY                  [((ch+1)*  1)-1:(ch*  1)]),
        .EYESCANDATAERROR             (GTYE4_CHANNEL_EYESCANDATAERROR        [((ch+1)*  1)-1:(ch*  1)]),
        .GTPOWERGOOD                  (GTYE4_CHANNEL_GTPOWERGOOD             [((ch+1)*  1)-1:(ch*  1)]),
        .GTREFCLKMONITOR              (GTYE4_CHANNEL_GTREFCLKMONITOR         [((ch+1)*  1)-1:(ch*  1)]),
        .GTYTXN                       (GTYE4_CHANNEL_GTYTXN                  [((ch+1)*  1)-1:(ch*  1)]),
        .GTYTXP                       (GTYE4_CHANNEL_GTYTXP                  [((ch+1)*  1)-1:(ch*  1)]),
        .PCIERATEGEN3                 (GTYE4_CHANNEL_PCIERATEGEN3            [((ch+1)*  1)-1:(ch*  1)]),
        .PCIERATEIDLE                 (GTYE4_CHANNEL_PCIERATEIDLE            [((ch+1)*  1)-1:(ch*  1)]),
        .PCIERATEQPLLPD               (GTYE4_CHANNEL_PCIERATEQPLLPD          [((ch+1)*  2)-1:(ch*  2)]),
        .PCIERATEQPLLRESET            (GTYE4_CHANNEL_PCIERATEQPLLRESET       [((ch+1)*  2)-1:(ch*  2)]),
        .PCIESYNCTXSYNCDONE           (GTYE4_CHANNEL_PCIESYNCTXSYNCDONE      [((ch+1)*  1)-1:(ch*  1)]),
        .PCIEUSERGEN3RDY              (GTYE4_CHANNEL_PCIEUSERGEN3RDY         [((ch+1)*  1)-1:(ch*  1)]),
        .PCIEUSERPHYSTATUSRST         (GTYE4_CHANNEL_PCIEUSERPHYSTATUSRST    [((ch+1)*  1)-1:(ch*  1)]),
        .PCIEUSERRATESTART            (GTYE4_CHANNEL_PCIEUSERRATESTART       [((ch+1)*  1)-1:(ch*  1)]),
        .PCSRSVDOUT                   (GTYE4_CHANNEL_PCSRSVDOUT              [((ch+1)* 16)-1:(ch* 16)]),
        .PHYSTATUS                    (GTYE4_CHANNEL_PHYSTATUS               [((ch+1)*  1)-1:(ch*  1)]),
        .PINRSRVDAS                   (GTYE4_CHANNEL_PINRSRVDAS              [((ch+1)* 16)-1:(ch* 16)]),
        .POWERPRESENT                 (GTYE4_CHANNEL_POWERPRESENT            [((ch+1)*  1)-1:(ch*  1)]),
        .RESETEXCEPTION               (GTYE4_CHANNEL_RESETEXCEPTION          [((ch+1)*  1)-1:(ch*  1)]),
        .RXBUFSTATUS                  (GTYE4_CHANNEL_RXBUFSTATUS             [((ch+1)*  3)-1:(ch*  3)]),
        .RXBYTEISALIGNED              (GTYE4_CHANNEL_RXBYTEISALIGNED         [((ch+1)*  1)-1:(ch*  1)]),
        .RXBYTEREALIGN                (GTYE4_CHANNEL_RXBYTEREALIGN           [((ch+1)*  1)-1:(ch*  1)]),
        .RXCDRLOCK                    (GTYE4_CHANNEL_RXCDRLOCK               [((ch+1)*  1)-1:(ch*  1)]),
        .RXCDRPHDONE                  (GTYE4_CHANNEL_RXCDRPHDONE             [((ch+1)*  1)-1:(ch*  1)]),
        .RXCHANBONDSEQ                (GTYE4_CHANNEL_RXCHANBONDSEQ           [((ch+1)*  1)-1:(ch*  1)]),
        .RXCHANISALIGNED              (GTYE4_CHANNEL_RXCHANISALIGNED         [((ch+1)*  1)-1:(ch*  1)]),
        .RXCHANREALIGN                (GTYE4_CHANNEL_RXCHANREALIGN           [((ch+1)*  1)-1:(ch*  1)]),
        .RXCHBONDO                    (GTYE4_CHANNEL_RXCHBONDO               [((ch+1)*  5)-1:(ch*  5)]),
        .RXCKCALDONE                  (GTYE4_CHANNEL_RXCKCALDONE             [((ch+1)*  1)-1:(ch*  1)]),
        .RXCLKCORCNT                  (GTYE4_CHANNEL_RXCLKCORCNT             [((ch+1)*  2)-1:(ch*  2)]),
        .RXCOMINITDET                 (GTYE4_CHANNEL_RXCOMINITDET            [((ch+1)*  1)-1:(ch*  1)]),
        .RXCOMMADET                   (GTYE4_CHANNEL_RXCOMMADET              [((ch+1)*  1)-1:(ch*  1)]),
        .RXCOMSASDET                  (GTYE4_CHANNEL_RXCOMSASDET             [((ch+1)*  1)-1:(ch*  1)]),
        .RXCOMWAKEDET                 (GTYE4_CHANNEL_RXCOMWAKEDET            [((ch+1)*  1)-1:(ch*  1)]),
        .RXCTRL0                      (GTYE4_CHANNEL_RXCTRL0                 [((ch+1)* 16)-1:(ch* 16)]),
        .RXCTRL1                      (GTYE4_CHANNEL_RXCTRL1                 [((ch+1)* 16)-1:(ch* 16)]),
        .RXCTRL2                      (GTYE4_CHANNEL_RXCTRL2                 [((ch+1)*  8)-1:(ch*  8)]),
        .RXCTRL3                      (GTYE4_CHANNEL_RXCTRL3                 [((ch+1)*  8)-1:(ch*  8)]),
        .RXDATA                       (GTYE4_CHANNEL_RXDATA                  [((ch+1)*128)-1:(ch*128)]),
        .RXDATAEXTENDRSVD             (GTYE4_CHANNEL_RXDATAEXTENDRSVD        [((ch+1)*  8)-1:(ch*  8)]),
        .RXDATAVALID                  (GTYE4_CHANNEL_RXDATAVALID             [((ch+1)*  2)-1:(ch*  2)]),
        .RXDLYSRESETDONE              (GTYE4_CHANNEL_RXDLYSRESETDONE         [((ch+1)*  1)-1:(ch*  1)]),
        .RXELECIDLE                   (GTYE4_CHANNEL_RXELECIDLE              [((ch+1)*  1)-1:(ch*  1)]),
        .RXHEADER                     (GTYE4_CHANNEL_RXHEADER                [((ch+1)*  6)-1:(ch*  6)]),
        .RXHEADERVALID                (GTYE4_CHANNEL_RXHEADERVALID           [((ch+1)*  2)-1:(ch*  2)]),
        .RXLFPSTRESETDET              (GTYE4_CHANNEL_RXLFPSTRESETDET         [((ch+1)*  1)-1:(ch*  1)]),
        .RXLFPSU2LPEXITDET            (GTYE4_CHANNEL_RXLFPSU2LPEXITDET       [((ch+1)*  1)-1:(ch*  1)]),
        .RXLFPSU3WAKEDET              (GTYE4_CHANNEL_RXLFPSU3WAKEDET         [((ch+1)*  1)-1:(ch*  1)]),
        .RXMONITOROUT                 (GTYE4_CHANNEL_RXMONITOROUT            [((ch+1)*  8)-1:(ch*  8)]),
        .RXOSINTDONE                  (GTYE4_CHANNEL_RXOSINTDONE             [((ch+1)*  1)-1:(ch*  1)]),
        .RXOSINTSTARTED               (GTYE4_CHANNEL_RXOSINTSTARTED          [((ch+1)*  1)-1:(ch*  1)]),
        .RXOSINTSTROBEDONE            (GTYE4_CHANNEL_RXOSINTSTROBEDONE       [((ch+1)*  1)-1:(ch*  1)]),
        .RXOSINTSTROBESTARTED         (GTYE4_CHANNEL_RXOSINTSTROBESTARTED    [((ch+1)*  1)-1:(ch*  1)]),
        .RXOUTCLK                     (GTYE4_CHANNEL_RXOUTCLK                [((ch+1)*  1)-1:(ch*  1)]),
        .RXOUTCLKFABRIC               (GTYE4_CHANNEL_RXOUTCLKFABRIC          [((ch+1)*  1)-1:(ch*  1)]),
        .RXOUTCLKPCS                  (GTYE4_CHANNEL_RXOUTCLKPCS             [((ch+1)*  1)-1:(ch*  1)]),
        .RXPHALIGNDONE                (GTYE4_CHANNEL_RXPHALIGNDONE           [((ch+1)*  1)-1:(ch*  1)]),
        .RXPHALIGNERR                 (GTYE4_CHANNEL_RXPHALIGNERR            [((ch+1)*  1)-1:(ch*  1)]),
        .RXPMARESETDONE               (GTYE4_CHANNEL_RXPMARESETDONE          [((ch+1)*  1)-1:(ch*  1)]),
        .RXPRBSERR                    (GTYE4_CHANNEL_RXPRBSERR               [((ch+1)*  1)-1:(ch*  1)]),
        .RXPRBSLOCKED                 (GTYE4_CHANNEL_RXPRBSLOCKED            [((ch+1)*  1)-1:(ch*  1)]),
        .RXPRGDIVRESETDONE            (GTYE4_CHANNEL_RXPRGDIVRESETDONE       [((ch+1)*  1)-1:(ch*  1)]),
        .RXRATEDONE                   (GTYE4_CHANNEL_RXRATEDONE              [((ch+1)*  1)-1:(ch*  1)]),
        .RXRECCLKOUT                  (GTYE4_CHANNEL_RXRECCLKOUT             [((ch+1)*  1)-1:(ch*  1)]),
        .RXRESETDONE                  (GTYE4_CHANNEL_RXRESETDONE             [((ch+1)*  1)-1:(ch*  1)]),
        .RXSLIDERDY                   (GTYE4_CHANNEL_RXSLIDERDY              [((ch+1)*  1)-1:(ch*  1)]),
        .RXSLIPDONE                   (GTYE4_CHANNEL_RXSLIPDONE              [((ch+1)*  1)-1:(ch*  1)]),
        .RXSLIPOUTCLKRDY              (GTYE4_CHANNEL_RXSLIPOUTCLKRDY         [((ch+1)*  1)-1:(ch*  1)]),
        .RXSLIPPMARDY                 (GTYE4_CHANNEL_RXSLIPPMARDY            [((ch+1)*  1)-1:(ch*  1)]),
        .RXSTARTOFSEQ                 (GTYE4_CHANNEL_RXSTARTOFSEQ            [((ch+1)*  2)-1:(ch*  2)]),
        .RXSTATUS                     (GTYE4_CHANNEL_RXSTATUS                [((ch+1)*  3)-1:(ch*  3)]),
        .RXSYNCDONE                   (GTYE4_CHANNEL_RXSYNCDONE              [((ch+1)*  1)-1:(ch*  1)]),
        .RXSYNCOUT                    (GTYE4_CHANNEL_RXSYNCOUT               [((ch+1)*  1)-1:(ch*  1)]),
        .RXVALID                      (GTYE4_CHANNEL_RXVALID                 [((ch+1)*  1)-1:(ch*  1)]),
        .TXBUFSTATUS                  (GTYE4_CHANNEL_TXBUFSTATUS             [((ch+1)*  2)-1:(ch*  2)]),
        .TXCOMFINISH                  (GTYE4_CHANNEL_TXCOMFINISH             [((ch+1)*  1)-1:(ch*  1)]),
        .TXDCCDONE                    (GTYE4_CHANNEL_TXDCCDONE               [((ch+1)*  1)-1:(ch*  1)]),
        .TXDLYSRESETDONE              (GTYE4_CHANNEL_TXDLYSRESETDONE         [((ch+1)*  1)-1:(ch*  1)]),
        .TXOUTCLK                     (GTYE4_CHANNEL_TXOUTCLK                [((ch+1)*  1)-1:(ch*  1)]),
        .TXOUTCLKFABRIC               (GTYE4_CHANNEL_TXOUTCLKFABRIC          [((ch+1)*  1)-1:(ch*  1)]),
        .TXOUTCLKPCS                  (GTYE4_CHANNEL_TXOUTCLKPCS             [((ch+1)*  1)-1:(ch*  1)]),
        .TXPHALIGNDONE                (GTYE4_CHANNEL_TXPHALIGNDONE           [((ch+1)*  1)-1:(ch*  1)]),
        .TXPHINITDONE                 (GTYE4_CHANNEL_TXPHINITDONE            [((ch+1)*  1)-1:(ch*  1)]),
        .TXPMARESETDONE               (GTYE4_CHANNEL_TXPMARESETDONE          [((ch+1)*  1)-1:(ch*  1)]),
        .TXPRGDIVRESETDONE            (GTYE4_CHANNEL_TXPRGDIVRESETDONE       [((ch+1)*  1)-1:(ch*  1)]),
        .TXRATEDONE                   (GTYE4_CHANNEL_TXRATEDONE              [((ch+1)*  1)-1:(ch*  1)]),
        .TXRESETDONE                  (GTYE4_CHANNEL_TXRESETDONE             [((ch+1)*  1)-1:(ch*  1)]),
        .TXSYNCDONE                   (GTYE4_CHANNEL_TXSYNCDONE              [((ch+1)*  1)-1:(ch*  1)]),
        .TXSYNCOUT                    (GTYE4_CHANNEL_TXSYNCOUT               [((ch+1)*  1)-1:(ch*  1)])
      );
    end

  end
  endgenerate


endmodule
