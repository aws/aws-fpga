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

module gtwizard_ultrascale_v1_7_18_gtye4_common #(


  // -------------------------------------------------------------------------------------------------------------------
  // Parameters relating to GTYE4_COMMON primitive
  // -------------------------------------------------------------------------------------------------------------------

  // primitive wrapper parameters which override corresponding GTYE4_COMMON primitive parameters
  parameter   [0:0] GTYE4_COMMON_AEN_QPLL0_FBDIV = 1'b1,
  parameter   [0:0] GTYE4_COMMON_AEN_QPLL1_FBDIV = 1'b1,
  parameter   [0:0] GTYE4_COMMON_AEN_SDM0TOGGLE = 1'b0,
  parameter   [0:0] GTYE4_COMMON_AEN_SDM1TOGGLE = 1'b0,
  parameter   [0:0] GTYE4_COMMON_A_SDM0TOGGLE = 1'b0,
  parameter   [8:0] GTYE4_COMMON_A_SDM1DATA_HIGH = 9'b000000000,
  parameter  [15:0] GTYE4_COMMON_A_SDM1DATA_LOW = 16'b0000000000000000,
  parameter   [0:0] GTYE4_COMMON_A_SDM1TOGGLE = 1'b0,
  parameter  [15:0] GTYE4_COMMON_BIAS_CFG0 = 16'h0000,
  parameter  [15:0] GTYE4_COMMON_BIAS_CFG1 = 16'h0000,
  parameter  [15:0] GTYE4_COMMON_BIAS_CFG2 = 16'h0000,
  parameter  [15:0] GTYE4_COMMON_BIAS_CFG3 = 16'h0000,
  parameter  [15:0] GTYE4_COMMON_BIAS_CFG4 = 16'h0000,
  parameter  [15:0] GTYE4_COMMON_BIAS_CFG_RSVD = 16'h0000,
  parameter  [15:0] GTYE4_COMMON_COMMON_CFG0 = 16'h0000,
  parameter  [15:0] GTYE4_COMMON_COMMON_CFG1 = 16'h0000,
  parameter  [15:0] GTYE4_COMMON_POR_CFG = 16'h0000,
  parameter  [15:0] GTYE4_COMMON_PPF0_CFG = 16'h0F00,
  parameter  [15:0] GTYE4_COMMON_PPF1_CFG = 16'h0F00,
  parameter         GTYE4_COMMON_QPLL0CLKOUT_RATE = "FULL",
  parameter  [15:0] GTYE4_COMMON_QPLL0_CFG0 = 16'h391C,
  parameter  [15:0] GTYE4_COMMON_QPLL0_CFG1 = 16'h0000,
  parameter  [15:0] GTYE4_COMMON_QPLL0_CFG1_G3 = 16'h0020,
  parameter  [15:0] GTYE4_COMMON_QPLL0_CFG2 = 16'h0F80,
  parameter  [15:0] GTYE4_COMMON_QPLL0_CFG2_G3 = 16'h0F80,
  parameter  [15:0] GTYE4_COMMON_QPLL0_CFG3 = 16'h0120,
  parameter  [15:0] GTYE4_COMMON_QPLL0_CFG4 = 16'h0002,
  parameter   [9:0] GTYE4_COMMON_QPLL0_CP = 10'b0000011111,
  parameter   [9:0] GTYE4_COMMON_QPLL0_CP_G3 = 10'b0000011111,
  parameter integer GTYE4_COMMON_QPLL0_FBDIV = 66,
  parameter integer GTYE4_COMMON_QPLL0_FBDIV_G3 = 80,
  parameter  [15:0] GTYE4_COMMON_QPLL0_INIT_CFG0 = 16'h0000,
  parameter   [7:0] GTYE4_COMMON_QPLL0_INIT_CFG1 = 8'h00,
  parameter  [15:0] GTYE4_COMMON_QPLL0_LOCK_CFG = 16'h01E8,
  parameter  [15:0] GTYE4_COMMON_QPLL0_LOCK_CFG_G3 = 16'h21E8,
  parameter   [9:0] GTYE4_COMMON_QPLL0_LPF = 10'b1011111111,
  parameter   [9:0] GTYE4_COMMON_QPLL0_LPF_G3 = 10'b1111111111,
  parameter   [0:0] GTYE4_COMMON_QPLL0_PCI_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_QPLL0_RATE_SW_USE_DRP = 1'b0,
  parameter integer GTYE4_COMMON_QPLL0_REFCLK_DIV = 1,
  parameter  [15:0] GTYE4_COMMON_QPLL0_SDM_CFG0 = 16'h0040,
  parameter  [15:0] GTYE4_COMMON_QPLL0_SDM_CFG1 = 16'h0000,
  parameter  [15:0] GTYE4_COMMON_QPLL0_SDM_CFG2 = 16'h0000,
  parameter         GTYE4_COMMON_QPLL1CLKOUT_RATE = "FULL",
  parameter  [15:0] GTYE4_COMMON_QPLL1_CFG0 = 16'h691C,
  parameter  [15:0] GTYE4_COMMON_QPLL1_CFG1 = 16'h0020,
  parameter  [15:0] GTYE4_COMMON_QPLL1_CFG1_G3 = 16'h0020,
  parameter  [15:0] GTYE4_COMMON_QPLL1_CFG2 = 16'h0F80,
  parameter  [15:0] GTYE4_COMMON_QPLL1_CFG2_G3 = 16'h0F80,
  parameter  [15:0] GTYE4_COMMON_QPLL1_CFG3 = 16'h0120,
  parameter  [15:0] GTYE4_COMMON_QPLL1_CFG4 = 16'h0002,
  parameter   [9:0] GTYE4_COMMON_QPLL1_CP = 10'b0000011111,
  parameter   [9:0] GTYE4_COMMON_QPLL1_CP_G3 = 10'b0000011111,
  parameter integer GTYE4_COMMON_QPLL1_FBDIV = 66,
  parameter integer GTYE4_COMMON_QPLL1_FBDIV_G3 = 80,
  parameter  [15:0] GTYE4_COMMON_QPLL1_INIT_CFG0 = 16'h0000,
  parameter   [7:0] GTYE4_COMMON_QPLL1_INIT_CFG1 = 8'h00,
  parameter  [15:0] GTYE4_COMMON_QPLL1_LOCK_CFG = 16'h01E8,
  parameter  [15:0] GTYE4_COMMON_QPLL1_LOCK_CFG_G3 = 16'h21E8,
  parameter   [9:0] GTYE4_COMMON_QPLL1_LPF = 10'b1011111111,
  parameter   [9:0] GTYE4_COMMON_QPLL1_LPF_G3 = 10'b1111111111,
  parameter   [0:0] GTYE4_COMMON_QPLL1_PCI_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_QPLL1_RATE_SW_USE_DRP = 1'b0,
  parameter integer GTYE4_COMMON_QPLL1_REFCLK_DIV = 1,
  parameter  [15:0] GTYE4_COMMON_QPLL1_SDM_CFG0 = 16'h0000,
  parameter  [15:0] GTYE4_COMMON_QPLL1_SDM_CFG1 = 16'h0000,
  parameter  [15:0] GTYE4_COMMON_QPLL1_SDM_CFG2 = 16'h0000,
  parameter  [15:0] GTYE4_COMMON_RSVD_ATTR0 = 16'h0000,
  parameter  [15:0] GTYE4_COMMON_RSVD_ATTR1 = 16'h0000,
  parameter  [15:0] GTYE4_COMMON_RSVD_ATTR2 = 16'h0000,
  parameter  [15:0] GTYE4_COMMON_RSVD_ATTR3 = 16'h0000,
  parameter   [1:0] GTYE4_COMMON_RXRECCLKOUT0_SEL = 2'b00,
  parameter   [1:0] GTYE4_COMMON_RXRECCLKOUT1_SEL = 2'b00,
  parameter   [0:0] GTYE4_COMMON_SARC_ENB = 1'b0,
  parameter   [0:0] GTYE4_COMMON_SARC_SEL = 1'b0,
  parameter  [15:0] GTYE4_COMMON_SDM0INITSEED0_0 = 16'b0000000000000000,
  parameter   [8:0] GTYE4_COMMON_SDM0INITSEED0_1 = 9'b000000000,
  parameter  [15:0] GTYE4_COMMON_SDM1INITSEED0_0 = 16'b0000000000000000,
  parameter   [8:0] GTYE4_COMMON_SDM1INITSEED0_1 = 9'b000000000,
  parameter         GTYE4_COMMON_SIM_MODE = "FAST",
  parameter         GTYE4_COMMON_SIM_RESET_SPEEDUP = "TRUE",
  parameter         GTYE4_COMMON_SIM_DEVICE  = "ULTRASCALE_PLUS",
  parameter  [15:0] GTYE4_COMMON_UB_CFG0 = 16'h0000,
  parameter  [15:0] GTYE4_COMMON_UB_CFG1 = 16'h0000,
  parameter  [15:0] GTYE4_COMMON_UB_CFG2 = 16'h0000,
  parameter  [15:0] GTYE4_COMMON_UB_CFG3 = 16'h0000,
  parameter  [15:0] GTYE4_COMMON_UB_CFG4 = 16'h0000,
  parameter  [15:0] GTYE4_COMMON_UB_CFG5 = 16'h0400,
  parameter  [15:0] GTYE4_COMMON_UB_CFG6 = 16'h0000,

  // primitive wrapper parameters which specify GTYE4_COMMON primitive input port default driver values
  parameter   [0:0] GTYE4_COMMON_BGBYPASSB_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_BGMONITORENB_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_BGPDB_VAL = 1'b0,
  parameter   [4:0] GTYE4_COMMON_BGRCALOVRD_VAL = 5'b0,
  parameter   [0:0] GTYE4_COMMON_BGRCALOVRDENB_VAL = 1'b0,
  parameter  [15:0] GTYE4_COMMON_DRPADDR_VAL = 16'b0,
  parameter   [0:0] GTYE4_COMMON_DRPCLK_VAL = 1'b0,
  parameter  [15:0] GTYE4_COMMON_DRPDI_VAL = 16'b0,
  parameter   [0:0] GTYE4_COMMON_DRPEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_DRPWE_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_GTGREFCLK0_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_GTGREFCLK1_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_GTNORTHREFCLK00_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_GTNORTHREFCLK01_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_GTNORTHREFCLK10_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_GTNORTHREFCLK11_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_GTREFCLK00_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_GTREFCLK01_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_GTREFCLK10_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_GTREFCLK11_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_GTSOUTHREFCLK00_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_GTSOUTHREFCLK01_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_GTSOUTHREFCLK10_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_GTSOUTHREFCLK11_VAL = 1'b0,
  parameter   [2:0] GTYE4_COMMON_PCIERATEQPLL0_VAL = 3'b0,
  parameter   [2:0] GTYE4_COMMON_PCIERATEQPLL1_VAL = 3'b0,
  parameter   [7:0] GTYE4_COMMON_PMARSVD0_VAL = 8'b0,
  parameter   [7:0] GTYE4_COMMON_PMARSVD1_VAL = 8'b0,
  parameter   [0:0] GTYE4_COMMON_QPLL0CLKRSVD0_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_QPLL0CLKRSVD1_VAL = 1'b0,
  parameter   [7:0] GTYE4_COMMON_QPLL0FBDIV_VAL = 8'b0,
  parameter   [0:0] GTYE4_COMMON_QPLL0LOCKDETCLK_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_QPLL0LOCKEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_QPLL0PD_VAL = 1'b0,
  parameter   [2:0] GTYE4_COMMON_QPLL0REFCLKSEL_VAL = 3'b0,
  parameter   [0:0] GTYE4_COMMON_QPLL0RESET_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_QPLL1CLKRSVD0_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_QPLL1CLKRSVD1_VAL = 1'b0,
  parameter   [7:0] GTYE4_COMMON_QPLL1FBDIV_VAL = 8'b0,
  parameter   [0:0] GTYE4_COMMON_QPLL1LOCKDETCLK_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_QPLL1LOCKEN_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_QPLL1PD_VAL = 1'b0,
  parameter   [2:0] GTYE4_COMMON_QPLL1REFCLKSEL_VAL = 3'b0,
  parameter   [0:0] GTYE4_COMMON_QPLL1RESET_VAL = 1'b0,
  parameter   [7:0] GTYE4_COMMON_QPLLRSVD1_VAL = 8'b0,
  parameter   [4:0] GTYE4_COMMON_QPLLRSVD2_VAL = 5'b0,
  parameter   [4:0] GTYE4_COMMON_QPLLRSVD3_VAL = 5'b0,
  parameter   [7:0] GTYE4_COMMON_QPLLRSVD4_VAL = 8'b0,
  parameter   [0:0] GTYE4_COMMON_RCALENB_VAL = 1'b0,
  parameter  [24:0] GTYE4_COMMON_SDM0DATA_VAL = 25'b0,
  parameter   [0:0] GTYE4_COMMON_SDM0RESET_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_SDM0TOGGLE_VAL = 1'b0,
  parameter   [1:0] GTYE4_COMMON_SDM0WIDTH_VAL = 2'b0,
  parameter  [24:0] GTYE4_COMMON_SDM1DATA_VAL = 25'b0,
  parameter   [0:0] GTYE4_COMMON_SDM1RESET_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_SDM1TOGGLE_VAL = 1'b0,
  parameter   [1:0] GTYE4_COMMON_SDM1WIDTH_VAL = 2'b0,
  parameter   [0:0] GTYE4_COMMON_UBCFGSTREAMEN_VAL = 1'b0,
  parameter  [15:0] GTYE4_COMMON_UBDO_VAL = 16'b0,
  parameter   [0:0] GTYE4_COMMON_UBDRDY_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_UBENABLE_VAL = 1'b0,
  parameter   [1:0] GTYE4_COMMON_UBGPI_VAL = 2'b0,
  parameter   [1:0] GTYE4_COMMON_UBINTR_VAL = 2'b0,
  parameter   [0:0] GTYE4_COMMON_UBIOLMBRST_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_UBMBRST_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_UBMDMCAPTURE_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_UBMDMDBGRST_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_UBMDMDBGUPDATE_VAL = 1'b0,
  parameter   [3:0] GTYE4_COMMON_UBMDMREGEN_VAL = 4'b0,
  parameter   [0:0] GTYE4_COMMON_UBMDMSHIFT_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_UBMDMSYSRST_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_UBMDMTCK_VAL = 1'b0,
  parameter   [0:0] GTYE4_COMMON_UBMDMTDI_VAL = 1'b0,

  // primitive wrapper parameters which control GTYE4_COMMON primitive input port tie-off enablement
  parameter   [0:0] GTYE4_COMMON_BGBYPASSB_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_BGMONITORENB_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_BGPDB_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_BGRCALOVRD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_BGRCALOVRDENB_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_DRPADDR_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_DRPCLK_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_DRPDI_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_DRPEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_DRPWE_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_GTGREFCLK0_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_GTGREFCLK1_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_GTNORTHREFCLK00_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_GTNORTHREFCLK01_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_GTNORTHREFCLK10_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_GTNORTHREFCLK11_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_GTREFCLK00_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_GTREFCLK01_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_GTREFCLK10_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_GTREFCLK11_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_GTSOUTHREFCLK00_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_GTSOUTHREFCLK01_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_GTSOUTHREFCLK10_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_GTSOUTHREFCLK11_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_PCIERATEQPLL0_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_PCIERATEQPLL1_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_PMARSVD0_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_PMARSVD1_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_QPLL0CLKRSVD0_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_QPLL0CLKRSVD1_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_QPLL0FBDIV_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_QPLL0LOCKDETCLK_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_QPLL0LOCKEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_QPLL0PD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_QPLL0REFCLKSEL_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_QPLL0RESET_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_QPLL1CLKRSVD0_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_QPLL1CLKRSVD1_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_QPLL1FBDIV_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_QPLL1LOCKDETCLK_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_QPLL1LOCKEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_QPLL1PD_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_QPLL1REFCLKSEL_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_QPLL1RESET_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_QPLLRSVD1_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_QPLLRSVD2_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_QPLLRSVD3_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_QPLLRSVD4_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_RCALENB_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_SDM0DATA_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_SDM0RESET_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_SDM0TOGGLE_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_SDM0WIDTH_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_SDM1DATA_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_SDM1RESET_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_SDM1TOGGLE_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_SDM1WIDTH_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_UBCFGSTREAMEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_UBDO_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_UBDRDY_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_UBENABLE_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_UBGPI_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_UBINTR_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_UBIOLMBRST_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_UBMBRST_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_UBMDMCAPTURE_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_UBMDMDBGRST_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_UBMDMDBGUPDATE_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_UBMDMREGEN_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_UBMDMSHIFT_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_UBMDMSYSRST_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_UBMDMTCK_TIE_EN = 1'b0,
  parameter   [0:0] GTYE4_COMMON_UBMDMTDI_TIE_EN = 1'b0

)(


  // -------------------------------------------------------------------------------------------------------------------
  // Ports relating to GTYE4_COMMON primitive
  // -------------------------------------------------------------------------------------------------------------------

  // primitive wrapper input ports which can drive corresponding GTYE4_COMMON primitive input ports
  input  wire [ 0:0] GTYE4_COMMON_BGBYPASSB,
  input  wire [ 0:0] GTYE4_COMMON_BGMONITORENB,
  input  wire [ 0:0] GTYE4_COMMON_BGPDB,
  input  wire [ 4:0] GTYE4_COMMON_BGRCALOVRD,
  input  wire [ 0:0] GTYE4_COMMON_BGRCALOVRDENB,
  input  wire [15:0] GTYE4_COMMON_DRPADDR,
  input  wire [ 0:0] GTYE4_COMMON_DRPCLK,
  input  wire [15:0] GTYE4_COMMON_DRPDI,
  input  wire [ 0:0] GTYE4_COMMON_DRPEN,
  input  wire [ 0:0] GTYE4_COMMON_DRPWE,
  input  wire [ 0:0] GTYE4_COMMON_GTGREFCLK0,
  input  wire [ 0:0] GTYE4_COMMON_GTGREFCLK1,
  input  wire [ 0:0] GTYE4_COMMON_GTNORTHREFCLK00,
  input  wire [ 0:0] GTYE4_COMMON_GTNORTHREFCLK01,
  input  wire [ 0:0] GTYE4_COMMON_GTNORTHREFCLK10,
  input  wire [ 0:0] GTYE4_COMMON_GTNORTHREFCLK11,
  input  wire [ 0:0] GTYE4_COMMON_GTREFCLK00,
  input  wire [ 0:0] GTYE4_COMMON_GTREFCLK01,
  input  wire [ 0:0] GTYE4_COMMON_GTREFCLK10,
  input  wire [ 0:0] GTYE4_COMMON_GTREFCLK11,
  input  wire [ 0:0] GTYE4_COMMON_GTSOUTHREFCLK00,
  input  wire [ 0:0] GTYE4_COMMON_GTSOUTHREFCLK01,
  input  wire [ 0:0] GTYE4_COMMON_GTSOUTHREFCLK10,
  input  wire [ 0:0] GTYE4_COMMON_GTSOUTHREFCLK11,
  input  wire [ 2:0] GTYE4_COMMON_PCIERATEQPLL0,
  input  wire [ 2:0] GTYE4_COMMON_PCIERATEQPLL1,
  input  wire [ 7:0] GTYE4_COMMON_PMARSVD0,
  input  wire [ 7:0] GTYE4_COMMON_PMARSVD1,
  input  wire [ 0:0] GTYE4_COMMON_QPLL0CLKRSVD0,
  input  wire [ 0:0] GTYE4_COMMON_QPLL0CLKRSVD1,
  input  wire [ 7:0] GTYE4_COMMON_QPLL0FBDIV,
  input  wire [ 0:0] GTYE4_COMMON_QPLL0LOCKDETCLK,
  input  wire [ 0:0] GTYE4_COMMON_QPLL0LOCKEN,
  input  wire [ 0:0] GTYE4_COMMON_QPLL0PD,
  input  wire [ 2:0] GTYE4_COMMON_QPLL0REFCLKSEL,
  input  wire [ 0:0] GTYE4_COMMON_QPLL0RESET,
  input  wire [ 0:0] GTYE4_COMMON_QPLL1CLKRSVD0,
  input  wire [ 0:0] GTYE4_COMMON_QPLL1CLKRSVD1,
  input  wire [ 7:0] GTYE4_COMMON_QPLL1FBDIV,
  input  wire [ 0:0] GTYE4_COMMON_QPLL1LOCKDETCLK,
  input  wire [ 0:0] GTYE4_COMMON_QPLL1LOCKEN,
  input  wire [ 0:0] GTYE4_COMMON_QPLL1PD,
  input  wire [ 2:0] GTYE4_COMMON_QPLL1REFCLKSEL,
  input  wire [ 0:0] GTYE4_COMMON_QPLL1RESET,
  input  wire [ 7:0] GTYE4_COMMON_QPLLRSVD1,
  input  wire [ 4:0] GTYE4_COMMON_QPLLRSVD2,
  input  wire [ 4:0] GTYE4_COMMON_QPLLRSVD3,
  input  wire [ 7:0] GTYE4_COMMON_QPLLRSVD4,
  input  wire [ 0:0] GTYE4_COMMON_RCALENB,
  input  wire [24:0] GTYE4_COMMON_SDM0DATA,
  input  wire [ 0:0] GTYE4_COMMON_SDM0RESET,
  input  wire [ 0:0] GTYE4_COMMON_SDM0TOGGLE,
  input  wire [ 1:0] GTYE4_COMMON_SDM0WIDTH,
  input  wire [24:0] GTYE4_COMMON_SDM1DATA,
  input  wire [ 0:0] GTYE4_COMMON_SDM1RESET,
  input  wire [ 0:0] GTYE4_COMMON_SDM1TOGGLE,
  input  wire [ 1:0] GTYE4_COMMON_SDM1WIDTH,
  input  wire [ 0:0] GTYE4_COMMON_UBCFGSTREAMEN,
  input  wire [15:0] GTYE4_COMMON_UBDO,
  input  wire [ 0:0] GTYE4_COMMON_UBDRDY,
  input  wire [ 0:0] GTYE4_COMMON_UBENABLE,
  input  wire [ 1:0] GTYE4_COMMON_UBGPI,
  input  wire [ 1:0] GTYE4_COMMON_UBINTR,
  input  wire [ 0:0] GTYE4_COMMON_UBIOLMBRST,
  input  wire [ 0:0] GTYE4_COMMON_UBMBRST,
  input  wire [ 0:0] GTYE4_COMMON_UBMDMCAPTURE,
  input  wire [ 0:0] GTYE4_COMMON_UBMDMDBGRST,
  input  wire [ 0:0] GTYE4_COMMON_UBMDMDBGUPDATE,
  input  wire [ 3:0] GTYE4_COMMON_UBMDMREGEN,
  input  wire [ 0:0] GTYE4_COMMON_UBMDMSHIFT,
  input  wire [ 0:0] GTYE4_COMMON_UBMDMSYSRST,
  input  wire [ 0:0] GTYE4_COMMON_UBMDMTCK,
  input  wire [ 0:0] GTYE4_COMMON_UBMDMTDI,

  // primitive wrapper output ports which are driven by corresponding GTYE4_COMMON primitive output ports
  output wire [15:0] GTYE4_COMMON_DRPDO,
  output wire [ 0:0] GTYE4_COMMON_DRPRDY,
  output wire [ 7:0] GTYE4_COMMON_PMARSVDOUT0,
  output wire [ 7:0] GTYE4_COMMON_PMARSVDOUT1,
  output wire [ 0:0] GTYE4_COMMON_QPLL0FBCLKLOST,
  output wire [ 0:0] GTYE4_COMMON_QPLL0LOCK,
  output wire [ 0:0] GTYE4_COMMON_QPLL0OUTCLK,
  output wire [ 0:0] GTYE4_COMMON_QPLL0OUTREFCLK,
  output wire [ 0:0] GTYE4_COMMON_QPLL0REFCLKLOST,
  output wire [ 0:0] GTYE4_COMMON_QPLL1FBCLKLOST,
  output wire [ 0:0] GTYE4_COMMON_QPLL1LOCK,
  output wire [ 0:0] GTYE4_COMMON_QPLL1OUTCLK,
  output wire [ 0:0] GTYE4_COMMON_QPLL1OUTREFCLK,
  output wire [ 0:0] GTYE4_COMMON_QPLL1REFCLKLOST,
  output wire [ 7:0] GTYE4_COMMON_QPLLDMONITOR0,
  output wire [ 7:0] GTYE4_COMMON_QPLLDMONITOR1,
  output wire [ 0:0] GTYE4_COMMON_REFCLKOUTMONITOR0,
  output wire [ 0:0] GTYE4_COMMON_REFCLKOUTMONITOR1,
  output wire [ 1:0] GTYE4_COMMON_RXRECCLK0SEL,
  output wire [ 1:0] GTYE4_COMMON_RXRECCLK1SEL,
  output wire [ 3:0] GTYE4_COMMON_SDM0FINALOUT,
  output wire [14:0] GTYE4_COMMON_SDM0TESTDATA,
  output wire [ 3:0] GTYE4_COMMON_SDM1FINALOUT,
  output wire [14:0] GTYE4_COMMON_SDM1TESTDATA,
  output wire [15:0] GTYE4_COMMON_UBDADDR,
  output wire [ 0:0] GTYE4_COMMON_UBDEN,
  output wire [15:0] GTYE4_COMMON_UBDI,
  output wire [ 0:0] GTYE4_COMMON_UBDWE,
  output wire [ 0:0] GTYE4_COMMON_UBMDMTDO,
  output wire [ 0:0] GTYE4_COMMON_UBRSVDOUT,
  output wire [ 0:0] GTYE4_COMMON_UBTXUART

);


  // -------------------------------------------------------------------------------------------------------------------
  // HDL generation of wiring and instances relating to GTYE4_COMMON primitive
  // -------------------------------------------------------------------------------------------------------------------

  generate if (1) begin : gtye4_common_gen

    // for each GTYE4_COMMON primitive input port, declare a properly-sized vector
    wire [ 0:0] GTYE4_COMMON_BGBYPASSB_int;
    wire [ 0:0] GTYE4_COMMON_BGMONITORENB_int;
    wire [ 0:0] GTYE4_COMMON_BGPDB_int;
    wire [ 4:0] GTYE4_COMMON_BGRCALOVRD_int;
    wire [ 0:0] GTYE4_COMMON_BGRCALOVRDENB_int;
    wire [15:0] GTYE4_COMMON_DRPADDR_int;
    wire [ 0:0] GTYE4_COMMON_DRPCLK_int;
    wire [15:0] GTYE4_COMMON_DRPDI_int;
    wire [ 0:0] GTYE4_COMMON_DRPEN_int;
    wire [ 0:0] GTYE4_COMMON_DRPWE_int;
    wire [ 0:0] GTYE4_COMMON_GTGREFCLK0_int;
    wire [ 0:0] GTYE4_COMMON_GTGREFCLK1_int;
    wire [ 0:0] GTYE4_COMMON_GTNORTHREFCLK00_int;
    wire [ 0:0] GTYE4_COMMON_GTNORTHREFCLK01_int;
    wire [ 0:0] GTYE4_COMMON_GTNORTHREFCLK10_int;
    wire [ 0:0] GTYE4_COMMON_GTNORTHREFCLK11_int;
    wire [ 0:0] GTYE4_COMMON_GTREFCLK00_int;
    wire [ 0:0] GTYE4_COMMON_GTREFCLK01_int;
    wire [ 0:0] GTYE4_COMMON_GTREFCLK10_int;
    wire [ 0:0] GTYE4_COMMON_GTREFCLK11_int;
    wire [ 0:0] GTYE4_COMMON_GTSOUTHREFCLK00_int;
    wire [ 0:0] GTYE4_COMMON_GTSOUTHREFCLK01_int;
    wire [ 0:0] GTYE4_COMMON_GTSOUTHREFCLK10_int;
    wire [ 0:0] GTYE4_COMMON_GTSOUTHREFCLK11_int;
    wire [ 2:0] GTYE4_COMMON_PCIERATEQPLL0_int;
    wire [ 2:0] GTYE4_COMMON_PCIERATEQPLL1_int;
    wire [ 7:0] GTYE4_COMMON_PMARSVD0_int;
    wire [ 7:0] GTYE4_COMMON_PMARSVD1_int;
    wire [ 0:0] GTYE4_COMMON_QPLL0CLKRSVD0_int;
    wire [ 0:0] GTYE4_COMMON_QPLL0CLKRSVD1_int;
    wire [ 7:0] GTYE4_COMMON_QPLL0FBDIV_int;
    wire [ 0:0] GTYE4_COMMON_QPLL0LOCKDETCLK_int;
    wire [ 0:0] GTYE4_COMMON_QPLL0LOCKEN_int;
    wire [ 0:0] GTYE4_COMMON_QPLL0PD_int;
    wire [ 2:0] GTYE4_COMMON_QPLL0REFCLKSEL_int;
    wire [ 0:0] GTYE4_COMMON_QPLL0RESET_int;
    wire [ 0:0] GTYE4_COMMON_QPLL1CLKRSVD0_int;
    wire [ 0:0] GTYE4_COMMON_QPLL1CLKRSVD1_int;
    wire [ 7:0] GTYE4_COMMON_QPLL1FBDIV_int;
    wire [ 0:0] GTYE4_COMMON_QPLL1LOCKDETCLK_int;
    wire [ 0:0] GTYE4_COMMON_QPLL1LOCKEN_int;
    wire [ 0:0] GTYE4_COMMON_QPLL1PD_int;
    wire [ 2:0] GTYE4_COMMON_QPLL1REFCLKSEL_int;
    wire [ 0:0] GTYE4_COMMON_QPLL1RESET_int;
    wire [ 7:0] GTYE4_COMMON_QPLLRSVD1_int;
    wire [ 4:0] GTYE4_COMMON_QPLLRSVD2_int;
    wire [ 4:0] GTYE4_COMMON_QPLLRSVD3_int;
    wire [ 7:0] GTYE4_COMMON_QPLLRSVD4_int;
    wire [ 0:0] GTYE4_COMMON_RCALENB_int;
    wire [24:0] GTYE4_COMMON_SDM0DATA_int;
    wire [ 0:0] GTYE4_COMMON_SDM0RESET_int;
    wire [ 0:0] GTYE4_COMMON_SDM0TOGGLE_int;
    wire [ 1:0] GTYE4_COMMON_SDM0WIDTH_int;
    wire [24:0] GTYE4_COMMON_SDM1DATA_int;
    wire [ 0:0] GTYE4_COMMON_SDM1RESET_int;
    wire [ 0:0] GTYE4_COMMON_SDM1TOGGLE_int;
    wire [ 1:0] GTYE4_COMMON_SDM1WIDTH_int;
    wire [ 0:0] GTYE4_COMMON_UBCFGSTREAMEN_int;
    wire [15:0] GTYE4_COMMON_UBDO_int;
    wire [ 0:0] GTYE4_COMMON_UBDRDY_int;
    wire [ 0:0] GTYE4_COMMON_UBENABLE_int;
    wire [ 1:0] GTYE4_COMMON_UBGPI_int;
    wire [ 1:0] GTYE4_COMMON_UBINTR_int;
    wire [ 0:0] GTYE4_COMMON_UBIOLMBRST_int;
    wire [ 0:0] GTYE4_COMMON_UBMBRST_int;
    wire [ 0:0] GTYE4_COMMON_UBMDMCAPTURE_int;
    wire [ 0:0] GTYE4_COMMON_UBMDMDBGRST_int;
    wire [ 0:0] GTYE4_COMMON_UBMDMDBGUPDATE_int;
    wire [ 3:0] GTYE4_COMMON_UBMDMREGEN_int;
    wire [ 0:0] GTYE4_COMMON_UBMDMSHIFT_int;
    wire [ 0:0] GTYE4_COMMON_UBMDMSYSRST_int;
    wire [ 0:0] GTYE4_COMMON_UBMDMTCK_int;
    wire [ 0:0] GTYE4_COMMON_UBMDMTDI_int;

    // assign each vector either the corresponding tie-off value or the corresponding input port
    if (GTYE4_COMMON_BGBYPASSB_TIE_EN == 1'b1)
      assign GTYE4_COMMON_BGBYPASSB_int = GTYE4_COMMON_BGBYPASSB_VAL;
    else
      assign GTYE4_COMMON_BGBYPASSB_int = GTYE4_COMMON_BGBYPASSB;

    if (GTYE4_COMMON_BGMONITORENB_TIE_EN == 1'b1)
      assign GTYE4_COMMON_BGMONITORENB_int = GTYE4_COMMON_BGMONITORENB_VAL;
    else
      assign GTYE4_COMMON_BGMONITORENB_int = GTYE4_COMMON_BGMONITORENB;

    if (GTYE4_COMMON_BGPDB_TIE_EN == 1'b1)
      assign GTYE4_COMMON_BGPDB_int = GTYE4_COMMON_BGPDB_VAL;
    else
      assign GTYE4_COMMON_BGPDB_int = GTYE4_COMMON_BGPDB;

    if (GTYE4_COMMON_BGRCALOVRD_TIE_EN == 1'b1)
      assign GTYE4_COMMON_BGRCALOVRD_int = GTYE4_COMMON_BGRCALOVRD_VAL;
    else
      assign GTYE4_COMMON_BGRCALOVRD_int = GTYE4_COMMON_BGRCALOVRD;

    if (GTYE4_COMMON_BGRCALOVRDENB_TIE_EN == 1'b1)
      assign GTYE4_COMMON_BGRCALOVRDENB_int = GTYE4_COMMON_BGRCALOVRDENB_VAL;
    else
      assign GTYE4_COMMON_BGRCALOVRDENB_int = GTYE4_COMMON_BGRCALOVRDENB;

    if (GTYE4_COMMON_DRPADDR_TIE_EN == 1'b1)
      assign GTYE4_COMMON_DRPADDR_int = GTYE4_COMMON_DRPADDR_VAL;
    else
      assign GTYE4_COMMON_DRPADDR_int = GTYE4_COMMON_DRPADDR;

    if (GTYE4_COMMON_DRPCLK_TIE_EN == 1'b1)
      assign GTYE4_COMMON_DRPCLK_int = GTYE4_COMMON_DRPCLK_VAL;
    else
      assign GTYE4_COMMON_DRPCLK_int = GTYE4_COMMON_DRPCLK;

    if (GTYE4_COMMON_DRPDI_TIE_EN == 1'b1)
      assign GTYE4_COMMON_DRPDI_int = GTYE4_COMMON_DRPDI_VAL;
    else
      assign GTYE4_COMMON_DRPDI_int = GTYE4_COMMON_DRPDI;

    if (GTYE4_COMMON_DRPEN_TIE_EN == 1'b1)
      assign GTYE4_COMMON_DRPEN_int = GTYE4_COMMON_DRPEN_VAL;
    else
      assign GTYE4_COMMON_DRPEN_int = GTYE4_COMMON_DRPEN;

    if (GTYE4_COMMON_DRPWE_TIE_EN == 1'b1)
      assign GTYE4_COMMON_DRPWE_int = GTYE4_COMMON_DRPWE_VAL;
    else
      assign GTYE4_COMMON_DRPWE_int = GTYE4_COMMON_DRPWE;

    if (GTYE4_COMMON_GTGREFCLK0_TIE_EN == 1'b1)
      assign GTYE4_COMMON_GTGREFCLK0_int = GTYE4_COMMON_GTGREFCLK0_VAL;
    else
      assign GTYE4_COMMON_GTGREFCLK0_int = GTYE4_COMMON_GTGREFCLK0;

    if (GTYE4_COMMON_GTGREFCLK1_TIE_EN == 1'b1)
      assign GTYE4_COMMON_GTGREFCLK1_int = GTYE4_COMMON_GTGREFCLK1_VAL;
    else
      assign GTYE4_COMMON_GTGREFCLK1_int = GTYE4_COMMON_GTGREFCLK1;

    if (GTYE4_COMMON_GTNORTHREFCLK00_TIE_EN == 1'b1)
      assign GTYE4_COMMON_GTNORTHREFCLK00_int = GTYE4_COMMON_GTNORTHREFCLK00_VAL;
    else
      assign GTYE4_COMMON_GTNORTHREFCLK00_int = GTYE4_COMMON_GTNORTHREFCLK00;

    if (GTYE4_COMMON_GTNORTHREFCLK01_TIE_EN == 1'b1)
      assign GTYE4_COMMON_GTNORTHREFCLK01_int = GTYE4_COMMON_GTNORTHREFCLK01_VAL;
    else
      assign GTYE4_COMMON_GTNORTHREFCLK01_int = GTYE4_COMMON_GTNORTHREFCLK01;

    if (GTYE4_COMMON_GTNORTHREFCLK10_TIE_EN == 1'b1)
      assign GTYE4_COMMON_GTNORTHREFCLK10_int = GTYE4_COMMON_GTNORTHREFCLK10_VAL;
    else
      assign GTYE4_COMMON_GTNORTHREFCLK10_int = GTYE4_COMMON_GTNORTHREFCLK10;

    if (GTYE4_COMMON_GTNORTHREFCLK11_TIE_EN == 1'b1)
      assign GTYE4_COMMON_GTNORTHREFCLK11_int = GTYE4_COMMON_GTNORTHREFCLK11_VAL;
    else
      assign GTYE4_COMMON_GTNORTHREFCLK11_int = GTYE4_COMMON_GTNORTHREFCLK11;

    if (GTYE4_COMMON_GTREFCLK00_TIE_EN == 1'b1)
      assign GTYE4_COMMON_GTREFCLK00_int = GTYE4_COMMON_GTREFCLK00_VAL;
    else
      assign GTYE4_COMMON_GTREFCLK00_int = GTYE4_COMMON_GTREFCLK00;

    if (GTYE4_COMMON_GTREFCLK01_TIE_EN == 1'b1)
      assign GTYE4_COMMON_GTREFCLK01_int = GTYE4_COMMON_GTREFCLK01_VAL;
    else
      assign GTYE4_COMMON_GTREFCLK01_int = GTYE4_COMMON_GTREFCLK01;

    if (GTYE4_COMMON_GTREFCLK10_TIE_EN == 1'b1)
      assign GTYE4_COMMON_GTREFCLK10_int = GTYE4_COMMON_GTREFCLK10_VAL;
    else
      assign GTYE4_COMMON_GTREFCLK10_int = GTYE4_COMMON_GTREFCLK10;

    if (GTYE4_COMMON_GTREFCLK11_TIE_EN == 1'b1)
      assign GTYE4_COMMON_GTREFCLK11_int = GTYE4_COMMON_GTREFCLK11_VAL;
    else
      assign GTYE4_COMMON_GTREFCLK11_int = GTYE4_COMMON_GTREFCLK11;

    if (GTYE4_COMMON_GTSOUTHREFCLK00_TIE_EN == 1'b1)
      assign GTYE4_COMMON_GTSOUTHREFCLK00_int = GTYE4_COMMON_GTSOUTHREFCLK00_VAL;
    else
      assign GTYE4_COMMON_GTSOUTHREFCLK00_int = GTYE4_COMMON_GTSOUTHREFCLK00;

    if (GTYE4_COMMON_GTSOUTHREFCLK01_TIE_EN == 1'b1)
      assign GTYE4_COMMON_GTSOUTHREFCLK01_int = GTYE4_COMMON_GTSOUTHREFCLK01_VAL;
    else
      assign GTYE4_COMMON_GTSOUTHREFCLK01_int = GTYE4_COMMON_GTSOUTHREFCLK01;

    if (GTYE4_COMMON_GTSOUTHREFCLK10_TIE_EN == 1'b1)
      assign GTYE4_COMMON_GTSOUTHREFCLK10_int = GTYE4_COMMON_GTSOUTHREFCLK10_VAL;
    else
      assign GTYE4_COMMON_GTSOUTHREFCLK10_int = GTYE4_COMMON_GTSOUTHREFCLK10;

    if (GTYE4_COMMON_GTSOUTHREFCLK11_TIE_EN == 1'b1)
      assign GTYE4_COMMON_GTSOUTHREFCLK11_int = GTYE4_COMMON_GTSOUTHREFCLK11_VAL;
    else
      assign GTYE4_COMMON_GTSOUTHREFCLK11_int = GTYE4_COMMON_GTSOUTHREFCLK11;

    if (GTYE4_COMMON_PCIERATEQPLL0_TIE_EN == 1'b1)
      assign GTYE4_COMMON_PCIERATEQPLL0_int = GTYE4_COMMON_PCIERATEQPLL0_VAL;
    else
      assign GTYE4_COMMON_PCIERATEQPLL0_int = GTYE4_COMMON_PCIERATEQPLL0;

    if (GTYE4_COMMON_PCIERATEQPLL1_TIE_EN == 1'b1)
      assign GTYE4_COMMON_PCIERATEQPLL1_int = GTYE4_COMMON_PCIERATEQPLL1_VAL;
    else
      assign GTYE4_COMMON_PCIERATEQPLL1_int = GTYE4_COMMON_PCIERATEQPLL1;

    if (GTYE4_COMMON_PMARSVD0_TIE_EN == 1'b1)
      assign GTYE4_COMMON_PMARSVD0_int = GTYE4_COMMON_PMARSVD0_VAL;
    else
      assign GTYE4_COMMON_PMARSVD0_int = GTYE4_COMMON_PMARSVD0;

    if (GTYE4_COMMON_PMARSVD1_TIE_EN == 1'b1)
      assign GTYE4_COMMON_PMARSVD1_int = GTYE4_COMMON_PMARSVD1_VAL;
    else
      assign GTYE4_COMMON_PMARSVD1_int = GTYE4_COMMON_PMARSVD1;

    if (GTYE4_COMMON_QPLL0CLKRSVD0_TIE_EN == 1'b1)
      assign GTYE4_COMMON_QPLL0CLKRSVD0_int = GTYE4_COMMON_QPLL0CLKRSVD0_VAL;
    else
      assign GTYE4_COMMON_QPLL0CLKRSVD0_int = GTYE4_COMMON_QPLL0CLKRSVD0;

    if (GTYE4_COMMON_QPLL0CLKRSVD1_TIE_EN == 1'b1)
      assign GTYE4_COMMON_QPLL0CLKRSVD1_int = GTYE4_COMMON_QPLL0CLKRSVD1_VAL;
    else
      assign GTYE4_COMMON_QPLL0CLKRSVD1_int = GTYE4_COMMON_QPLL0CLKRSVD1;

    if (GTYE4_COMMON_QPLL0FBDIV_TIE_EN == 1'b1)
      assign GTYE4_COMMON_QPLL0FBDIV_int = GTYE4_COMMON_QPLL0FBDIV_VAL;
    else
      assign GTYE4_COMMON_QPLL0FBDIV_int = GTYE4_COMMON_QPLL0FBDIV;

    if (GTYE4_COMMON_QPLL0LOCKDETCLK_TIE_EN == 1'b1)
      assign GTYE4_COMMON_QPLL0LOCKDETCLK_int = GTYE4_COMMON_QPLL0LOCKDETCLK_VAL;
    else
      assign GTYE4_COMMON_QPLL0LOCKDETCLK_int = GTYE4_COMMON_QPLL0LOCKDETCLK;

    if (GTYE4_COMMON_QPLL0LOCKEN_TIE_EN == 1'b1)
      assign GTYE4_COMMON_QPLL0LOCKEN_int = GTYE4_COMMON_QPLL0LOCKEN_VAL;
    else
      assign GTYE4_COMMON_QPLL0LOCKEN_int = GTYE4_COMMON_QPLL0LOCKEN;

    if (GTYE4_COMMON_QPLL0PD_TIE_EN == 1'b1)
      assign GTYE4_COMMON_QPLL0PD_int = GTYE4_COMMON_QPLL0PD_VAL;
    else
      assign GTYE4_COMMON_QPLL0PD_int = GTYE4_COMMON_QPLL0PD;

    if (GTYE4_COMMON_QPLL0REFCLKSEL_TIE_EN == 1'b1)
      assign GTYE4_COMMON_QPLL0REFCLKSEL_int = GTYE4_COMMON_QPLL0REFCLKSEL_VAL;
    else
      assign GTYE4_COMMON_QPLL0REFCLKSEL_int = GTYE4_COMMON_QPLL0REFCLKSEL;

    if (GTYE4_COMMON_QPLL0RESET_TIE_EN == 1'b1)
      assign GTYE4_COMMON_QPLL0RESET_int = GTYE4_COMMON_QPLL0RESET_VAL;
    else
      assign GTYE4_COMMON_QPLL0RESET_int = GTYE4_COMMON_QPLL0RESET;

    if (GTYE4_COMMON_QPLL1CLKRSVD0_TIE_EN == 1'b1)
      assign GTYE4_COMMON_QPLL1CLKRSVD0_int = GTYE4_COMMON_QPLL1CLKRSVD0_VAL;
    else
      assign GTYE4_COMMON_QPLL1CLKRSVD0_int = GTYE4_COMMON_QPLL1CLKRSVD0;

    if (GTYE4_COMMON_QPLL1CLKRSVD1_TIE_EN == 1'b1)
      assign GTYE4_COMMON_QPLL1CLKRSVD1_int = GTYE4_COMMON_QPLL1CLKRSVD1_VAL;
    else
      assign GTYE4_COMMON_QPLL1CLKRSVD1_int = GTYE4_COMMON_QPLL1CLKRSVD1;

    if (GTYE4_COMMON_QPLL1FBDIV_TIE_EN == 1'b1)
      assign GTYE4_COMMON_QPLL1FBDIV_int = GTYE4_COMMON_QPLL1FBDIV_VAL;
    else
      assign GTYE4_COMMON_QPLL1FBDIV_int = GTYE4_COMMON_QPLL1FBDIV;

    if (GTYE4_COMMON_QPLL1LOCKDETCLK_TIE_EN == 1'b1)
      assign GTYE4_COMMON_QPLL1LOCKDETCLK_int = GTYE4_COMMON_QPLL1LOCKDETCLK_VAL;
    else
      assign GTYE4_COMMON_QPLL1LOCKDETCLK_int = GTYE4_COMMON_QPLL1LOCKDETCLK;

    if (GTYE4_COMMON_QPLL1LOCKEN_TIE_EN == 1'b1)
      assign GTYE4_COMMON_QPLL1LOCKEN_int = GTYE4_COMMON_QPLL1LOCKEN_VAL;
    else
      assign GTYE4_COMMON_QPLL1LOCKEN_int = GTYE4_COMMON_QPLL1LOCKEN;

    if (GTYE4_COMMON_QPLL1PD_TIE_EN == 1'b1)
      assign GTYE4_COMMON_QPLL1PD_int = GTYE4_COMMON_QPLL1PD_VAL;
    else
      assign GTYE4_COMMON_QPLL1PD_int = GTYE4_COMMON_QPLL1PD;

    if (GTYE4_COMMON_QPLL1REFCLKSEL_TIE_EN == 1'b1)
      assign GTYE4_COMMON_QPLL1REFCLKSEL_int = GTYE4_COMMON_QPLL1REFCLKSEL_VAL;
    else
      assign GTYE4_COMMON_QPLL1REFCLKSEL_int = GTYE4_COMMON_QPLL1REFCLKSEL;

    if (GTYE4_COMMON_QPLL1RESET_TIE_EN == 1'b1)
      assign GTYE4_COMMON_QPLL1RESET_int = GTYE4_COMMON_QPLL1RESET_VAL;
    else
      assign GTYE4_COMMON_QPLL1RESET_int = GTYE4_COMMON_QPLL1RESET;

    if (GTYE4_COMMON_QPLLRSVD1_TIE_EN == 1'b1)
      assign GTYE4_COMMON_QPLLRSVD1_int = GTYE4_COMMON_QPLLRSVD1_VAL;
    else
      assign GTYE4_COMMON_QPLLRSVD1_int = GTYE4_COMMON_QPLLRSVD1;

    if (GTYE4_COMMON_QPLLRSVD2_TIE_EN == 1'b1)
      assign GTYE4_COMMON_QPLLRSVD2_int = GTYE4_COMMON_QPLLRSVD2_VAL;
    else
      assign GTYE4_COMMON_QPLLRSVD2_int = GTYE4_COMMON_QPLLRSVD2;

    if (GTYE4_COMMON_QPLLRSVD3_TIE_EN == 1'b1)
      assign GTYE4_COMMON_QPLLRSVD3_int = GTYE4_COMMON_QPLLRSVD3_VAL;
    else
      assign GTYE4_COMMON_QPLLRSVD3_int = GTYE4_COMMON_QPLLRSVD3;

    if (GTYE4_COMMON_QPLLRSVD4_TIE_EN == 1'b1)
      assign GTYE4_COMMON_QPLLRSVD4_int = GTYE4_COMMON_QPLLRSVD4_VAL;
    else
      assign GTYE4_COMMON_QPLLRSVD4_int = GTYE4_COMMON_QPLLRSVD4;

    if (GTYE4_COMMON_RCALENB_TIE_EN == 1'b1)
      assign GTYE4_COMMON_RCALENB_int = GTYE4_COMMON_RCALENB_VAL;
    else
      assign GTYE4_COMMON_RCALENB_int = GTYE4_COMMON_RCALENB;

    if (GTYE4_COMMON_SDM0DATA_TIE_EN == 1'b1)
      assign GTYE4_COMMON_SDM0DATA_int = GTYE4_COMMON_SDM0DATA_VAL;
    else
      assign GTYE4_COMMON_SDM0DATA_int = GTYE4_COMMON_SDM0DATA;

    if (GTYE4_COMMON_SDM0RESET_TIE_EN == 1'b1)
      assign GTYE4_COMMON_SDM0RESET_int = GTYE4_COMMON_SDM0RESET_VAL;
    else
      assign GTYE4_COMMON_SDM0RESET_int = GTYE4_COMMON_SDM0RESET;

    if (GTYE4_COMMON_SDM0TOGGLE_TIE_EN == 1'b1)
      assign GTYE4_COMMON_SDM0TOGGLE_int = GTYE4_COMMON_SDM0TOGGLE_VAL;
    else
      assign GTYE4_COMMON_SDM0TOGGLE_int = GTYE4_COMMON_SDM0TOGGLE;

    if (GTYE4_COMMON_SDM0WIDTH_TIE_EN == 1'b1)
      assign GTYE4_COMMON_SDM0WIDTH_int = GTYE4_COMMON_SDM0WIDTH_VAL;
    else
      assign GTYE4_COMMON_SDM0WIDTH_int = GTYE4_COMMON_SDM0WIDTH;

    if (GTYE4_COMMON_SDM1DATA_TIE_EN == 1'b1)
      assign GTYE4_COMMON_SDM1DATA_int = GTYE4_COMMON_SDM1DATA_VAL;
    else
      assign GTYE4_COMMON_SDM1DATA_int = GTYE4_COMMON_SDM1DATA;

    if (GTYE4_COMMON_SDM1RESET_TIE_EN == 1'b1)
      assign GTYE4_COMMON_SDM1RESET_int = GTYE4_COMMON_SDM1RESET_VAL;
    else
      assign GTYE4_COMMON_SDM1RESET_int = GTYE4_COMMON_SDM1RESET;

    if (GTYE4_COMMON_SDM1TOGGLE_TIE_EN == 1'b1)
      assign GTYE4_COMMON_SDM1TOGGLE_int = GTYE4_COMMON_SDM1TOGGLE_VAL;
    else
      assign GTYE4_COMMON_SDM1TOGGLE_int = GTYE4_COMMON_SDM1TOGGLE;

    if (GTYE4_COMMON_SDM1WIDTH_TIE_EN == 1'b1)
      assign GTYE4_COMMON_SDM1WIDTH_int = GTYE4_COMMON_SDM1WIDTH_VAL;
    else
      assign GTYE4_COMMON_SDM1WIDTH_int = GTYE4_COMMON_SDM1WIDTH;

    if (GTYE4_COMMON_UBCFGSTREAMEN_TIE_EN == 1'b1)
      assign GTYE4_COMMON_UBCFGSTREAMEN_int = GTYE4_COMMON_UBCFGSTREAMEN_VAL;
    else
      assign GTYE4_COMMON_UBCFGSTREAMEN_int = GTYE4_COMMON_UBCFGSTREAMEN;

    if (GTYE4_COMMON_UBDO_TIE_EN == 1'b1)
      assign GTYE4_COMMON_UBDO_int = GTYE4_COMMON_UBDO_VAL;
    else
      assign GTYE4_COMMON_UBDO_int = GTYE4_COMMON_UBDO;

    if (GTYE4_COMMON_UBDRDY_TIE_EN == 1'b1)
      assign GTYE4_COMMON_UBDRDY_int = GTYE4_COMMON_UBDRDY_VAL;
    else
      assign GTYE4_COMMON_UBDRDY_int = GTYE4_COMMON_UBDRDY;

    if (GTYE4_COMMON_UBENABLE_TIE_EN == 1'b1)
      assign GTYE4_COMMON_UBENABLE_int = GTYE4_COMMON_UBENABLE_VAL;
    else
      assign GTYE4_COMMON_UBENABLE_int = GTYE4_COMMON_UBENABLE;

    if (GTYE4_COMMON_UBGPI_TIE_EN == 1'b1)
      assign GTYE4_COMMON_UBGPI_int = GTYE4_COMMON_UBGPI_VAL;
    else
      assign GTYE4_COMMON_UBGPI_int = GTYE4_COMMON_UBGPI;

    if (GTYE4_COMMON_UBINTR_TIE_EN == 1'b1)
      assign GTYE4_COMMON_UBINTR_int = GTYE4_COMMON_UBINTR_VAL;
    else
      assign GTYE4_COMMON_UBINTR_int = GTYE4_COMMON_UBINTR;

    if (GTYE4_COMMON_UBIOLMBRST_TIE_EN == 1'b1)
      assign GTYE4_COMMON_UBIOLMBRST_int = GTYE4_COMMON_UBIOLMBRST_VAL;
    else
      assign GTYE4_COMMON_UBIOLMBRST_int = GTYE4_COMMON_UBIOLMBRST;

    if (GTYE4_COMMON_UBMBRST_TIE_EN == 1'b1)
      assign GTYE4_COMMON_UBMBRST_int = GTYE4_COMMON_UBMBRST_VAL;
    else
      assign GTYE4_COMMON_UBMBRST_int = GTYE4_COMMON_UBMBRST;

    if (GTYE4_COMMON_UBMDMCAPTURE_TIE_EN == 1'b1)
      assign GTYE4_COMMON_UBMDMCAPTURE_int = GTYE4_COMMON_UBMDMCAPTURE_VAL;
    else
      assign GTYE4_COMMON_UBMDMCAPTURE_int = GTYE4_COMMON_UBMDMCAPTURE;

    if (GTYE4_COMMON_UBMDMDBGRST_TIE_EN == 1'b1)
      assign GTYE4_COMMON_UBMDMDBGRST_int = GTYE4_COMMON_UBMDMDBGRST_VAL;
    else
      assign GTYE4_COMMON_UBMDMDBGRST_int = GTYE4_COMMON_UBMDMDBGRST;

    if (GTYE4_COMMON_UBMDMDBGUPDATE_TIE_EN == 1'b1)
      assign GTYE4_COMMON_UBMDMDBGUPDATE_int = GTYE4_COMMON_UBMDMDBGUPDATE_VAL;
    else
      assign GTYE4_COMMON_UBMDMDBGUPDATE_int = GTYE4_COMMON_UBMDMDBGUPDATE;

    if (GTYE4_COMMON_UBMDMREGEN_TIE_EN == 1'b1)
      assign GTYE4_COMMON_UBMDMREGEN_int = GTYE4_COMMON_UBMDMREGEN_VAL;
    else
      assign GTYE4_COMMON_UBMDMREGEN_int = GTYE4_COMMON_UBMDMREGEN;

    if (GTYE4_COMMON_UBMDMSHIFT_TIE_EN == 1'b1)
      assign GTYE4_COMMON_UBMDMSHIFT_int = GTYE4_COMMON_UBMDMSHIFT_VAL;
    else
      assign GTYE4_COMMON_UBMDMSHIFT_int = GTYE4_COMMON_UBMDMSHIFT;

    if (GTYE4_COMMON_UBMDMSYSRST_TIE_EN == 1'b1)
      assign GTYE4_COMMON_UBMDMSYSRST_int = GTYE4_COMMON_UBMDMSYSRST_VAL;
    else
      assign GTYE4_COMMON_UBMDMSYSRST_int = GTYE4_COMMON_UBMDMSYSRST;

    if (GTYE4_COMMON_UBMDMTCK_TIE_EN == 1'b1)
      assign GTYE4_COMMON_UBMDMTCK_int = GTYE4_COMMON_UBMDMTCK_VAL;
    else
      assign GTYE4_COMMON_UBMDMTCK_int = GTYE4_COMMON_UBMDMTCK;

    if (GTYE4_COMMON_UBMDMTDI_TIE_EN == 1'b1)
      assign GTYE4_COMMON_UBMDMTDI_int = GTYE4_COMMON_UBMDMTDI_VAL;
    else
      assign GTYE4_COMMON_UBMDMTDI_int = GTYE4_COMMON_UBMDMTDI;

    // generate the GTYE4_COMMON primitive instance, mapping parameters and ports
    GTYE4_COMMON #(
      .AEN_QPLL0_FBDIV       (GTYE4_COMMON_AEN_QPLL0_FBDIV      ),
      .AEN_QPLL1_FBDIV       (GTYE4_COMMON_AEN_QPLL1_FBDIV      ),
      .AEN_SDM0TOGGLE        (GTYE4_COMMON_AEN_SDM0TOGGLE       ),
      .AEN_SDM1TOGGLE        (GTYE4_COMMON_AEN_SDM1TOGGLE       ),
      .A_SDM0TOGGLE          (GTYE4_COMMON_A_SDM0TOGGLE         ),
      .A_SDM1DATA_HIGH       (GTYE4_COMMON_A_SDM1DATA_HIGH      ),
      .A_SDM1DATA_LOW        (GTYE4_COMMON_A_SDM1DATA_LOW       ),
      .A_SDM1TOGGLE          (GTYE4_COMMON_A_SDM1TOGGLE         ),
      .BIAS_CFG0             (GTYE4_COMMON_BIAS_CFG0            ),
      .BIAS_CFG1             (GTYE4_COMMON_BIAS_CFG1            ),
      .BIAS_CFG2             (GTYE4_COMMON_BIAS_CFG2            ),
      .BIAS_CFG3             (GTYE4_COMMON_BIAS_CFG3            ),
      .BIAS_CFG4             (GTYE4_COMMON_BIAS_CFG4            ),
      .BIAS_CFG_RSVD         (GTYE4_COMMON_BIAS_CFG_RSVD        ),
      .COMMON_CFG0           (GTYE4_COMMON_COMMON_CFG0          ),
      .COMMON_CFG1           (GTYE4_COMMON_COMMON_CFG1          ),
      .POR_CFG               (GTYE4_COMMON_POR_CFG              ),
      .PPF0_CFG              (GTYE4_COMMON_PPF0_CFG             ),
      .PPF1_CFG              (GTYE4_COMMON_PPF1_CFG             ),
      .QPLL0CLKOUT_RATE      (GTYE4_COMMON_QPLL0CLKOUT_RATE     ),
      .QPLL0_CFG0            (GTYE4_COMMON_QPLL0_CFG0           ),
      .QPLL0_CFG1            (GTYE4_COMMON_QPLL0_CFG1           ),
      .QPLL0_CFG1_G3         (GTYE4_COMMON_QPLL0_CFG1_G3        ),
      .QPLL0_CFG2            (GTYE4_COMMON_QPLL0_CFG2           ),
      .QPLL0_CFG2_G3         (GTYE4_COMMON_QPLL0_CFG2_G3        ),
      .QPLL0_CFG3            (GTYE4_COMMON_QPLL0_CFG3           ),
      .QPLL0_CFG4            (GTYE4_COMMON_QPLL0_CFG4           ),
      .QPLL0_CP              (GTYE4_COMMON_QPLL0_CP             ),
      .QPLL0_CP_G3           (GTYE4_COMMON_QPLL0_CP_G3          ),
      .QPLL0_FBDIV           (GTYE4_COMMON_QPLL0_FBDIV          ),
      .QPLL0_FBDIV_G3        (GTYE4_COMMON_QPLL0_FBDIV_G3       ),
      .QPLL0_INIT_CFG0       (GTYE4_COMMON_QPLL0_INIT_CFG0      ),
      .QPLL0_INIT_CFG1       (GTYE4_COMMON_QPLL0_INIT_CFG1      ),
      .QPLL0_LOCK_CFG        (GTYE4_COMMON_QPLL0_LOCK_CFG       ),
      .QPLL0_LOCK_CFG_G3     (GTYE4_COMMON_QPLL0_LOCK_CFG_G3    ),
      .QPLL0_LPF             (GTYE4_COMMON_QPLL0_LPF            ),
      .QPLL0_LPF_G3          (GTYE4_COMMON_QPLL0_LPF_G3         ),
      .QPLL0_PCI_EN          (GTYE4_COMMON_QPLL0_PCI_EN         ),
      .QPLL0_RATE_SW_USE_DRP (GTYE4_COMMON_QPLL0_RATE_SW_USE_DRP),
      .QPLL0_REFCLK_DIV      (GTYE4_COMMON_QPLL0_REFCLK_DIV     ),
      .QPLL0_SDM_CFG0        (GTYE4_COMMON_QPLL0_SDM_CFG0       ),
      .QPLL0_SDM_CFG1        (GTYE4_COMMON_QPLL0_SDM_CFG1       ),
      .QPLL0_SDM_CFG2        (GTYE4_COMMON_QPLL0_SDM_CFG2       ),
      .QPLL1CLKOUT_RATE      (GTYE4_COMMON_QPLL1CLKOUT_RATE     ),
      .QPLL1_CFG0            (GTYE4_COMMON_QPLL1_CFG0           ),
      .QPLL1_CFG1            (GTYE4_COMMON_QPLL1_CFG1           ),
      .QPLL1_CFG1_G3         (GTYE4_COMMON_QPLL1_CFG1_G3        ),
      .QPLL1_CFG2            (GTYE4_COMMON_QPLL1_CFG2           ),
      .QPLL1_CFG2_G3         (GTYE4_COMMON_QPLL1_CFG2_G3        ),
      .QPLL1_CFG3            (GTYE4_COMMON_QPLL1_CFG3           ),
      .QPLL1_CFG4            (GTYE4_COMMON_QPLL1_CFG4           ),
      .QPLL1_CP              (GTYE4_COMMON_QPLL1_CP             ),
      .QPLL1_CP_G3           (GTYE4_COMMON_QPLL1_CP_G3          ),
      .QPLL1_FBDIV           (GTYE4_COMMON_QPLL1_FBDIV          ),
      .QPLL1_FBDIV_G3        (GTYE4_COMMON_QPLL1_FBDIV_G3       ),
      .QPLL1_INIT_CFG0       (GTYE4_COMMON_QPLL1_INIT_CFG0      ),
      .QPLL1_INIT_CFG1       (GTYE4_COMMON_QPLL1_INIT_CFG1      ),
      .QPLL1_LOCK_CFG        (GTYE4_COMMON_QPLL1_LOCK_CFG       ),
      .QPLL1_LOCK_CFG_G3     (GTYE4_COMMON_QPLL1_LOCK_CFG_G3    ),
      .QPLL1_LPF             (GTYE4_COMMON_QPLL1_LPF            ),
      .QPLL1_LPF_G3          (GTYE4_COMMON_QPLL1_LPF_G3         ),
      .QPLL1_PCI_EN          (GTYE4_COMMON_QPLL1_PCI_EN         ),
      .QPLL1_RATE_SW_USE_DRP (GTYE4_COMMON_QPLL1_RATE_SW_USE_DRP),
      .QPLL1_REFCLK_DIV      (GTYE4_COMMON_QPLL1_REFCLK_DIV     ),
      .QPLL1_SDM_CFG0        (GTYE4_COMMON_QPLL1_SDM_CFG0       ),
      .QPLL1_SDM_CFG1        (GTYE4_COMMON_QPLL1_SDM_CFG1       ),
      .QPLL1_SDM_CFG2        (GTYE4_COMMON_QPLL1_SDM_CFG2       ),
      .RSVD_ATTR0            (GTYE4_COMMON_RSVD_ATTR0           ),
      .RSVD_ATTR1            (GTYE4_COMMON_RSVD_ATTR1           ),
      .RSVD_ATTR2            (GTYE4_COMMON_RSVD_ATTR2           ),
      .RSVD_ATTR3            (GTYE4_COMMON_RSVD_ATTR3           ),
      .RXRECCLKOUT0_SEL      (GTYE4_COMMON_RXRECCLKOUT0_SEL     ),
      .RXRECCLKOUT1_SEL      (GTYE4_COMMON_RXRECCLKOUT1_SEL     ),
      .SARC_ENB              (GTYE4_COMMON_SARC_ENB             ),
      .SARC_SEL              (GTYE4_COMMON_SARC_SEL             ),
      .SDM0INITSEED0_0       (GTYE4_COMMON_SDM0INITSEED0_0      ),
      .SDM0INITSEED0_1       (GTYE4_COMMON_SDM0INITSEED0_1      ),
      .SDM1INITSEED0_0       (GTYE4_COMMON_SDM1INITSEED0_0      ),
      .SDM1INITSEED0_1       (GTYE4_COMMON_SDM1INITSEED0_1      ),
      .SIM_MODE              (GTYE4_COMMON_SIM_MODE             ),
      .SIM_RESET_SPEEDUP     (GTYE4_COMMON_SIM_RESET_SPEEDUP    ),
      .SIM_DEVICE            (GTYE4_COMMON_SIM_DEVICE           ),
      .UB_CFG0               (GTYE4_COMMON_UB_CFG0              ),
      .UB_CFG1               (GTYE4_COMMON_UB_CFG1              ),
      .UB_CFG2               (GTYE4_COMMON_UB_CFG2              ),
      .UB_CFG3               (GTYE4_COMMON_UB_CFG3              ),
      .UB_CFG4               (GTYE4_COMMON_UB_CFG4              ),
      .UB_CFG5               (GTYE4_COMMON_UB_CFG5              ),
      .UB_CFG6               (GTYE4_COMMON_UB_CFG6              )
    ) GTYE4_COMMON_PRIM_INST (
      .BGBYPASSB            (GTYE4_COMMON_BGBYPASSB_int       [ 0:0]),
      .BGMONITORENB         (GTYE4_COMMON_BGMONITORENB_int    [ 0:0]),
      .BGPDB                (GTYE4_COMMON_BGPDB_int           [ 0:0]),
      .BGRCALOVRD           (GTYE4_COMMON_BGRCALOVRD_int      [ 4:0]),
      .BGRCALOVRDENB        (GTYE4_COMMON_BGRCALOVRDENB_int   [ 0:0]),
      .DRPADDR              (GTYE4_COMMON_DRPADDR_int         [15:0]),
      .DRPCLK               (GTYE4_COMMON_DRPCLK_int          [ 0:0]),
      .DRPDI                (GTYE4_COMMON_DRPDI_int           [15:0]),
      .DRPEN                (GTYE4_COMMON_DRPEN_int           [ 0:0]),
      .DRPWE                (GTYE4_COMMON_DRPWE_int           [ 0:0]),
      .GTGREFCLK0           (GTYE4_COMMON_GTGREFCLK0_int      [ 0:0]),
      .GTGREFCLK1           (GTYE4_COMMON_GTGREFCLK1_int      [ 0:0]),
      .GTNORTHREFCLK00      (GTYE4_COMMON_GTNORTHREFCLK00_int [ 0:0]),
      .GTNORTHREFCLK01      (GTYE4_COMMON_GTNORTHREFCLK01_int [ 0:0]),
      .GTNORTHREFCLK10      (GTYE4_COMMON_GTNORTHREFCLK10_int [ 0:0]),
      .GTNORTHREFCLK11      (GTYE4_COMMON_GTNORTHREFCLK11_int [ 0:0]),
      .GTREFCLK00           (GTYE4_COMMON_GTREFCLK00_int      [ 0:0]),
      .GTREFCLK01           (GTYE4_COMMON_GTREFCLK01_int      [ 0:0]),
      .GTREFCLK10           (GTYE4_COMMON_GTREFCLK10_int      [ 0:0]),
      .GTREFCLK11           (GTYE4_COMMON_GTREFCLK11_int      [ 0:0]),
      .GTSOUTHREFCLK00      (GTYE4_COMMON_GTSOUTHREFCLK00_int [ 0:0]),
      .GTSOUTHREFCLK01      (GTYE4_COMMON_GTSOUTHREFCLK01_int [ 0:0]),
      .GTSOUTHREFCLK10      (GTYE4_COMMON_GTSOUTHREFCLK10_int [ 0:0]),
      .GTSOUTHREFCLK11      (GTYE4_COMMON_GTSOUTHREFCLK11_int [ 0:0]),
      .PCIERATEQPLL0        (GTYE4_COMMON_PCIERATEQPLL0_int   [ 2:0]),
      .PCIERATEQPLL1        (GTYE4_COMMON_PCIERATEQPLL1_int   [ 2:0]),
      .PMARSVD0             (GTYE4_COMMON_PMARSVD0_int        [ 7:0]),
      .PMARSVD1             (GTYE4_COMMON_PMARSVD1_int        [ 7:0]),
      .QPLL0CLKRSVD0        (GTYE4_COMMON_QPLL0CLKRSVD0_int   [ 0:0]),
      .QPLL0CLKRSVD1        (GTYE4_COMMON_QPLL0CLKRSVD1_int   [ 0:0]),
      .QPLL0FBDIV           (GTYE4_COMMON_QPLL0FBDIV_int      [ 7:0]),
      .QPLL0LOCKDETCLK      (GTYE4_COMMON_QPLL0LOCKDETCLK_int [ 0:0]),
      .QPLL0LOCKEN          (GTYE4_COMMON_QPLL0LOCKEN_int     [ 0:0]),
      .QPLL0PD              (GTYE4_COMMON_QPLL0PD_int         [ 0:0]),
      .QPLL0REFCLKSEL       (GTYE4_COMMON_QPLL0REFCLKSEL_int  [ 2:0]),
      .QPLL0RESET           (GTYE4_COMMON_QPLL0RESET_int      [ 0:0]),
      .QPLL1CLKRSVD0        (GTYE4_COMMON_QPLL1CLKRSVD0_int   [ 0:0]),
      .QPLL1CLKRSVD1        (GTYE4_COMMON_QPLL1CLKRSVD1_int   [ 0:0]),
      .QPLL1FBDIV           (GTYE4_COMMON_QPLL1FBDIV_int      [ 7:0]),
      .QPLL1LOCKDETCLK      (GTYE4_COMMON_QPLL1LOCKDETCLK_int [ 0:0]),
      .QPLL1LOCKEN          (GTYE4_COMMON_QPLL1LOCKEN_int     [ 0:0]),
      .QPLL1PD              (GTYE4_COMMON_QPLL1PD_int         [ 0:0]),
      .QPLL1REFCLKSEL       (GTYE4_COMMON_QPLL1REFCLKSEL_int  [ 2:0]),
      .QPLL1RESET           (GTYE4_COMMON_QPLL1RESET_int      [ 0:0]),
      .QPLLRSVD1            (GTYE4_COMMON_QPLLRSVD1_int       [ 7:0]),
      .QPLLRSVD2            (GTYE4_COMMON_QPLLRSVD2_int       [ 4:0]),
      .QPLLRSVD3            (GTYE4_COMMON_QPLLRSVD3_int       [ 4:0]),
      .QPLLRSVD4            (GTYE4_COMMON_QPLLRSVD4_int       [ 7:0]),
      .RCALENB              (GTYE4_COMMON_RCALENB_int         [ 0:0]),
      .SDM0DATA             (GTYE4_COMMON_SDM0DATA_int        [24:0]),
      .SDM0RESET            (GTYE4_COMMON_SDM0RESET_int       [ 0:0]),
      .SDM0TOGGLE           (GTYE4_COMMON_SDM0TOGGLE_int      [ 0:0]),
      .SDM0WIDTH            (GTYE4_COMMON_SDM0WIDTH_int       [ 1:0]),
      .SDM1DATA             (GTYE4_COMMON_SDM1DATA_int        [24:0]),
      .SDM1RESET            (GTYE4_COMMON_SDM1RESET_int       [ 0:0]),
      .SDM1TOGGLE           (GTYE4_COMMON_SDM1TOGGLE_int      [ 0:0]),
      .SDM1WIDTH            (GTYE4_COMMON_SDM1WIDTH_int       [ 1:0]),
      .UBCFGSTREAMEN        (GTYE4_COMMON_UBCFGSTREAMEN_int   [ 0:0]),
      .UBDO                 (GTYE4_COMMON_UBDO_int            [15:0]),
      .UBDRDY               (GTYE4_COMMON_UBDRDY_int          [ 0:0]),
      .UBENABLE             (GTYE4_COMMON_UBENABLE_int        [ 0:0]),
      .UBGPI                (GTYE4_COMMON_UBGPI_int           [ 1:0]),
      .UBINTR               (GTYE4_COMMON_UBINTR_int          [ 1:0]),
      .UBIOLMBRST           (GTYE4_COMMON_UBIOLMBRST_int      [ 0:0]),
      .UBMBRST              (GTYE4_COMMON_UBMBRST_int         [ 0:0]),
      .UBMDMCAPTURE         (GTYE4_COMMON_UBMDMCAPTURE_int    [ 0:0]),
      .UBMDMDBGRST          (GTYE4_COMMON_UBMDMDBGRST_int     [ 0:0]),
      .UBMDMDBGUPDATE       (GTYE4_COMMON_UBMDMDBGUPDATE_int  [ 0:0]),
      .UBMDMREGEN           (GTYE4_COMMON_UBMDMREGEN_int      [ 3:0]),
      .UBMDMSHIFT           (GTYE4_COMMON_UBMDMSHIFT_int      [ 0:0]),
      .UBMDMSYSRST          (GTYE4_COMMON_UBMDMSYSRST_int     [ 0:0]),
      .UBMDMTCK             (GTYE4_COMMON_UBMDMTCK_int        [ 0:0]),
      .UBMDMTDI             (GTYE4_COMMON_UBMDMTDI_int        [ 0:0]),

      .DRPDO                (GTYE4_COMMON_DRPDO               [15:0]),
      .DRPRDY               (GTYE4_COMMON_DRPRDY              [ 0:0]),
      .PMARSVDOUT0          (GTYE4_COMMON_PMARSVDOUT0         [ 7:0]),
      .PMARSVDOUT1          (GTYE4_COMMON_PMARSVDOUT1         [ 7:0]),
      .QPLL0FBCLKLOST       (GTYE4_COMMON_QPLL0FBCLKLOST      [ 0:0]),
      .QPLL0LOCK            (GTYE4_COMMON_QPLL0LOCK           [ 0:0]),
      .QPLL0OUTCLK          (GTYE4_COMMON_QPLL0OUTCLK         [ 0:0]),
      .QPLL0OUTREFCLK       (GTYE4_COMMON_QPLL0OUTREFCLK      [ 0:0]),
      .QPLL0REFCLKLOST      (GTYE4_COMMON_QPLL0REFCLKLOST     [ 0:0]),
      .QPLL1FBCLKLOST       (GTYE4_COMMON_QPLL1FBCLKLOST      [ 0:0]),
      .QPLL1LOCK            (GTYE4_COMMON_QPLL1LOCK           [ 0:0]),
      .QPLL1OUTCLK          (GTYE4_COMMON_QPLL1OUTCLK         [ 0:0]),
      .QPLL1OUTREFCLK       (GTYE4_COMMON_QPLL1OUTREFCLK      [ 0:0]),
      .QPLL1REFCLKLOST      (GTYE4_COMMON_QPLL1REFCLKLOST     [ 0:0]),
      .QPLLDMONITOR0        (GTYE4_COMMON_QPLLDMONITOR0       [ 7:0]),
      .QPLLDMONITOR1        (GTYE4_COMMON_QPLLDMONITOR1       [ 7:0]),
      .REFCLKOUTMONITOR0    (GTYE4_COMMON_REFCLKOUTMONITOR0   [ 0:0]),
      .REFCLKOUTMONITOR1    (GTYE4_COMMON_REFCLKOUTMONITOR1   [ 0:0]),
      .RXRECCLK0SEL         (GTYE4_COMMON_RXRECCLK0SEL        [ 1:0]),
      .RXRECCLK1SEL         (GTYE4_COMMON_RXRECCLK1SEL        [ 1:0]),
      .SDM0FINALOUT         (GTYE4_COMMON_SDM0FINALOUT        [ 3:0]),
      .SDM0TESTDATA         (GTYE4_COMMON_SDM0TESTDATA        [14:0]),
      .SDM1FINALOUT         (GTYE4_COMMON_SDM1FINALOUT        [ 3:0]),
      .SDM1TESTDATA         (GTYE4_COMMON_SDM1TESTDATA        [14:0]),
      .UBDADDR              (GTYE4_COMMON_UBDADDR             [15:0]),
      .UBDEN                (GTYE4_COMMON_UBDEN               [ 0:0]),
      .UBDI                 (GTYE4_COMMON_UBDI                [15:0]),
      .UBDWE                (GTYE4_COMMON_UBDWE               [ 0:0]),
      .UBMDMTDO             (GTYE4_COMMON_UBMDMTDO            [ 0:0]),
      .UBRSVDOUT            (GTYE4_COMMON_UBRSVDOUT           [ 0:0]),
      .UBTXUART             (GTYE4_COMMON_UBTXUART            [ 0:0])
    );

  end
  endgenerate


endmodule
