//------------------------------------------------------------------------------
//  (c) Copyright 2013-2015 Xilinx, Inc. All rights reserved.
//
//  This file contains confidential and proprietary information
//  of Xilinx, Inc. and is protected under U.S. and
//  international copyright and other intellectual property
//  laws.
//
//  DISCLAIMER
//  This disclaimer is not a license and does not grant any
//  rights to the materials distributed herewith. Except as
//  otherwise provided in a valid license issued to you by
//  Xilinx, and to the maximum extent permitted by applicable
//  law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
//  WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
//  AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
//  BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
//  INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
//  (2) Xilinx shall not be liable (whether in contract or tort,
//  including negligence, or under any other theory of
//  liability) for any loss or damage of any kind or nature
//  related to, arising under or in connection with these
//  materials, including for any direct, or any indirect,
//  special, incidental, or consequential loss or damage
//  (including loss of data, profits, goodwill, or any type of
//  loss or damage suffered as a result of any action brought
//  by a third party) even if such damage or loss was
//  reasonably foreseeable or Xilinx had been advised of the
//  possibility of the same.
//
//  CRITICAL APPLICATIONS
//  Xilinx products are not designed or intended to be fail-
//  safe, or for use in any application requiring fail-safe
//  performance, such as life-support or safety devices or
//  systems, Class III medical devices, nuclear facilities,
//  applications related to the deployment of airbags, or any
//  other applications that could lead to death, personal
//  injury, or severe property or environmental damage
//  (individually and collectively, "Critical
//  Applications"). Customer assumes the sole risk and
//  liability of any use of Xilinx products in Critical
//  Applications, subject only to applicable laws and
//  regulations governing limitations on product liability.
//
//  THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
//  PART OF THIS FILE AT ALL TIMES.
//------------------------------------------------------------------------------

// ***************************
// * DO NOT MODIFY THIS FILE *
// ***************************

`timescale 1ps/1ps

`define xdma_0_pcie4_ip_gt_MAX_NUM_CHANNELS 192
`define xdma_0_pcie4_ip_gt_MAX_NUM_COMMONS 48
`define xdma_0_pcie4_ip_gt_N_CM C_TOTAL_NUM_COMMONS
`define xdma_0_pcie4_ip_gt_N_CH C_TOTAL_NUM_CHANNELS
`define xdma_0_pcie4_ip_gt_SF_CM C_COMMON_SCALING_FACTOR
`define xdma_0_pcie4_ip_gt_FORCE_COMMONS__DO_NOT_FORCE 0
`define xdma_0_pcie4_ip_gt_FORCE_COMMONS__FORCE 1
`define xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3 0
`define xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3 1
`define xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4 2
`define xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4 3
`define xdma_0_pcie4_ip_gt_INCLUDE_CPLL_CAL__EXCLUDE 0
`define xdma_0_pcie4_ip_gt_INCLUDE_CPLL_CAL__INCLUDE 1
`define xdma_0_pcie4_ip_gt_INCLUDE_CPLL_CAL__DEPENDENT 2
`define xdma_0_pcie4_ip_gt_LOCATE_COMMON__CORE 0
`define xdma_0_pcie4_ip_gt_LOCATE_COMMON__EXAMPLE_DESIGN 1
`define xdma_0_pcie4_ip_gt_LOCATE_RESET_CONTROLLER__CORE 0
`define xdma_0_pcie4_ip_gt_LOCATE_RESET_CONTROLLER__EXAMPLE_DESIGN 1
`define xdma_0_pcie4_ip_gt_LOCATE_USER_DATA_WIDTH_SIZING__CORE 0
`define xdma_0_pcie4_ip_gt_LOCATE_USER_DATA_WIDTH_SIZING__EXAMPLE_DESIGN 1
`define xdma_0_pcie4_ip_gt_LOCATE_RX_BUFFER_BYPASS_CONTROLLER__CORE 0
`define xdma_0_pcie4_ip_gt_LOCATE_RX_BUFFER_BYPASS_CONTROLLER__EXAMPLE_DESIGN 1
`define xdma_0_pcie4_ip_gt_LOCATE_IN_SYSTEM_IBERT_CORE__EXAMPLE_DESIGN 1
`define xdma_0_pcie4_ip_gt_LOCATE_IN_SYSTEM_IBERT_CORE__NONE 2
`define xdma_0_pcie4_ip_gt_LOCATE_RX_USER_CLOCKING__CORE 0
`define xdma_0_pcie4_ip_gt_LOCATE_RX_USER_CLOCKING__EXAMPLE_DESIGN 1
`define xdma_0_pcie4_ip_gt_LOCATE_TX_BUFFER_BYPASS_CONTROLLER__CORE 0
`define xdma_0_pcie4_ip_gt_LOCATE_TX_BUFFER_BYPASS_CONTROLLER__EXAMPLE_DESIGN 1
`define xdma_0_pcie4_ip_gt_LOCATE_TX_USER_CLOCKING__CORE 0
`define xdma_0_pcie4_ip_gt_LOCATE_TX_USER_CLOCKING__EXAMPLE_DESIGN 1
`define xdma_0_pcie4_ip_gt_RESET_CONTROLLER_INSTANCE_CTRL__SINGLE_INSTANCE 0
`define xdma_0_pcie4_ip_gt_RESET_CONTROLLER_INSTANCE_CTRL__PER_CHANNEL 0
`define xdma_0_pcie4_ip_gt_RX_BUFFBYPASS_MODE__AUTO 0
`define xdma_0_pcie4_ip_gt_RX_BUFFBYPASS_MODE__MANUAL 1
`define xdma_0_pcie4_ip_gt_RX_BUFFER_BYPASS_INSTANCE_CTRL__SINGLE_INSTANCE 0
`define xdma_0_pcie4_ip_gt_RX_BUFFER_BYPASS_INSTANCE_CTRL__PER_CHANNEL 1
`define xdma_0_pcie4_ip_gt_RX_BUFFER_MODE__BYPASS 0
`define xdma_0_pcie4_ip_gt_RX_BUFFER_MODE__USE 1
`define xdma_0_pcie4_ip_gt_RX_CC_ENABLE__DISABLED 0
`define xdma_0_pcie4_ip_gt_RX_CC_ENABLE__ENABLED 1
`define xdma_0_pcie4_ip_gt_RX_COMMA_M_ENABLE__DISABLED 0
`define xdma_0_pcie4_ip_gt_RX_COMMA_M_ENABLE__ENABLED 1
`define xdma_0_pcie4_ip_gt_RX_COMMA_P_ENABLE__DISABLED 0
`define xdma_0_pcie4_ip_gt_RX_COMMA_P_ENABLE__ENABLED 1
`define xdma_0_pcie4_ip_gt_RX_DATA_DECODING__RAW 0
`define xdma_0_pcie4_ip_gt_RX_DATA_DECODING__8B10B 1
`define xdma_0_pcie4_ip_gt_RX_DATA_DECODING__64B66B 2
`define xdma_0_pcie4_ip_gt_RX_DATA_DECODING__64B66B_CAUI 3
`define xdma_0_pcie4_ip_gt_RX_DATA_DECODING__64B66B_ASYNC 4
`define xdma_0_pcie4_ip_gt_RX_DATA_DECODING__64B66B_ASYNC_CAUI 5
`define xdma_0_pcie4_ip_gt_RX_DATA_DECODING__64B67B 6
`define xdma_0_pcie4_ip_gt_RX_DATA_DECODING__64B67B_CAUI 7
`define xdma_0_pcie4_ip_gt_RX_DATA_DECODING__128B130B 10
`define xdma_0_pcie4_ip_gt_RX_ENABLE__DISABLED 0
`define xdma_0_pcie4_ip_gt_RX_ENABLE__ENABLED 1
`define xdma_0_pcie4_ip_gt_RX_OUTCLK_SOURCE__RXOUTCLKPCS 0
`define xdma_0_pcie4_ip_gt_RX_OUTCLK_SOURCE__RXOUTCLKPMA 1
`define xdma_0_pcie4_ip_gt_RX_OUTCLK_SOURCE__RXPLLREFCLK_DIV1 2
`define xdma_0_pcie4_ip_gt_RX_OUTCLK_SOURCE__RXPLLREFCLK_DIV2 3
`define xdma_0_pcie4_ip_gt_RX_OUTCLK_SOURCE__RXPROGDIVCLK 4
`define xdma_0_pcie4_ip_gt_RX_PLL_TYPE__QPLL0 0
`define xdma_0_pcie4_ip_gt_RX_PLL_TYPE__QPLL1 1
`define xdma_0_pcie4_ip_gt_RX_PLL_TYPE__CPLL 2
`define xdma_0_pcie4_ip_gt_RX_SLIDE_MODE__OFF 0
`define xdma_0_pcie4_ip_gt_RX_SLIDE_MODE__PCS 1
`define xdma_0_pcie4_ip_gt_RX_SLIDE_MODE__PMA 2
`define xdma_0_pcie4_ip_gt_RX_SLIDE_MODE__AUTO 3
`define xdma_0_pcie4_ip_gt_RX_USER_CLOCKING_CONTENTS__BUFG_GT 0
`define xdma_0_pcie4_ip_gt_RX_USER_CLOCKING_CONTENTS__BUFG 1
`define xdma_0_pcie4_ip_gt_RX_USER_CLOCKING_CONTENTS__MMCM 2
`define xdma_0_pcie4_ip_gt_RX_USER_CLOCKING_INSTANCE_CTRL__SINGLE_INSTANCE 0
`define xdma_0_pcie4_ip_gt_RX_USER_CLOCKING_INSTANCE_CTRL__PER_CHANNEL 1
`define xdma_0_pcie4_ip_gt_RX_USER_CLOCKING_SOURCE__RXOUTCLK 0
`define xdma_0_pcie4_ip_gt_RX_USER_CLOCKING_SOURCE__IBUFDS 1
`define xdma_0_pcie4_ip_gt_RX_USER_CLOCKING_SOURCE__TXOUTCLK 2
`define xdma_0_pcie4_ip_gt_SECONDARY_QPLL_ENABLE__DISABLED 0
`define xdma_0_pcie4_ip_gt_SECONDARY_QPLL_ENABLE__ENABLED 1
`define xdma_0_pcie4_ip_gt_TXPROGDIV_FREQ_ENABLE__DISABLED 0
`define xdma_0_pcie4_ip_gt_TXPROGDIV_FREQ_ENABLE__ENABLED 1
`define xdma_0_pcie4_ip_gt_TXPROGDIV_FREQ_SOURCE__QPLL0 0
`define xdma_0_pcie4_ip_gt_TXPROGDIV_FREQ_SOURCE__QPLL1 1
`define xdma_0_pcie4_ip_gt_TXPROGDIV_FREQ_SOURCE__CPLL 2
`define xdma_0_pcie4_ip_gt_TX_BUFFBYPASS_MODE__AUTO 0
`define xdma_0_pcie4_ip_gt_TX_BUFFBYPASS_MODE__MANUAL 1
`define xdma_0_pcie4_ip_gt_TX_BUFFER_BYPASS_INSTANCE_CTRL__SINGLE_INSTANCE 0
`define xdma_0_pcie4_ip_gt_TX_BUFFER_BYPASS_INSTANCE_CTRL__PER_CHANNEL 1
`define xdma_0_pcie4_ip_gt_TX_BUFFER_MODE__BYPASS 0
`define xdma_0_pcie4_ip_gt_TX_BUFFER_MODE__USE 1
`define xdma_0_pcie4_ip_gt_TX_DATA_ENCODING__RAW 0
`define xdma_0_pcie4_ip_gt_TX_DATA_ENCODING__8B10B 1
`define xdma_0_pcie4_ip_gt_TX_DATA_ENCODING__64B66B 2
`define xdma_0_pcie4_ip_gt_TX_DATA_ENCODING__64B66B_CAUI 3
`define xdma_0_pcie4_ip_gt_TX_DATA_ENCODING__64B66B_ASYNC 4
`define xdma_0_pcie4_ip_gt_TX_DATA_ENCODING__64B66B_ASYNC_CAUI 5
`define xdma_0_pcie4_ip_gt_TX_DATA_ENCODING__64B67B 6
`define xdma_0_pcie4_ip_gt_TX_DATA_ENCODING__64B67B_CAUI 7
`define xdma_0_pcie4_ip_gt_TX_DATA_ENCODING__128B130B 10
`define xdma_0_pcie4_ip_gt_TX_ENABLE__DISABLED 0
`define xdma_0_pcie4_ip_gt_TX_ENABLE__ENABLED 1
`define xdma_0_pcie4_ip_gt_TX_OUTCLK_SOURCE__TXOUTCLKPCS 0
`define xdma_0_pcie4_ip_gt_TX_OUTCLK_SOURCE__TXOUTCLKPMA 1
`define xdma_0_pcie4_ip_gt_TX_OUTCLK_SOURCE__TXPLLREFCLK_DIV1 2
`define xdma_0_pcie4_ip_gt_TX_OUTCLK_SOURCE__TXPLLREFCLK_DIV2 3
`define xdma_0_pcie4_ip_gt_TX_OUTCLK_SOURCE__TXPROGDIVCLK 4
`define xdma_0_pcie4_ip_gt_TX_PLL_TYPE__QPLL0 0
`define xdma_0_pcie4_ip_gt_TX_PLL_TYPE__QPLL1 1
`define xdma_0_pcie4_ip_gt_TX_PLL_TYPE__CPLL 2
`define xdma_0_pcie4_ip_gt_TX_USER_CLOCKING_CONTENTS__BUFG_GT 0
`define xdma_0_pcie4_ip_gt_TX_USER_CLOCKING_CONTENTS__BUFG 1
`define xdma_0_pcie4_ip_gt_TX_USER_CLOCKING_CONTENTS__MMCM 2
`define xdma_0_pcie4_ip_gt_TX_USER_CLOCKING_INSTANCE_CTRL__SINGLE_INSTANCE 0
`define xdma_0_pcie4_ip_gt_TX_USER_CLOCKING_INSTANCE_CTRL__PER_CHANNEL 1
`define xdma_0_pcie4_ip_gt_TX_USER_CLOCKING_SOURCE__TXOUTCLK 0
`define xdma_0_pcie4_ip_gt_TX_USER_CLOCKING_SOURCE__IBUFDS 1

module xdma_0_pcie4_ip_gt_gtwizard_top #(

  parameter [191:0] C_CHANNEL_ENABLE                          = 192'b1,
  parameter integer C_COMMON_SCALING_FACTOR                   = 1,
  parameter real    C_CPLL_VCO_FREQUENCY                      = 5156.25,
  parameter integer C_FORCE_COMMONS                           = `xdma_0_pcie4_ip_gt_FORCE_COMMONS__DO_NOT_FORCE,
  parameter real    C_FREERUN_FREQUENCY                       = 200,
  parameter integer C_GT_TYPE                                 = `xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3,
  parameter integer C_GT_REV                                  = 17,
  parameter integer C_INCLUDE_CPLL_CAL                        = `xdma_0_pcie4_ip_gt_INCLUDE_CPLL_CAL__DEPENDENT,
  parameter         C_SIM_CPLL_CAL_BYPASS                     = 1'b0,
  parameter integer C_LOCATE_COMMON                           = `xdma_0_pcie4_ip_gt_LOCATE_COMMON__CORE,
  parameter integer C_LOCATE_RESET_CONTROLLER                 = `xdma_0_pcie4_ip_gt_LOCATE_RESET_CONTROLLER__CORE,
  parameter integer C_LOCATE_USER_DATA_WIDTH_SIZING           = `xdma_0_pcie4_ip_gt_LOCATE_USER_DATA_WIDTH_SIZING__CORE,
  parameter integer C_LOCATE_RX_BUFFER_BYPASS_CONTROLLER      = `xdma_0_pcie4_ip_gt_LOCATE_RX_BUFFER_BYPASS_CONTROLLER__CORE,
  parameter integer C_LOCATE_IN_SYSTEM_IBERT_CORE             = `xdma_0_pcie4_ip_gt_LOCATE_IN_SYSTEM_IBERT_CORE__NONE,
  parameter integer C_LOCATE_RX_USER_CLOCKING                 = `xdma_0_pcie4_ip_gt_LOCATE_RX_USER_CLOCKING__EXAMPLE_DESIGN,
  parameter integer C_LOCATE_TX_BUFFER_BYPASS_CONTROLLER      = `xdma_0_pcie4_ip_gt_LOCATE_TX_BUFFER_BYPASS_CONTROLLER__CORE,
  parameter integer C_LOCATE_TX_USER_CLOCKING                 = `xdma_0_pcie4_ip_gt_LOCATE_TX_USER_CLOCKING__EXAMPLE_DESIGN,
  parameter integer C_RESET_CONTROLLER_INSTANCE_CTRL          = `xdma_0_pcie4_ip_gt_RESET_CONTROLLER_INSTANCE_CTRL__SINGLE_INSTANCE,
  parameter integer C_RX_BUFFBYPASS_MODE                      = `xdma_0_pcie4_ip_gt_RX_BUFFBYPASS_MODE__AUTO,
  parameter integer C_RX_BUFFER_BYPASS_INSTANCE_CTRL          = `xdma_0_pcie4_ip_gt_RX_BUFFER_BYPASS_INSTANCE_CTRL__SINGLE_INSTANCE,
  parameter integer C_RX_BUFFER_MODE                          = `xdma_0_pcie4_ip_gt_RX_BUFFER_MODE__USE,
  parameter   [7:0] C_RX_CB_DISP                              = 8'b0,
  parameter   [7:0] C_RX_CB_K                                 = 8'b0,
  parameter integer C_RX_CB_MAX_LEVEL                         = 1,
  parameter integer C_RX_CB_LEN_SEQ                           = 1,
  parameter integer C_RX_CB_NUM_SEQ                           = 0,
  parameter  [79:0] C_RX_CB_VAL                               = 80'b0,
  parameter   [7:0] C_RX_CC_DISP                              = 8'b0,
  parameter integer C_RX_CC_ENABLE                            = `xdma_0_pcie4_ip_gt_RX_CC_ENABLE__DISABLED,
  parameter integer C_RESET_SEQUENCE_INTERVAL                 = 0,
  parameter   [7:0] C_RX_CC_K                                 = 8'b0,
  parameter integer C_RX_CC_LEN_SEQ                           = 1,
  parameter integer C_RX_CC_NUM_SEQ                           = 0,
  parameter integer C_RX_CC_PERIODICITY                       = 5000,
  parameter  [79:0] C_RX_CC_VAL                               = 80'b0,
  parameter integer C_RX_COMMA_M_ENABLE                       = `xdma_0_pcie4_ip_gt_RX_COMMA_M_ENABLE__DISABLED,
  parameter   [9:0] C_RX_COMMA_M_VAL                          = 10'b1010000011,
  parameter integer C_RX_COMMA_P_ENABLE                       = `xdma_0_pcie4_ip_gt_RX_COMMA_P_ENABLE__DISABLED,
  parameter   [9:0] C_RX_COMMA_P_VAL                          = 10'b0101111100,
  parameter integer C_RX_DATA_DECODING                        = `xdma_0_pcie4_ip_gt_RX_DATA_DECODING__RAW,
  parameter integer C_RX_ENABLE                               = `xdma_0_pcie4_ip_gt_RX_ENABLE__ENABLED,
  parameter integer C_RX_INT_DATA_WIDTH                       = 32,
  parameter real    C_RX_LINE_RATE                            = 10.3125,
  parameter integer C_RX_MASTER_CHANNEL_IDX                   = 0,
  parameter integer C_RX_OUTCLK_BUFG_GT_DIV                   = 1,
  parameter real    C_RX_OUTCLK_FREQUENCY                     = 322.265625,
  parameter integer C_RX_OUTCLK_SOURCE                        = `xdma_0_pcie4_ip_gt_RX_OUTCLK_SOURCE__RXOUTCLKPMA,
  parameter integer C_RX_PLL_TYPE                             = `xdma_0_pcie4_ip_gt_RX_PLL_TYPE__QPLL0,
  parameter [191:0] C_RX_RECCLK_OUTPUT                        = 192'b0,
  parameter real    C_RX_REFCLK_FREQUENCY                     = 257.8125,
  parameter integer C_RX_SLIDE_MODE                           = `xdma_0_pcie4_ip_gt_RX_SLIDE_MODE__OFF,
  parameter integer C_RX_USER_CLOCKING_CONTENTS               = `xdma_0_pcie4_ip_gt_RX_USER_CLOCKING_CONTENTS__BUFG_GT,
  parameter integer C_RX_USER_CLOCKING_INSTANCE_CTRL          = `xdma_0_pcie4_ip_gt_RX_USER_CLOCKING_INSTANCE_CTRL__SINGLE_INSTANCE,
  parameter integer C_RX_USER_CLOCKING_RATIO_FSRC_FUSRCLK     = 1,
  parameter integer C_RX_USER_CLOCKING_RATIO_FUSRCLK_FUSRCLK2 = 1,
  parameter integer C_RX_USER_CLOCKING_SOURCE                 = `xdma_0_pcie4_ip_gt_RX_USER_CLOCKING_SOURCE__RXOUTCLK,
  parameter integer C_RX_USER_DATA_WIDTH                      = 32,
  parameter real    C_RX_USRCLK_FREQUENCY                     = 322.265625,
  parameter real    C_RX_USRCLK2_FREQUENCY                    = 322.265625,
  parameter integer C_SECONDARY_QPLL_ENABLE                   = `xdma_0_pcie4_ip_gt_SECONDARY_QPLL_ENABLE__DISABLED,
  parameter real    C_SECONDARY_QPLL_REFCLK_FREQUENCY         = 257.8125,
  parameter integer C_TOTAL_NUM_CHANNELS                      = 1,
  parameter integer C_TOTAL_NUM_COMMONS                       = 1,
  parameter integer C_TOTAL_NUM_COMMONS_EXAMPLE               = 0,
  parameter integer C_TXPROGDIV_FREQ_ENABLE                   = `xdma_0_pcie4_ip_gt_TXPROGDIV_FREQ_ENABLE__DISABLED,
  parameter integer C_TXPROGDIV_FREQ_SOURCE                   = `xdma_0_pcie4_ip_gt_TXPROGDIV_FREQ_SOURCE__QPLL0,
  parameter real    C_TXPROGDIV_FREQ_VAL                      = 322.265625,
  parameter integer C_TX_BUFFBYPASS_MODE                      = `xdma_0_pcie4_ip_gt_TX_BUFFBYPASS_MODE__AUTO,
  parameter integer C_TX_BUFFER_BYPASS_INSTANCE_CTRL          = `xdma_0_pcie4_ip_gt_TX_BUFFER_BYPASS_INSTANCE_CTRL__SINGLE_INSTANCE,
  parameter integer C_TX_BUFFER_MODE                          = `xdma_0_pcie4_ip_gt_TX_BUFFER_MODE__USE,
  parameter integer C_TX_DATA_ENCODING                        = `xdma_0_pcie4_ip_gt_TX_DATA_ENCODING__RAW,
  parameter integer C_TX_ENABLE                               = `xdma_0_pcie4_ip_gt_TX_ENABLE__ENABLED,
  parameter integer C_TX_INT_DATA_WIDTH                       = 32,
  parameter real    C_TX_LINE_RATE                            = 10.3125,
  parameter integer C_TX_MASTER_CHANNEL_IDX                   = 0,
  parameter integer C_TX_OUTCLK_BUFG_GT_DIV                   = 1,
  parameter real    C_TX_OUTCLK_FREQUENCY                     = 322.265625,
  parameter integer C_TX_OUTCLK_SOURCE                        = `xdma_0_pcie4_ip_gt_TX_OUTCLK_SOURCE__TXOUTCLKPMA,
  parameter integer C_TX_PLL_TYPE                             = `xdma_0_pcie4_ip_gt_TX_PLL_TYPE__QPLL0,
  parameter real    C_TX_REFCLK_FREQUENCY                     = 257.8125,
  parameter integer C_TX_USER_CLOCKING_CONTENTS               = `xdma_0_pcie4_ip_gt_TX_USER_CLOCKING_CONTENTS__BUFG_GT,
  parameter integer C_TX_USER_CLOCKING_INSTANCE_CTRL          = `xdma_0_pcie4_ip_gt_TX_USER_CLOCKING_INSTANCE_CTRL__SINGLE_INSTANCE,
  parameter integer C_TX_USER_CLOCKING_RATIO_FSRC_FUSRCLK     = 1,
  parameter integer C_TX_USER_CLOCKING_RATIO_FUSRCLK_FUSRCLK2 = 1,
  parameter integer C_TX_USER_CLOCKING_SOURCE                 = `xdma_0_pcie4_ip_gt_TX_USER_CLOCKING_SOURCE__TXOUTCLK,
  parameter integer C_TX_USER_DATA_WIDTH                      = 32,
  parameter real    C_TX_USRCLK_FREQUENCY                     = 322.265625,
  parameter real    C_TX_USRCLK2_FREQUENCY                    = 322.265625

)(

  // Transmitter user clocking network helper block ports
  input  wire [(C_TX_USER_CLOCKING_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_userclk_tx_reset_in,
  input  wire [(C_TX_USER_CLOCKING_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_userclk_tx_active_in,
  output wire [(C_TX_USER_CLOCKING_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_userclk_tx_srcclk_out,
  output wire [(C_TX_USER_CLOCKING_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_userclk_tx_usrclk_out,
  output wire [(C_TX_USER_CLOCKING_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_userclk_tx_usrclk2_out,
  output wire [(C_TX_USER_CLOCKING_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_userclk_tx_active_out,

  // Receiver user clocking network helper block ports
  input  wire [(C_RX_USER_CLOCKING_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_userclk_rx_reset_in,
  input  wire [(C_RX_USER_CLOCKING_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_userclk_rx_active_in,
  output wire [(C_RX_USER_CLOCKING_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_userclk_rx_srcclk_out,
  output wire [(C_RX_USER_CLOCKING_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_userclk_rx_usrclk_out,
  output wire [(C_RX_USER_CLOCKING_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_userclk_rx_usrclk2_out,
  output wire [(C_RX_USER_CLOCKING_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_userclk_rx_active_out,

  // Transmitter buffer bypass controller helper block ports
  input  wire [(C_TX_BUFFER_BYPASS_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_buffbypass_tx_reset_in,
  input  wire [(C_TX_BUFFER_BYPASS_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_buffbypass_tx_start_user_in,
  output wire [(C_TX_BUFFER_BYPASS_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_buffbypass_tx_done_out,
  output wire [(C_TX_BUFFER_BYPASS_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_buffbypass_tx_error_out,

  // Receiver buffer bypass controller helper block ports
  input  wire [(C_RX_BUFFER_BYPASS_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_buffbypass_rx_reset_in,
  input  wire [(C_RX_BUFFER_BYPASS_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_buffbypass_rx_start_user_in,
  output wire [(C_RX_BUFFER_BYPASS_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_buffbypass_rx_done_out,
  output wire [(C_RX_BUFFER_BYPASS_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_buffbypass_rx_error_out,

  // Reset controller helper block ports
  input  wire [(C_RESET_CONTROLLER_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_reset_clk_freerun_in,
  input  wire [(C_RESET_CONTROLLER_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_reset_all_in,
  input  wire [(C_RESET_CONTROLLER_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_reset_tx_pll_and_datapath_in,
  input  wire [(C_RESET_CONTROLLER_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_reset_tx_datapath_in,
  input  wire [(C_RESET_CONTROLLER_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_reset_rx_pll_and_datapath_in,
  input  wire [(C_RESET_CONTROLLER_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_reset_rx_datapath_in,
  input  wire [(C_RESET_CONTROLLER_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_reset_tx_done_in,
  input  wire [(C_RESET_CONTROLLER_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_reset_rx_done_in,
  input  wire [                                  (`xdma_0_pcie4_ip_gt_SF_CM-1):0] gtwiz_reset_qpll0lock_in,
  input  wire [                                  (`xdma_0_pcie4_ip_gt_SF_CM-1):0] gtwiz_reset_qpll1lock_in,
  output wire [(C_RESET_CONTROLLER_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_reset_rx_cdr_stable_out,
  output wire [(C_RESET_CONTROLLER_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_reset_tx_done_out,
  output wire [(C_RESET_CONTROLLER_INSTANCE_CTRL*(`xdma_0_pcie4_ip_gt_N_CH-1)):0] gtwiz_reset_rx_done_out,
  output wire [                                  (`xdma_0_pcie4_ip_gt_SF_CM-1):0] gtwiz_reset_qpll0reset_out,
  output wire [                                  (`xdma_0_pcie4_ip_gt_SF_CM-1):0] gtwiz_reset_qpll1reset_out,

  // CPLL calibration block ports
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH* 18)-1:0] gtwiz_gthe3_cpll_cal_txoutclk_period_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH* 18)-1:0] gtwiz_gthe3_cpll_cal_cnt_tol_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] gtwiz_gthe3_cpll_cal_bufg_ce_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH* 18)-1:0] gtwiz_gthe4_cpll_cal_txoutclk_period_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH* 18)-1:0] gtwiz_gthe4_cpll_cal_cnt_tol_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] gtwiz_gthe4_cpll_cal_bufg_ce_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH* 18)-1:0] gtwiz_gtye4_cpll_cal_txoutclk_period_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH* 18)-1:0] gtwiz_gtye4_cpll_cal_cnt_tol_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] gtwiz_gtye4_cpll_cal_bufg_ce_in,

  // Transmitter user data width sizing helper block ports
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*C_TX_USER_DATA_WIDTH)-1:0] gtwiz_userdata_tx_in,

  // Receiver user data width sizing helper block ports
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*C_RX_USER_DATA_WIDTH)-1:0] gtwiz_userdata_rx_out,

  // Transceiver common block ports
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] bgbypassb_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] bgmonitorenb_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] bgpdb_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  5)-1:0] bgrcalovrd_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] bgrcalovrdenb_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_SF_CM*  9))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_SF_CM* 10))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_SF_CM* 16))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM* 16))-1:0] drpaddr_common_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] drpclk_common_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM* 16)-1:0] drpdi_common_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] drpen_common_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] drpwe_common_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] gtgrefclk0_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] gtgrefclk1_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] gtnorthrefclk00_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] gtnorthrefclk01_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] gtnorthrefclk10_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] gtnorthrefclk11_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] gtrefclk00_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] gtrefclk01_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] gtrefclk10_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] gtrefclk11_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] gtsouthrefclk00_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] gtsouthrefclk01_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] gtsouthrefclk10_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] gtsouthrefclk11_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  3))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  3))-1:0] pcierateqpll0_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  3))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  3))-1:0] pcierateqpll1_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  8)-1:0] pmarsvd0_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  8)-1:0] pmarsvd1_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] qpll0clkrsvd0_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))-1:0] qpll0clkrsvd1_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  8))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  8))-1:0] qpll0fbdiv_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] qpll0lockdetclk_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] qpll0locken_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] qpll0pd_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  3)-1:0] qpll0refclksel_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] qpll0reset_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] qpll1clkrsvd0_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))-1:0] qpll1clkrsvd1_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  8))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  8))-1:0] qpll1fbdiv_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] qpll1lockdetclk_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] qpll1locken_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] qpll1pd_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  3)-1:0] qpll1refclksel_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] qpll1reset_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  8)-1:0] qpllrsvd1_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  5)-1:0] qpllrsvd2_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  5)-1:0] qpllrsvd3_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  8)-1:0] qpllrsvd4_in,
  input  wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] rcalenb_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_SF_CM* 25))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_SF_CM* 25))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM* 25))-1:0] sdm0data_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))-1:0] sdm0reset_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))-1:0] sdm0toggle_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_SF_CM*  2))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  2))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  2))-1:0] sdm0width_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_SF_CM* 25))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_SF_CM* 25))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM* 25))-1:0] sdm1data_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))-1:0] sdm1reset_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))-1:0] sdm1toggle_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_SF_CM*  2))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  2))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  2))-1:0] sdm1width_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_SF_CM* 10))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] tcongpi_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] tconpowerup_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  2))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] tconreset_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  2))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] tconrsvdin1_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))-1:0] ubcfgstreamen_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM* 16))-1:0] ubdo_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))-1:0] ubdrdy_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))-1:0] ubenable_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  2))-1:0] ubgpi_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  2))-1:0] ubintr_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))-1:0] ubiolmbrst_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))-1:0] ubmbrst_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))-1:0] ubmdmcapture_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))-1:0] ubmdmdbgrst_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))-1:0] ubmdmdbgupdate_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  4))-1:0] ubmdmregen_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))-1:0] ubmdmshift_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))-1:0] ubmdmsysrst_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))-1:0] ubmdmtck_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))-1:0] ubmdmtdi_in,

  output wire [(`xdma_0_pcie4_ip_gt_SF_CM* 16)-1:0] drpdo_common_out,
  output wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] drprdy_common_out,
  output wire [(`xdma_0_pcie4_ip_gt_SF_CM*  8)-1:0] pmarsvdout0_out,
  output wire [(`xdma_0_pcie4_ip_gt_SF_CM*  8)-1:0] pmarsvdout1_out,
  output wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] qpll0fbclklost_out,
  output wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] qpll0lock_out,
  output wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] qpll0outclk_out,
  output wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] qpll0outrefclk_out,
  output wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] qpll0refclklost_out,
  output wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] qpll1fbclklost_out,
  output wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] qpll1lock_out,
  output wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] qpll1outclk_out,
  output wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] qpll1outrefclk_out,
  output wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] qpll1refclklost_out,
  output wire [(`xdma_0_pcie4_ip_gt_SF_CM*  8)-1:0] qplldmonitor0_out,
  output wire [(`xdma_0_pcie4_ip_gt_SF_CM*  8)-1:0] qplldmonitor1_out,
  output wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] refclkoutmonitor0_out,
  output wire [(`xdma_0_pcie4_ip_gt_SF_CM*  1)-1:0] refclkoutmonitor1_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_SF_CM*  2))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_SF_CM*  2))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] rxrecclk0_sel_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_SF_CM*  2))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_SF_CM*  2))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] rxrecclk1_sel_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  2))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  2))-1:0] rxrecclk0sel_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  2))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  2))-1:0] rxrecclk1sel_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_SF_CM*  4))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  4))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  4))-1:0] sdm0finalout_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_SF_CM* 15))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_SF_CM* 15))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM* 15))-1:0] sdm0testdata_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_SF_CM*  4))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  4))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  4))-1:0] sdm1finalout_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_SF_CM* 15))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_SF_CM* 15))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM* 15))-1:0] sdm1testdata_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_SF_CM* 10))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] tcongpo_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] tconrsvdout0_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM* 16))-1:0] ubdaddr_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))-1:0] ubden_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM* 16))-1:0] ubdi_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))-1:0] ubdwe_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))-1:0] ubmdmtdo_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))-1:0] ubrsvdout_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_SF_CM*  1))-1:0] ubtxuart_out,

  // Transceiver channel block ports
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] cdrstepdir_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] cdrstepsq_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] cdrstepsx_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] cfgreset_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] clkrsvd0_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] clkrsvd1_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] cpllfreqlock_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] cplllockdetclk_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] cplllocken_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] cpllpd_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  3)-1:0] cpllrefclksel_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] cpllreset_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] dmonfiforeset_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] dmonitorclk_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  9))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH* 10))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH* 10))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH* 10))-1:0] drpaddr_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] drpclk_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH* 16)-1:0] drpdi_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] drpen_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] drprst_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] drpwe_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] elpcaldvorwren_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] elpcalpaorwren_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] evoddphicaldone_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] evoddphicalstart_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] evoddphidrden_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] evoddphidwren_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] evoddphixrden_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] evoddphixwren_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] eyescanmode_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] eyescanreset_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] eyescantrigger_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] freqos_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] gtgrefclk_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] gthrxn_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] gthrxp_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] gtnorthrefclk0_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] gtnorthrefclk1_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] gtrefclk0_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] gtrefclk1_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] gtresetsel_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH* 16)-1:0] gtrsvd_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] gtrxreset_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] gtrxresetsel_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] gtsouthrefclk0_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] gtsouthrefclk1_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] gttxreset_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] gttxresetsel_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] incpctrl_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] gtyrxn_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] gtyrxp_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  3)-1:0] loopback_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH* 16))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] looprsvd_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] lpbkrxtxseren_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] lpbktxrxseren_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] pcieeqrxeqadaptdone_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] pcierstidle_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] pciersttxsyncstart_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] pcieuserratedone_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH* 16)-1:0] pcsrsvdin_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  5))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  5))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] pcsrsvdin2_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  5))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  5))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] pmarsvdin_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] qpll0clk_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] qpll0freqlock_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] qpll0refclk_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] qpll1clk_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] qpll1freqlock_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] qpll1refclk_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] resetovrd_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] rstclkentx_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rx8b10ben_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] rxafecfoken_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxbufreset_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxcdrfreqreset_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxcdrhold_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxcdrovrden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxcdrreset_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] rxcdrresetrsv_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxchbonden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  5)-1:0] rxchbondi_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  3)-1:0] rxchbondlevel_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxchbondmaster_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxchbondslave_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] rxckcalreset_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  7))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  7))-1:0] rxckcalstart_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxcommadeten_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  2))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  2))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] rxdfeagcctrl_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] rxdccforcestart_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfeagchold_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfeagcovrden_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  4))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  4))-1:0] rxdfecfokfcnum_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] rxdfecfokfen_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] rxdfecfokfpulse_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] rxdfecfokhold_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] rxdfecfokovren_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] rxdfekhhold_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] rxdfekhovrden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfelfhold_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfelfovrden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfelpmreset_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfetap10hold_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfetap10ovrden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfetap11hold_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfetap11ovrden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfetap12hold_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfetap12ovrden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfetap13hold_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfetap13ovrden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfetap14hold_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfetap14ovrden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfetap15hold_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfetap15ovrden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfetap2hold_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfetap2ovrden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfetap3hold_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfetap3ovrden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfetap4hold_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfetap4ovrden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfetap5hold_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfetap5ovrden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfetap6hold_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfetap6ovrden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfetap7hold_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfetap7ovrden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfetap8hold_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfetap8ovrden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfetap9hold_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfetap9ovrden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfeuthold_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfeutovrden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfevphold_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfevpovrden_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] rxdfevsen_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdfexyden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdlybypass_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdlyen_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdlyovrden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdlysreset_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  2)-1:0] rxelecidlemode_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] rxeqtraining_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxgearboxslip_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxlatclk_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxlpmen_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxlpmgchold_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxlpmgcovrden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxlpmhfhold_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxlpmhfovrden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxlpmlfhold_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxlpmlfklovrden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxlpmoshold_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxlpmosovrden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxmcommaalignen_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  2)-1:0] rxmonitorsel_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxoobreset_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxoscalreset_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxoshold_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  4))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  4))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] rxosintcfg_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] rxosinten_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] rxosinthold_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] rxosintovrden_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] rxosintstrobe_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] rxosinttestovrden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxosovrden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  3)-1:0] rxoutclksel_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxpcommaalignen_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxpcsreset_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  2)-1:0] rxpd_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxphalign_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxphalignen_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxphdlypd_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxphdlyreset_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] rxphovrden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  2)-1:0] rxpllclksel_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxpmareset_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxpolarity_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxprbscntreset_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  4)-1:0] rxprbssel_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxprogdivreset_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] rxqpien_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  3)-1:0] rxrate_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxratemode_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxslide_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxslipoutclk_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxslippma_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxsyncallin_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxsyncin_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxsyncmode_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  2)-1:0] rxsysclksel_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] rxtermination_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxuserrdy_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxusrclk_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxusrclk2_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] sigvalidclk_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH* 20)-1:0] tstin_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  8)-1:0] tx8b10bbypass_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] tx8b10ben_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  3))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  3))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] txbufdiffctrl_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txcominit_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txcomsas_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txcomwake_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH* 16)-1:0] txctrl0_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH* 16)-1:0] txctrl1_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  8)-1:0] txctrl2_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*128)-1:0] txdata_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  8)-1:0] txdataextendrsvd_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] txdccforcestart_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] txdccreset_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  2))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  2))-1:0] txdeemph_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txdetectrx_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  4))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  5))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  5))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  5))-1:0] txdiffctrl_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] txdiffpd_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txdlybypass_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txdlyen_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txdlyhold_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txdlyovrden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txdlysreset_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txdlyupdown_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txelecidle_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] txelforcestart_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  6)-1:0] txheader_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txinhibit_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txlatclk_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] txlfpstreset_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] txlfpsu2lpexit_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] txlfpsu3wake_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  7)-1:0] txmaincursor_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  3)-1:0] txmargin_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] txmuxdcdexhold_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] txmuxdcdorwren_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] txoneszeros_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  3)-1:0] txoutclksel_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txpcsreset_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  2)-1:0] txpd_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txpdelecidlemode_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txphalign_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txphalignen_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txphdlypd_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txphdlyreset_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txphdlytstclk_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txphinit_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txphovrden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txpippmen_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txpippmovrden_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txpippmpd_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txpippmsel_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  5)-1:0] txpippmstepsize_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txpisopd_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  2)-1:0] txpllclksel_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txpmareset_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txpolarity_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  5)-1:0] txpostcursor_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] txpostcursorinv_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txprbsforceerr_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  4)-1:0] txprbssel_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  5)-1:0] txprecursor_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] txprecursorinv_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txprogdivreset_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] txqpibiasen_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] txqpistrongpdown_in,
  input  wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] txqpiweakpup_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  3)-1:0] txrate_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txratemode_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  7)-1:0] txsequence_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txswing_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txsyncallin_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txsyncin_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txsyncmode_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  2)-1:0] txsysclksel_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txuserrdy_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txusrclk_in,
  input  wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txusrclk2_in,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  3))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  3))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] bufgtce_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  3)-1:0] bufgtcemask_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  9)-1:0] bufgtdiv_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  3))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  3))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] bufgtreset_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  3)-1:0] bufgtrstmask_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] cpllfbclklost_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] cplllock_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] cpllrefclklost_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH* 17))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH* 17))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH* 16))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH* 16))-1:0] dmonitorout_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] dmonitoroutclk_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH* 16)-1:0] drpdo_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] drprdy_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] eyescandataerror_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] gthtxn_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] gthtxp_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] gtpowergood_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] gtrefclkmonitor_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] gtytxn_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] gtytxp_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] pcierategen3_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] pcierateidle_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  2)-1:0] pcierateqpllpd_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  2)-1:0] pcierateqpllreset_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] pciesynctxsyncdone_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] pcieusergen3rdy_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] pcieuserphystatusrst_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] pcieuserratestart_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH* 12))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH* 16))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH* 16))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH* 16))-1:0] pcsrsvdout_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] phystatus_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  8))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  8))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH* 16))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH* 16))-1:0] pinrsrvdas_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] powerpresent_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] resetexception_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  3)-1:0] rxbufstatus_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxbyteisaligned_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxbyterealign_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxcdrlock_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxcdrphdone_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxchanbondseq_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxchanisaligned_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxchanrealign_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  5)-1:0] rxchbondo_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] rxckcaldone_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  2)-1:0] rxclkcorcnt_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxcominitdet_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxcommadet_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxcomsasdet_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxcomwakedet_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH* 16)-1:0] rxctrl0_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH* 16)-1:0] rxctrl1_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  8)-1:0] rxctrl2_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  8)-1:0] rxctrl3_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*128)-1:0] rxdata_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  8)-1:0] rxdataextendrsvd_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  2)-1:0] rxdatavalid_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxdlysresetdone_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxelecidle_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  6)-1:0] rxheader_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  2)-1:0] rxheadervalid_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] rxlfpstresetdet_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] rxlfpsu2lpexitdet_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] rxlfpsu3wakedet_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  7))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  7))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  8))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  8))-1:0] rxmonitorout_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxosintdone_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxosintstarted_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxosintstrobedone_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxosintstrobestarted_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxoutclk_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxoutclkfabric_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxoutclkpcs_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxphaligndone_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxphalignerr_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxpmaresetdone_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxprbserr_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxprbslocked_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxprgdivresetdone_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] rxqpisenn_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] rxqpisenp_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxratedone_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxrecclkout_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxresetdone_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxsliderdy_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxslipdone_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxslipoutclkrdy_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxslippmardy_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  2)-1:0] rxstartofseq_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  3)-1:0] rxstatus_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxsyncdone_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxsyncout_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] rxvalid_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  2)-1:0] txbufstatus_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txcomfinish_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))-1:0] txdccdone_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txdlysresetdone_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txoutclk_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txoutclkfabric_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txoutclkpcs_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txphaligndone_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txphinitdone_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txpmaresetdone_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txprgdivresetdone_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] txqpisenn_out,
  output wire [((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3)*(1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4)*(`xdma_0_pcie4_ip_gt_N_CH*  1))+
               ((C_GT_TYPE==`xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4)*(1))-1:0] txqpisenp_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txratedone_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txresetdone_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txsyncdone_out,
  output wire [(`xdma_0_pcie4_ip_gt_N_CH*  1)-1:0] txsyncout_out

);


  // ================================================================================================================
  // CONDITIONAL INSTANTIATION OF TRANSCEIVERS WIZARD SUBMODULE BASED ON TRANSCEIVER TYPE
  // ================================================================================================================

  generate if (C_GT_TYPE == `xdma_0_pcie4_ip_gt_GT_TYPE__GTHE3) begin : gen_gtwizard_gthe3_top

    // Generate GTHE3-type Transceivers Wizard submodule
    xdma_0_pcie4_ip_gt_gtwizard_gthe3 #(
      .C_CHANNEL_ENABLE                          (C_CHANNEL_ENABLE                         ),
      .C_COMMON_SCALING_FACTOR                   (C_COMMON_SCALING_FACTOR                  ),
      .C_CPLL_VCO_FREQUENCY                      (C_CPLL_VCO_FREQUENCY                     ),
      .C_FREERUN_FREQUENCY                       (C_FREERUN_FREQUENCY                      ),
      .C_GT_REV                                  (C_GT_REV                                 ),
      .C_INCLUDE_CPLL_CAL                        (C_INCLUDE_CPLL_CAL                       ),
      .C_LOCATE_RESET_CONTROLLER                 (C_LOCATE_RESET_CONTROLLER                ),
      .C_LOCATE_USER_DATA_WIDTH_SIZING           (C_LOCATE_USER_DATA_WIDTH_SIZING          ),
      .C_LOCATE_RX_BUFFER_BYPASS_CONTROLLER      (C_LOCATE_RX_BUFFER_BYPASS_CONTROLLER     ),
      .C_LOCATE_RX_USER_CLOCKING                 (C_LOCATE_RX_USER_CLOCKING                ),
      .C_LOCATE_TX_BUFFER_BYPASS_CONTROLLER      (C_LOCATE_TX_BUFFER_BYPASS_CONTROLLER     ),
      .C_LOCATE_TX_USER_CLOCKING                 (C_LOCATE_TX_USER_CLOCKING                ),
      .C_RESET_CONTROLLER_INSTANCE_CTRL          (C_RESET_CONTROLLER_INSTANCE_CTRL         ),
      .C_RX_BUFFBYPASS_MODE                      (C_RX_BUFFBYPASS_MODE                     ),
      .C_RX_BUFFER_BYPASS_INSTANCE_CTRL          (C_RX_BUFFER_BYPASS_INSTANCE_CTRL         ),
      .C_RX_BUFFER_MODE                          (C_RX_BUFFER_MODE                         ),
      .C_RX_DATA_DECODING                        (C_RX_DATA_DECODING                       ),
      .C_RX_ENABLE                               (C_RX_ENABLE                              ),
      .C_RX_INT_DATA_WIDTH                       (C_RX_INT_DATA_WIDTH                      ),
      .C_RX_LINE_RATE                            (C_RX_LINE_RATE                           ),
      .C_RX_MASTER_CHANNEL_IDX                   (C_RX_MASTER_CHANNEL_IDX                  ),
      .C_RX_OUTCLK_BUFG_GT_DIV                   (C_RX_OUTCLK_BUFG_GT_DIV                  ),
      .C_RX_PLL_TYPE                             (C_RX_PLL_TYPE                            ),
      .C_RX_USER_CLOCKING_CONTENTS               (C_RX_USER_CLOCKING_CONTENTS              ),
      .C_RX_USER_CLOCKING_INSTANCE_CTRL          (C_RX_USER_CLOCKING_INSTANCE_CTRL         ),
      .C_RX_USER_CLOCKING_RATIO_FUSRCLK_FUSRCLK2 (C_RX_USER_CLOCKING_RATIO_FUSRCLK_FUSRCLK2),
      .C_RX_USER_CLOCKING_SOURCE                 (C_RX_USER_CLOCKING_SOURCE                ),
      .C_RX_USER_DATA_WIDTH                      (C_RX_USER_DATA_WIDTH                     ),
      .C_TOTAL_NUM_CHANNELS                      (C_TOTAL_NUM_CHANNELS                     ),
      .C_TOTAL_NUM_COMMONS                       (C_TOTAL_NUM_COMMONS                      ),
      .C_TXPROGDIV_FREQ_ENABLE                   (C_TXPROGDIV_FREQ_ENABLE                  ),
      .C_TXPROGDIV_FREQ_SOURCE                   (C_TXPROGDIV_FREQ_SOURCE                  ),
      .C_TX_BUFFBYPASS_MODE                      (C_TX_BUFFBYPASS_MODE                     ),
      .C_TX_BUFFER_BYPASS_INSTANCE_CTRL          (C_TX_BUFFER_BYPASS_INSTANCE_CTRL         ),
      .C_TX_BUFFER_MODE                          (C_TX_BUFFER_MODE                         ),
      .C_TX_DATA_ENCODING                        (C_TX_DATA_ENCODING                       ),
      .C_TX_ENABLE                               (C_TX_ENABLE                              ),
      .C_TX_INT_DATA_WIDTH                       (C_TX_INT_DATA_WIDTH                      ),
      .C_TX_MASTER_CHANNEL_IDX                   (C_TX_MASTER_CHANNEL_IDX                  ),
      .C_TX_OUTCLK_BUFG_GT_DIV                   (C_TX_OUTCLK_BUFG_GT_DIV                  ),
      .C_TX_PLL_TYPE                             (C_TX_PLL_TYPE                            ),
      .C_TX_USER_CLOCKING_CONTENTS               (C_TX_USER_CLOCKING_CONTENTS              ),
      .C_TX_USER_CLOCKING_INSTANCE_CTRL          (C_TX_USER_CLOCKING_INSTANCE_CTRL         ),
      .C_TX_USER_CLOCKING_RATIO_FUSRCLK_FUSRCLK2 (C_TX_USER_CLOCKING_RATIO_FUSRCLK_FUSRCLK2),
      .C_TX_USER_CLOCKING_SOURCE                 (C_TX_USER_CLOCKING_SOURCE                ),
      .C_TX_USER_DATA_WIDTH                      (C_TX_USER_DATA_WIDTH                     )
    ) xdma_0_pcie4_ip_gt_gtwizard_gthe3_inst (
      .gtwiz_userclk_tx_reset_in               (gtwiz_userclk_tx_reset_in              ),
      .gtwiz_userclk_tx_active_in              (gtwiz_userclk_tx_active_in             ),
      .gtwiz_userclk_tx_srcclk_out             (gtwiz_userclk_tx_srcclk_out            ),
      .gtwiz_userclk_tx_usrclk_out             (gtwiz_userclk_tx_usrclk_out            ),
      .gtwiz_userclk_tx_usrclk2_out            (gtwiz_userclk_tx_usrclk2_out           ),
      .gtwiz_userclk_tx_active_out             (gtwiz_userclk_tx_active_out            ),
      .gtwiz_userclk_rx_reset_in               (gtwiz_userclk_rx_reset_in              ),
      .gtwiz_userclk_rx_active_in              (gtwiz_userclk_rx_active_in             ),
      .gtwiz_userclk_rx_srcclk_out             (gtwiz_userclk_rx_srcclk_out            ),
      .gtwiz_userclk_rx_usrclk_out             (gtwiz_userclk_rx_usrclk_out            ),
      .gtwiz_userclk_rx_usrclk2_out            (gtwiz_userclk_rx_usrclk2_out           ),
      .gtwiz_userclk_rx_active_out             (gtwiz_userclk_rx_active_out            ),
      .gtwiz_buffbypass_tx_reset_in            (gtwiz_buffbypass_tx_reset_in           ),
      .gtwiz_buffbypass_tx_start_user_in       (gtwiz_buffbypass_tx_start_user_in      ),
      .gtwiz_buffbypass_tx_done_out            (gtwiz_buffbypass_tx_done_out           ),
      .gtwiz_buffbypass_tx_error_out           (gtwiz_buffbypass_tx_error_out          ),
      .gtwiz_buffbypass_rx_reset_in            (gtwiz_buffbypass_rx_reset_in           ),
      .gtwiz_buffbypass_rx_start_user_in       (gtwiz_buffbypass_rx_start_user_in      ),
      .gtwiz_buffbypass_rx_done_out            (gtwiz_buffbypass_rx_done_out           ),
      .gtwiz_buffbypass_rx_error_out           (gtwiz_buffbypass_rx_error_out          ),
      .gtwiz_reset_clk_freerun_in              (gtwiz_reset_clk_freerun_in             ),
      .gtwiz_reset_all_in                      (gtwiz_reset_all_in                     ),
      .gtwiz_reset_tx_pll_and_datapath_in      (gtwiz_reset_tx_pll_and_datapath_in     ),
      .gtwiz_reset_tx_datapath_in              (gtwiz_reset_tx_datapath_in             ),
      .gtwiz_reset_rx_pll_and_datapath_in      (gtwiz_reset_rx_pll_and_datapath_in     ),
      .gtwiz_reset_rx_datapath_in              (gtwiz_reset_rx_datapath_in             ),
      .gtwiz_reset_tx_done_in                  (gtwiz_reset_tx_done_in                 ),
      .gtwiz_reset_rx_done_in                  (gtwiz_reset_rx_done_in                 ),
      .gtwiz_reset_qpll0lock_in                (gtwiz_reset_qpll0lock_in               ),
      .gtwiz_reset_qpll1lock_in                (gtwiz_reset_qpll1lock_in               ),
      .gtwiz_reset_rx_cdr_stable_out           (gtwiz_reset_rx_cdr_stable_out          ),
      .gtwiz_reset_tx_done_out                 (gtwiz_reset_tx_done_out                ),
      .gtwiz_reset_rx_done_out                 (gtwiz_reset_rx_done_out                ),
      .gtwiz_reset_qpll0reset_out              (gtwiz_reset_qpll0reset_out             ),
      .gtwiz_reset_qpll1reset_out              (gtwiz_reset_qpll1reset_out             ),
      .gtwiz_gthe3_cpll_cal_txoutclk_period_in (gtwiz_gthe3_cpll_cal_txoutclk_period_in),
      .gtwiz_gthe3_cpll_cal_cnt_tol_in         (gtwiz_gthe3_cpll_cal_cnt_tol_in        ),
      .gtwiz_gthe3_cpll_cal_bufg_ce_in         (gtwiz_gthe3_cpll_cal_bufg_ce_in        ),
      .gtwiz_userdata_tx_in                    (gtwiz_userdata_tx_in                   ),
      .gtwiz_userdata_rx_out                   (gtwiz_userdata_rx_out                  ),
      .bgbypassb_in                            (bgbypassb_in                           ),
      .bgmonitorenb_in                         (bgmonitorenb_in                        ),
      .bgpdb_in                                (bgpdb_in                               ),
      .bgrcalovrd_in                           (bgrcalovrd_in                          ),
      .bgrcalovrdenb_in                        (bgrcalovrdenb_in                       ),
      .drpaddr_common_in                       (drpaddr_common_in                      ),
      .drpclk_common_in                        (drpclk_common_in                       ),
      .drpdi_common_in                         (drpdi_common_in                        ),
      .drpen_common_in                         (drpen_common_in                        ),
      .drpwe_common_in                         (drpwe_common_in                        ),
      .gtgrefclk0_in                           (gtgrefclk0_in                          ),
      .gtgrefclk1_in                           (gtgrefclk1_in                          ),
      .gtnorthrefclk00_in                      (gtnorthrefclk00_in                     ),
      .gtnorthrefclk01_in                      (gtnorthrefclk01_in                     ),
      .gtnorthrefclk10_in                      (gtnorthrefclk10_in                     ),
      .gtnorthrefclk11_in                      (gtnorthrefclk11_in                     ),
      .gtrefclk00_in                           (gtrefclk00_in                          ),
      .gtrefclk01_in                           (gtrefclk01_in                          ),
      .gtrefclk10_in                           (gtrefclk10_in                          ),
      .gtrefclk11_in                           (gtrefclk11_in                          ),
      .gtsouthrefclk00_in                      (gtsouthrefclk00_in                     ),
      .gtsouthrefclk01_in                      (gtsouthrefclk01_in                     ),
      .gtsouthrefclk10_in                      (gtsouthrefclk10_in                     ),
      .gtsouthrefclk11_in                      (gtsouthrefclk11_in                     ),
      .pmarsvd0_in                             (pmarsvd0_in                            ),
      .pmarsvd1_in                             (pmarsvd1_in                            ),
      .qpll0clkrsvd0_in                        (qpll0clkrsvd0_in                       ),
      .qpll0clkrsvd1_in                        (qpll0clkrsvd1_in                       ),
      .qpll0lockdetclk_in                      (qpll0lockdetclk_in                     ),
      .qpll0locken_in                          (qpll0locken_in                         ),
      .qpll0pd_in                              (qpll0pd_in                             ),
      .qpll0refclksel_in                       (qpll0refclksel_in                      ),
      .qpll0reset_in                           (qpll0reset_in                          ),
      .qpll1clkrsvd0_in                        (qpll1clkrsvd0_in                       ),
      .qpll1clkrsvd1_in                        (qpll1clkrsvd1_in                       ),
      .qpll1lockdetclk_in                      (qpll1lockdetclk_in                     ),
      .qpll1locken_in                          (qpll1locken_in                         ),
      .qpll1pd_in                              (qpll1pd_in                             ),
      .qpll1refclksel_in                       (qpll1refclksel_in                      ),
      .qpll1reset_in                           (qpll1reset_in                          ),
      .qpllrsvd1_in                            (qpllrsvd1_in                           ),
      .qpllrsvd2_in                            (qpllrsvd2_in                           ),
      .qpllrsvd3_in                            (qpllrsvd3_in                           ),
      .qpllrsvd4_in                            (qpllrsvd4_in                           ),
      .rcalenb_in                              (rcalenb_in                             ),
      .drpdo_common_out                        (drpdo_common_out                       ),
      .drprdy_common_out                       (drprdy_common_out                      ),
      .pmarsvdout0_out                         (pmarsvdout0_out                        ),
      .pmarsvdout1_out                         (pmarsvdout1_out                        ),
      .qpll0fbclklost_out                      (qpll0fbclklost_out                     ),
      .qpll0lock_out                           (qpll0lock_out                          ),
      .qpll0outclk_out                         (qpll0outclk_out                        ),
      .qpll0outrefclk_out                      (qpll0outrefclk_out                     ),
      .qpll0refclklost_out                     (qpll0refclklost_out                    ),
      .qpll1fbclklost_out                      (qpll1fbclklost_out                     ),
      .qpll1lock_out                           (qpll1lock_out                          ),
      .qpll1outclk_out                         (qpll1outclk_out                        ),
      .qpll1outrefclk_out                      (qpll1outrefclk_out                     ),
      .qpll1refclklost_out                     (qpll1refclklost_out                    ),
      .qplldmonitor0_out                       (qplldmonitor0_out                      ),
      .qplldmonitor1_out                       (qplldmonitor1_out                      ),
      .refclkoutmonitor0_out                   (refclkoutmonitor0_out                  ),
      .refclkoutmonitor1_out                   (refclkoutmonitor1_out                  ),
      .rxrecclk0_sel_out                       (rxrecclk0_sel_out                      ),
      .rxrecclk1_sel_out                       (rxrecclk1_sel_out                      ),
      .cfgreset_in                             (cfgreset_in                            ),
      .clkrsvd0_in                             (clkrsvd0_in                            ),
      .clkrsvd1_in                             (clkrsvd1_in                            ),
      .cplllockdetclk_in                       (cplllockdetclk_in                      ),
      .cplllocken_in                           (cplllocken_in                          ),
      .cpllpd_in                               (cpllpd_in                              ),
      .cpllrefclksel_in                        (cpllrefclksel_in                       ),
      .cpllreset_in                            (cpllreset_in                           ),
      .dmonfiforeset_in                        (dmonfiforeset_in                       ),
      .dmonitorclk_in                          (dmonitorclk_in                         ),
      .drpaddr_in                              (drpaddr_in                             ),
      .drpclk_in                               (drpclk_in                              ),
      .drpdi_in                                (drpdi_in                               ),
      .drpen_in                                (drpen_in                               ),
      .drpwe_in                                (drpwe_in                               ),
      .evoddphicaldone_in                      (evoddphicaldone_in                     ),
      .evoddphicalstart_in                     (evoddphicalstart_in                    ),
      .evoddphidrden_in                        (evoddphidrden_in                       ),
      .evoddphidwren_in                        (evoddphidwren_in                       ),
      .evoddphixrden_in                        (evoddphixrden_in                       ),
      .evoddphixwren_in                        (evoddphixwren_in                       ),
      .eyescanmode_in                          (eyescanmode_in                         ),
      .eyescanreset_in                         (eyescanreset_in                        ),
      .eyescantrigger_in                       (eyescantrigger_in                      ),
      .gtgrefclk_in                            (gtgrefclk_in                           ),
      .gthrxn_in                               (gthrxn_in                              ),
      .gthrxp_in                               (gthrxp_in                              ),
      .gtnorthrefclk0_in                       (gtnorthrefclk0_in                      ),
      .gtnorthrefclk1_in                       (gtnorthrefclk1_in                      ),
      .gtrefclk0_in                            (gtrefclk0_in                           ),
      .gtrefclk1_in                            (gtrefclk1_in                           ),
      .gtresetsel_in                           (gtresetsel_in                          ),
      .gtrsvd_in                               (gtrsvd_in                              ),
      .gtrxreset_in                            (gtrxreset_in                           ),
      .gtsouthrefclk0_in                       (gtsouthrefclk0_in                      ),
      .gtsouthrefclk1_in                       (gtsouthrefclk1_in                      ),
      .gttxreset_in                            (gttxreset_in                           ),
      .loopback_in                             (loopback_in                            ),
      .lpbkrxtxseren_in                        (lpbkrxtxseren_in                       ),
      .lpbktxrxseren_in                        (lpbktxrxseren_in                       ),
      .pcieeqrxeqadaptdone_in                  (pcieeqrxeqadaptdone_in                 ),
      .pcierstidle_in                          (pcierstidle_in                         ),
      .pciersttxsyncstart_in                   (pciersttxsyncstart_in                  ),
      .pcieuserratedone_in                     (pcieuserratedone_in                    ),
      .pcsrsvdin_in                            (pcsrsvdin_in                           ),
      .pcsrsvdin2_in                           (pcsrsvdin2_in                          ),
      .pmarsvdin_in                            (pmarsvdin_in                           ),
      .qpll0clk_in                             (qpll0clk_in                            ),
      .qpll0refclk_in                          (qpll0refclk_in                         ),
      .qpll1clk_in                             (qpll1clk_in                            ),
      .qpll1refclk_in                          (qpll1refclk_in                         ),
      .resetovrd_in                            (resetovrd_in                           ),
      .rstclkentx_in                           (rstclkentx_in                          ),
      .rx8b10ben_in                            (rx8b10ben_in                           ),
      .rxbufreset_in                           (rxbufreset_in                          ),
      .rxcdrfreqreset_in                       (rxcdrfreqreset_in                      ),
      .rxcdrhold_in                            (rxcdrhold_in                           ),
      .rxcdrovrden_in                          (rxcdrovrden_in                         ),
      .rxcdrreset_in                           (rxcdrreset_in                          ),
      .rxcdrresetrsv_in                        (rxcdrresetrsv_in                       ),
      .rxchbonden_in                           (rxchbonden_in                          ),
      .rxchbondi_in                            (rxchbondi_in                           ),
      .rxchbondlevel_in                        (rxchbondlevel_in                       ),
      .rxchbondmaster_in                       (rxchbondmaster_in                      ),
      .rxchbondslave_in                        (rxchbondslave_in                       ),
      .rxcommadeten_in                         (rxcommadeten_in                        ),
      .rxdfeagcctrl_in                         (rxdfeagcctrl_in                        ),
      .rxdfeagchold_in                         (rxdfeagchold_in                        ),
      .rxdfeagcovrden_in                       (rxdfeagcovrden_in                      ),
      .rxdfelfhold_in                          (rxdfelfhold_in                         ),
      .rxdfelfovrden_in                        (rxdfelfovrden_in                       ),
      .rxdfelpmreset_in                        (rxdfelpmreset_in                       ),
      .rxdfetap10hold_in                       (rxdfetap10hold_in                      ),
      .rxdfetap10ovrden_in                     (rxdfetap10ovrden_in                    ),
      .rxdfetap11hold_in                       (rxdfetap11hold_in                      ),
      .rxdfetap11ovrden_in                     (rxdfetap11ovrden_in                    ),
      .rxdfetap12hold_in                       (rxdfetap12hold_in                      ),
      .rxdfetap12ovrden_in                     (rxdfetap12ovrden_in                    ),
      .rxdfetap13hold_in                       (rxdfetap13hold_in                      ),
      .rxdfetap13ovrden_in                     (rxdfetap13ovrden_in                    ),
      .rxdfetap14hold_in                       (rxdfetap14hold_in                      ),
      .rxdfetap14ovrden_in                     (rxdfetap14ovrden_in                    ),
      .rxdfetap15hold_in                       (rxdfetap15hold_in                      ),
      .rxdfetap15ovrden_in                     (rxdfetap15ovrden_in                    ),
      .rxdfetap2hold_in                        (rxdfetap2hold_in                       ),
      .rxdfetap2ovrden_in                      (rxdfetap2ovrden_in                     ),
      .rxdfetap3hold_in                        (rxdfetap3hold_in                       ),
      .rxdfetap3ovrden_in                      (rxdfetap3ovrden_in                     ),
      .rxdfetap4hold_in                        (rxdfetap4hold_in                       ),
      .rxdfetap4ovrden_in                      (rxdfetap4ovrden_in                     ),
      .rxdfetap5hold_in                        (rxdfetap5hold_in                       ),
      .rxdfetap5ovrden_in                      (rxdfetap5ovrden_in                     ),
      .rxdfetap6hold_in                        (rxdfetap6hold_in                       ),
      .rxdfetap6ovrden_in                      (rxdfetap6ovrden_in                     ),
      .rxdfetap7hold_in                        (rxdfetap7hold_in                       ),
      .rxdfetap7ovrden_in                      (rxdfetap7ovrden_in                     ),
      .rxdfetap8hold_in                        (rxdfetap8hold_in                       ),
      .rxdfetap8ovrden_in                      (rxdfetap8ovrden_in                     ),
      .rxdfetap9hold_in                        (rxdfetap9hold_in                       ),
      .rxdfetap9ovrden_in                      (rxdfetap9ovrden_in                     ),
      .rxdfeuthold_in                          (rxdfeuthold_in                         ),
      .rxdfeutovrden_in                        (rxdfeutovrden_in                       ),
      .rxdfevphold_in                          (rxdfevphold_in                         ),
      .rxdfevpovrden_in                        (rxdfevpovrden_in                       ),
      .rxdfevsen_in                            (rxdfevsen_in                           ),
      .rxdfexyden_in                           (rxdfexyden_in                          ),
      .rxdlybypass_in                          (rxdlybypass_in                         ),
      .rxdlyen_in                              (rxdlyen_in                             ),
      .rxdlyovrden_in                          (rxdlyovrden_in                         ),
      .rxdlysreset_in                          (rxdlysreset_in                         ),
      .rxelecidlemode_in                       (rxelecidlemode_in                      ),
      .rxgearboxslip_in                        (rxgearboxslip_in                       ),
      .rxlatclk_in                             (rxlatclk_in                            ),
      .rxlpmen_in                              (rxlpmen_in                             ),
      .rxlpmgchold_in                          (rxlpmgchold_in                         ),
      .rxlpmgcovrden_in                        (rxlpmgcovrden_in                       ),
      .rxlpmhfhold_in                          (rxlpmhfhold_in                         ),
      .rxlpmhfovrden_in                        (rxlpmhfovrden_in                       ),
      .rxlpmlfhold_in                          (rxlpmlfhold_in                         ),
      .rxlpmlfklovrden_in                      (rxlpmlfklovrden_in                     ),
      .rxlpmoshold_in                          (rxlpmoshold_in                         ),
      .rxlpmosovrden_in                        (rxlpmosovrden_in                       ),
      .rxmcommaalignen_in                      (rxmcommaalignen_in                     ),
      .rxmonitorsel_in                         (rxmonitorsel_in                        ),
      .rxoobreset_in                           (rxoobreset_in                          ),
      .rxoscalreset_in                         (rxoscalreset_in                        ),
      .rxoshold_in                             (rxoshold_in                            ),
      .rxosintcfg_in                           (rxosintcfg_in                          ),
      .rxosinten_in                            (rxosinten_in                           ),
      .rxosinthold_in                          (rxosinthold_in                         ),
      .rxosintovrden_in                        (rxosintovrden_in                       ),
      .rxosintstrobe_in                        (rxosintstrobe_in                       ),
      .rxosinttestovrden_in                    (rxosinttestovrden_in                   ),
      .rxosovrden_in                           (rxosovrden_in                          ),
      .rxoutclksel_in                          (rxoutclksel_in                         ),
      .rxpcommaalignen_in                      (rxpcommaalignen_in                     ),
      .rxpcsreset_in                           (rxpcsreset_in                          ),
      .rxpd_in                                 (rxpd_in                                ),
      .rxphalign_in                            (rxphalign_in                           ),
      .rxphalignen_in                          (rxphalignen_in                         ),
      .rxphdlypd_in                            (rxphdlypd_in                           ),
      .rxphdlyreset_in                         (rxphdlyreset_in                        ),
      .rxphovrden_in                           (rxphovrden_in                          ),
      .rxpllclksel_in                          (rxpllclksel_in                         ),
      .rxpmareset_in                           (rxpmareset_in                          ),
      .rxpolarity_in                           (rxpolarity_in                          ),
      .rxprbscntreset_in                       (rxprbscntreset_in                      ),
      .rxprbssel_in                            (rxprbssel_in                           ),
      .rxprogdivreset_in                       (rxprogdivreset_in                      ),
      .rxqpien_in                              (rxqpien_in                             ),
      .rxrate_in                               (rxrate_in                              ),
      .rxratemode_in                           (rxratemode_in                          ),
      .rxslide_in                              (rxslide_in                             ),
      .rxslipoutclk_in                         (rxslipoutclk_in                        ),
      .rxslippma_in                            (rxslippma_in                           ),
      .rxsyncallin_in                          (rxsyncallin_in                         ),
      .rxsyncin_in                             (rxsyncin_in                            ),
      .rxsyncmode_in                           (rxsyncmode_in                          ),
      .rxsysclksel_in                          (rxsysclksel_in                         ),
      .rxuserrdy_in                            (rxuserrdy_in                           ),
      .rxusrclk_in                             (rxusrclk_in                            ),
      .rxusrclk2_in                            (rxusrclk2_in                           ),
      .sigvalidclk_in                          (sigvalidclk_in                         ),
      .tstin_in                                (tstin_in                               ),
      .tx8b10bbypass_in                        (tx8b10bbypass_in                       ),
      .tx8b10ben_in                            (tx8b10ben_in                           ),
      .txbufdiffctrl_in                        (txbufdiffctrl_in                       ),
      .txcominit_in                            (txcominit_in                           ),
      .txcomsas_in                             (txcomsas_in                            ),
      .txcomwake_in                            (txcomwake_in                           ),
      .txctrl0_in                              (txctrl0_in                             ),
      .txctrl1_in                              (txctrl1_in                             ),
      .txctrl2_in                              (txctrl2_in                             ),
      .txdata_in                               (txdata_in                              ),
      .txdataextendrsvd_in                     (txdataextendrsvd_in                    ),
      .txdeemph_in                             (txdeemph_in                            ),
      .txdetectrx_in                           (txdetectrx_in                          ),
      .txdiffctrl_in                           (txdiffctrl_in                          ),
      .txdiffpd_in                             (txdiffpd_in                            ),
      .txdlybypass_in                          (txdlybypass_in                         ),
      .txdlyen_in                              (txdlyen_in                             ),
      .txdlyhold_in                            (txdlyhold_in                           ),
      .txdlyovrden_in                          (txdlyovrden_in                         ),
      .txdlysreset_in                          (txdlysreset_in                         ),
      .txdlyupdown_in                          (txdlyupdown_in                         ),
      .txelecidle_in                           (txelecidle_in                          ),
      .txheader_in                             (txheader_in                            ),
      .txinhibit_in                            (txinhibit_in                           ),
      .txlatclk_in                             (txlatclk_in                            ),
      .txmaincursor_in                         (txmaincursor_in                        ),
      .txmargin_in                             (txmargin_in                            ),
      .txoutclksel_in                          (txoutclksel_in                         ),
      .txpcsreset_in                           (txpcsreset_in                          ),
      .txpd_in                                 (txpd_in                                ),
      .txpdelecidlemode_in                     (txpdelecidlemode_in                    ),
      .txphalign_in                            (txphalign_in                           ),
      .txphalignen_in                          (txphalignen_in                         ),
      .txphdlypd_in                            (txphdlypd_in                           ),
      .txphdlyreset_in                         (txphdlyreset_in                        ),
      .txphdlytstclk_in                        (txphdlytstclk_in                       ),
      .txphinit_in                             (txphinit_in                            ),
      .txphovrden_in                           (txphovrden_in                          ),
      .txpippmen_in                            (txpippmen_in                           ),
      .txpippmovrden_in                        (txpippmovrden_in                       ),
      .txpippmpd_in                            (txpippmpd_in                           ),
      .txpippmsel_in                           (txpippmsel_in                          ),
      .txpippmstepsize_in                      (txpippmstepsize_in                     ),
      .txpisopd_in                             (txpisopd_in                            ),
      .txpllclksel_in                          (txpllclksel_in                         ),
      .txpmareset_in                           (txpmareset_in                          ),
      .txpolarity_in                           (txpolarity_in                          ),
      .txpostcursor_in                         (txpostcursor_in                        ),
      .txpostcursorinv_in                      (txpostcursorinv_in                     ),
      .txprbsforceerr_in                       (txprbsforceerr_in                      ),
      .txprbssel_in                            (txprbssel_in                           ),
      .txprecursor_in                          (txprecursor_in                         ),
      .txprecursorinv_in                       (txprecursorinv_in                      ),
      .txprogdivreset_in                       (txprogdivreset_in                      ),
      .txqpibiasen_in                          (txqpibiasen_in                         ),
      .txqpistrongpdown_in                     (txqpistrongpdown_in                    ),
      .txqpiweakpup_in                         (txqpiweakpup_in                        ),
      .txrate_in                               (txrate_in                              ),
      .txratemode_in                           (txratemode_in                          ),
      .txsequence_in                           (txsequence_in                          ),
      .txswing_in                              (txswing_in                             ),
      .txsyncallin_in                          (txsyncallin_in                         ),
      .txsyncin_in                             (txsyncin_in                            ),
      .txsyncmode_in                           (txsyncmode_in                          ),
      .txsysclksel_in                          (txsysclksel_in                         ),
      .txuserrdy_in                            (txuserrdy_in                           ),
      .txusrclk_in                             (txusrclk_in                            ),
      .txusrclk2_in                            (txusrclk2_in                           ),
      .bufgtce_out                             (bufgtce_out                            ),
      .bufgtcemask_out                         (bufgtcemask_out                        ),
      .bufgtdiv_out                            (bufgtdiv_out                           ),
      .bufgtreset_out                          (bufgtreset_out                         ),
      .bufgtrstmask_out                        (bufgtrstmask_out                       ),
      .cpllfbclklost_out                       (cpllfbclklost_out                      ),
      .cplllock_out                            (cplllock_out                           ),
      .cpllrefclklost_out                      (cpllrefclklost_out                     ),
      .dmonitorout_out                         (dmonitorout_out                        ),
      .drpdo_out                               (drpdo_out                              ),
      .drprdy_out                              (drprdy_out                             ),
      .eyescandataerror_out                    (eyescandataerror_out                   ),
      .gthtxn_out                              (gthtxn_out                             ),
      .gthtxp_out                              (gthtxp_out                             ),
      .gtpowergood_out                         (gtpowergood_out                        ),
      .gtrefclkmonitor_out                     (gtrefclkmonitor_out                    ),
      .pcierategen3_out                        (pcierategen3_out                       ),
      .pcierateidle_out                        (pcierateidle_out                       ),
      .pcierateqpllpd_out                      (pcierateqpllpd_out                     ),
      .pcierateqpllreset_out                   (pcierateqpllreset_out                  ),
      .pciesynctxsyncdone_out                  (pciesynctxsyncdone_out                 ),
      .pcieusergen3rdy_out                     (pcieusergen3rdy_out                    ),
      .pcieuserphystatusrst_out                (pcieuserphystatusrst_out               ),
      .pcieuserratestart_out                   (pcieuserratestart_out                  ),
      .pcsrsvdout_out                          (pcsrsvdout_out                         ),
      .phystatus_out                           (phystatus_out                          ),
      .pinrsrvdas_out                          (pinrsrvdas_out                         ),
      .resetexception_out                      (resetexception_out                     ),
      .rxbufstatus_out                         (rxbufstatus_out                        ),
      .rxbyteisaligned_out                     (rxbyteisaligned_out                    ),
      .rxbyterealign_out                       (rxbyterealign_out                      ),
      .rxcdrlock_out                           (rxcdrlock_out                          ),
      .rxcdrphdone_out                         (rxcdrphdone_out                        ),
      .rxchanbondseq_out                       (rxchanbondseq_out                      ),
      .rxchanisaligned_out                     (rxchanisaligned_out                    ),
      .rxchanrealign_out                       (rxchanrealign_out                      ),
      .rxchbondo_out                           (rxchbondo_out                          ),
      .rxclkcorcnt_out                         (rxclkcorcnt_out                        ),
      .rxcominitdet_out                        (rxcominitdet_out                       ),
      .rxcommadet_out                          (rxcommadet_out                         ),
      .rxcomsasdet_out                         (rxcomsasdet_out                        ),
      .rxcomwakedet_out                        (rxcomwakedet_out                       ),
      .rxctrl0_out                             (rxctrl0_out                            ),
      .rxctrl1_out                             (rxctrl1_out                            ),
      .rxctrl2_out                             (rxctrl2_out                            ),
      .rxctrl3_out                             (rxctrl3_out                            ),
      .rxdata_out                              (rxdata_out                             ),
      .rxdataextendrsvd_out                    (rxdataextendrsvd_out                   ),
      .rxdatavalid_out                         (rxdatavalid_out                        ),
      .rxdlysresetdone_out                     (rxdlysresetdone_out                    ),
      .rxelecidle_out                          (rxelecidle_out                         ),
      .rxheader_out                            (rxheader_out                           ),
      .rxheadervalid_out                       (rxheadervalid_out                      ),
      .rxmonitorout_out                        (rxmonitorout_out                       ),
      .rxosintdone_out                         (rxosintdone_out                        ),
      .rxosintstarted_out                      (rxosintstarted_out                     ),
      .rxosintstrobedone_out                   (rxosintstrobedone_out                  ),
      .rxosintstrobestarted_out                (rxosintstrobestarted_out               ),
      .rxoutclk_out                            (rxoutclk_out                           ),
      .rxoutclkfabric_out                      (rxoutclkfabric_out                     ),
      .rxoutclkpcs_out                         (rxoutclkpcs_out                        ),
      .rxphaligndone_out                       (rxphaligndone_out                      ),
      .rxphalignerr_out                        (rxphalignerr_out                       ),
      .rxpmaresetdone_out                      (rxpmaresetdone_out                     ),
      .rxprbserr_out                           (rxprbserr_out                          ),
      .rxprbslocked_out                        (rxprbslocked_out                       ),
      .rxprgdivresetdone_out                   (rxprgdivresetdone_out                  ),
      .rxqpisenn_out                           (rxqpisenn_out                          ),
      .rxqpisenp_out                           (rxqpisenp_out                          ),
      .rxratedone_out                          (rxratedone_out                         ),
      .rxrecclkout_out                         (rxrecclkout_out                        ),
      .rxresetdone_out                         (rxresetdone_out                        ),
      .rxsliderdy_out                          (rxsliderdy_out                         ),
      .rxslipdone_out                          (rxslipdone_out                         ),
      .rxslipoutclkrdy_out                     (rxslipoutclkrdy_out                    ),
      .rxslippmardy_out                        (rxslippmardy_out                       ),
      .rxstartofseq_out                        (rxstartofseq_out                       ),
      .rxstatus_out                            (rxstatus_out                           ),
      .rxsyncdone_out                          (rxsyncdone_out                         ),
      .rxsyncout_out                           (rxsyncout_out                          ),
      .rxvalid_out                             (rxvalid_out                            ),
      .txbufstatus_out                         (txbufstatus_out                        ),
      .txcomfinish_out                         (txcomfinish_out                        ),
      .txdlysresetdone_out                     (txdlysresetdone_out                    ),
      .txoutclk_out                            (txoutclk_out                           ),
      .txoutclkfabric_out                      (txoutclkfabric_out                     ),
      .txoutclkpcs_out                         (txoutclkpcs_out                        ),
      .txphaligndone_out                       (txphaligndone_out                      ),
      .txphinitdone_out                        (txphinitdone_out                       ),
      .txpmaresetdone_out                      (txpmaresetdone_out                     ),
      .txprgdivresetdone_out                   (txprgdivresetdone_out                  ),
      .txqpisenn_out                           (txqpisenn_out                          ),
      .txqpisenp_out                           (txqpisenp_out                          ),
      .txratedone_out                          (txratedone_out                         ),
      .txresetdone_out                         (txresetdone_out                        ),
      .txsyncdone_out                          (txsyncdone_out                         ),
      .txsyncout_out                           (txsyncout_out                          )
    );

    // Drive unused outputs to constant values
    assign rxrecclk0sel_out      = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign rxrecclk1sel_out      = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign sdm0finalout_out      = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign sdm0testdata_out      = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign sdm1finalout_out      = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign sdm1testdata_out      = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign tcongpo_out           = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign tconrsvdout0_out      = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign ubdaddr_out           = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign ubden_out             = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign ubdi_out              = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign ubdwe_out             = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign ubmdmtdo_out          = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign ubrsvdout_out         = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign ubtxuart_out          = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign dmonitoroutclk_out    = {{`xdma_0_pcie4_ip_gt_N_CH}{1'b0}};
    assign gtytxn_out            = {{`xdma_0_pcie4_ip_gt_N_CH}{1'b0}};
    assign gtytxp_out            = {{`xdma_0_pcie4_ip_gt_N_CH}{1'b0}};
    assign powerpresent_out      = {{`xdma_0_pcie4_ip_gt_N_CH}{1'b0}};
    assign rxckcaldone_out       = {{`xdma_0_pcie4_ip_gt_N_CH}{1'b0}};
    assign rxlfpstresetdet_out   = {{`xdma_0_pcie4_ip_gt_N_CH}{1'b0}};
    assign rxlfpsu2lpexitdet_out = {{`xdma_0_pcie4_ip_gt_N_CH}{1'b0}};
    assign rxlfpsu3wakedet_out   = {{`xdma_0_pcie4_ip_gt_N_CH}{1'b0}};
    assign txdccdone_out         = {{`xdma_0_pcie4_ip_gt_N_CH}{1'b0}};

  end
  else if (C_GT_TYPE == `xdma_0_pcie4_ip_gt_GT_TYPE__GTYE3) begin : gen_gtwizard_gtye3_top

    // Generate GTYE3-type Transceivers Wizard submodule
    xdma_0_pcie4_ip_gt_gtwizard_gtye3 #(
      .C_CHANNEL_ENABLE                          (C_CHANNEL_ENABLE                         ),
      .C_COMMON_SCALING_FACTOR                   (C_COMMON_SCALING_FACTOR                  ),
      .C_FREERUN_FREQUENCY                       (C_FREERUN_FREQUENCY                      ),
      .C_GT_REV                                  (C_GT_REV                                 ),
      .C_LOCATE_RESET_CONTROLLER                 (C_LOCATE_RESET_CONTROLLER                ),
      .C_LOCATE_USER_DATA_WIDTH_SIZING           (C_LOCATE_USER_DATA_WIDTH_SIZING          ),
      .C_LOCATE_RX_BUFFER_BYPASS_CONTROLLER      (C_LOCATE_RX_BUFFER_BYPASS_CONTROLLER     ),
      .C_LOCATE_RX_USER_CLOCKING                 (C_LOCATE_RX_USER_CLOCKING                ),
      .C_LOCATE_TX_BUFFER_BYPASS_CONTROLLER      (C_LOCATE_TX_BUFFER_BYPASS_CONTROLLER     ),
      .C_LOCATE_TX_USER_CLOCKING                 (C_LOCATE_TX_USER_CLOCKING                ),
      .C_RESET_CONTROLLER_INSTANCE_CTRL          (C_RESET_CONTROLLER_INSTANCE_CTRL         ),
      .C_RX_BUFFBYPASS_MODE                      (C_RX_BUFFBYPASS_MODE                     ),
      .C_RX_BUFFER_BYPASS_INSTANCE_CTRL          (C_RX_BUFFER_BYPASS_INSTANCE_CTRL         ),
      .C_RX_BUFFER_MODE                          (C_RX_BUFFER_MODE                         ),
      .C_RX_DATA_DECODING                        (C_RX_DATA_DECODING                       ),
      .C_RX_ENABLE                               (C_RX_ENABLE                              ),
      .C_RX_INT_DATA_WIDTH                       (C_RX_INT_DATA_WIDTH                      ),
      .C_RX_LINE_RATE                            (C_RX_LINE_RATE                           ),
      .C_RX_MASTER_CHANNEL_IDX                   (C_RX_MASTER_CHANNEL_IDX                  ),
      .C_RX_OUTCLK_BUFG_GT_DIV                   (C_RX_OUTCLK_BUFG_GT_DIV                  ),
      .C_RX_PLL_TYPE                             (C_RX_PLL_TYPE                            ),
      .C_RX_USER_CLOCKING_CONTENTS               (C_RX_USER_CLOCKING_CONTENTS              ),
      .C_RX_USER_CLOCKING_INSTANCE_CTRL          (C_RX_USER_CLOCKING_INSTANCE_CTRL         ),
      .C_RX_USER_CLOCKING_RATIO_FUSRCLK_FUSRCLK2 (C_RX_USER_CLOCKING_RATIO_FUSRCLK_FUSRCLK2),
      .C_RX_USER_CLOCKING_SOURCE                 (C_RX_USER_CLOCKING_SOURCE                ),
      .C_RX_USER_DATA_WIDTH                      (C_RX_USER_DATA_WIDTH                     ),
      .C_TOTAL_NUM_CHANNELS                      (C_TOTAL_NUM_CHANNELS                     ),
      .C_TOTAL_NUM_COMMONS                       (C_TOTAL_NUM_COMMONS                      ),
      .C_TX_BUFFBYPASS_MODE                      (C_TX_BUFFBYPASS_MODE                     ),
      .C_TX_BUFFER_BYPASS_INSTANCE_CTRL          (C_TX_BUFFER_BYPASS_INSTANCE_CTRL         ),
      .C_TX_BUFFER_MODE                          (C_TX_BUFFER_MODE                         ),
      .C_TX_DATA_ENCODING                        (C_TX_DATA_ENCODING                       ),
      .C_TX_ENABLE                               (C_TX_ENABLE                              ),
      .C_TX_INT_DATA_WIDTH                       (C_TX_INT_DATA_WIDTH                      ),
      .C_TX_MASTER_CHANNEL_IDX                   (C_TX_MASTER_CHANNEL_IDX                  ),
      .C_TX_OUTCLK_BUFG_GT_DIV                   (C_TX_OUTCLK_BUFG_GT_DIV                  ),
      .C_TX_PLL_TYPE                             (C_TX_PLL_TYPE                            ),
      .C_TX_USER_CLOCKING_CONTENTS               (C_TX_USER_CLOCKING_CONTENTS              ),
      .C_TX_USER_CLOCKING_INSTANCE_CTRL          (C_TX_USER_CLOCKING_INSTANCE_CTRL         ),
      .C_TX_USER_CLOCKING_RATIO_FUSRCLK_FUSRCLK2 (C_TX_USER_CLOCKING_RATIO_FUSRCLK_FUSRCLK2),
      .C_TX_USER_CLOCKING_SOURCE                 (C_TX_USER_CLOCKING_SOURCE                ),
      .C_TX_USER_DATA_WIDTH                      (C_TX_USER_DATA_WIDTH                     )
    ) xdma_0_pcie4_ip_gt_gtwizard_gtye3_inst (
      .gtwiz_userclk_tx_reset_in          (gtwiz_userclk_tx_reset_in         ),
      .gtwiz_userclk_tx_active_in         (gtwiz_userclk_tx_active_in        ),
      .gtwiz_userclk_tx_srcclk_out        (gtwiz_userclk_tx_srcclk_out       ),
      .gtwiz_userclk_tx_usrclk_out        (gtwiz_userclk_tx_usrclk_out       ),
      .gtwiz_userclk_tx_usrclk2_out       (gtwiz_userclk_tx_usrclk2_out      ),
      .gtwiz_userclk_tx_active_out        (gtwiz_userclk_tx_active_out       ),
      .gtwiz_userclk_rx_reset_in          (gtwiz_userclk_rx_reset_in         ),
      .gtwiz_userclk_rx_active_in         (gtwiz_userclk_rx_active_in        ),
      .gtwiz_userclk_rx_srcclk_out        (gtwiz_userclk_rx_srcclk_out       ),
      .gtwiz_userclk_rx_usrclk_out        (gtwiz_userclk_rx_usrclk_out       ),
      .gtwiz_userclk_rx_usrclk2_out       (gtwiz_userclk_rx_usrclk2_out      ),
      .gtwiz_userclk_rx_active_out        (gtwiz_userclk_rx_active_out       ),
      .gtwiz_buffbypass_tx_reset_in       (gtwiz_buffbypass_tx_reset_in      ),
      .gtwiz_buffbypass_tx_start_user_in  (gtwiz_buffbypass_tx_start_user_in ),
      .gtwiz_buffbypass_tx_done_out       (gtwiz_buffbypass_tx_done_out      ),
      .gtwiz_buffbypass_tx_error_out      (gtwiz_buffbypass_tx_error_out     ),
      .gtwiz_buffbypass_rx_reset_in       (gtwiz_buffbypass_rx_reset_in      ),
      .gtwiz_buffbypass_rx_start_user_in  (gtwiz_buffbypass_rx_start_user_in ),
      .gtwiz_buffbypass_rx_done_out       (gtwiz_buffbypass_rx_done_out      ),
      .gtwiz_buffbypass_rx_error_out      (gtwiz_buffbypass_rx_error_out     ),
      .gtwiz_reset_clk_freerun_in         (gtwiz_reset_clk_freerun_in        ),
      .gtwiz_reset_all_in                 (gtwiz_reset_all_in                ),
      .gtwiz_reset_tx_pll_and_datapath_in (gtwiz_reset_tx_pll_and_datapath_in),
      .gtwiz_reset_tx_datapath_in         (gtwiz_reset_tx_datapath_in        ),
      .gtwiz_reset_rx_pll_and_datapath_in (gtwiz_reset_rx_pll_and_datapath_in),
      .gtwiz_reset_rx_datapath_in         (gtwiz_reset_rx_datapath_in        ),
      .gtwiz_reset_tx_done_in             (gtwiz_reset_tx_done_in            ),
      .gtwiz_reset_rx_done_in             (gtwiz_reset_rx_done_in            ),
      .gtwiz_reset_qpll0lock_in           (gtwiz_reset_qpll0lock_in          ),
      .gtwiz_reset_qpll1lock_in           (gtwiz_reset_qpll1lock_in          ),
      .gtwiz_reset_rx_cdr_stable_out      (gtwiz_reset_rx_cdr_stable_out     ),
      .gtwiz_reset_tx_done_out            (gtwiz_reset_tx_done_out           ),
      .gtwiz_reset_rx_done_out            (gtwiz_reset_rx_done_out           ),
      .gtwiz_reset_qpll0reset_out         (gtwiz_reset_qpll0reset_out        ),
      .gtwiz_reset_qpll1reset_out         (gtwiz_reset_qpll1reset_out        ),
      .gtwiz_userdata_tx_in               (gtwiz_userdata_tx_in              ),
      .gtwiz_userdata_rx_out              (gtwiz_userdata_rx_out             ),
      .bgbypassb_in                       (bgbypassb_in                      ),
      .bgmonitorenb_in                    (bgmonitorenb_in                   ),
      .bgpdb_in                           (bgpdb_in                          ),
      .bgrcalovrd_in                      (bgrcalovrd_in                     ),
      .bgrcalovrdenb_in                   (bgrcalovrdenb_in                  ),
      .drpaddr_common_in                  (drpaddr_common_in                 ),
      .drpclk_common_in                   (drpclk_common_in                  ),
      .drpdi_common_in                    (drpdi_common_in                   ),
      .drpen_common_in                    (drpen_common_in                   ),
      .drpwe_common_in                    (drpwe_common_in                   ),
      .gtgrefclk0_in                      (gtgrefclk0_in                     ),
      .gtgrefclk1_in                      (gtgrefclk1_in                     ),
      .gtnorthrefclk00_in                 (gtnorthrefclk00_in                ),
      .gtnorthrefclk01_in                 (gtnorthrefclk01_in                ),
      .gtnorthrefclk10_in                 (gtnorthrefclk10_in                ),
      .gtnorthrefclk11_in                 (gtnorthrefclk11_in                ),
      .gtrefclk00_in                      (gtrefclk00_in                     ),
      .gtrefclk01_in                      (gtrefclk01_in                     ),
      .gtrefclk10_in                      (gtrefclk10_in                     ),
      .gtrefclk11_in                      (gtrefclk11_in                     ),
      .gtsouthrefclk00_in                 (gtsouthrefclk00_in                ),
      .gtsouthrefclk01_in                 (gtsouthrefclk01_in                ),
      .gtsouthrefclk10_in                 (gtsouthrefclk10_in                ),
      .gtsouthrefclk11_in                 (gtsouthrefclk11_in                ),
      .pmarsvd0_in                        (pmarsvd0_in                       ),
      .pmarsvd1_in                        (pmarsvd1_in                       ),
      .qpll0clkrsvd0_in                   (qpll0clkrsvd0_in                  ),
      .qpll0lockdetclk_in                 (qpll0lockdetclk_in                ),
      .qpll0locken_in                     (qpll0locken_in                    ),
      .qpll0pd_in                         (qpll0pd_in                        ),
      .qpll0refclksel_in                  (qpll0refclksel_in                 ),
      .qpll0reset_in                      (qpll0reset_in                     ),
      .qpll1clkrsvd0_in                   (qpll1clkrsvd0_in                  ),
      .qpll1lockdetclk_in                 (qpll1lockdetclk_in                ),
      .qpll1locken_in                     (qpll1locken_in                    ),
      .qpll1pd_in                         (qpll1pd_in                        ),
      .qpll1refclksel_in                  (qpll1refclksel_in                 ),
      .qpll1reset_in                      (qpll1reset_in                     ),
      .qpllrsvd1_in                       (qpllrsvd1_in                      ),
      .qpllrsvd2_in                       (qpllrsvd2_in                      ),
      .qpllrsvd3_in                       (qpllrsvd3_in                      ),
      .qpllrsvd4_in                       (qpllrsvd4_in                      ),
      .rcalenb_in                         (rcalenb_in                        ),
      .sdm0data_in                        (sdm0data_in                       ),
      .sdm0reset_in                       (sdm0reset_in                      ),
      .sdm0width_in                       (sdm0width_in                      ),
      .sdm1data_in                        (sdm1data_in                       ),
      .sdm1reset_in                       (sdm1reset_in                      ),
      .sdm1width_in                       (sdm1width_in                      ),
      .drpdo_common_out                   (drpdo_common_out                  ),
      .drprdy_common_out                  (drprdy_common_out                 ),
      .pmarsvdout0_out                    (pmarsvdout0_out                   ),
      .pmarsvdout1_out                    (pmarsvdout1_out                   ),
      .qpll0fbclklost_out                 (qpll0fbclklost_out                ),
      .qpll0lock_out                      (qpll0lock_out                     ),
      .qpll0outclk_out                    (qpll0outclk_out                   ),
      .qpll0outrefclk_out                 (qpll0outrefclk_out                ),
      .qpll0refclklost_out                (qpll0refclklost_out               ),
      .qpll1fbclklost_out                 (qpll1fbclklost_out                ),
      .qpll1lock_out                      (qpll1lock_out                     ),
      .qpll1outclk_out                    (qpll1outclk_out                   ),
      .qpll1outrefclk_out                 (qpll1outrefclk_out                ),
      .qpll1refclklost_out                (qpll1refclklost_out               ),
      .qplldmonitor0_out                  (qplldmonitor0_out                 ),
      .qplldmonitor1_out                  (qplldmonitor1_out                 ),
      .refclkoutmonitor0_out              (refclkoutmonitor0_out             ),
      .refclkoutmonitor1_out              (refclkoutmonitor1_out             ),
      .rxrecclk0_sel_out                  (rxrecclk0_sel_out                 ),
      .rxrecclk1_sel_out                  (rxrecclk1_sel_out                 ),
      .sdm0finalout_out                   (sdm0finalout_out                  ),
      .sdm0testdata_out                   (sdm0testdata_out                  ),
      .sdm1finalout_out                   (sdm1finalout_out                  ),
      .sdm1testdata_out                   (sdm1testdata_out                  ),
      .cdrstepdir_in                      (cdrstepdir_in                     ),
      .cdrstepsq_in                       (cdrstepsq_in                      ),
      .cdrstepsx_in                       (cdrstepsx_in                      ),
      .cfgreset_in                        (cfgreset_in                       ),
      .clkrsvd0_in                        (clkrsvd0_in                       ),
      .clkrsvd1_in                        (clkrsvd1_in                       ),
      .cplllockdetclk_in                  (cplllockdetclk_in                 ),
      .cplllocken_in                      (cplllocken_in                     ),
      .cpllpd_in                          (cpllpd_in                         ),
      .cpllrefclksel_in                   (cpllrefclksel_in                  ),
      .cpllreset_in                       (cpllreset_in                      ),
      .dmonfiforeset_in                   (dmonfiforeset_in                  ),
      .dmonitorclk_in                     (dmonitorclk_in                    ),
      .drpaddr_in                         (drpaddr_in                        ),
      .drpclk_in                          (drpclk_in                         ),
      .drpdi_in                           (drpdi_in                          ),
      .drpen_in                           (drpen_in                          ),
      .drpwe_in                           (drpwe_in                          ),
      .elpcaldvorwren_in                  (elpcaldvorwren_in                 ),
      .elpcalpaorwren_in                  (elpcalpaorwren_in                 ),
      .evoddphicaldone_in                 (evoddphicaldone_in                ),
      .evoddphicalstart_in                (evoddphicalstart_in               ),
      .evoddphidrden_in                   (evoddphidrden_in                  ),
      .evoddphidwren_in                   (evoddphidwren_in                  ),
      .evoddphixrden_in                   (evoddphixrden_in                  ),
      .evoddphixwren_in                   (evoddphixwren_in                  ),
      .eyescanmode_in                     (eyescanmode_in                    ),
      .eyescanreset_in                    (eyescanreset_in                   ),
      .eyescantrigger_in                  (eyescantrigger_in                 ),
      .gtgrefclk_in                       (gtgrefclk_in                      ),
      .gtnorthrefclk0_in                  (gtnorthrefclk0_in                 ),
      .gtnorthrefclk1_in                  (gtnorthrefclk1_in                 ),
      .gtrefclk0_in                       (gtrefclk0_in                      ),
      .gtrefclk1_in                       (gtrefclk1_in                      ),
      .gtresetsel_in                      (gtresetsel_in                     ),
      .gtrsvd_in                          (gtrsvd_in                         ),
      .gtrxreset_in                       (gtrxreset_in                      ),
      .gtsouthrefclk0_in                  (gtsouthrefclk0_in                 ),
      .gtsouthrefclk1_in                  (gtsouthrefclk1_in                 ),
      .gttxreset_in                       (gttxreset_in                      ),
      .gtyrxn_in                          (gtyrxn_in                         ),
      .gtyrxp_in                          (gtyrxp_in                         ),
      .loopback_in                        (loopback_in                       ),
      .looprsvd_in                        (looprsvd_in                       ),
      .lpbkrxtxseren_in                   (lpbkrxtxseren_in                  ),
      .lpbktxrxseren_in                   (lpbktxrxseren_in                  ),
      .pcieeqrxeqadaptdone_in             (pcieeqrxeqadaptdone_in            ),
      .pcierstidle_in                     (pcierstidle_in                    ),
      .pciersttxsyncstart_in              (pciersttxsyncstart_in             ),
      .pcieuserratedone_in                (pcieuserratedone_in               ),
      .pcsrsvdin_in                       (pcsrsvdin_in                      ),
      .pcsrsvdin2_in                      (pcsrsvdin2_in                     ),
      .pmarsvdin_in                       (pmarsvdin_in                      ),
      .qpll0clk_in                        (qpll0clk_in                       ),
      .qpll0refclk_in                     (qpll0refclk_in                    ),
      .qpll1clk_in                        (qpll1clk_in                       ),
      .qpll1refclk_in                     (qpll1refclk_in                    ),
      .resetovrd_in                       (resetovrd_in                      ),
      .rstclkentx_in                      (rstclkentx_in                     ),
      .rx8b10ben_in                       (rx8b10ben_in                      ),
      .rxbufreset_in                      (rxbufreset_in                     ),
      .rxcdrfreqreset_in                  (rxcdrfreqreset_in                 ),
      .rxcdrhold_in                       (rxcdrhold_in                      ),
      .rxcdrovrden_in                     (rxcdrovrden_in                    ),
      .rxcdrreset_in                      (rxcdrreset_in                     ),
      .rxcdrresetrsv_in                   (rxcdrresetrsv_in                  ),
      .rxchbonden_in                      (rxchbonden_in                     ),
      .rxchbondi_in                       (rxchbondi_in                      ),
      .rxchbondlevel_in                   (rxchbondlevel_in                  ),
      .rxchbondmaster_in                  (rxchbondmaster_in                 ),
      .rxchbondslave_in                   (rxchbondslave_in                  ),
      .rxckcalreset_in                    (rxckcalreset_in                   ),
      .rxcommadeten_in                    (rxcommadeten_in                   ),
      .rxdccforcestart_in                 (rxdccforcestart_in                ),
      .rxdfeagchold_in                    (rxdfeagchold_in                   ),
      .rxdfeagcovrden_in                  (rxdfeagcovrden_in                 ),
      .rxdfelfhold_in                     (rxdfelfhold_in                    ),
      .rxdfelfovrden_in                   (rxdfelfovrden_in                  ),
      .rxdfelpmreset_in                   (rxdfelpmreset_in                  ),
      .rxdfetap10hold_in                  (rxdfetap10hold_in                 ),
      .rxdfetap10ovrden_in                (rxdfetap10ovrden_in               ),
      .rxdfetap11hold_in                  (rxdfetap11hold_in                 ),
      .rxdfetap11ovrden_in                (rxdfetap11ovrden_in               ),
      .rxdfetap12hold_in                  (rxdfetap12hold_in                 ),
      .rxdfetap12ovrden_in                (rxdfetap12ovrden_in               ),
      .rxdfetap13hold_in                  (rxdfetap13hold_in                 ),
      .rxdfetap13ovrden_in                (rxdfetap13ovrden_in               ),
      .rxdfetap14hold_in                  (rxdfetap14hold_in                 ),
      .rxdfetap14ovrden_in                (rxdfetap14ovrden_in               ),
      .rxdfetap15hold_in                  (rxdfetap15hold_in                 ),
      .rxdfetap15ovrden_in                (rxdfetap15ovrden_in               ),
      .rxdfetap2hold_in                   (rxdfetap2hold_in                  ),
      .rxdfetap2ovrden_in                 (rxdfetap2ovrden_in                ),
      .rxdfetap3hold_in                   (rxdfetap3hold_in                  ),
      .rxdfetap3ovrden_in                 (rxdfetap3ovrden_in                ),
      .rxdfetap4hold_in                   (rxdfetap4hold_in                  ),
      .rxdfetap4ovrden_in                 (rxdfetap4ovrden_in                ),
      .rxdfetap5hold_in                   (rxdfetap5hold_in                  ),
      .rxdfetap5ovrden_in                 (rxdfetap5ovrden_in                ),
      .rxdfetap6hold_in                   (rxdfetap6hold_in                  ),
      .rxdfetap6ovrden_in                 (rxdfetap6ovrden_in                ),
      .rxdfetap7hold_in                   (rxdfetap7hold_in                  ),
      .rxdfetap7ovrden_in                 (rxdfetap7ovrden_in                ),
      .rxdfetap8hold_in                   (rxdfetap8hold_in                  ),
      .rxdfetap8ovrden_in                 (rxdfetap8ovrden_in                ),
      .rxdfetap9hold_in                   (rxdfetap9hold_in                  ),
      .rxdfetap9ovrden_in                 (rxdfetap9ovrden_in                ),
      .rxdfeuthold_in                     (rxdfeuthold_in                    ),
      .rxdfeutovrden_in                   (rxdfeutovrden_in                  ),
      .rxdfevphold_in                     (rxdfevphold_in                    ),
      .rxdfevpovrden_in                   (rxdfevpovrden_in                  ),
      .rxdfevsen_in                       (rxdfevsen_in                      ),
      .rxdfexyden_in                      (rxdfexyden_in                     ),
      .rxdlybypass_in                     (rxdlybypass_in                    ),
      .rxdlyen_in                         (rxdlyen_in                        ),
      .rxdlyovrden_in                     (rxdlyovrden_in                    ),
      .rxdlysreset_in                     (rxdlysreset_in                    ),
      .rxelecidlemode_in                  (rxelecidlemode_in                 ),
      .rxgearboxslip_in                   (rxgearboxslip_in                  ),
      .rxlatclk_in                        (rxlatclk_in                       ),
      .rxlpmen_in                         (rxlpmen_in                        ),
      .rxlpmgchold_in                     (rxlpmgchold_in                    ),
      .rxlpmgcovrden_in                   (rxlpmgcovrden_in                  ),
      .rxlpmhfhold_in                     (rxlpmhfhold_in                    ),
      .rxlpmhfovrden_in                   (rxlpmhfovrden_in                  ),
      .rxlpmlfhold_in                     (rxlpmlfhold_in                    ),
      .rxlpmlfklovrden_in                 (rxlpmlfklovrden_in                ),
      .rxlpmoshold_in                     (rxlpmoshold_in                    ),
      .rxlpmosovrden_in                   (rxlpmosovrden_in                  ),
      .rxmcommaalignen_in                 (rxmcommaalignen_in                ),
      .rxmonitorsel_in                    (rxmonitorsel_in                   ),
      .rxoobreset_in                      (rxoobreset_in                     ),
      .rxoscalreset_in                    (rxoscalreset_in                   ),
      .rxoshold_in                        (rxoshold_in                       ),
      .rxosintcfg_in                      (rxosintcfg_in                     ),
      .rxosinten_in                       (rxosinten_in                      ),
      .rxosinthold_in                     (rxosinthold_in                    ),
      .rxosintovrden_in                   (rxosintovrden_in                  ),
      .rxosintstrobe_in                   (rxosintstrobe_in                  ),
      .rxosinttestovrden_in               (rxosinttestovrden_in              ),
      .rxosovrden_in                      (rxosovrden_in                     ),
      .rxoutclksel_in                     (rxoutclksel_in                    ),
      .rxpcommaalignen_in                 (rxpcommaalignen_in                ),
      .rxpcsreset_in                      (rxpcsreset_in                     ),
      .rxpd_in                            (rxpd_in                           ),
      .rxphalign_in                       (rxphalign_in                      ),
      .rxphalignen_in                     (rxphalignen_in                    ),
      .rxphdlypd_in                       (rxphdlypd_in                      ),
      .rxphdlyreset_in                    (rxphdlyreset_in                   ),
      .rxphovrden_in                      (rxphovrden_in                     ),
      .rxpllclksel_in                     (rxpllclksel_in                    ),
      .rxpmareset_in                      (rxpmareset_in                     ),
      .rxpolarity_in                      (rxpolarity_in                     ),
      .rxprbscntreset_in                  (rxprbscntreset_in                 ),
      .rxprbssel_in                       (rxprbssel_in                      ),
      .rxprogdivreset_in                  (rxprogdivreset_in                 ),
      .rxrate_in                          (rxrate_in                         ),
      .rxratemode_in                      (rxratemode_in                     ),
      .rxslide_in                         (rxslide_in                        ),
      .rxslipoutclk_in                    (rxslipoutclk_in                   ),
      .rxslippma_in                       (rxslippma_in                      ),
      .rxsyncallin_in                     (rxsyncallin_in                    ),
      .rxsyncin_in                        (rxsyncin_in                       ),
      .rxsyncmode_in                      (rxsyncmode_in                     ),
      .rxsysclksel_in                     (rxsysclksel_in                    ),
      .rxuserrdy_in                       (rxuserrdy_in                      ),
      .rxusrclk_in                        (rxusrclk_in                       ),
      .rxusrclk2_in                       (rxusrclk2_in                      ),
      .sigvalidclk_in                     (sigvalidclk_in                    ),
      .tstin_in                           (tstin_in                          ),
      .tx8b10bbypass_in                   (tx8b10bbypass_in                  ),
      .tx8b10ben_in                       (tx8b10ben_in                      ),
      .txbufdiffctrl_in                   (txbufdiffctrl_in                  ),
      .txcominit_in                       (txcominit_in                      ),
      .txcomsas_in                        (txcomsas_in                       ),
      .txcomwake_in                       (txcomwake_in                      ),
      .txctrl0_in                         (txctrl0_in                        ),
      .txctrl1_in                         (txctrl1_in                        ),
      .txctrl2_in                         (txctrl2_in                        ),
      .txdata_in                          (txdata_in                         ),
      .txdataextendrsvd_in                (txdataextendrsvd_in               ),
      .txdccforcestart_in                 (txdccforcestart_in                ),
      .txdccreset_in                      (txdccreset_in                     ),
      .txdeemph_in                        (txdeemph_in                       ),
      .txdetectrx_in                      (txdetectrx_in                     ),
      .txdiffctrl_in                      (txdiffctrl_in                     ),
      .txdiffpd_in                        (txdiffpd_in                       ),
      .txdlybypass_in                     (txdlybypass_in                    ),
      .txdlyen_in                         (txdlyen_in                        ),
      .txdlyhold_in                       (txdlyhold_in                      ),
      .txdlyovrden_in                     (txdlyovrden_in                    ),
      .txdlysreset_in                     (txdlysreset_in                    ),
      .txdlyupdown_in                     (txdlyupdown_in                    ),
      .txelecidle_in                      (txelecidle_in                     ),
      .txelforcestart_in                  (txelforcestart_in                 ),
      .txheader_in                        (txheader_in                       ),
      .txinhibit_in                       (txinhibit_in                      ),
      .txlatclk_in                        (txlatclk_in                       ),
      .txmaincursor_in                    (txmaincursor_in                   ),
      .txmargin_in                        (txmargin_in                       ),
      .txoutclksel_in                     (txoutclksel_in                    ),
      .txpcsreset_in                      (txpcsreset_in                     ),
      .txpd_in                            (txpd_in                           ),
      .txpdelecidlemode_in                (txpdelecidlemode_in               ),
      .txphalign_in                       (txphalign_in                      ),
      .txphalignen_in                     (txphalignen_in                    ),
      .txphdlypd_in                       (txphdlypd_in                      ),
      .txphdlyreset_in                    (txphdlyreset_in                   ),
      .txphdlytstclk_in                   (txphdlytstclk_in                  ),
      .txphinit_in                        (txphinit_in                       ),
      .txphovrden_in                      (txphovrden_in                     ),
      .txpippmen_in                       (txpippmen_in                      ),
      .txpippmovrden_in                   (txpippmovrden_in                  ),
      .txpippmpd_in                       (txpippmpd_in                      ),
      .txpippmsel_in                      (txpippmsel_in                     ),
      .txpippmstepsize_in                 (txpippmstepsize_in                ),
      .txpisopd_in                        (txpisopd_in                       ),
      .txpllclksel_in                     (txpllclksel_in                    ),
      .txpmareset_in                      (txpmareset_in                     ),
      .txpolarity_in                      (txpolarity_in                     ),
      .txpostcursor_in                    (txpostcursor_in                   ),
      .txprbsforceerr_in                  (txprbsforceerr_in                 ),
      .txprbssel_in                       (txprbssel_in                      ),
      .txprecursor_in                     (txprecursor_in                    ),
      .txprogdivreset_in                  (txprogdivreset_in                 ),
      .txrate_in                          (txrate_in                         ),
      .txratemode_in                      (txratemode_in                     ),
      .txsequence_in                      (txsequence_in                     ),
      .txswing_in                         (txswing_in                        ),
      .txsyncallin_in                     (txsyncallin_in                    ),
      .txsyncin_in                        (txsyncin_in                       ),
      .txsyncmode_in                      (txsyncmode_in                     ),
      .txsysclksel_in                     (txsysclksel_in                    ),
      .txuserrdy_in                       (txuserrdy_in                      ),
      .txusrclk_in                        (txusrclk_in                       ),
      .txusrclk2_in                       (txusrclk2_in                      ),
      .bufgtce_out                        (bufgtce_out                       ),
      .bufgtcemask_out                    (bufgtcemask_out                   ),
      .bufgtdiv_out                       (bufgtdiv_out                      ),
      .bufgtreset_out                     (bufgtreset_out                    ),
      .bufgtrstmask_out                   (bufgtrstmask_out                  ),
      .cpllfbclklost_out                  (cpllfbclklost_out                 ),
      .cplllock_out                       (cplllock_out                      ),
      .cpllrefclklost_out                 (cpllrefclklost_out                ),
      .dmonitorout_out                    (dmonitorout_out                   ),
      .drpdo_out                          (drpdo_out                         ),
      .drprdy_out                         (drprdy_out                        ),
      .eyescandataerror_out               (eyescandataerror_out              ),
      .gtpowergood_out                    (gtpowergood_out                   ),
      .gtrefclkmonitor_out                (gtrefclkmonitor_out               ),
      .gtytxn_out                         (gtytxn_out                        ),
      .gtytxp_out                         (gtytxp_out                        ),
      .pcierategen3_out                   (pcierategen3_out                  ),
      .pcierateidle_out                   (pcierateidle_out                  ),
      .pcierateqpllpd_out                 (pcierateqpllpd_out                ),
      .pcierateqpllreset_out              (pcierateqpllreset_out             ),
      .pciesynctxsyncdone_out             (pciesynctxsyncdone_out            ),
      .pcieusergen3rdy_out                (pcieusergen3rdy_out               ),
      .pcieuserphystatusrst_out           (pcieuserphystatusrst_out          ),
      .pcieuserratestart_out              (pcieuserratestart_out             ),
      .pcsrsvdout_out                     (pcsrsvdout_out                    ),
      .phystatus_out                      (phystatus_out                     ),
      .pinrsrvdas_out                     (pinrsrvdas_out                    ),
      .resetexception_out                 (resetexception_out                ),
      .rxbufstatus_out                    (rxbufstatus_out                   ),
      .rxbyteisaligned_out                (rxbyteisaligned_out               ),
      .rxbyterealign_out                  (rxbyterealign_out                 ),
      .rxcdrlock_out                      (rxcdrlock_out                     ),
      .rxcdrphdone_out                    (rxcdrphdone_out                   ),
      .rxchanbondseq_out                  (rxchanbondseq_out                 ),
      .rxchanisaligned_out                (rxchanisaligned_out               ),
      .rxchanrealign_out                  (rxchanrealign_out                 ),
      .rxchbondo_out                      (rxchbondo_out                     ),
      .rxckcaldone_out                    (rxckcaldone_out                   ),
      .rxclkcorcnt_out                    (rxclkcorcnt_out                   ),
      .rxcominitdet_out                   (rxcominitdet_out                  ),
      .rxcommadet_out                     (rxcommadet_out                    ),
      .rxcomsasdet_out                    (rxcomsasdet_out                   ),
      .rxcomwakedet_out                   (rxcomwakedet_out                  ),
      .rxctrl0_out                        (rxctrl0_out                       ),
      .rxctrl1_out                        (rxctrl1_out                       ),
      .rxctrl2_out                        (rxctrl2_out                       ),
      .rxctrl3_out                        (rxctrl3_out                       ),
      .rxdata_out                         (rxdata_out                        ),
      .rxdataextendrsvd_out               (rxdataextendrsvd_out              ),
      .rxdatavalid_out                    (rxdatavalid_out                   ),
      .rxdlysresetdone_out                (rxdlysresetdone_out               ),
      .rxelecidle_out                     (rxelecidle_out                    ),
      .rxheader_out                       (rxheader_out                      ),
      .rxheadervalid_out                  (rxheadervalid_out                 ),
      .rxmonitorout_out                   (rxmonitorout_out                  ),
      .rxosintdone_out                    (rxosintdone_out                   ),
      .rxosintstarted_out                 (rxosintstarted_out                ),
      .rxosintstrobedone_out              (rxosintstrobedone_out             ),
      .rxosintstrobestarted_out           (rxosintstrobestarted_out          ),
      .rxoutclk_out                       (rxoutclk_out                      ),
      .rxoutclkfabric_out                 (rxoutclkfabric_out                ),
      .rxoutclkpcs_out                    (rxoutclkpcs_out                   ),
      .rxphaligndone_out                  (rxphaligndone_out                 ),
      .rxphalignerr_out                   (rxphalignerr_out                  ),
      .rxpmaresetdone_out                 (rxpmaresetdone_out                ),
      .rxprbserr_out                      (rxprbserr_out                     ),
      .rxprbslocked_out                   (rxprbslocked_out                  ),
      .rxprgdivresetdone_out              (rxprgdivresetdone_out             ),
      .rxratedone_out                     (rxratedone_out                    ),
      .rxrecclkout_out                    (rxrecclkout_out                   ),
      .rxresetdone_out                    (rxresetdone_out                   ),
      .rxsliderdy_out                     (rxsliderdy_out                    ),
      .rxslipdone_out                     (rxslipdone_out                    ),
      .rxslipoutclkrdy_out                (rxslipoutclkrdy_out               ),
      .rxslippmardy_out                   (rxslippmardy_out                  ),
      .rxstartofseq_out                   (rxstartofseq_out                  ),
      .rxstatus_out                       (rxstatus_out                      ),
      .rxsyncdone_out                     (rxsyncdone_out                    ),
      .rxsyncout_out                      (rxsyncout_out                     ),
      .rxvalid_out                        (rxvalid_out                       ),
      .txbufstatus_out                    (txbufstatus_out                   ),
      .txcomfinish_out                    (txcomfinish_out                   ),
      .txdccdone_out                      (txdccdone_out                     ),
      .txdlysresetdone_out                (txdlysresetdone_out               ),
      .txoutclk_out                       (txoutclk_out                      ),
      .txoutclkfabric_out                 (txoutclkfabric_out                ),
      .txoutclkpcs_out                    (txoutclkpcs_out                   ),
      .txphaligndone_out                  (txphaligndone_out                 ),
      .txphinitdone_out                   (txphinitdone_out                  ),
      .txpmaresetdone_out                 (txpmaresetdone_out                ),
      .txprgdivresetdone_out              (txprgdivresetdone_out             ),
      .txratedone_out                     (txratedone_out                    ),
      .txresetdone_out                    (txresetdone_out                   ),
      .txsyncdone_out                     (txsyncdone_out                    ),
      .txsyncout_out                      (txsyncout_out                     )
    );

    // Drive unused outputs to constant values
    assign rxrecclk0sel_out      = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign rxrecclk1sel_out      = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign tcongpo_out           = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign tconrsvdout0_out      = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign ubdaddr_out           = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign ubden_out             = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign ubdi_out              = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign ubdwe_out             = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign ubmdmtdo_out          = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign ubrsvdout_out         = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign ubtxuart_out          = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign dmonitoroutclk_out    = {{`xdma_0_pcie4_ip_gt_N_CH}{1'b0}};
    assign gthtxn_out            = {{`xdma_0_pcie4_ip_gt_N_CH}{1'b0}};
    assign gthtxp_out            = {{`xdma_0_pcie4_ip_gt_N_CH}{1'b0}};
    assign powerpresent_out      = {{`xdma_0_pcie4_ip_gt_N_CH}{1'b0}};
    assign rxlfpstresetdet_out   = {{`xdma_0_pcie4_ip_gt_N_CH}{1'b0}};
    assign rxlfpsu2lpexitdet_out = {{`xdma_0_pcie4_ip_gt_N_CH}{1'b0}};
    assign rxlfpsu3wakedet_out   = {{`xdma_0_pcie4_ip_gt_N_CH}{1'b0}};
    assign rxqpisenn_out         = {{`xdma_0_pcie4_ip_gt_N_CH}{1'b0}};
    assign rxqpisenp_out         = {{`xdma_0_pcie4_ip_gt_N_CH}{1'b0}};
    assign txqpisenn_out         = {{`xdma_0_pcie4_ip_gt_N_CH}{1'b0}};
    assign txqpisenp_out         = {{`xdma_0_pcie4_ip_gt_N_CH}{1'b0}};

  end
  else if (C_GT_TYPE == `xdma_0_pcie4_ip_gt_GT_TYPE__GTHE4) begin : gen_gtwizard_gthe4_top

    // Generate GTHE4-type Transceivers Wizard submodule
    xdma_0_pcie4_ip_gt_gtwizard_gthe4 #(
      .C_CHANNEL_ENABLE                          (C_CHANNEL_ENABLE                         ),
      .C_COMMON_SCALING_FACTOR                   (C_COMMON_SCALING_FACTOR                  ),
      .C_FREERUN_FREQUENCY                       (C_FREERUN_FREQUENCY                      ),
      .C_INCLUDE_CPLL_CAL                        (C_INCLUDE_CPLL_CAL                       ),
      .C_SIM_CPLL_CAL_BYPASS                     (C_SIM_CPLL_CAL_BYPASS                    ),
      .C_LOCATE_RESET_CONTROLLER                 (C_LOCATE_RESET_CONTROLLER                ),
      .C_LOCATE_USER_DATA_WIDTH_SIZING           (C_LOCATE_USER_DATA_WIDTH_SIZING          ),
      .C_LOCATE_RX_BUFFER_BYPASS_CONTROLLER      (C_LOCATE_RX_BUFFER_BYPASS_CONTROLLER     ),
      .C_LOCATE_RX_USER_CLOCKING                 (C_LOCATE_RX_USER_CLOCKING                ),
      .C_LOCATE_TX_BUFFER_BYPASS_CONTROLLER      (C_LOCATE_TX_BUFFER_BYPASS_CONTROLLER     ),
      .C_LOCATE_TX_USER_CLOCKING                 (C_LOCATE_TX_USER_CLOCKING                ),
      .C_RESET_CONTROLLER_INSTANCE_CTRL          (C_RESET_CONTROLLER_INSTANCE_CTRL         ),
      .C_RX_BUFFBYPASS_MODE                      (C_RX_BUFFBYPASS_MODE                     ),
      .C_RX_BUFFER_BYPASS_INSTANCE_CTRL          (C_RX_BUFFER_BYPASS_INSTANCE_CTRL         ),
      .C_RX_BUFFER_MODE                          (C_RX_BUFFER_MODE                         ),
      .C_RX_DATA_DECODING                        (C_RX_DATA_DECODING                       ),
      .C_RX_ENABLE                               (C_RX_ENABLE                              ),
      .C_RX_INT_DATA_WIDTH                       (C_RX_INT_DATA_WIDTH                      ),
      .C_RX_LINE_RATE                            (C_RX_LINE_RATE                           ),
      .C_RX_MASTER_CHANNEL_IDX                   (C_RX_MASTER_CHANNEL_IDX                  ),
      .C_RX_OUTCLK_BUFG_GT_DIV                   (C_RX_OUTCLK_BUFG_GT_DIV                  ),
      .C_RX_PLL_TYPE                             (C_RX_PLL_TYPE                            ),
      .C_RX_USER_CLOCKING_CONTENTS               (C_RX_USER_CLOCKING_CONTENTS              ),
      .C_RX_USER_CLOCKING_INSTANCE_CTRL          (C_RX_USER_CLOCKING_INSTANCE_CTRL         ),
      .C_RX_USER_CLOCKING_RATIO_FUSRCLK_FUSRCLK2 (C_RX_USER_CLOCKING_RATIO_FUSRCLK_FUSRCLK2),
      .C_RX_USER_CLOCKING_SOURCE                 (C_RX_USER_CLOCKING_SOURCE                ),
      .C_RX_USER_DATA_WIDTH                      (C_RX_USER_DATA_WIDTH                     ),
      .C_TOTAL_NUM_CHANNELS                      (C_TOTAL_NUM_CHANNELS                     ),
      .C_TOTAL_NUM_COMMONS                       (C_TOTAL_NUM_COMMONS                      ),
      .C_TX_BUFFBYPASS_MODE                      (C_TX_BUFFBYPASS_MODE                     ),
      .C_TX_BUFFER_BYPASS_INSTANCE_CTRL          (C_TX_BUFFER_BYPASS_INSTANCE_CTRL         ),
      .C_TX_BUFFER_MODE                          (C_TX_BUFFER_MODE                         ),
      .C_TX_DATA_ENCODING                        (C_TX_DATA_ENCODING                       ),
      .C_TX_ENABLE                               (C_TX_ENABLE                              ),
      .C_TX_INT_DATA_WIDTH                       (C_TX_INT_DATA_WIDTH                      ),
      .C_TX_MASTER_CHANNEL_IDX                   (C_TX_MASTER_CHANNEL_IDX                  ),
      .C_TX_OUTCLK_BUFG_GT_DIV                   (C_TX_OUTCLK_BUFG_GT_DIV                  ),
      .C_TX_PLL_TYPE                             (C_TX_PLL_TYPE                            ),
      .C_TX_USER_CLOCKING_CONTENTS               (C_TX_USER_CLOCKING_CONTENTS              ),
      .C_TX_USER_CLOCKING_INSTANCE_CTRL          (C_TX_USER_CLOCKING_INSTANCE_CTRL         ),
      .C_TX_USER_CLOCKING_RATIO_FUSRCLK_FUSRCLK2 (C_TX_USER_CLOCKING_RATIO_FUSRCLK_FUSRCLK2),
      .C_TX_USER_CLOCKING_SOURCE                 (C_TX_USER_CLOCKING_SOURCE                ),
      .C_TX_USER_DATA_WIDTH                      (C_TX_USER_DATA_WIDTH                     )
    ) xdma_0_pcie4_ip_gt_gtwizard_gthe4_inst (
      .gtwiz_userclk_tx_reset_in          (gtwiz_userclk_tx_reset_in         ),
      .gtwiz_userclk_tx_active_in         (gtwiz_userclk_tx_active_in        ),
      .gtwiz_userclk_tx_srcclk_out        (gtwiz_userclk_tx_srcclk_out       ),
      .gtwiz_userclk_tx_usrclk_out        (gtwiz_userclk_tx_usrclk_out       ),
      .gtwiz_userclk_tx_usrclk2_out       (gtwiz_userclk_tx_usrclk2_out      ),
      .gtwiz_userclk_tx_active_out        (gtwiz_userclk_tx_active_out       ),
      .gtwiz_userclk_rx_reset_in          (gtwiz_userclk_rx_reset_in         ),
      .gtwiz_userclk_rx_active_in         (gtwiz_userclk_rx_active_in        ),
      .gtwiz_userclk_rx_srcclk_out        (gtwiz_userclk_rx_srcclk_out       ),
      .gtwiz_userclk_rx_usrclk_out        (gtwiz_userclk_rx_usrclk_out       ),
      .gtwiz_userclk_rx_usrclk2_out       (gtwiz_userclk_rx_usrclk2_out      ),
      .gtwiz_userclk_rx_active_out        (gtwiz_userclk_rx_active_out       ),
      .gtwiz_buffbypass_tx_reset_in       (gtwiz_buffbypass_tx_reset_in      ),
      .gtwiz_buffbypass_tx_start_user_in  (gtwiz_buffbypass_tx_start_user_in ),
      .gtwiz_buffbypass_tx_done_out       (gtwiz_buffbypass_tx_done_out      ),
      .gtwiz_buffbypass_tx_error_out      (gtwiz_buffbypass_tx_error_out     ),
      .gtwiz_buffbypass_rx_reset_in       (gtwiz_buffbypass_rx_reset_in      ),
      .gtwiz_buffbypass_rx_start_user_in  (gtwiz_buffbypass_rx_start_user_in ),
      .gtwiz_buffbypass_rx_done_out       (gtwiz_buffbypass_rx_done_out      ),
      .gtwiz_buffbypass_rx_error_out      (gtwiz_buffbypass_rx_error_out     ),
      .gtwiz_reset_clk_freerun_in         (gtwiz_reset_clk_freerun_in        ),
      .gtwiz_reset_all_in                 (gtwiz_reset_all_in                ),
      .gtwiz_reset_tx_pll_and_datapath_in (gtwiz_reset_tx_pll_and_datapath_in),
      .gtwiz_reset_tx_datapath_in         (gtwiz_reset_tx_datapath_in        ),
      .gtwiz_reset_rx_pll_and_datapath_in (gtwiz_reset_rx_pll_and_datapath_in),
      .gtwiz_reset_rx_datapath_in         (gtwiz_reset_rx_datapath_in        ),
      .gtwiz_reset_tx_done_in             (gtwiz_reset_tx_done_in            ),
      .gtwiz_reset_rx_done_in             (gtwiz_reset_rx_done_in            ),
      .gtwiz_reset_qpll0lock_in           (gtwiz_reset_qpll0lock_in          ),
      .gtwiz_reset_qpll1lock_in           (gtwiz_reset_qpll1lock_in          ),
      .gtwiz_reset_rx_cdr_stable_out      (gtwiz_reset_rx_cdr_stable_out     ),
      .gtwiz_reset_tx_done_out            (gtwiz_reset_tx_done_out           ),
      .gtwiz_reset_rx_done_out            (gtwiz_reset_rx_done_out           ),
      .gtwiz_reset_qpll0reset_out         (gtwiz_reset_qpll0reset_out        ),
      .gtwiz_reset_qpll1reset_out         (gtwiz_reset_qpll1reset_out        ),
      .gtwiz_gthe4_cpll_cal_txoutclk_period_in (gtwiz_gthe4_cpll_cal_txoutclk_period_in),
      .gtwiz_gthe4_cpll_cal_cnt_tol_in         (gtwiz_gthe4_cpll_cal_cnt_tol_in        ),
      .gtwiz_gthe4_cpll_cal_bufg_ce_in         (gtwiz_gthe4_cpll_cal_bufg_ce_in        ),
      .gtwiz_userdata_tx_in               (gtwiz_userdata_tx_in              ),
      .gtwiz_userdata_rx_out              (gtwiz_userdata_rx_out             ),
      .bgbypassb_in                       (bgbypassb_in                      ),
      .bgmonitorenb_in                    (bgmonitorenb_in                   ),
      .bgpdb_in                           (bgpdb_in                          ),
      .bgrcalovrd_in                      (bgrcalovrd_in                     ),
      .bgrcalovrdenb_in                   (bgrcalovrdenb_in                  ),
      .drpaddr_common_in                  (drpaddr_common_in                 ),
      .drpclk_common_in                   (drpclk_common_in                  ),
      .drpdi_common_in                    (drpdi_common_in                   ),
      .drpen_common_in                    (drpen_common_in                   ),
      .drpwe_common_in                    (drpwe_common_in                   ),
      .gtgrefclk0_in                      (gtgrefclk0_in                     ),
      .gtgrefclk1_in                      (gtgrefclk1_in                     ),
      .gtnorthrefclk00_in                 (gtnorthrefclk00_in                ),
      .gtnorthrefclk01_in                 (gtnorthrefclk01_in                ),
      .gtnorthrefclk10_in                 (gtnorthrefclk10_in                ),
      .gtnorthrefclk11_in                 (gtnorthrefclk11_in                ),
      .gtrefclk00_in                      (gtrefclk00_in                     ),
      .gtrefclk01_in                      (gtrefclk01_in                     ),
      .gtrefclk10_in                      (gtrefclk10_in                     ),
      .gtrefclk11_in                      (gtrefclk11_in                     ),
      .gtsouthrefclk00_in                 (gtsouthrefclk00_in                ),
      .gtsouthrefclk01_in                 (gtsouthrefclk01_in                ),
      .gtsouthrefclk10_in                 (gtsouthrefclk10_in                ),
      .gtsouthrefclk11_in                 (gtsouthrefclk11_in                ),
      .pcierateqpll0_in                   (pcierateqpll0_in                  ),
      .pcierateqpll1_in                   (pcierateqpll1_in                  ),
      .pmarsvd0_in                        (pmarsvd0_in                       ),
      .pmarsvd1_in                        (pmarsvd1_in                       ),
      .qpll0clkrsvd0_in                   (qpll0clkrsvd0_in                  ),
      .qpll0clkrsvd1_in                   (qpll0clkrsvd1_in                  ),
      .qpll0fbdiv_in                      (qpll0fbdiv_in                     ),
      .qpll0lockdetclk_in                 (qpll0lockdetclk_in                ),
      .qpll0locken_in                     (qpll0locken_in                    ),
      .qpll0pd_in                         (qpll0pd_in                        ),
      .qpll0refclksel_in                  (qpll0refclksel_in                 ),
      .qpll0reset_in                      (qpll0reset_in                     ),
      .qpll1clkrsvd0_in                   (qpll1clkrsvd0_in                  ),
      .qpll1clkrsvd1_in                   (qpll1clkrsvd1_in                  ),
      .qpll1fbdiv_in                      (qpll1fbdiv_in                     ),
      .qpll1lockdetclk_in                 (qpll1lockdetclk_in                ),
      .qpll1locken_in                     (qpll1locken_in                    ),
      .qpll1pd_in                         (qpll1pd_in                        ),
      .qpll1refclksel_in                  (qpll1refclksel_in                 ),
      .qpll1reset_in                      (qpll1reset_in                     ),
      .qpllrsvd1_in                       (qpllrsvd1_in                      ),
      .qpllrsvd2_in                       (qpllrsvd2_in                      ),
      .qpllrsvd3_in                       (qpllrsvd3_in                      ),
      .qpllrsvd4_in                       (qpllrsvd4_in                      ),
      .rcalenb_in                         (rcalenb_in                        ),
      .sdm0data_in                        (sdm0data_in                       ),
      .sdm0reset_in                       (sdm0reset_in                      ),
      .sdm0toggle_in                      (sdm0toggle_in                     ),
      .sdm0width_in                       (sdm0width_in                      ),
      .sdm1data_in                        (sdm1data_in                       ),
      .sdm1reset_in                       (sdm1reset_in                      ),
      .sdm1toggle_in                      (sdm1toggle_in                     ),
      .sdm1width_in                       (sdm1width_in                      ),
      .tcongpi_in                         (tcongpi_in                        ),
      .tconpowerup_in                     (tconpowerup_in                    ),
      .tconreset_in                       (tconreset_in                      ),
      .tconrsvdin1_in                     (tconrsvdin1_in                    ),
      .drpdo_common_out                   (drpdo_common_out                  ),
      .drprdy_common_out                  (drprdy_common_out                 ),
      .pmarsvdout0_out                    (pmarsvdout0_out                   ),
      .pmarsvdout1_out                    (pmarsvdout1_out                   ),
      .qpll0fbclklost_out                 (qpll0fbclklost_out                ),
      .qpll0lock_out                      (qpll0lock_out                     ),
      .qpll0outclk_out                    (qpll0outclk_out                   ),
      .qpll0outrefclk_out                 (qpll0outrefclk_out                ),
      .qpll0refclklost_out                (qpll0refclklost_out               ),
      .qpll1fbclklost_out                 (qpll1fbclklost_out                ),
      .qpll1lock_out                      (qpll1lock_out                     ),
      .qpll1outclk_out                    (qpll1outclk_out                   ),
      .qpll1outrefclk_out                 (qpll1outrefclk_out                ),
      .qpll1refclklost_out                (qpll1refclklost_out               ),
      .qplldmonitor0_out                  (qplldmonitor0_out                 ),
      .qplldmonitor1_out                  (qplldmonitor1_out                 ),
      .refclkoutmonitor0_out              (refclkoutmonitor0_out             ),
      .refclkoutmonitor1_out              (refclkoutmonitor1_out             ),
      .rxrecclk0sel_out                   (rxrecclk0sel_out                  ),
      .rxrecclk1sel_out                   (rxrecclk1sel_out                  ),
      .sdm0finalout_out                   (sdm0finalout_out                  ),
      .sdm0testdata_out                   (sdm0testdata_out                  ),
      .sdm1finalout_out                   (sdm1finalout_out                  ),
      .sdm1testdata_out                   (sdm1testdata_out                  ),
      .tcongpo_out                        (tcongpo_out                       ),
      .tconrsvdout0_out                   (tconrsvdout0_out                  ),
      .cdrstepdir_in                      (cdrstepdir_in                     ),
      .cdrstepsq_in                       (cdrstepsq_in                      ),
      .cdrstepsx_in                       (cdrstepsx_in                      ),
      .cfgreset_in                        (cfgreset_in                       ),
      .clkrsvd0_in                        (clkrsvd0_in                       ),
      .clkrsvd1_in                        (clkrsvd1_in                       ),
      .cpllfreqlock_in                    (cpllfreqlock_in                   ),
      .cplllockdetclk_in                  (cplllockdetclk_in                 ),
      .cplllocken_in                      (cplllocken_in                     ),
      .cpllpd_in                          (cpllpd_in                         ),
      .cpllrefclksel_in                   (cpllrefclksel_in                  ),
      .cpllreset_in                       (cpllreset_in                      ),
      .dmonfiforeset_in                   (dmonfiforeset_in                  ),
      .dmonitorclk_in                     (dmonitorclk_in                    ),
      .drpaddr_in                         (drpaddr_in                        ),
      .drpclk_in                          (drpclk_in                         ),
      .drpdi_in                           (drpdi_in                          ),
      .drpen_in                           (drpen_in                          ),
      .drprst_in                          (drprst_in                         ),
      .drpwe_in                           (drpwe_in                          ),
      .eyescanreset_in                    (eyescanreset_in                   ),
      .eyescantrigger_in                  (eyescantrigger_in                 ),
      .freqos_in                          (freqos_in                         ),
      .gtgrefclk_in                       (gtgrefclk_in                      ),
      .gthrxn_in                          (gthrxn_in                         ),
      .gthrxp_in                          (gthrxp_in                         ),
      .gtnorthrefclk0_in                  (gtnorthrefclk0_in                 ),
      .gtnorthrefclk1_in                  (gtnorthrefclk1_in                 ),
      .gtrefclk0_in                       (gtrefclk0_in                      ),
      .gtrefclk1_in                       (gtrefclk1_in                      ),
      .gtrsvd_in                          (gtrsvd_in                         ),
      .gtrxreset_in                       (gtrxreset_in                      ),
      .gtrxresetsel_in                    (gtrxresetsel_in                   ),
      .gtsouthrefclk0_in                  (gtsouthrefclk0_in                 ),
      .gtsouthrefclk1_in                  (gtsouthrefclk1_in                 ),
      .gttxreset_in                       (gttxreset_in                      ),
      .gttxresetsel_in                    (gttxresetsel_in                   ),
      .incpctrl_in                        (incpctrl_in                       ),
      .loopback_in                        (loopback_in                       ),
      .pcieeqrxeqadaptdone_in             (pcieeqrxeqadaptdone_in            ),
      .pcierstidle_in                     (pcierstidle_in                    ),
      .pciersttxsyncstart_in              (pciersttxsyncstart_in             ),
      .pcieuserratedone_in                (pcieuserratedone_in               ),
      .pcsrsvdin_in                       (pcsrsvdin_in                      ),
      .qpll0clk_in                        (qpll0clk_in                       ),
      .qpll0freqlock_in                   (qpll0freqlock_in                  ),
      .qpll0refclk_in                     (qpll0refclk_in                    ),
      .qpll1clk_in                        (qpll1clk_in                       ),
      .qpll1freqlock_in                   (qpll1freqlock_in                  ),
      .qpll1refclk_in                     (qpll1refclk_in                    ),
      .resetovrd_in                       (resetovrd_in                      ),
      .rx8b10ben_in                       (rx8b10ben_in                      ),
      .rxafecfoken_in                     (rxafecfoken_in                    ),
      .rxbufreset_in                      (rxbufreset_in                     ),
      .rxcdrfreqreset_in                  (rxcdrfreqreset_in                 ),
      .rxcdrhold_in                       (rxcdrhold_in                      ),
      .rxcdrovrden_in                     (rxcdrovrden_in                    ),
      .rxcdrreset_in                      (rxcdrreset_in                     ),
      .rxchbonden_in                      (rxchbonden_in                     ),
      .rxchbondi_in                       (rxchbondi_in                      ),
      .rxchbondlevel_in                   (rxchbondlevel_in                  ),
      .rxchbondmaster_in                  (rxchbondmaster_in                 ),
      .rxchbondslave_in                   (rxchbondslave_in                  ),
      .rxckcalreset_in                    (rxckcalreset_in                   ),
      .rxckcalstart_in                    (rxckcalstart_in                   ),
      .rxcommadeten_in                    (rxcommadeten_in                   ),
      .rxdfeagcctrl_in                    (rxdfeagcctrl_in                   ),
      .rxdfeagchold_in                    (rxdfeagchold_in                   ),
      .rxdfeagcovrden_in                  (rxdfeagcovrden_in                 ),
      .rxdfecfokfcnum_in                  (rxdfecfokfcnum_in                 ),
      .rxdfecfokfen_in                    (rxdfecfokfen_in                   ),
      .rxdfecfokfpulse_in                 (rxdfecfokfpulse_in                ),
      .rxdfecfokhold_in                   (rxdfecfokhold_in                  ),
      .rxdfecfokovren_in                  (rxdfecfokovren_in                 ),
      .rxdfekhhold_in                     (rxdfekhhold_in                    ),
      .rxdfekhovrden_in                   (rxdfekhovrden_in                  ),
      .rxdfelfhold_in                     (rxdfelfhold_in                    ),
      .rxdfelfovrden_in                   (rxdfelfovrden_in                  ),
      .rxdfelpmreset_in                   (rxdfelpmreset_in                  ),
      .rxdfetap10hold_in                  (rxdfetap10hold_in                 ),
      .rxdfetap10ovrden_in                (rxdfetap10ovrden_in               ),
      .rxdfetap11hold_in                  (rxdfetap11hold_in                 ),
      .rxdfetap11ovrden_in                (rxdfetap11ovrden_in               ),
      .rxdfetap12hold_in                  (rxdfetap12hold_in                 ),
      .rxdfetap12ovrden_in                (rxdfetap12ovrden_in               ),
      .rxdfetap13hold_in                  (rxdfetap13hold_in                 ),
      .rxdfetap13ovrden_in                (rxdfetap13ovrden_in               ),
      .rxdfetap14hold_in                  (rxdfetap14hold_in                 ),
      .rxdfetap14ovrden_in                (rxdfetap14ovrden_in               ),
      .rxdfetap15hold_in                  (rxdfetap15hold_in                 ),
      .rxdfetap15ovrden_in                (rxdfetap15ovrden_in               ),
      .rxdfetap2hold_in                   (rxdfetap2hold_in                  ),
      .rxdfetap2ovrden_in                 (rxdfetap2ovrden_in                ),
      .rxdfetap3hold_in                   (rxdfetap3hold_in                  ),
      .rxdfetap3ovrden_in                 (rxdfetap3ovrden_in                ),
      .rxdfetap4hold_in                   (rxdfetap4hold_in                  ),
      .rxdfetap4ovrden_in                 (rxdfetap4ovrden_in                ),
      .rxdfetap5hold_in                   (rxdfetap5hold_in                  ),
      .rxdfetap5ovrden_in                 (rxdfetap5ovrden_in                ),
      .rxdfetap6hold_in                   (rxdfetap6hold_in                  ),
      .rxdfetap6ovrden_in                 (rxdfetap6ovrden_in                ),
      .rxdfetap7hold_in                   (rxdfetap7hold_in                  ),
      .rxdfetap7ovrden_in                 (rxdfetap7ovrden_in                ),
      .rxdfetap8hold_in                   (rxdfetap8hold_in                  ),
      .rxdfetap8ovrden_in                 (rxdfetap8ovrden_in                ),
      .rxdfetap9hold_in                   (rxdfetap9hold_in                  ),
      .rxdfetap9ovrden_in                 (rxdfetap9ovrden_in                ),
      .rxdfeuthold_in                     (rxdfeuthold_in                    ),
      .rxdfeutovrden_in                   (rxdfeutovrden_in                  ),
      .rxdfevphold_in                     (rxdfevphold_in                    ),
      .rxdfevpovrden_in                   (rxdfevpovrden_in                  ),
      .rxdfexyden_in                      (rxdfexyden_in                     ),
      .rxdlybypass_in                     (rxdlybypass_in                    ),
      .rxdlyen_in                         (rxdlyen_in                        ),
      .rxdlyovrden_in                     (rxdlyovrden_in                    ),
      .rxdlysreset_in                     (rxdlysreset_in                    ),
      .rxelecidlemode_in                  (rxelecidlemode_in                 ),
      .rxeqtraining_in                    (rxeqtraining_in                   ),
      .rxgearboxslip_in                   (rxgearboxslip_in                  ),
      .rxlatclk_in                        (rxlatclk_in                       ),
      .rxlpmen_in                         (rxlpmen_in                        ),
      .rxlpmgchold_in                     (rxlpmgchold_in                    ),
      .rxlpmgcovrden_in                   (rxlpmgcovrden_in                  ),
      .rxlpmhfhold_in                     (rxlpmhfhold_in                    ),
      .rxlpmhfovrden_in                   (rxlpmhfovrden_in                  ),
      .rxlpmlfhold_in                     (rxlpmlfhold_in                    ),
      .rxlpmlfklovrden_in                 (rxlpmlfklovrden_in                ),
      .rxlpmoshold_in                     (rxlpmoshold_in                    ),
      .rxlpmosovrden_in                   (rxlpmosovrden_in                  ),
      .rxmcommaalignen_in                 (rxmcommaalignen_in                ),
      .rxmonitorsel_in                    (rxmonitorsel_in                   ),
      .rxoobreset_in                      (rxoobreset_in                     ),
      .rxoscalreset_in                    (rxoscalreset_in                   ),
      .rxoshold_in                        (rxoshold_in                       ),
      .rxosovrden_in                      (rxosovrden_in                     ),
      .rxoutclksel_in                     (rxoutclksel_in                    ),
      .rxpcommaalignen_in                 (rxpcommaalignen_in                ),
      .rxpcsreset_in                      (rxpcsreset_in                     ),
      .rxpd_in                            (rxpd_in                           ),
      .rxphalign_in                       (rxphalign_in                      ),
      .rxphalignen_in                     (rxphalignen_in                    ),
      .rxphdlypd_in                       (rxphdlypd_in                      ),
      .rxphdlyreset_in                    (rxphdlyreset_in                   ),
      .rxphovrden_in                      (rxphovrden_in                     ),
      .rxpllclksel_in                     (rxpllclksel_in                    ),
      .rxpmareset_in                      (rxpmareset_in                     ),
      .rxpolarity_in                      (rxpolarity_in                     ),
      .rxprbscntreset_in                  (rxprbscntreset_in                 ),
      .rxprbssel_in                       (rxprbssel_in                      ),
      .rxprogdivreset_in                  (rxprogdivreset_in                 ),
      .rxqpien_in                         (rxqpien_in                        ),
      .rxrate_in                          (rxrate_in                         ),
      .rxratemode_in                      (rxratemode_in                     ),
      .rxslide_in                         (rxslide_in                        ),
      .rxslipoutclk_in                    (rxslipoutclk_in                   ),
      .rxslippma_in                       (rxslippma_in                      ),
      .rxsyncallin_in                     (rxsyncallin_in                    ),
      .rxsyncin_in                        (rxsyncin_in                       ),
      .rxsyncmode_in                      (rxsyncmode_in                     ),
      .rxsysclksel_in                     (rxsysclksel_in                    ),
      .rxtermination_in                   (rxtermination_in                  ),
      .rxuserrdy_in                       (rxuserrdy_in                      ),
      .rxusrclk_in                        (rxusrclk_in                       ),
      .rxusrclk2_in                       (rxusrclk2_in                      ),
      .sigvalidclk_in                     (sigvalidclk_in                    ),
      .tstin_in                           (tstin_in                          ),
      .tx8b10bbypass_in                   (tx8b10bbypass_in                  ),
      .tx8b10ben_in                       (tx8b10ben_in                      ),
      .txcominit_in                       (txcominit_in                      ),
      .txcomsas_in                        (txcomsas_in                       ),
      .txcomwake_in                       (txcomwake_in                      ),
      .txctrl0_in                         (txctrl0_in                        ),
      .txctrl1_in                         (txctrl1_in                        ),
      .txctrl2_in                         (txctrl2_in                        ),
      .txdata_in                          (txdata_in                         ),
      .txdataextendrsvd_in                (txdataextendrsvd_in               ),
      .txdccforcestart_in                 (txdccforcestart_in                ),
      .txdccreset_in                      (txdccreset_in                     ),
      .txdeemph_in                        (txdeemph_in                       ),
      .txdetectrx_in                      (txdetectrx_in                     ),
      .txdiffctrl_in                      (txdiffctrl_in                     ),
      .txdlybypass_in                     (txdlybypass_in                    ),
      .txdlyen_in                         (txdlyen_in                        ),
      .txdlyhold_in                       (txdlyhold_in                      ),
      .txdlyovrden_in                     (txdlyovrden_in                    ),
      .txdlysreset_in                     (txdlysreset_in                    ),
      .txdlyupdown_in                     (txdlyupdown_in                    ),
      .txelecidle_in                      (txelecidle_in                     ),
      .txheader_in                        (txheader_in                       ),
      .txinhibit_in                       (txinhibit_in                      ),
      .txlatclk_in                        (txlatclk_in                       ),
      .txlfpstreset_in                    (txlfpstreset_in                   ),
      .txlfpsu2lpexit_in                  (txlfpsu2lpexit_in                 ),
      .txlfpsu3wake_in                    (txlfpsu3wake_in                   ),
      .txmaincursor_in                    (txmaincursor_in                   ),
      .txmargin_in                        (txmargin_in                       ),
      .txmuxdcdexhold_in                  (txmuxdcdexhold_in                 ),
      .txmuxdcdorwren_in                  (txmuxdcdorwren_in                 ),
      .txoneszeros_in                     (txoneszeros_in                    ),
      .txoutclksel_in                     (txoutclksel_in                    ),
      .txpcsreset_in                      (txpcsreset_in                     ),
      .txpd_in                            (txpd_in                           ),
      .txpdelecidlemode_in                (txpdelecidlemode_in               ),
      .txphalign_in                       (txphalign_in                      ),
      .txphalignen_in                     (txphalignen_in                    ),
      .txphdlypd_in                       (txphdlypd_in                      ),
      .txphdlyreset_in                    (txphdlyreset_in                   ),
      .txphdlytstclk_in                   (txphdlytstclk_in                  ),
      .txphinit_in                        (txphinit_in                       ),
      .txphovrden_in                      (txphovrden_in                     ),
      .txpippmen_in                       (txpippmen_in                      ),
      .txpippmovrden_in                   (txpippmovrden_in                  ),
      .txpippmpd_in                       (txpippmpd_in                      ),
      .txpippmsel_in                      (txpippmsel_in                     ),
      .txpippmstepsize_in                 (txpippmstepsize_in                ),
      .txpisopd_in                        (txpisopd_in                       ),
      .txpllclksel_in                     (txpllclksel_in                    ),
      .txpmareset_in                      (txpmareset_in                     ),
      .txpolarity_in                      (txpolarity_in                     ),
      .txpostcursor_in                    (txpostcursor_in                   ),
      .txprbsforceerr_in                  (txprbsforceerr_in                 ),
      .txprbssel_in                       (txprbssel_in                      ),
      .txprecursor_in                     (txprecursor_in                    ),
      .txprogdivreset_in                  (txprogdivreset_in                 ),
      .txqpibiasen_in                     (txqpibiasen_in                    ),
      .txqpiweakpup_in                    (txqpiweakpup_in                   ),
      .txrate_in                          (txrate_in                         ),
      .txratemode_in                      (txratemode_in                     ),
      .txsequence_in                      (txsequence_in                     ),
      .txswing_in                         (txswing_in                        ),
      .txsyncallin_in                     (txsyncallin_in                    ),
      .txsyncin_in                        (txsyncin_in                       ),
      .txsyncmode_in                      (txsyncmode_in                     ),
      .txsysclksel_in                     (txsysclksel_in                    ),
      .txuserrdy_in                       (txuserrdy_in                      ),
      .txusrclk_in                        (txusrclk_in                       ),
      .txusrclk2_in                       (txusrclk2_in                      ),
      .bufgtce_out                        (bufgtce_out                       ),
      .bufgtcemask_out                    (bufgtcemask_out                   ),
      .bufgtdiv_out                       (bufgtdiv_out                      ),
      .bufgtreset_out                     (bufgtreset_out                    ),
      .bufgtrstmask_out                   (bufgtrstmask_out                  ),
      .cpllfbclklost_out                  (cpllfbclklost_out                 ),
      .cplllock_out                       (cplllock_out                      ),
      .cpllrefclklost_out                 (cpllrefclklost_out                ),
      .dmonitorout_out                    (dmonitorout_out                   ),
      .dmonitoroutclk_out                 (dmonitoroutclk_out                ),
      .drpdo_out                          (drpdo_out                         ),
      .drprdy_out                         (drprdy_out                        ),
      .eyescandataerror_out               (eyescandataerror_out              ),
      .gthtxn_out                         (gthtxn_out                        ),
      .gthtxp_out                         (gthtxp_out                        ),
      .gtpowergood_out                    (gtpowergood_out                   ),
      .gtrefclkmonitor_out                (gtrefclkmonitor_out               ),
      .pcierategen3_out                   (pcierategen3_out                  ),
      .pcierateidle_out                   (pcierateidle_out                  ),
      .pcierateqpllpd_out                 (pcierateqpllpd_out                ),
      .pcierateqpllreset_out              (pcierateqpllreset_out             ),
      .pciesynctxsyncdone_out             (pciesynctxsyncdone_out            ),
      .pcieusergen3rdy_out                (pcieusergen3rdy_out               ),
      .pcieuserphystatusrst_out           (pcieuserphystatusrst_out          ),
      .pcieuserratestart_out              (pcieuserratestart_out             ),
      .pcsrsvdout_out                     (pcsrsvdout_out                    ),
      .phystatus_out                      (phystatus_out                     ),
      .pinrsrvdas_out                     (pinrsrvdas_out                    ),
      .powerpresent_out                   (powerpresent_out                  ),
      .resetexception_out                 (resetexception_out                ),
      .rxbufstatus_out                    (rxbufstatus_out                   ),
      .rxbyteisaligned_out                (rxbyteisaligned_out               ),
      .rxbyterealign_out                  (rxbyterealign_out                 ),
      .rxcdrlock_out                      (rxcdrlock_out                     ),
      .rxcdrphdone_out                    (rxcdrphdone_out                   ),
      .rxchanbondseq_out                  (rxchanbondseq_out                 ),
      .rxchanisaligned_out                (rxchanisaligned_out               ),
      .rxchanrealign_out                  (rxchanrealign_out                 ),
      .rxchbondo_out                      (rxchbondo_out                     ),
      .rxckcaldone_out                    (rxckcaldone_out                   ),
      .rxclkcorcnt_out                    (rxclkcorcnt_out                   ),
      .rxcominitdet_out                   (rxcominitdet_out                  ),
      .rxcommadet_out                     (rxcommadet_out                    ),
      .rxcomsasdet_out                    (rxcomsasdet_out                   ),
      .rxcomwakedet_out                   (rxcomwakedet_out                  ),
      .rxctrl0_out                        (rxctrl0_out                       ),
      .rxctrl1_out                        (rxctrl1_out                       ),
      .rxctrl2_out                        (rxctrl2_out                       ),
      .rxctrl3_out                        (rxctrl3_out                       ),
      .rxdata_out                         (rxdata_out                        ),
      .rxdataextendrsvd_out               (rxdataextendrsvd_out              ),
      .rxdatavalid_out                    (rxdatavalid_out                   ),
      .rxdlysresetdone_out                (rxdlysresetdone_out               ),
      .rxelecidle_out                     (rxelecidle_out                    ),
      .rxheader_out                       (rxheader_out                      ),
      .rxheadervalid_out                  (rxheadervalid_out                 ),
      .rxlfpstresetdet_out                (rxlfpstresetdet_out               ),
      .rxlfpsu2lpexitdet_out              (rxlfpsu2lpexitdet_out             ),
      .rxlfpsu3wakedet_out                (rxlfpsu3wakedet_out               ),
      .rxmonitorout_out                   (rxmonitorout_out                  ),
      .rxosintdone_out                    (rxosintdone_out                   ),
      .rxosintstarted_out                 (rxosintstarted_out                ),
      .rxosintstrobedone_out              (rxosintstrobedone_out             ),
      .rxosintstrobestarted_out           (rxosintstrobestarted_out          ),
      .rxoutclk_out                       (rxoutclk_out                      ),
      .rxoutclkfabric_out                 (rxoutclkfabric_out                ),
      .rxoutclkpcs_out                    (rxoutclkpcs_out                   ),
      .rxphaligndone_out                  (rxphaligndone_out                 ),
      .rxphalignerr_out                   (rxphalignerr_out                  ),
      .rxpmaresetdone_out                 (rxpmaresetdone_out                ),
      .rxprbserr_out                      (rxprbserr_out                     ),
      .rxprbslocked_out                   (rxprbslocked_out                  ),
      .rxprgdivresetdone_out              (rxprgdivresetdone_out             ),
      .rxqpisenn_out                      (rxqpisenn_out                     ),
      .rxqpisenp_out                      (rxqpisenp_out                     ),
      .rxratedone_out                     (rxratedone_out                    ),
      .rxrecclkout_out                    (rxrecclkout_out                   ),
      .rxresetdone_out                    (rxresetdone_out                   ),
      .rxsliderdy_out                     (rxsliderdy_out                    ),
      .rxslipdone_out                     (rxslipdone_out                    ),
      .rxslipoutclkrdy_out                (rxslipoutclkrdy_out               ),
      .rxslippmardy_out                   (rxslippmardy_out                  ),
      .rxstartofseq_out                   (rxstartofseq_out                  ),
      .rxstatus_out                       (rxstatus_out                      ),
      .rxsyncdone_out                     (rxsyncdone_out                    ),
      .rxsyncout_out                      (rxsyncout_out                     ),
      .rxvalid_out                        (rxvalid_out                       ),
      .txbufstatus_out                    (txbufstatus_out                   ),
      .txcomfinish_out                    (txcomfinish_out                   ),
      .txdccdone_out                      (txdccdone_out                     ),
      .txdlysresetdone_out                (txdlysresetdone_out               ),
      .txoutclk_out                       (txoutclk_out                      ),
      .txoutclkfabric_out                 (txoutclkfabric_out                ),
      .txoutclkpcs_out                    (txoutclkpcs_out                   ),
      .txphaligndone_out                  (txphaligndone_out                 ),
      .txphinitdone_out                   (txphinitdone_out                  ),
      .txpmaresetdone_out                 (txpmaresetdone_out                ),
      .txprgdivresetdone_out              (txprgdivresetdone_out             ),
      .txqpisenn_out                      (txqpisenn_out                     ),
      .txqpisenp_out                      (txqpisenp_out                     ),
      .txratedone_out                     (txratedone_out                    ),
      .txresetdone_out                    (txresetdone_out                   ),
      .txsyncdone_out                     (txsyncdone_out                    ),
      .txsyncout_out                      (txsyncout_out                     )
    );

    // Drive unused outputs to constant values
    assign rxrecclk0_sel_out  = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign rxrecclk1_sel_out  = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign ubdaddr_out        = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign ubden_out          = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign ubdi_out           = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign ubdwe_out          = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign ubmdmtdo_out       = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign ubrsvdout_out      = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign ubtxuart_out       = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign gtytxn_out         = {{`xdma_0_pcie4_ip_gt_N_CH}{1'b0}};
    assign gtytxp_out         = {{`xdma_0_pcie4_ip_gt_N_CH}{1'b0}};

  end
  else if (C_GT_TYPE == `xdma_0_pcie4_ip_gt_GT_TYPE__GTYE4) begin : gen_gtwizard_gtye4_top

    // Generate GTYE4-type Transceivers Wizard submodule
    xdma_0_pcie4_ip_gt_gtwizard_gtye4 #(
      .C_CHANNEL_ENABLE                          (C_CHANNEL_ENABLE                         ),
      .C_COMMON_SCALING_FACTOR                   (C_COMMON_SCALING_FACTOR                  ),
      .C_FREERUN_FREQUENCY                       (C_FREERUN_FREQUENCY                      ),
      .C_INCLUDE_CPLL_CAL                        (C_INCLUDE_CPLL_CAL                       ),
      .C_SIM_CPLL_CAL_BYPASS                     (C_SIM_CPLL_CAL_BYPASS                    ),
      .C_LOCATE_RESET_CONTROLLER                 (C_LOCATE_RESET_CONTROLLER                ),
      .C_LOCATE_USER_DATA_WIDTH_SIZING           (C_LOCATE_USER_DATA_WIDTH_SIZING          ),
      .C_LOCATE_RX_BUFFER_BYPASS_CONTROLLER      (C_LOCATE_RX_BUFFER_BYPASS_CONTROLLER     ),
      .C_LOCATE_RX_USER_CLOCKING                 (C_LOCATE_RX_USER_CLOCKING                ),
      .C_LOCATE_TX_BUFFER_BYPASS_CONTROLLER      (C_LOCATE_TX_BUFFER_BYPASS_CONTROLLER     ),
      .C_LOCATE_TX_USER_CLOCKING                 (C_LOCATE_TX_USER_CLOCKING                ),
      .C_RESET_CONTROLLER_INSTANCE_CTRL          (C_RESET_CONTROLLER_INSTANCE_CTRL         ),
      .C_RX_BUFFBYPASS_MODE                      (C_RX_BUFFBYPASS_MODE                     ),
      .C_RX_BUFFER_BYPASS_INSTANCE_CTRL          (C_RX_BUFFER_BYPASS_INSTANCE_CTRL         ),
      .C_RX_BUFFER_MODE                          (C_RX_BUFFER_MODE                         ),
      .C_RX_DATA_DECODING                        (C_RX_DATA_DECODING                       ),
      .C_RX_ENABLE                               (C_RX_ENABLE                              ),
      .C_RX_INT_DATA_WIDTH                       (C_RX_INT_DATA_WIDTH                      ),
      .C_RX_LINE_RATE                            (C_RX_LINE_RATE                           ),
      .C_RX_MASTER_CHANNEL_IDX                   (C_RX_MASTER_CHANNEL_IDX                  ),
      .C_RX_OUTCLK_BUFG_GT_DIV                   (C_RX_OUTCLK_BUFG_GT_DIV                  ),
      .C_RX_PLL_TYPE                             (C_RX_PLL_TYPE                            ),
      .C_RX_USER_CLOCKING_CONTENTS               (C_RX_USER_CLOCKING_CONTENTS              ),
      .C_RX_USER_CLOCKING_INSTANCE_CTRL          (C_RX_USER_CLOCKING_INSTANCE_CTRL         ),
      .C_RX_USER_CLOCKING_RATIO_FUSRCLK_FUSRCLK2 (C_RX_USER_CLOCKING_RATIO_FUSRCLK_FUSRCLK2),
      .C_RX_USER_CLOCKING_SOURCE                 (C_RX_USER_CLOCKING_SOURCE                ),
      .C_RX_USER_DATA_WIDTH                      (C_RX_USER_DATA_WIDTH                     ),
      .C_TOTAL_NUM_CHANNELS                      (C_TOTAL_NUM_CHANNELS                     ),
      .C_TOTAL_NUM_COMMONS                       (C_TOTAL_NUM_COMMONS                      ),
      .C_TX_BUFFBYPASS_MODE                      (C_TX_BUFFBYPASS_MODE                     ),
      .C_TX_BUFFER_BYPASS_INSTANCE_CTRL          (C_TX_BUFFER_BYPASS_INSTANCE_CTRL         ),
      .C_TX_BUFFER_MODE                          (C_TX_BUFFER_MODE                         ),
      .C_TX_DATA_ENCODING                        (C_TX_DATA_ENCODING                       ),
      .C_TX_ENABLE                               (C_TX_ENABLE                              ),
      .C_TX_INT_DATA_WIDTH                       (C_TX_INT_DATA_WIDTH                      ),
      .C_TX_MASTER_CHANNEL_IDX                   (C_TX_MASTER_CHANNEL_IDX                  ),
      .C_TX_OUTCLK_BUFG_GT_DIV                   (C_TX_OUTCLK_BUFG_GT_DIV                  ),
      .C_TX_PLL_TYPE                             (C_TX_PLL_TYPE                            ),
      .C_TX_USER_CLOCKING_CONTENTS               (C_TX_USER_CLOCKING_CONTENTS              ),
      .C_TX_USER_CLOCKING_INSTANCE_CTRL          (C_TX_USER_CLOCKING_INSTANCE_CTRL         ),
      .C_TX_USER_CLOCKING_RATIO_FUSRCLK_FUSRCLK2 (C_TX_USER_CLOCKING_RATIO_FUSRCLK_FUSRCLK2),
      .C_TX_USER_CLOCKING_SOURCE                 (C_TX_USER_CLOCKING_SOURCE                ),
      .C_TX_USER_DATA_WIDTH                      (C_TX_USER_DATA_WIDTH                     )
    ) xdma_0_pcie4_ip_gt_gtwizard_gtye4_inst (
      .gtwiz_userclk_tx_reset_in          (gtwiz_userclk_tx_reset_in         ),
      .gtwiz_userclk_tx_active_in         (gtwiz_userclk_tx_active_in        ),
      .gtwiz_userclk_tx_srcclk_out        (gtwiz_userclk_tx_srcclk_out       ),
      .gtwiz_userclk_tx_usrclk_out        (gtwiz_userclk_tx_usrclk_out       ),
      .gtwiz_userclk_tx_usrclk2_out       (gtwiz_userclk_tx_usrclk2_out      ),
      .gtwiz_userclk_tx_active_out        (gtwiz_userclk_tx_active_out       ),
      .gtwiz_userclk_rx_reset_in          (gtwiz_userclk_rx_reset_in         ),
      .gtwiz_userclk_rx_active_in         (gtwiz_userclk_rx_active_in        ),
      .gtwiz_userclk_rx_srcclk_out        (gtwiz_userclk_rx_srcclk_out       ),
      .gtwiz_userclk_rx_usrclk_out        (gtwiz_userclk_rx_usrclk_out       ),
      .gtwiz_userclk_rx_usrclk2_out       (gtwiz_userclk_rx_usrclk2_out      ),
      .gtwiz_userclk_rx_active_out        (gtwiz_userclk_rx_active_out       ),
      .gtwiz_buffbypass_tx_reset_in       (gtwiz_buffbypass_tx_reset_in      ),
      .gtwiz_buffbypass_tx_start_user_in  (gtwiz_buffbypass_tx_start_user_in ),
      .gtwiz_buffbypass_tx_done_out       (gtwiz_buffbypass_tx_done_out      ),
      .gtwiz_buffbypass_tx_error_out      (gtwiz_buffbypass_tx_error_out     ),
      .gtwiz_buffbypass_rx_reset_in       (gtwiz_buffbypass_rx_reset_in      ),
      .gtwiz_buffbypass_rx_start_user_in  (gtwiz_buffbypass_rx_start_user_in ),
      .gtwiz_buffbypass_rx_done_out       (gtwiz_buffbypass_rx_done_out      ),
      .gtwiz_buffbypass_rx_error_out      (gtwiz_buffbypass_rx_error_out     ),
      .gtwiz_reset_clk_freerun_in         (gtwiz_reset_clk_freerun_in        ),
      .gtwiz_reset_all_in                 (gtwiz_reset_all_in                ),
      .gtwiz_reset_tx_pll_and_datapath_in (gtwiz_reset_tx_pll_and_datapath_in),
      .gtwiz_reset_tx_datapath_in         (gtwiz_reset_tx_datapath_in        ),
      .gtwiz_reset_rx_pll_and_datapath_in (gtwiz_reset_rx_pll_and_datapath_in),
      .gtwiz_reset_rx_datapath_in         (gtwiz_reset_rx_datapath_in        ),
      .gtwiz_reset_tx_done_in             (gtwiz_reset_tx_done_in            ),
      .gtwiz_reset_rx_done_in             (gtwiz_reset_rx_done_in            ),
      .gtwiz_reset_qpll0lock_in           (gtwiz_reset_qpll0lock_in          ),
      .gtwiz_reset_qpll1lock_in           (gtwiz_reset_qpll1lock_in          ),
      .gtwiz_reset_rx_cdr_stable_out      (gtwiz_reset_rx_cdr_stable_out     ),
      .gtwiz_reset_tx_done_out            (gtwiz_reset_tx_done_out           ),
      .gtwiz_reset_rx_done_out            (gtwiz_reset_rx_done_out           ),
      .gtwiz_reset_qpll0reset_out         (gtwiz_reset_qpll0reset_out        ),
      .gtwiz_reset_qpll1reset_out         (gtwiz_reset_qpll1reset_out        ),
      .gtwiz_gtye4_cpll_cal_txoutclk_period_in (gtwiz_gtye4_cpll_cal_txoutclk_period_in),
      .gtwiz_gtye4_cpll_cal_cnt_tol_in         (gtwiz_gtye4_cpll_cal_cnt_tol_in        ),
      .gtwiz_gtye4_cpll_cal_bufg_ce_in         (gtwiz_gtye4_cpll_cal_bufg_ce_in        ),
      .gtwiz_userdata_tx_in               (gtwiz_userdata_tx_in              ),
      .gtwiz_userdata_rx_out              (gtwiz_userdata_rx_out             ),
      .bgbypassb_in                       (bgbypassb_in                      ),
      .bgmonitorenb_in                    (bgmonitorenb_in                   ),
      .bgpdb_in                           (bgpdb_in                          ),
      .bgrcalovrd_in                      (bgrcalovrd_in                     ),
      .bgrcalovrdenb_in                   (bgrcalovrdenb_in                  ),
      .drpaddr_common_in                  (drpaddr_common_in                 ),
      .drpclk_common_in                   (drpclk_common_in                  ),
      .drpdi_common_in                    (drpdi_common_in                   ),
      .drpen_common_in                    (drpen_common_in                   ),
      .drpwe_common_in                    (drpwe_common_in                   ),
      .gtgrefclk0_in                      (gtgrefclk0_in                     ),
      .gtgrefclk1_in                      (gtgrefclk1_in                     ),
      .gtnorthrefclk00_in                 (gtnorthrefclk00_in                ),
      .gtnorthrefclk01_in                 (gtnorthrefclk01_in                ),
      .gtnorthrefclk10_in                 (gtnorthrefclk10_in                ),
      .gtnorthrefclk11_in                 (gtnorthrefclk11_in                ),
      .gtrefclk00_in                      (gtrefclk00_in                     ),
      .gtrefclk01_in                      (gtrefclk01_in                     ),
      .gtrefclk10_in                      (gtrefclk10_in                     ),
      .gtrefclk11_in                      (gtrefclk11_in                     ),
      .gtsouthrefclk00_in                 (gtsouthrefclk00_in                ),
      .gtsouthrefclk01_in                 (gtsouthrefclk01_in                ),
      .gtsouthrefclk10_in                 (gtsouthrefclk10_in                ),
      .gtsouthrefclk11_in                 (gtsouthrefclk11_in                ),
      .pcierateqpll0_in                   (pcierateqpll0_in                  ),
      .pcierateqpll1_in                   (pcierateqpll1_in                  ),
      .pmarsvd0_in                        (pmarsvd0_in                       ),
      .pmarsvd1_in                        (pmarsvd1_in                       ),
      .qpll0clkrsvd0_in                   (qpll0clkrsvd0_in                  ),
      .qpll0clkrsvd1_in                   (qpll0clkrsvd1_in                  ),
      .qpll0fbdiv_in                      (qpll0fbdiv_in                     ),
      .qpll0lockdetclk_in                 (qpll0lockdetclk_in                ),
      .qpll0locken_in                     (qpll0locken_in                    ),
      .qpll0pd_in                         (qpll0pd_in                        ),
      .qpll0refclksel_in                  (qpll0refclksel_in                 ),
      .qpll0reset_in                      (qpll0reset_in                     ),
      .qpll1clkrsvd0_in                   (qpll1clkrsvd0_in                  ),
      .qpll1clkrsvd1_in                   (qpll1clkrsvd1_in                  ),
      .qpll1fbdiv_in                      (qpll1fbdiv_in                     ),
      .qpll1lockdetclk_in                 (qpll1lockdetclk_in                ),
      .qpll1locken_in                     (qpll1locken_in                    ),
      .qpll1pd_in                         (qpll1pd_in                        ),
      .qpll1refclksel_in                  (qpll1refclksel_in                 ),
      .qpll1reset_in                      (qpll1reset_in                     ),
      .qpllrsvd1_in                       (qpllrsvd1_in                      ),
      .qpllrsvd2_in                       (qpllrsvd2_in                      ),
      .qpllrsvd3_in                       (qpllrsvd3_in                      ),
      .qpllrsvd4_in                       (qpllrsvd4_in                      ),
      .rcalenb_in                         (rcalenb_in                        ),
      .sdm0data_in                        (sdm0data_in                       ),
      .sdm0reset_in                       (sdm0reset_in                      ),
      .sdm0toggle_in                      (sdm0toggle_in                     ),
      .sdm0width_in                       (sdm0width_in                      ),
      .sdm1data_in                        (sdm1data_in                       ),
      .sdm1reset_in                       (sdm1reset_in                      ),
      .sdm1toggle_in                      (sdm1toggle_in                     ),
      .sdm1width_in                       (sdm1width_in                      ),
      .ubcfgstreamen_in                   (ubcfgstreamen_in                  ),
      .ubdo_in                            (ubdo_in                           ),
      .ubdrdy_in                          (ubdrdy_in                         ),
      .ubenable_in                        (ubenable_in                       ),
      .ubgpi_in                           (ubgpi_in                          ),
      .ubintr_in                          (ubintr_in                         ),
      .ubiolmbrst_in                      (ubiolmbrst_in                     ),
      .ubmbrst_in                         (ubmbrst_in                        ),
      .ubmdmcapture_in                    (ubmdmcapture_in                   ),
      .ubmdmdbgrst_in                     (ubmdmdbgrst_in                    ),
      .ubmdmdbgupdate_in                  (ubmdmdbgupdate_in                 ),
      .ubmdmregen_in                      (ubmdmregen_in                     ),
      .ubmdmshift_in                      (ubmdmshift_in                     ),
      .ubmdmsysrst_in                     (ubmdmsysrst_in                    ),
      .ubmdmtck_in                        (ubmdmtck_in                       ),
      .ubmdmtdi_in                        (ubmdmtdi_in                       ),
      .drpdo_common_out                   (drpdo_common_out                  ),
      .drprdy_common_out                  (drprdy_common_out                 ),
      .pmarsvdout0_out                    (pmarsvdout0_out                   ),
      .pmarsvdout1_out                    (pmarsvdout1_out                   ),
      .qpll0fbclklost_out                 (qpll0fbclklost_out                ),
      .qpll0lock_out                      (qpll0lock_out                     ),
      .qpll0outclk_out                    (qpll0outclk_out                   ),
      .qpll0outrefclk_out                 (qpll0outrefclk_out                ),
      .qpll0refclklost_out                (qpll0refclklost_out               ),
      .qpll1fbclklost_out                 (qpll1fbclklost_out                ),
      .qpll1lock_out                      (qpll1lock_out                     ),
      .qpll1outclk_out                    (qpll1outclk_out                   ),
      .qpll1outrefclk_out                 (qpll1outrefclk_out                ),
      .qpll1refclklost_out                (qpll1refclklost_out               ),
      .qplldmonitor0_out                  (qplldmonitor0_out                 ),
      .qplldmonitor1_out                  (qplldmonitor1_out                 ),
      .refclkoutmonitor0_out              (refclkoutmonitor0_out             ),
      .refclkoutmonitor1_out              (refclkoutmonitor1_out             ),
      .rxrecclk0sel_out                   (rxrecclk0sel_out                  ),
      .rxrecclk1sel_out                   (rxrecclk1sel_out                  ),
      .sdm0finalout_out                   (sdm0finalout_out                  ),
      .sdm0testdata_out                   (sdm0testdata_out                  ),
      .sdm1finalout_out                   (sdm1finalout_out                  ),
      .sdm1testdata_out                   (sdm1testdata_out                  ),
      .ubdaddr_out                        (ubdaddr_out                       ),
      .ubden_out                          (ubden_out                         ),
      .ubdi_out                           (ubdi_out                          ),
      .ubdwe_out                          (ubdwe_out                         ),
      .ubmdmtdo_out                       (ubmdmtdo_out                      ),
      .ubrsvdout_out                      (ubrsvdout_out                     ),
      .ubtxuart_out                       (ubtxuart_out                      ),
      .cdrstepdir_in                      (cdrstepdir_in                     ),
      .cdrstepsq_in                       (cdrstepsq_in                      ),
      .cdrstepsx_in                       (cdrstepsx_in                      ),
      .cfgreset_in                        (cfgreset_in                       ),
      .clkrsvd0_in                        (clkrsvd0_in                       ),
      .clkrsvd1_in                        (clkrsvd1_in                       ),
      .cpllfreqlock_in                    (cpllfreqlock_in                   ),
      .cplllockdetclk_in                  (cplllockdetclk_in                 ),
      .cplllocken_in                      (cplllocken_in                     ),
      .cpllpd_in                          (cpllpd_in                         ),
      .cpllrefclksel_in                   (cpllrefclksel_in                  ),
      .cpllreset_in                       (cpllreset_in                      ),
      .dmonfiforeset_in                   (dmonfiforeset_in                  ),
      .dmonitorclk_in                     (dmonitorclk_in                    ),
      .drpaddr_in                         (drpaddr_in                        ),
      .drpclk_in                          (drpclk_in                         ),
      .drpdi_in                           (drpdi_in                          ),
      .drpen_in                           (drpen_in                          ),
      .drprst_in                          (drprst_in                         ),
      .drpwe_in                           (drpwe_in                          ),
      .eyescanreset_in                    (eyescanreset_in                   ),
      .eyescantrigger_in                  (eyescantrigger_in                 ),
      .freqos_in                          (freqos_in                         ),
      .gtgrefclk_in                       (gtgrefclk_in                      ),
      .gtnorthrefclk0_in                  (gtnorthrefclk0_in                 ),
      .gtnorthrefclk1_in                  (gtnorthrefclk1_in                 ),
      .gtrefclk0_in                       (gtrefclk0_in                      ),
      .gtrefclk1_in                       (gtrefclk1_in                      ),
      .gtrsvd_in                          (gtrsvd_in                         ),
      .gtrxreset_in                       (gtrxreset_in                      ),
      .gtrxresetsel_in                    (gtrxresetsel_in                   ),
      .gtsouthrefclk0_in                  (gtsouthrefclk0_in                 ),
      .gtsouthrefclk1_in                  (gtsouthrefclk1_in                 ),
      .gttxreset_in                       (gttxreset_in                      ),
      .gttxresetsel_in                    (gttxresetsel_in                   ),
      .incpctrl_in                        (incpctrl_in                       ),
      .gtyrxn_in                          (gtyrxn_in                         ),
      .gtyrxp_in                          (gtyrxp_in                         ),
      .loopback_in                        (loopback_in                       ),
      .pcieeqrxeqadaptdone_in             (pcieeqrxeqadaptdone_in            ),
      .pcierstidle_in                     (pcierstidle_in                    ),
      .pciersttxsyncstart_in              (pciersttxsyncstart_in             ),
      .pcieuserratedone_in                (pcieuserratedone_in               ),
      .pcsrsvdin_in                       (pcsrsvdin_in                      ),
      .qpll0clk_in                        (qpll0clk_in                       ),
      .qpll0freqlock_in                   (qpll0freqlock_in                  ),
      .qpll0refclk_in                     (qpll0refclk_in                    ),
      .qpll1clk_in                        (qpll1clk_in                       ),
      .qpll1freqlock_in                   (qpll1freqlock_in                  ),
      .qpll1refclk_in                     (qpll1refclk_in                    ),
      .resetovrd_in                       (resetovrd_in                      ),
      .rx8b10ben_in                       (rx8b10ben_in                      ),
      .rxafecfoken_in                     (rxafecfoken_in                    ),
      .rxbufreset_in                      (rxbufreset_in                     ),
      .rxcdrfreqreset_in                  (rxcdrfreqreset_in                 ),
      .rxcdrhold_in                       (rxcdrhold_in                      ),
      .rxcdrovrden_in                     (rxcdrovrden_in                    ),
      .rxcdrreset_in                      (rxcdrreset_in                     ),
      .rxchbonden_in                      (rxchbonden_in                     ),
      .rxchbondi_in                       (rxchbondi_in                      ),
      .rxchbondlevel_in                   (rxchbondlevel_in                  ),
      .rxchbondmaster_in                  (rxchbondmaster_in                 ),
      .rxchbondslave_in                   (rxchbondslave_in                  ),
      .rxckcalreset_in                    (rxckcalreset_in                   ),
      .rxckcalstart_in                    (rxckcalstart_in                   ),
      .rxcommadeten_in                    (rxcommadeten_in                   ),
      .rxdfeagchold_in                    (rxdfeagchold_in                   ),
      .rxdfeagcovrden_in                  (rxdfeagcovrden_in                 ),
      .rxdfecfokfcnum_in                  (rxdfecfokfcnum_in                 ),
      .rxdfecfokfen_in                    (rxdfecfokfen_in                   ),
      .rxdfecfokfpulse_in                 (rxdfecfokfpulse_in                ),
      .rxdfecfokhold_in                   (rxdfecfokhold_in                  ),
      .rxdfecfokovren_in                  (rxdfecfokovren_in                 ),
      .rxdfekhhold_in                     (rxdfekhhold_in                    ),
      .rxdfekhovrden_in                   (rxdfekhovrden_in                  ),
      .rxdfelfhold_in                     (rxdfelfhold_in                    ),
      .rxdfelfovrden_in                   (rxdfelfovrden_in                  ),
      .rxdfelpmreset_in                   (rxdfelpmreset_in                  ),
      .rxdfetap10hold_in                  (rxdfetap10hold_in                 ),
      .rxdfetap10ovrden_in                (rxdfetap10ovrden_in               ),
      .rxdfetap11hold_in                  (rxdfetap11hold_in                 ),
      .rxdfetap11ovrden_in                (rxdfetap11ovrden_in               ),
      .rxdfetap12hold_in                  (rxdfetap12hold_in                 ),
      .rxdfetap12ovrden_in                (rxdfetap12ovrden_in               ),
      .rxdfetap13hold_in                  (rxdfetap13hold_in                 ),
      .rxdfetap13ovrden_in                (rxdfetap13ovrden_in               ),
      .rxdfetap14hold_in                  (rxdfetap14hold_in                 ),
      .rxdfetap14ovrden_in                (rxdfetap14ovrden_in               ),
      .rxdfetap15hold_in                  (rxdfetap15hold_in                 ),
      .rxdfetap15ovrden_in                (rxdfetap15ovrden_in               ),
      .rxdfetap2hold_in                   (rxdfetap2hold_in                  ),
      .rxdfetap2ovrden_in                 (rxdfetap2ovrden_in                ),
      .rxdfetap3hold_in                   (rxdfetap3hold_in                  ),
      .rxdfetap3ovrden_in                 (rxdfetap3ovrden_in                ),
      .rxdfetap4hold_in                   (rxdfetap4hold_in                  ),
      .rxdfetap4ovrden_in                 (rxdfetap4ovrden_in                ),
      .rxdfetap5hold_in                   (rxdfetap5hold_in                  ),
      .rxdfetap5ovrden_in                 (rxdfetap5ovrden_in                ),
      .rxdfetap6hold_in                   (rxdfetap6hold_in                  ),
      .rxdfetap6ovrden_in                 (rxdfetap6ovrden_in                ),
      .rxdfetap7hold_in                   (rxdfetap7hold_in                  ),
      .rxdfetap7ovrden_in                 (rxdfetap7ovrden_in                ),
      .rxdfetap8hold_in                   (rxdfetap8hold_in                  ),
      .rxdfetap8ovrden_in                 (rxdfetap8ovrden_in                ),
      .rxdfetap9hold_in                   (rxdfetap9hold_in                  ),
      .rxdfetap9ovrden_in                 (rxdfetap9ovrden_in                ),
      .rxdfeuthold_in                     (rxdfeuthold_in                    ),
      .rxdfeutovrden_in                   (rxdfeutovrden_in                  ),
      .rxdfevphold_in                     (rxdfevphold_in                    ),
      .rxdfevpovrden_in                   (rxdfevpovrden_in                  ),
      .rxdfexyden_in                      (rxdfexyden_in                     ),
      .rxdlybypass_in                     (rxdlybypass_in                    ),
      .rxdlyen_in                         (rxdlyen_in                        ),
      .rxdlyovrden_in                     (rxdlyovrden_in                    ),
      .rxdlysreset_in                     (rxdlysreset_in                    ),
      .rxelecidlemode_in                  (rxelecidlemode_in                 ),
      .rxeqtraining_in                    (rxeqtraining_in                   ),
      .rxgearboxslip_in                   (rxgearboxslip_in                  ),
      .rxlatclk_in                        (rxlatclk_in                       ),
      .rxlpmen_in                         (rxlpmen_in                        ),
      .rxlpmgchold_in                     (rxlpmgchold_in                    ),
      .rxlpmgcovrden_in                   (rxlpmgcovrden_in                  ),
      .rxlpmhfhold_in                     (rxlpmhfhold_in                    ),
      .rxlpmhfovrden_in                   (rxlpmhfovrden_in                  ),
      .rxlpmlfhold_in                     (rxlpmlfhold_in                    ),
      .rxlpmlfklovrden_in                 (rxlpmlfklovrden_in                ),
      .rxlpmoshold_in                     (rxlpmoshold_in                    ),
      .rxlpmosovrden_in                   (rxlpmosovrden_in                  ),
      .rxmcommaalignen_in                 (rxmcommaalignen_in                ),
      .rxmonitorsel_in                    (rxmonitorsel_in                   ),
      .rxoobreset_in                      (rxoobreset_in                     ),
      .rxoscalreset_in                    (rxoscalreset_in                   ),
      .rxoshold_in                        (rxoshold_in                       ),
      .rxosovrden_in                      (rxosovrden_in                     ),
      .rxoutclksel_in                     (rxoutclksel_in                    ),
      .rxpcommaalignen_in                 (rxpcommaalignen_in                ),
      .rxpcsreset_in                      (rxpcsreset_in                     ),
      .rxpd_in                            (rxpd_in                           ),
      .rxphalign_in                       (rxphalign_in                      ),
      .rxphalignen_in                     (rxphalignen_in                    ),
      .rxphdlypd_in                       (rxphdlypd_in                      ),
      .rxphdlyreset_in                    (rxphdlyreset_in                   ),
      .rxpllclksel_in                     (rxpllclksel_in                    ),
      .rxpmareset_in                      (rxpmareset_in                     ),
      .rxpolarity_in                      (rxpolarity_in                     ),
      .rxprbscntreset_in                  (rxprbscntreset_in                 ),
      .rxprbssel_in                       (rxprbssel_in                      ),
      .rxprogdivreset_in                  (rxprogdivreset_in                 ),
      .rxrate_in                          (rxrate_in                         ),
      .rxratemode_in                      (rxratemode_in                     ),
      .rxslide_in                         (rxslide_in                        ),
      .rxslipoutclk_in                    (rxslipoutclk_in                   ),
      .rxslippma_in                       (rxslippma_in                      ),
      .rxsyncallin_in                     (rxsyncallin_in                    ),
      .rxsyncin_in                        (rxsyncin_in                       ),
      .rxsyncmode_in                      (rxsyncmode_in                     ),
      .rxsysclksel_in                     (rxsysclksel_in                    ),
      .rxtermination_in                   (rxtermination_in                  ),
      .rxuserrdy_in                       (rxuserrdy_in                      ),
      .rxusrclk_in                        (rxusrclk_in                       ),
      .rxusrclk2_in                       (rxusrclk2_in                      ),
      .sigvalidclk_in                     (sigvalidclk_in                    ),
      .tstin_in                           (tstin_in                          ),
      .tx8b10bbypass_in                   (tx8b10bbypass_in                  ),
      .tx8b10ben_in                       (tx8b10ben_in                      ),
      .txcominit_in                       (txcominit_in                      ),
      .txcomsas_in                        (txcomsas_in                       ),
      .txcomwake_in                       (txcomwake_in                      ),
      .txctrl0_in                         (txctrl0_in                        ),
      .txctrl1_in                         (txctrl1_in                        ),
      .txctrl2_in                         (txctrl2_in                        ),
      .txdata_in                          (txdata_in                         ),
      .txdataextendrsvd_in                (txdataextendrsvd_in               ),
      .txdccforcestart_in                 (txdccforcestart_in                ),
      .txdccreset_in                      (txdccreset_in                     ),
      .txdeemph_in                        (txdeemph_in                       ),
      .txdetectrx_in                      (txdetectrx_in                     ),
      .txdiffctrl_in                      (txdiffctrl_in                     ),
      .txdlybypass_in                     (txdlybypass_in                    ),
      .txdlyen_in                         (txdlyen_in                        ),
      .txdlyhold_in                       (txdlyhold_in                      ),
      .txdlyovrden_in                     (txdlyovrden_in                    ),
      .txdlysreset_in                     (txdlysreset_in                    ),
      .txdlyupdown_in                     (txdlyupdown_in                    ),
      .txelecidle_in                      (txelecidle_in                     ),
      .txheader_in                        (txheader_in                       ),
      .txinhibit_in                       (txinhibit_in                      ),
      .txlatclk_in                        (txlatclk_in                       ),
      .txlfpstreset_in                    (txlfpstreset_in                   ),
      .txlfpsu2lpexit_in                  (txlfpsu2lpexit_in                 ),
      .txlfpsu3wake_in                    (txlfpsu3wake_in                   ),
      .txmaincursor_in                    (txmaincursor_in                   ),
      .txmargin_in                        (txmargin_in                       ),
      .txmuxdcdexhold_in                  (txmuxdcdexhold_in                 ),
      .txmuxdcdorwren_in                  (txmuxdcdorwren_in                 ),
      .txoneszeros_in                     (txoneszeros_in                    ),
      .txoutclksel_in                     (txoutclksel_in                    ),
      .txpcsreset_in                      (txpcsreset_in                     ),
      .txpd_in                            (txpd_in                           ),
      .txpdelecidlemode_in                (txpdelecidlemode_in               ),
      .txphalign_in                       (txphalign_in                      ),
      .txphalignen_in                     (txphalignen_in                    ),
      .txphdlypd_in                       (txphdlypd_in                      ),
      .txphdlyreset_in                    (txphdlyreset_in                   ),
      .txphdlytstclk_in                   (txphdlytstclk_in                  ),
      .txphinit_in                        (txphinit_in                       ),
      .txphovrden_in                      (txphovrden_in                     ),
      .txpippmen_in                       (txpippmen_in                      ),
      .txpippmovrden_in                   (txpippmovrden_in                  ),
      .txpippmpd_in                       (txpippmpd_in                      ),
      .txpippmsel_in                      (txpippmsel_in                     ),
      .txpippmstepsize_in                 (txpippmstepsize_in                ),
      .txpisopd_in                        (txpisopd_in                       ),
      .txpllclksel_in                     (txpllclksel_in                    ),
      .txpmareset_in                      (txpmareset_in                     ),
      .txpolarity_in                      (txpolarity_in                     ),
      .txpostcursor_in                    (txpostcursor_in                   ),
      .txprbsforceerr_in                  (txprbsforceerr_in                 ),
      .txprbssel_in                       (txprbssel_in                      ),
      .txprecursor_in                     (txprecursor_in                    ),
      .txprogdivreset_in                  (txprogdivreset_in                 ),
      .txrate_in                          (txrate_in                         ),
      .txratemode_in                      (txratemode_in                     ),
      .txsequence_in                      (txsequence_in                     ),
      .txswing_in                         (txswing_in                        ),
      .txsyncallin_in                     (txsyncallin_in                    ),
      .txsyncin_in                        (txsyncin_in                       ),
      .txsyncmode_in                      (txsyncmode_in                     ),
      .txsysclksel_in                     (txsysclksel_in                    ),
      .txuserrdy_in                       (txuserrdy_in                      ),
      .txusrclk_in                        (txusrclk_in                       ),
      .txusrclk2_in                       (txusrclk2_in                      ),
      .bufgtce_out                        (bufgtce_out                       ),
      .bufgtcemask_out                    (bufgtcemask_out                   ),
      .bufgtdiv_out                       (bufgtdiv_out                      ),
      .bufgtreset_out                     (bufgtreset_out                    ),
      .bufgtrstmask_out                   (bufgtrstmask_out                  ),
      .cpllfbclklost_out                  (cpllfbclklost_out                 ),
      .cplllock_out                       (cplllock_out                      ),
      .cpllrefclklost_out                 (cpllrefclklost_out                ),
      .dmonitorout_out                    (dmonitorout_out                   ),
      .dmonitoroutclk_out                 (dmonitoroutclk_out                ),
      .drpdo_out                          (drpdo_out                         ),
      .drprdy_out                         (drprdy_out                        ),
      .eyescandataerror_out               (eyescandataerror_out              ),
      .gtpowergood_out                    (gtpowergood_out                   ),
      .gtrefclkmonitor_out                (gtrefclkmonitor_out               ),
      .gtytxn_out                         (gtytxn_out                        ),
      .gtytxp_out                         (gtytxp_out                        ),
      .pcierategen3_out                   (pcierategen3_out                  ),
      .pcierateidle_out                   (pcierateidle_out                  ),
      .pcierateqpllpd_out                 (pcierateqpllpd_out                ),
      .pcierateqpllreset_out              (pcierateqpllreset_out             ),
      .pciesynctxsyncdone_out             (pciesynctxsyncdone_out            ),
      .pcieusergen3rdy_out                (pcieusergen3rdy_out               ),
      .pcieuserphystatusrst_out           (pcieuserphystatusrst_out          ),
      .pcieuserratestart_out              (pcieuserratestart_out             ),
      .pcsrsvdout_out                     (pcsrsvdout_out                    ),
      .phystatus_out                      (phystatus_out                     ),
      .pinrsrvdas_out                     (pinrsrvdas_out                    ),
      .powerpresent_out                   (powerpresent_out                  ),
      .resetexception_out                 (resetexception_out                ),
      .rxbufstatus_out                    (rxbufstatus_out                   ),
      .rxbyteisaligned_out                (rxbyteisaligned_out               ),
      .rxbyterealign_out                  (rxbyterealign_out                 ),
      .rxcdrlock_out                      (rxcdrlock_out                     ),
      .rxcdrphdone_out                    (rxcdrphdone_out                   ),
      .rxchanbondseq_out                  (rxchanbondseq_out                 ),
      .rxchanisaligned_out                (rxchanisaligned_out               ),
      .rxchanrealign_out                  (rxchanrealign_out                 ),
      .rxchbondo_out                      (rxchbondo_out                     ),
      .rxckcaldone_out                    (rxckcaldone_out                   ),
      .rxclkcorcnt_out                    (rxclkcorcnt_out                   ),
      .rxcominitdet_out                   (rxcominitdet_out                  ),
      .rxcommadet_out                     (rxcommadet_out                    ),
      .rxcomsasdet_out                    (rxcomsasdet_out                   ),
      .rxcomwakedet_out                   (rxcomwakedet_out                  ),
      .rxctrl0_out                        (rxctrl0_out                       ),
      .rxctrl1_out                        (rxctrl1_out                       ),
      .rxctrl2_out                        (rxctrl2_out                       ),
      .rxctrl3_out                        (rxctrl3_out                       ),
      .rxdata_out                         (rxdata_out                        ),
      .rxdataextendrsvd_out               (rxdataextendrsvd_out              ),
      .rxdatavalid_out                    (rxdatavalid_out                   ),
      .rxdlysresetdone_out                (rxdlysresetdone_out               ),
      .rxelecidle_out                     (rxelecidle_out                    ),
      .rxheader_out                       (rxheader_out                      ),
      .rxheadervalid_out                  (rxheadervalid_out                 ),
      .rxlfpstresetdet_out                (rxlfpstresetdet_out               ),
      .rxlfpsu2lpexitdet_out              (rxlfpsu2lpexitdet_out             ),
      .rxlfpsu3wakedet_out                (rxlfpsu3wakedet_out               ),
      .rxmonitorout_out                   (rxmonitorout_out                  ),
      .rxosintdone_out                    (rxosintdone_out                   ),
      .rxosintstarted_out                 (rxosintstarted_out                ),
      .rxosintstrobedone_out              (rxosintstrobedone_out             ),
      .rxosintstrobestarted_out           (rxosintstrobestarted_out          ),
      .rxoutclk_out                       (rxoutclk_out                      ),
      .rxoutclkfabric_out                 (rxoutclkfabric_out                ),
      .rxoutclkpcs_out                    (rxoutclkpcs_out                   ),
      .rxphaligndone_out                  (rxphaligndone_out                 ),
      .rxphalignerr_out                   (rxphalignerr_out                  ),
      .rxpmaresetdone_out                 (rxpmaresetdone_out                ),
      .rxprbserr_out                      (rxprbserr_out                     ),
      .rxprbslocked_out                   (rxprbslocked_out                  ),
      .rxprgdivresetdone_out              (rxprgdivresetdone_out             ),
      .rxratedone_out                     (rxratedone_out                    ),
      .rxrecclkout_out                    (rxrecclkout_out                   ),
      .rxresetdone_out                    (rxresetdone_out                   ),
      .rxsliderdy_out                     (rxsliderdy_out                    ),
      .rxslipdone_out                     (rxslipdone_out                    ),
      .rxslipoutclkrdy_out                (rxslipoutclkrdy_out               ),
      .rxslippmardy_out                   (rxslippmardy_out                  ),
      .rxstartofseq_out                   (rxstartofseq_out                  ),
      .rxstatus_out                       (rxstatus_out                      ),
      .rxsyncdone_out                     (rxsyncdone_out                    ),
      .rxsyncout_out                      (rxsyncout_out                     ),
      .rxvalid_out                        (rxvalid_out                       ),
      .txbufstatus_out                    (txbufstatus_out                   ),
      .txcomfinish_out                    (txcomfinish_out                   ),
      .txdccdone_out                      (txdccdone_out                     ),
      .txdlysresetdone_out                (txdlysresetdone_out               ),
      .txoutclk_out                       (txoutclk_out                      ),
      .txoutclkfabric_out                 (txoutclkfabric_out                ),
      .txoutclkpcs_out                    (txoutclkpcs_out                   ),
      .txphaligndone_out                  (txphaligndone_out                 ),
      .txphinitdone_out                   (txphinitdone_out                  ),
      .txpmaresetdone_out                 (txpmaresetdone_out                ),
      .txprgdivresetdone_out              (txprgdivresetdone_out             ),
      .txratedone_out                     (txratedone_out                    ),
      .txresetdone_out                    (txresetdone_out                   ),
      .txsyncdone_out                     (txsyncdone_out                    ),
      .txsyncout_out                      (txsyncout_out                     )
    );

    // Drive unused outputs to constant values
    assign rxrecclk0_sel_out = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign rxrecclk1_sel_out = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign tcongpo_out       = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign tconrsvdout0_out  = {{`xdma_0_pcie4_ip_gt_SF_CM}{1'b0}};
    assign gthtxn_out        = {{`xdma_0_pcie4_ip_gt_N_CH}{1'b0}};
    assign gthtxp_out        = {{`xdma_0_pcie4_ip_gt_N_CH}{1'b0}};
    assign rxqpisenn_out     = {{`xdma_0_pcie4_ip_gt_N_CH}{1'b0}};
    assign rxqpisenp_out     = {{`xdma_0_pcie4_ip_gt_N_CH}{1'b0}};
    assign txqpisenn_out     = {{`xdma_0_pcie4_ip_gt_N_CH}{1'b0}};
    assign txqpisenp_out     = {{`xdma_0_pcie4_ip_gt_N_CH}{1'b0}};

  end
  endgenerate


endmodule

