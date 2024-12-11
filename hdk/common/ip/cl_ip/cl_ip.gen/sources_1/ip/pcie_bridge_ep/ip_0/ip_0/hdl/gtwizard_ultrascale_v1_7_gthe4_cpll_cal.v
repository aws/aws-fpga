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

module gtwizard_ultrascale_v1_7_18_gthe4_cpll_cal # (
  parameter integer C_RX_PLL_TYPE = 0,
  parameter integer C_TX_PLL_TYPE = 0,
  parameter C_SIM_CPLL_CAL_BYPASS = 1'b1,
  parameter SIM_RESET_SPEEDUP     = "TRUE",
  parameter C_FREERUN_FREQUENCY   = 100, 
  parameter REVISION              = 2,
  parameter C_PCIE_ENABLE         = "FALSE",
  parameter C_PCIE_CORECLK_FREQ   = 250
)(
  // control signals
  input   wire  [17:0]  TXOUTCLK_PERIOD_IN,
  input   wire  [17:0]  CNT_TOL_IN,
  input   wire  [15:0]  FREQ_COUNT_WINDOW_IN,
  // User Interface
  input   wire          RESET_IN,
  input   wire          CLK_IN,
  input   wire          DRPRST_IN,
  input   wire  [1:0]   USER_TXPLLCLKSEL,
  input   wire  [1:0]   USER_RXPLLCLKSEL,
  input   wire          USER_RXPROGDIVRESET_IN,
  output  wire          USER_RXPRGDIVRESETDONE_OUT,
  output  wire          USER_RXPMARESETDONE_OUT,
  input   wire  [2:0]   USER_RXOUTCLKSEL_IN,
  input   wire          USER_RXOUTCLK_BUFG_CE_IN,
  input   wire          USER_RXOUTCLK_BUFG_CLR_IN,
  input   wire          USER_GTRXRESET_IN,
  input   wire          USER_RXCDRHOLD_IN,
  input   wire          USER_RXPMARESET_IN,
  input   wire          USER_TXPROGDIVRESET_IN,
  output  wire          USER_TXPRGDIVRESETDONE_OUT,
  input   wire  [2:0]   USER_TXOUTCLKSEL_IN,
  input   wire          USER_TXOUTCLK_BUFG_CE_IN,
  input   wire          USER_TXOUTCLK_BUFG_CLR_IN,
  output  wire          USER_CPLLLOCK_OUT,
  input   wire  [9:0]   USER_CHANNEL_DRPADDR_IN,
  input   wire  [15:0]  USER_CHANNEL_DRPDI_IN,
  input   wire          USER_CHANNEL_DRPEN_IN,
  input   wire          USER_CHANNEL_DRPWE_IN,
  output  wire          USER_CHANNEL_DRPRDY_OUT,
  output  wire  [15:0]  USER_CHANNEL_DRPDO_OUT,
  // Debug Interface
  output  wire          CPLL_CAL_FAIL,
  output  wire          CPLL_CAL_DONE,
  output  wire  [15:0]  DEBUG_OUT,
  output  wire  [17:0]  CAL_FREQ_CNT,
  input         [3:0]   REPEAT_RESET_LIMIT,
  // GT Interface
  input   wire          GTHE4_TXOUTCLK_IN,
  input   wire          GTHE4_RXOUTCLK_IN,
  input   wire          GTHE4_CPLLLOCK_IN,
  output  wire          GTHE4_CPLLRESET_OUT,
  output  wire          GTHE4_RXCDRHOLD_OUT,
  output  wire          GTHE4_GTRXRESET_OUT,
  output  wire          GTHE4_RXPMARESET_OUT,
  output  wire          GTHE4_RXPROGDIVRESET_OUT,
  output  wire  [2:0]   GTHE4_RXOUTCLKSEL_OUT,
  input   wire          GTHE4_RXPRGDIVRESETDONE_IN,
  input   wire          GTHE4_RXPMARESETDONE_IN,
  output  wire          GTHE4_CPLLPD_OUT,
  output  wire          GTHE4_TXPROGDIVRESET_OUT,
  output  wire  [2:0]   GTHE4_TXOUTCLKSEL_OUT,
  input   wire          GTHE4_TXPRGDIVRESETDONE_IN,
  output  wire  [9:0]   GTHE4_CHANNEL_DRPADDR_OUT,
  output  wire  [15:0]  GTHE4_CHANNEL_DRPDI_OUT,
  output  wire          GTHE4_CHANNEL_DRPEN_OUT,
  output  wire          GTHE4_CHANNEL_DRPWE_OUT,
  input   wire          GTHE4_CHANNEL_DRPRDY_IN,
  input   wire  [15:0]  GTHE4_CHANNEL_DRPDO_IN
);

  wire rx_done;
  wire tx_done; 
  
  wire cal_on_rx_cal_fail;
  wire cal_on_rx_cal_done; 
  wire [15:0] cal_on_rx_debug_out; 
  wire [17:0] cal_on_rx_cal_freq_cnt;
  wire cal_on_rx_cpllreset_out;
  wire cal_on_rx_cpllpd_out;
  wire cal_on_rx_cplllock_out;
  
  wire cal_on_rx_drpen_out;
  wire cal_on_rx_drpwe_out;
  wire [9:0] cal_on_rx_drpaddr_out;
  wire [15:0] cal_on_rx_drpdi_out;
  wire [15:0] cal_on_rx_dout;
  wire cal_on_rx_drdy;

  wire cal_on_tx_cal_fail;
  wire cal_on_tx_cal_done; 
  wire [15:0] cal_on_tx_debug_out; 
  wire [17:0] cal_on_tx_cal_freq_cnt;
  wire cal_on_tx_cpllreset_out;
  wire cal_on_tx_cpllpd_out;
  wire cal_on_tx_cplllock_out;
  
  wire cal_on_tx_drpen_out;
  wire cal_on_tx_drpwe_out;
  wire [9:0] cal_on_tx_drpaddr_out;
  wire [15:0] cal_on_tx_drpdi_out;
  wire [15:0] cal_on_tx_dout;
  wire cal_on_tx_drdy;  
  
  localparam [9:0]  ADDR_TX_PROGCLK_SEL = 10'h00C;
  localparam [9:0]  ADDR_TX_PROGDIV_CFG = 10'h03E;  // GTH /GTY addresses are different (003E in GTH; 0057 in GTY)
  localparam [9:0]  ADDR_RX_PROGDIV_CFG = 10'h0C6;
  localparam [9:0]  ADDR_X0E1 = 10'h0E1;
  localparam [9:0]  ADDR_X079 = 10'h079;
  localparam [9:0]  ADDR_X114 = 10'h114; 
  localparam CPLL_CAL_ONLY_TX = (C_RX_PLL_TYPE == C_TX_PLL_TYPE); // If top level configuration of TX and RX PLL TYPE are same, don't use RX Cal block

  wire cpll_cal_on_tx_or_rx;  //1: RX cal block, 0: TX cal block;
  assign cpll_cal_on_tx_or_rx = CPLL_CAL_ONLY_TX ? 1'b0 : ((USER_TXPLLCLKSEL != 2'b00 && USER_RXPLLCLKSEL == 2'b00) ? 1'b1 : 1'b0); 
  
  // TX reset version
  wire cal_on_tx_reset_in; 
  assign cal_on_tx_reset_in = RESET_IN | cpll_cal_on_tx_or_rx;
  
  wire cal_on_tx_reset_in_sync;
  gtwizard_ultrascale_v1_7_18_reset_synchronizer reset_synchronizer_resetin_tx_inst (
    .clk_in   (CLK_IN),
    .rst_in   (cal_on_tx_reset_in),
    .rst_out  (cal_on_tx_reset_in_sync)
  );
  
  // RX reset version
  wire cal_on_rx_reset_in; 
  assign cal_on_rx_reset_in = RESET_IN | !cpll_cal_on_tx_or_rx;  
  
  wire cal_on_rx_reset_in_sync;
  gtwizard_ultrascale_v1_7_18_reset_synchronizer reset_synchronizer_resetin_rx_inst (
    .clk_in   (CLK_IN),
    .rst_in   (cal_on_rx_reset_in),
    .rst_out  (cal_on_rx_reset_in_sync)
  );

  wire drprst_in_sync;
  gtwizard_ultrascale_v1_7_18_bit_synchronizer bit_synchronizer_drprst_inst (
    .clk_in (CLK_IN),
    .i_in   (DRPRST_IN),
    .o_out  (drprst_in_sync)
  );

  gtwizard_ultrascale_v1_7_18_gthe4_cpll_cal_tx #
  (
    .C_SIM_CPLL_CAL_BYPASS(C_SIM_CPLL_CAL_BYPASS),
    .SIM_RESET_SPEEDUP(SIM_RESET_SPEEDUP),
    .C_FREERUN_FREQUENCY(C_FREERUN_FREQUENCY),
    .C_PCIE_ENABLE(C_PCIE_ENABLE),
    .C_PCIE_CORECLK_FREQ(C_PCIE_CORECLK_FREQ)
  ) gtwizard_ultrascale_v1_7_18_gthe4_cpll_cal_tx_i
  (
    // control signals
    .TXOUTCLK_PERIOD_IN(TXOUTCLK_PERIOD_IN),
    .CNT_TOL_IN(CNT_TOL_IN),
    .FREQ_COUNT_WINDOW_IN(FREQ_COUNT_WINDOW_IN),
    // User Interface
    .RESET_IN(cal_on_tx_reset_in_sync),
    .CLK_IN(CLK_IN),
    .USER_TXPLLCLKSEL(USER_TXPLLCLKSEL),
    .USER_TXPROGDIVRESET_IN(USER_TXPROGDIVRESET_IN),
    .USER_TXPRGDIVRESETDONE_OUT(USER_TXPRGDIVRESETDONE_OUT),
    .USER_TXOUTCLKSEL_IN(USER_TXOUTCLKSEL_IN),
    .USER_TXOUTCLK_BUFG_CE_IN(USER_TXOUTCLK_BUFG_CE_IN),
    .USER_TXOUTCLK_BUFG_CLR_IN(USER_TXOUTCLK_BUFG_CLR_IN),
    .USER_CPLLLOCK_OUT(cal_on_tx_cplllock_out),
    // Debug Interface
    .CPLL_CAL_FAIL(cal_on_tx_cal_fail),
    .CPLL_CAL_DONE(cal_on_tx_cal_done),
    .DEBUG_OUT(cal_on_tx_debug_out),
    .CAL_FREQ_CNT(cal_on_tx_cal_freq_cnt),
    .REPEAT_RESET_LIMIT(REPEAT_RESET_LIMIT),
    // GT Interface
    .GTHE4_TXOUTCLK_IN(GTHE4_TXOUTCLK_IN),
    .GTHE4_CPLLLOCK_IN(GTHE4_CPLLLOCK_IN),
    .GTHE4_CPLLRESET_OUT(cal_on_tx_cpllreset_out),
    .GTHE4_CPLLPD_OUT(cal_on_tx_cpllpd_out),
    .GTHE4_TXPROGDIVRESET_OUT(GTHE4_TXPROGDIVRESET_OUT),
    .GTHE4_TXOUTCLKSEL_OUT(GTHE4_TXOUTCLKSEL_OUT),
    .GTHE4_TXPRGDIVRESETDONE_IN(GTHE4_TXPRGDIVRESETDONE_IN),
    .GTHE4_CHANNEL_DRPADDR_OUT(cal_on_tx_drpaddr_out),
    .GTHE4_CHANNEL_DRPDI_OUT(cal_on_tx_drpdi_out),
    .GTHE4_CHANNEL_DRPEN_OUT(cal_on_tx_drpen_out),
    .GTHE4_CHANNEL_DRPWE_OUT(cal_on_tx_drpwe_out),
    .GTHE4_CHANNEL_DRPRDY_IN(cal_on_tx_drdy),
    .GTHE4_CHANNEL_DRPDO_IN(cal_on_tx_dout),
    .DONE(tx_done)
  );  
  
  gtwizard_ultrascale_v1_7_18_gthe4_cpll_cal_rx #
  (
    .C_SIM_CPLL_CAL_BYPASS(C_SIM_CPLL_CAL_BYPASS),
    .SIM_RESET_SPEEDUP(SIM_RESET_SPEEDUP),
    .CPLL_CAL_ONLY_TX(CPLL_CAL_ONLY_TX),
    .C_FREERUN_FREQUENCY(C_FREERUN_FREQUENCY)
  ) gtwizard_ultrascale_v1_7_18_gthe4_cpll_cal_rx_i
  (
    // control signals
    .RXOUTCLK_PERIOD_IN(TXOUTCLK_PERIOD_IN),
    .CNT_TOL_IN(CNT_TOL_IN),
    .FREQ_COUNT_WINDOW_IN(FREQ_COUNT_WINDOW_IN),
    // User Interface
    .RESET_IN(cal_on_rx_reset_in_sync),
    .CLK_IN(CLK_IN),
    .USER_RXPROGDIVRESET_IN(USER_RXPROGDIVRESET_IN),
    .USER_RXPRGDIVRESETDONE_OUT(USER_RXPRGDIVRESETDONE_OUT),
    .USER_RXPMARESETDONE_OUT(USER_RXPMARESETDONE_OUT),
    .USER_RXOUTCLKSEL_IN(USER_RXOUTCLKSEL_IN),
    .USER_RXOUTCLK_BUFG_CE_IN(USER_RXOUTCLK_BUFG_CE_IN),
    .USER_RXOUTCLK_BUFG_CLR_IN(USER_RXOUTCLK_BUFG_CLR_IN),
    .USER_CPLLLOCK_OUT(cal_on_rx_cplllock_out),
    .USER_RXCDRHOLD_IN(USER_RXCDRHOLD_IN),
    .USER_GTRXRESET_IN(USER_GTRXRESET_IN),
    .USER_RXPMARESET_IN(USER_RXPMARESET_IN),
    // Debug Interface
    .CPLL_CAL_FAIL(cal_on_rx_cal_fail),
    .CPLL_CAL_DONE(cal_on_rx_cal_done),
    .DEBUG_OUT(cal_on_rx_debug_out),
    .CAL_FREQ_CNT(cal_on_rx_cal_freq_cnt),
    .REPEAT_RESET_LIMIT(REPEAT_RESET_LIMIT),
    // GT Interface
    .GTHE4_RXOUTCLK_IN(GTHE4_RXOUTCLK_IN),
    .GTHE4_CPLLLOCK_IN(GTHE4_CPLLLOCK_IN),
    .GTHE4_CPLLRESET_OUT(cal_on_rx_cpllreset_out),
    .GTHE4_CPLLPD_OUT(cal_on_rx_cpllpd_out),
    .GTHE4_RXPROGDIVRESET_OUT(GTHE4_RXPROGDIVRESET_OUT),
    .GTHE4_RXOUTCLKSEL_OUT(GTHE4_RXOUTCLKSEL_OUT),
    .GTHE4_RXPRGDIVRESETDONE_IN(GTHE4_RXPRGDIVRESETDONE_IN),
    .GTHE4_CHANNEL_DRPADDR_OUT(cal_on_rx_drpaddr_out),
    .GTHE4_CHANNEL_DRPDI_OUT(cal_on_rx_drpdi_out),
    .GTHE4_CHANNEL_DRPEN_OUT(cal_on_rx_drpen_out),
    .GTHE4_CHANNEL_DRPWE_OUT(cal_on_rx_drpwe_out),
    .GTHE4_CHANNEL_DRPRDY_IN(cal_on_rx_drdy),
    .GTHE4_CHANNEL_DRPDO_IN(cal_on_rx_dout),
    .GTHE4_GTRXRESET_OUT(GTHE4_GTRXRESET_OUT),
    .GTHE4_RXPMARESET_OUT(GTHE4_RXPMARESET_OUT),
    .GTHE4_RXCDRHOLD_OUT(GTHE4_RXCDRHOLD_OUT),
    .GTHE4_RXPMARESETDONE_IN(GTHE4_RXPMARESETDONE_IN),
    .DONE(rx_done)
  );
  
  //OR with TX versions
  assign GTHE4_CPLLRESET_OUT = cal_on_rx_cpllreset_out | cal_on_tx_cpllreset_out; 
  assign GTHE4_CPLLPD_OUT = cal_on_rx_cpllpd_out | cal_on_tx_cpllpd_out;
  assign USER_CPLLLOCK_OUT = cal_on_rx_cplllock_out | cal_on_tx_cplllock_out;

  //Mux the debug signals out
  assign CPLL_CAL_DONE = cpll_cal_on_tx_or_rx ? cal_on_rx_cal_done : cal_on_tx_cal_done;
  assign CPLL_CAL_FAIL = cpll_cal_on_tx_or_rx ? cal_on_rx_cal_fail : cal_on_tx_cal_fail;
  assign DEBUG_OUT = cpll_cal_on_tx_or_rx ? cal_on_rx_debug_out : cal_on_tx_debug_out;
  assign CAL_FREQ_CNT = cpll_cal_on_tx_or_rx ? cal_on_rx_cal_freq_cnt : cal_on_tx_cal_freq_cnt;
  
  //----------------------------------------------------------------------------------------------
  // DRP ARBITER
  //----------------------------------------------------------------------------------------------
  
  gtwizard_ultrascale_v1_7_18_gte4_drp_arb #
  (
    .ADDR_TX_PROGCLK_SEL(ADDR_TX_PROGCLK_SEL),
    .ADDR_TX_PROGDIV_CFG(ADDR_TX_PROGDIV_CFG),
    .ADDR_RX_PROGDIV_CFG(ADDR_RX_PROGDIV_CFG),
    .ADDR_X0E1(ADDR_X0E1),
    .ADDR_X079(ADDR_X079),
    .ADDR_X114(ADDR_X114),
    .C_NUM_CLIENTS(3),
    .C_ADDR_WIDTH(10),
    .C_DATA_WIDTH(16)
  ) gtwizard_ultrascale_v1_7_18_gte4_drp_arb_i
  (
    .DCLK_I         (CLK_IN),
    .RESET_I        (drprst_in_sync),
    .DEN_USR_I      ({cal_on_tx_drpen_out, cal_on_rx_drpen_out, USER_CHANNEL_DRPEN_IN}),
    .DWE_USR_I      ({cal_on_tx_drpwe_out, cal_on_rx_drpwe_out, USER_CHANNEL_DRPWE_IN}),
    .DADDR_USR_I    ({cal_on_tx_drpaddr_out, cal_on_rx_drpaddr_out, USER_CHANNEL_DRPADDR_IN}),
    .DI_USR_I       ({cal_on_tx_drpdi_out, cal_on_rx_drpdi_out, USER_CHANNEL_DRPDI_IN}),
    .DO_USR_O       ({cal_on_tx_dout, cal_on_rx_dout, USER_CHANNEL_DRPDO_OUT}),
    .DRDY_USR_O     ({cal_on_tx_drdy, cal_on_rx_drdy, USER_CHANNEL_DRPRDY_OUT}),
    // arbitrated port
    .DEN_O          (GTHE4_CHANNEL_DRPEN_OUT),
    .DWE_O          (GTHE4_CHANNEL_DRPWE_OUT),
    .DADDR_O        (GTHE4_CHANNEL_DRPADDR_OUT),
    .DI_O           (GTHE4_CHANNEL_DRPDI_OUT),
    .DO_I           (GTHE4_CHANNEL_DRPDO_IN),
    .DRDY_I         (GTHE4_CHANNEL_DRPRDY_IN),
    .TX_CAL_DONE_I  (tx_done),
    .RX_CAL_DONE_I  (rx_done)
  );

endmodule //CPLL_CAL


