// (c) Copyright 1995-2016 Xilinx, Inc. All rights reserved.
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
// DO NOT MODIFY THIS FILE.


// IP VLNV: xilinx.com:ip:gtwizard_ultrascale:1.6
// IP Revision: 5

(* X_CORE_INFO = "xdma_0_pcie4_ip_gt_gtwizard_top,Vivado 2016.3_AR68069" *)
(* CHECK_LICENSE_TYPE = "xdma_0_pcie4_ip_gt,xdma_0_pcie4_ip_gt_gtwizard_top,{}" *)
(* CORE_GENERATION_INFO = "xdma_0_pcie4_ip_gt,xdma_0_pcie4_ip_gt_gtwizard_top,{x_ipProduct=Vivado 2016.3_AR68069,x_ipVendor=xilinx.com,x_ipLibrary=ip,x_ipName=gtwizard_ultrascale,x_ipVersion=1.6,x_ipCoreRevision=5,x_ipLanguage=VERILOG,x_ipSimLanguage=MIXED,C_CHANNEL_ENABLE=000000000000000000000000000000000000000000000000000000000000111111111111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,C_COMMON_SCALING_FACTOR=4,C_CPLL_VCO_FREQUENCY=2500.0,C_FORC\
E_COMMONS=0,C_FREERUN_FREQUENCY=100,C_GT_TYPE=3,C_GT_REV=61,C_INCLUDE_CPLL_CAL=1,C_SIM_CPLL_CAL_BYPASS=1,C_LOCATE_COMMON=0,C_LOCATE_RESET_CONTROLLER=1,C_LOCATE_USER_DATA_WIDTH_SIZING=1,C_LOCATE_RX_BUFFER_BYPASS_CONTROLLER=0,C_LOCATE_IN_SYSTEM_IBERT_CORE=2,C_LOCATE_RX_USER_CLOCKING=1,C_LOCATE_TX_BUFFER_BYPASS_CONTROLLER=1,C_LOCATE_TX_USER_CLOCKING=1,C_RESET_CONTROLLER_INSTANCE_CTRL=0,C_RX_BUFFBYPASS_MODE=0,C_RX_BUFFER_BYPASS_INSTANCE_CTRL=0,C_RX_BUFFER_MODE=1,C_RX_CB_DISP=00000000,C_RX_CB_K=00000\
000,C_RX_CB_MAX_LEVEL=5,C_RX_CB_LEN_SEQ=1,C_RX_CB_NUM_SEQ=0,C_RX_CB_VAL=00000000000000000000000000000000000000000000000000000000000000000000000000000000,C_RX_CC_DISP=00000000,C_RX_CC_ENABLE=1,C_RESET_SEQUENCE_INTERVAL=0,C_RX_CC_K=00000001,C_RX_CC_LEN_SEQ=1,C_RX_CC_NUM_SEQ=1,C_RX_CC_PERIODICITY=5000,C_RX_CC_VAL=00000000000000000000000000000000000000000000000000000000000000000000000000011100,C_RX_COMMA_M_ENABLE=1,C_RX_COMMA_M_VAL=1010000011,C_RX_COMMA_P_ENABLE=1,C_RX_COMMA_P_VAL=0101111100,C_RX_DA\
TA_DECODING=1,C_RX_ENABLE=1,C_RX_INT_DATA_WIDTH=20,C_RX_LINE_RATE=8,C_RX_MASTER_CHANNEL_IDX=131,C_RX_OUTCLK_BUFG_GT_DIV=1,C_RX_OUTCLK_FREQUENCY=400.0000000,C_RX_OUTCLK_SOURCE=1,C_RX_PLL_TYPE=1,C_RX_RECCLK_OUTPUT=0x000000000000000000000000000000000000000000000000,C_RX_REFCLK_FREQUENCY=100,C_RX_SLIDE_MODE=2,C_RX_USER_CLOCKING_CONTENTS=0,C_RX_USER_CLOCKING_INSTANCE_CTRL=0,C_RX_USER_CLOCKING_RATIO_FSRC_FUSRCLK=1,C_RX_USER_CLOCKING_RATIO_FUSRCLK_FUSRCLK2=1,C_RX_USER_CLOCKING_SOURCE=0,C_RX_USER_DATA_W\
IDTH=16,C_RX_USRCLK_FREQUENCY=400.0000000,C_RX_USRCLK2_FREQUENCY=400.0000000,C_SECONDARY_QPLL_ENABLE=0,C_SECONDARY_QPLL_REFCLK_FREQUENCY=257.8125,C_TOTAL_NUM_CHANNELS=16,C_TOTAL_NUM_COMMONS=4,C_TOTAL_NUM_COMMONS_EXAMPLE=0,C_TXPROGDIV_FREQ_ENABLE=0,C_TXPROGDIV_FREQ_SOURCE=1,C_TXPROGDIV_FREQ_VAL=400,C_TX_BUFFBYPASS_MODE=0,C_TX_BUFFER_BYPASS_INSTANCE_CTRL=0,C_TX_BUFFER_MODE=0,C_TX_DATA_ENCODING=1,C_TX_ENABLE=1,C_TX_INT_DATA_WIDTH=20,C_TX_LINE_RATE=8,C_TX_MASTER_CHANNEL_IDX=131,C_TX_OUTCLK_BUFG_GT_D\
IV=1,C_TX_OUTCLK_FREQUENCY=400.0000000,C_TX_OUTCLK_SOURCE=4,C_TX_PLL_TYPE=1,C_TX_REFCLK_FREQUENCY=100,C_TX_USER_CLOCKING_CONTENTS=0,C_TX_USER_CLOCKING_INSTANCE_CTRL=0,C_TX_USER_CLOCKING_RATIO_FSRC_FUSRCLK=1,C_TX_USER_CLOCKING_RATIO_FUSRCLK_FUSRCLK2=1,C_TX_USER_CLOCKING_SOURCE=0,C_TX_USER_DATA_WIDTH=16,C_TX_USRCLK_FREQUENCY=400.0000000,C_TX_USRCLK2_FREQUENCY=400.0000000}" *)
(* DowngradeIPIdentifiedWarnings = "yes" *)
module xdma_0_pcie4_ip_gt (
  gtwiz_userclk_tx_reset_in,
  gtwiz_userclk_tx_active_in,
  gtwiz_userclk_rx_active_in,
  gtwiz_reset_tx_done_in,
  gtwiz_reset_rx_done_in,
  gtwiz_gtye4_cpll_cal_txoutclk_period_in,
  gtwiz_gtye4_cpll_cal_cnt_tol_in,
  gtwiz_gtye4_cpll_cal_bufg_ce_in,
  drpaddr_common_in,
  drpclk_common_in,
  drpdi_common_in,
  drpen_common_in,
  drpwe_common_in,
  gtrefclk00_in,
  gtrefclk01_in,
  pcierateqpll0_in,
  pcierateqpll1_in,
  qpll0pd_in,
  qpll0reset_in,
  qpll1pd_in,
  qpll1reset_in,
  drpdo_common_out,
  drprdy_common_out,
  qpll0lock_out,
  qpll0outclk_out,
  qpll0outrefclk_out,
  qpll1lock_out,
  qpll1outclk_out,
  qpll1outrefclk_out,
  cpllfreqlock_in,
  cpllpd_in,
  cpllreset_in,
  dmonfiforeset_in,
  dmonitorclk_in,
  drpaddr_in,
  drpclk_in,
  drpdi_in,
  drpen_in,
  drpwe_in,
  eyescanreset_in,
  gtrefclk0_in,
  gtrxreset_in,
  gttxreset_in,
  gtyrxn_in,
  gtyrxp_in,
  loopback_in,
  pcieeqrxeqadaptdone_in,
  pcierstidle_in,
  pciersttxsyncstart_in,
  pcieuserratedone_in,
  qpll0freqlock_in,
  qpll1freqlock_in,
  resetovrd_in,
  rx8b10ben_in,
  rxbufreset_in,
  rxcdrfreqreset_in,
  rxcdrhold_in,
  rxcdrreset_in,
  rxcommadeten_in,
  rxdfeagchold_in,
  rxdfecfokhold_in,
  rxdfekhhold_in,
  rxdfelfhold_in,
  rxdfelpmreset_in,
  rxdfetap10hold_in,
  rxdfetap11hold_in,
  rxdfetap12hold_in,
  rxdfetap13hold_in,
  rxdfetap14hold_in,
  rxdfetap15hold_in,
  rxdfetap2hold_in,
  rxdfetap3hold_in,
  rxdfetap4hold_in,
  rxdfetap5hold_in,
  rxdfetap6hold_in,
  rxdfetap7hold_in,
  rxdfetap8hold_in,
  rxdfetap9hold_in,
  rxdfeuthold_in,
  rxdfevphold_in,
  rxlpmen_in,
  rxlpmgchold_in,
  rxlpmhfhold_in,
  rxlpmlfhold_in,
  rxlpmoshold_in,
  rxmcommaalignen_in,
  rxoshold_in,
  rxpcommaalignen_in,
  rxpcsreset_in,
  rxpd_in,
  rxpmareset_in,
  rxpolarity_in,
  rxprbscntreset_in,
  rxprbssel_in,
  rxprogdivreset_in,
  rxrate_in,
  rxratemode_in,
  rxslide_in,
  rxtermination_in,
  rxuserrdy_in,
  rxusrclk_in,
  rxusrclk2_in,
  tx8b10ben_in,
  txctrl0_in,
  txctrl1_in,
  txctrl2_in,
  txdata_in,
  txdeemph_in,
  txdetectrx_in,
  txdiffctrl_in,
  txdlybypass_in,
  txdlyen_in,
  txdlyhold_in,
  txdlyovrden_in,
  txdlysreset_in,
  txdlyupdown_in,
  txelecidle_in,
  txmaincursor_in,
  txmargin_in,
  txoutclksel_in,
  txpcsreset_in,
  txpd_in,
  txphalign_in,
  txphalignen_in,
  txphdlypd_in,
  txphdlyreset_in,
  txphdlytstclk_in,
  txphinit_in,
  txphovrden_in,
  txpmareset_in,
  txpostcursor_in,
  txprbsforceerr_in,
  txprbssel_in,
  txprecursor_in,
  txprogdivreset_in,
  txrate_in,
  txswing_in,
  txsyncallin_in,
  txsyncin_in,
  txsyncmode_in,
  txuserrdy_in,
  txusrclk_in,
  txusrclk2_in,
  bufgtce_out,
  bufgtcemask_out,
  bufgtdiv_out,
  bufgtreset_out,
  bufgtrstmask_out,
  cplllock_out,
  dmonitorout_out,
  drpdo_out,
  drprdy_out,
  gtpowergood_out,
  gtytxn_out,
  gtytxp_out,
  pcierategen3_out,
  pcierateidle_out,
  pcierateqpllpd_out,
  pcierateqpllreset_out,
  pciesynctxsyncdone_out,
  pcieusergen3rdy_out,
  pcieuserphystatusrst_out,
  pcieuserratestart_out,
  phystatus_out,
  rxbufstatus_out,
  rxbyteisaligned_out,
  rxbyterealign_out,
  rxcdrlock_out,
  rxclkcorcnt_out,
  rxcommadet_out,
  rxctrl0_out,
  rxctrl1_out,
  rxctrl2_out,
  rxctrl3_out,
  rxdata_out,
  rxdlysresetdone_out,
  rxelecidle_out,
  rxoutclk_out,
  rxoutclkfabric_out,
  rxoutclkpcs_out,
  rxphaligndone_out,
  rxpmaresetdone_out,
  rxprbserr_out,
  rxprbslocked_out,
  rxratedone_out,
  rxrecclkout_out,
  rxresetdone_out,
  rxstatus_out,
  rxsyncdone_out,
  rxvalid_out,
  txdlysresetdone_out,
  txoutclk_out,
  txoutclkfabric_out,
  txoutclkpcs_out,
  txphaligndone_out,
  txphinitdone_out,
  txpmaresetdone_out,
  txprgdivresetdone_out,
  txresetdone_out,
  txsyncdone_out,
  txsyncout_out
);

input wire [0 : 0] gtwiz_userclk_tx_reset_in;
input wire [0 : 0] gtwiz_userclk_tx_active_in;
input wire [0 : 0] gtwiz_userclk_rx_active_in;
input wire [0 : 0] gtwiz_reset_tx_done_in;
input wire [0 : 0] gtwiz_reset_rx_done_in;
input wire [287 : 0] gtwiz_gtye4_cpll_cal_txoutclk_period_in;
input wire [287 : 0] gtwiz_gtye4_cpll_cal_cnt_tol_in;
input wire [15 : 0] gtwiz_gtye4_cpll_cal_bufg_ce_in;
input wire [63 : 0] drpaddr_common_in;
input wire [3 : 0] drpclk_common_in;
input wire [63 : 0] drpdi_common_in;
input wire [3 : 0] drpen_common_in;
input wire [3 : 0] drpwe_common_in;
input wire [3 : 0] gtrefclk00_in;
input wire [3 : 0] gtrefclk01_in;
input wire [11 : 0] pcierateqpll0_in;
input wire [11 : 0] pcierateqpll1_in;
input wire [3 : 0] qpll0pd_in;
input wire [3 : 0] qpll0reset_in;
input wire [3 : 0] qpll1pd_in;
input wire [3 : 0] qpll1reset_in;
output wire [63 : 0] drpdo_common_out;
output wire [3 : 0] drprdy_common_out;
output wire [3 : 0] qpll0lock_out;
output wire [3 : 0] qpll0outclk_out;
output wire [3 : 0] qpll0outrefclk_out;
output wire [3 : 0] qpll1lock_out;
output wire [3 : 0] qpll1outclk_out;
output wire [3 : 0] qpll1outrefclk_out;
input wire [15 : 0] cpllfreqlock_in;
input wire [15 : 0] cpllpd_in;
input wire [15 : 0] cpllreset_in;
input wire [15 : 0] dmonfiforeset_in;
input wire [15 : 0] dmonitorclk_in;
input wire [159 : 0] drpaddr_in;
input wire [15 : 0] drpclk_in;
input wire [255 : 0] drpdi_in;
input wire [15 : 0] drpen_in;
input wire [15 : 0] drpwe_in;
input wire [15 : 0] eyescanreset_in;
input wire [15 : 0] gtrefclk0_in;
input wire [15 : 0] gtrxreset_in;
input wire [15 : 0] gttxreset_in;
input wire [15 : 0] gtyrxn_in;
input wire [15 : 0] gtyrxp_in;
input wire [47 : 0] loopback_in;
input wire [15 : 0] pcieeqrxeqadaptdone_in;
input wire [15 : 0] pcierstidle_in;
input wire [15 : 0] pciersttxsyncstart_in;
input wire [15 : 0] pcieuserratedone_in;
input wire [15 : 0] qpll0freqlock_in;
input wire [15 : 0] qpll1freqlock_in;
input wire [15 : 0] resetovrd_in;
input wire [15 : 0] rx8b10ben_in;
input wire [15 : 0] rxbufreset_in;
input wire [15 : 0] rxcdrfreqreset_in;
input wire [15 : 0] rxcdrhold_in;
input wire [15 : 0] rxcdrreset_in;
input wire [15 : 0] rxcommadeten_in;
input wire [15 : 0] rxdfeagchold_in;
input wire [15 : 0] rxdfecfokhold_in;
input wire [15 : 0] rxdfekhhold_in;
input wire [15 : 0] rxdfelfhold_in;
input wire [15 : 0] rxdfelpmreset_in;
input wire [15 : 0] rxdfetap10hold_in;
input wire [15 : 0] rxdfetap11hold_in;
input wire [15 : 0] rxdfetap12hold_in;
input wire [15 : 0] rxdfetap13hold_in;
input wire [15 : 0] rxdfetap14hold_in;
input wire [15 : 0] rxdfetap15hold_in;
input wire [15 : 0] rxdfetap2hold_in;
input wire [15 : 0] rxdfetap3hold_in;
input wire [15 : 0] rxdfetap4hold_in;
input wire [15 : 0] rxdfetap5hold_in;
input wire [15 : 0] rxdfetap6hold_in;
input wire [15 : 0] rxdfetap7hold_in;
input wire [15 : 0] rxdfetap8hold_in;
input wire [15 : 0] rxdfetap9hold_in;
input wire [15 : 0] rxdfeuthold_in;
input wire [15 : 0] rxdfevphold_in;
input wire [15 : 0] rxlpmen_in;
input wire [15 : 0] rxlpmgchold_in;
input wire [15 : 0] rxlpmhfhold_in;
input wire [15 : 0] rxlpmlfhold_in;
input wire [15 : 0] rxlpmoshold_in;
input wire [15 : 0] rxmcommaalignen_in;
input wire [15 : 0] rxoshold_in;
input wire [15 : 0] rxpcommaalignen_in;
input wire [15 : 0] rxpcsreset_in;
input wire [31 : 0] rxpd_in;
input wire [15 : 0] rxpmareset_in;
input wire [15 : 0] rxpolarity_in;
input wire [15 : 0] rxprbscntreset_in;
input wire [63 : 0] rxprbssel_in;
input wire [15 : 0] rxprogdivreset_in;
input wire [47 : 0] rxrate_in;
input wire [15 : 0] rxratemode_in;
input wire [15 : 0] rxslide_in;
input wire [15 : 0] rxtermination_in;
input wire [15 : 0] rxuserrdy_in;
input wire [15 : 0] rxusrclk_in;
input wire [15 : 0] rxusrclk2_in;
input wire [15 : 0] tx8b10ben_in;
input wire [255 : 0] txctrl0_in;
input wire [255 : 0] txctrl1_in;
input wire [127 : 0] txctrl2_in;
input wire [2047 : 0] txdata_in;
input wire [31 : 0] txdeemph_in;
input wire [15 : 0] txdetectrx_in;
input wire [79 : 0] txdiffctrl_in;
input wire [15 : 0] txdlybypass_in;
input wire [15 : 0] txdlyen_in;
input wire [15 : 0] txdlyhold_in;
input wire [15 : 0] txdlyovrden_in;
input wire [15 : 0] txdlysreset_in;
input wire [15 : 0] txdlyupdown_in;
input wire [15 : 0] txelecidle_in;
input wire [111 : 0] txmaincursor_in;
input wire [47 : 0] txmargin_in;
input wire [47 : 0] txoutclksel_in;
input wire [15 : 0] txpcsreset_in;
input wire [31 : 0] txpd_in;
input wire [15 : 0] txphalign_in;
input wire [15 : 0] txphalignen_in;
input wire [15 : 0] txphdlypd_in;
input wire [15 : 0] txphdlyreset_in;
input wire [15 : 0] txphdlytstclk_in;
input wire [15 : 0] txphinit_in;
input wire [15 : 0] txphovrden_in;
input wire [15 : 0] txpmareset_in;
input wire [79 : 0] txpostcursor_in;
input wire [15 : 0] txprbsforceerr_in;
input wire [63 : 0] txprbssel_in;
input wire [79 : 0] txprecursor_in;
input wire [15 : 0] txprogdivreset_in;
input wire [47 : 0] txrate_in;
input wire [15 : 0] txswing_in;
input wire [15 : 0] txsyncallin_in;
input wire [15 : 0] txsyncin_in;
input wire [15 : 0] txsyncmode_in;
input wire [15 : 0] txuserrdy_in;
input wire [15 : 0] txusrclk_in;
input wire [15 : 0] txusrclk2_in;
output wire [15 : 0] bufgtce_out;
output wire [47 : 0] bufgtcemask_out;
output wire [143 : 0] bufgtdiv_out;
output wire [15 : 0] bufgtreset_out;
output wire [47 : 0] bufgtrstmask_out;
output wire [15 : 0] cplllock_out;
output wire [255 : 0] dmonitorout_out;
output wire [255 : 0] drpdo_out;
output wire [15 : 0] drprdy_out;
output wire [15 : 0] gtpowergood_out;
output wire [15 : 0] gtytxn_out;
output wire [15 : 0] gtytxp_out;
output wire [15 : 0] pcierategen3_out;
output wire [15 : 0] pcierateidle_out;
output wire [31 : 0] pcierateqpllpd_out;
output wire [31 : 0] pcierateqpllreset_out;
output wire [15 : 0] pciesynctxsyncdone_out;
output wire [15 : 0] pcieusergen3rdy_out;
output wire [15 : 0] pcieuserphystatusrst_out;
output wire [15 : 0] pcieuserratestart_out;
output wire [15 : 0] phystatus_out;
output wire [47 : 0] rxbufstatus_out;
output wire [15 : 0] rxbyteisaligned_out;
output wire [15 : 0] rxbyterealign_out;
output wire [15 : 0] rxcdrlock_out;
output wire [31 : 0] rxclkcorcnt_out;
output wire [15 : 0] rxcommadet_out;
output wire [255 : 0] rxctrl0_out;
output wire [255 : 0] rxctrl1_out;
output wire [127 : 0] rxctrl2_out;
output wire [127 : 0] rxctrl3_out;
output wire [2047 : 0] rxdata_out;
output wire [15 : 0] rxdlysresetdone_out;
output wire [15 : 0] rxelecidle_out;
output wire [15 : 0] rxoutclk_out;
output wire [15 : 0] rxoutclkfabric_out;
output wire [15 : 0] rxoutclkpcs_out;
output wire [15 : 0] rxphaligndone_out;
output wire [15 : 0] rxpmaresetdone_out;
output wire [15 : 0] rxprbserr_out;
output wire [15 : 0] rxprbslocked_out;
output wire [15 : 0] rxratedone_out;
output wire [15 : 0] rxrecclkout_out;
output wire [15 : 0] rxresetdone_out;
output wire [47 : 0] rxstatus_out;
output wire [15 : 0] rxsyncdone_out;
output wire [15 : 0] rxvalid_out;
output wire [15 : 0] txdlysresetdone_out;
output wire [15 : 0] txoutclk_out;
output wire [15 : 0] txoutclkfabric_out;
output wire [15 : 0] txoutclkpcs_out;
output wire [15 : 0] txphaligndone_out;
output wire [15 : 0] txphinitdone_out;
output wire [15 : 0] txpmaresetdone_out;
output wire [15 : 0] txprgdivresetdone_out;
output wire [15 : 0] txresetdone_out;
output wire [15 : 0] txsyncdone_out;
output wire [15 : 0] txsyncout_out;

  xdma_0_pcie4_ip_gt_gtwizard_top #(
    .C_CHANNEL_ENABLE(192'B000000000000000000000000000000000000000000000000000000000000111111111111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    .C_COMMON_SCALING_FACTOR(4),
    .C_CPLL_VCO_FREQUENCY(2500.0),
    .C_FORCE_COMMONS(0),
    .C_FREERUN_FREQUENCY(100),
    .C_GT_TYPE(3),
    .C_GT_REV(61),
    .C_INCLUDE_CPLL_CAL(1),
    .C_SIM_CPLL_CAL_BYPASS(1'D1),
    .C_LOCATE_COMMON(0),
    .C_LOCATE_RESET_CONTROLLER(1),
    .C_LOCATE_USER_DATA_WIDTH_SIZING(1),
    .C_LOCATE_RX_BUFFER_BYPASS_CONTROLLER(0),
    .C_LOCATE_IN_SYSTEM_IBERT_CORE(2),
    .C_LOCATE_RX_USER_CLOCKING(1),
    .C_LOCATE_TX_BUFFER_BYPASS_CONTROLLER(1),
    .C_LOCATE_TX_USER_CLOCKING(1),
    .C_RESET_CONTROLLER_INSTANCE_CTRL(0),
    .C_RX_BUFFBYPASS_MODE(0),
    .C_RX_BUFFER_BYPASS_INSTANCE_CTRL(0),
    .C_RX_BUFFER_MODE(1),
    .C_RX_CB_DISP(8'B00000000),
    .C_RX_CB_K(8'B00000000),
    .C_RX_CB_MAX_LEVEL(5),
    .C_RX_CB_LEN_SEQ(1),
    .C_RX_CB_NUM_SEQ(0),
    .C_RX_CB_VAL(80'B00000000000000000000000000000000000000000000000000000000000000000000000000000000),
    .C_RX_CC_DISP(8'B00000000),
    .C_RX_CC_ENABLE(1),
    .C_RESET_SEQUENCE_INTERVAL(0),
    .C_RX_CC_K(8'B00000001),
    .C_RX_CC_LEN_SEQ(1),
    .C_RX_CC_NUM_SEQ(1),
    .C_RX_CC_PERIODICITY(5000),
    .C_RX_CC_VAL(80'B00000000000000000000000000000000000000000000000000000000000000000000000000011100),
    .C_RX_COMMA_M_ENABLE(1),
    .C_RX_COMMA_M_VAL(10'B1010000011),
    .C_RX_COMMA_P_ENABLE(1),
    .C_RX_COMMA_P_VAL(10'B0101111100),
    .C_RX_DATA_DECODING(1),
    .C_RX_ENABLE(1),
    .C_RX_INT_DATA_WIDTH(20),
    .C_RX_LINE_RATE(8),
    .C_RX_MASTER_CHANNEL_IDX(131),
    .C_RX_OUTCLK_BUFG_GT_DIV(1),
    .C_RX_OUTCLK_FREQUENCY(400.0000000),
    .C_RX_OUTCLK_SOURCE(1),
    .C_RX_PLL_TYPE(1),
    .C_RX_RECCLK_OUTPUT(192'H000000000000000000000000000000000000000000000000),
    .C_RX_REFCLK_FREQUENCY(100),
    .C_RX_SLIDE_MODE(2),
    .C_RX_USER_CLOCKING_CONTENTS(0),
    .C_RX_USER_CLOCKING_INSTANCE_CTRL(0),
    .C_RX_USER_CLOCKING_RATIO_FSRC_FUSRCLK(1),
    .C_RX_USER_CLOCKING_RATIO_FUSRCLK_FUSRCLK2(1),
    .C_RX_USER_CLOCKING_SOURCE(0),
    .C_RX_USER_DATA_WIDTH(16),
    .C_RX_USRCLK_FREQUENCY(400.0000000),
    .C_RX_USRCLK2_FREQUENCY(400.0000000),
    .C_SECONDARY_QPLL_ENABLE(0),
    .C_SECONDARY_QPLL_REFCLK_FREQUENCY(257.8125),
    .C_TOTAL_NUM_CHANNELS(16),
    .C_TOTAL_NUM_COMMONS(4),
    .C_TOTAL_NUM_COMMONS_EXAMPLE(0),
    .C_TXPROGDIV_FREQ_ENABLE(0),
    .C_TXPROGDIV_FREQ_SOURCE(1),
    .C_TXPROGDIV_FREQ_VAL(400),
    .C_TX_BUFFBYPASS_MODE(0),
    .C_TX_BUFFER_BYPASS_INSTANCE_CTRL(0),
    .C_TX_BUFFER_MODE(0),
    .C_TX_DATA_ENCODING(1),
    .C_TX_ENABLE(1),
    .C_TX_INT_DATA_WIDTH(20),
    .C_TX_LINE_RATE(8),
    .C_TX_MASTER_CHANNEL_IDX(131),
    .C_TX_OUTCLK_BUFG_GT_DIV(1),
    .C_TX_OUTCLK_FREQUENCY(400.0000000),
    .C_TX_OUTCLK_SOURCE(4),
    .C_TX_PLL_TYPE(1),
    .C_TX_REFCLK_FREQUENCY(100),
    .C_TX_USER_CLOCKING_CONTENTS(0),
    .C_TX_USER_CLOCKING_INSTANCE_CTRL(0),
    .C_TX_USER_CLOCKING_RATIO_FSRC_FUSRCLK(1),
    .C_TX_USER_CLOCKING_RATIO_FUSRCLK_FUSRCLK2(1),
    .C_TX_USER_CLOCKING_SOURCE(0),
    .C_TX_USER_DATA_WIDTH(16),
    .C_TX_USRCLK_FREQUENCY(400.0000000),
    .C_TX_USRCLK2_FREQUENCY(400.0000000)
  ) inst (
    .gtwiz_userclk_tx_reset_in(gtwiz_userclk_tx_reset_in),
    .gtwiz_userclk_tx_active_in(gtwiz_userclk_tx_active_in),
    .gtwiz_userclk_tx_srcclk_out(),
    .gtwiz_userclk_tx_usrclk_out(),
    .gtwiz_userclk_tx_usrclk2_out(),
    .gtwiz_userclk_tx_active_out(),
    .gtwiz_userclk_rx_reset_in(1'B0),
    .gtwiz_userclk_rx_active_in(gtwiz_userclk_rx_active_in),
    .gtwiz_userclk_rx_srcclk_out(),
    .gtwiz_userclk_rx_usrclk_out(),
    .gtwiz_userclk_rx_usrclk2_out(),
    .gtwiz_userclk_rx_active_out(),
    .gtwiz_buffbypass_tx_reset_in(1'B0),
    .gtwiz_buffbypass_tx_start_user_in(1'B0),
    .gtwiz_buffbypass_tx_done_out(),
    .gtwiz_buffbypass_tx_error_out(),
    .gtwiz_buffbypass_rx_reset_in(1'B0),
    .gtwiz_buffbypass_rx_start_user_in(1'B0),
    .gtwiz_buffbypass_rx_done_out(),
    .gtwiz_buffbypass_rx_error_out(),
    .gtwiz_reset_clk_freerun_in(1'B0),
    .gtwiz_reset_all_in(1'B0),
    .gtwiz_reset_tx_pll_and_datapath_in(1'B0),
    .gtwiz_reset_tx_datapath_in(1'B0),
    .gtwiz_reset_rx_pll_and_datapath_in(1'B0),
    .gtwiz_reset_rx_datapath_in(1'B0),
    .gtwiz_reset_tx_done_in(gtwiz_reset_tx_done_in),
    .gtwiz_reset_rx_done_in(gtwiz_reset_rx_done_in),
    .gtwiz_reset_qpll0lock_in(4'B0),
    .gtwiz_reset_qpll1lock_in(4'B0),
    .gtwiz_reset_rx_cdr_stable_out(),
    .gtwiz_reset_tx_done_out(),
    .gtwiz_reset_rx_done_out(),
    .gtwiz_reset_qpll0reset_out(),
    .gtwiz_reset_qpll1reset_out(),
    .gtwiz_gthe3_cpll_cal_txoutclk_period_in(288'B0),
    .gtwiz_gthe3_cpll_cal_cnt_tol_in(288'B0),
    .gtwiz_gthe3_cpll_cal_bufg_ce_in(16'B0),
    .gtwiz_gthe4_cpll_cal_txoutclk_period_in(288'B0),
    .gtwiz_gthe4_cpll_cal_cnt_tol_in(288'B0),
    .gtwiz_gthe4_cpll_cal_bufg_ce_in(16'B0),
    .gtwiz_gtye4_cpll_cal_txoutclk_period_in(gtwiz_gtye4_cpll_cal_txoutclk_period_in),
    .gtwiz_gtye4_cpll_cal_cnt_tol_in(gtwiz_gtye4_cpll_cal_cnt_tol_in),
    .gtwiz_gtye4_cpll_cal_bufg_ce_in(gtwiz_gtye4_cpll_cal_bufg_ce_in),
    .gtwiz_userdata_tx_in(256'B0),
    .gtwiz_userdata_rx_out(),
    .bgbypassb_in(4'HF),
    .bgmonitorenb_in(4'HF),
    .bgpdb_in(4'HF),
    .bgrcalovrd_in(20'H84210),
    .bgrcalovrdenb_in(4'HF),
    .drpaddr_common_in(drpaddr_common_in),
    .drpclk_common_in(drpclk_common_in),
    .drpdi_common_in(drpdi_common_in),
    .drpen_common_in(drpen_common_in),
    .drpwe_common_in(drpwe_common_in),
    .gtgrefclk0_in(4'H0),
    .gtgrefclk1_in(4'H0),
    .gtnorthrefclk00_in(4'H0),
    .gtnorthrefclk01_in(4'H0),
    .gtnorthrefclk10_in(4'H0),
    .gtnorthrefclk11_in(4'H0),
    .gtrefclk00_in(gtrefclk00_in),
    .gtrefclk01_in(gtrefclk01_in),
    .gtrefclk10_in(4'H0),
    .gtrefclk11_in(4'H0),
    .gtsouthrefclk00_in(4'H0),
    .gtsouthrefclk01_in(4'H0),
    .gtsouthrefclk10_in(4'H0),
    .gtsouthrefclk11_in(4'H0),
    .pcierateqpll0_in(pcierateqpll0_in),
    .pcierateqpll1_in(pcierateqpll1_in),
    .pmarsvd0_in(32'H00000000),
    .pmarsvd1_in(32'H00000000),
    .qpll0clkrsvd0_in(4'H0),
    .qpll0clkrsvd1_in(4'H0),
    .qpll0fbdiv_in(32'H00000000),
    .qpll0lockdetclk_in(4'H0),
    .qpll0locken_in(4'H0),
    .qpll0pd_in(qpll0pd_in),
    .qpll0refclksel_in(12'H249),
    .qpll0reset_in(qpll0reset_in),
    .qpll1clkrsvd0_in(4'H0),
    .qpll1clkrsvd1_in(4'H0),
    .qpll1fbdiv_in(32'H00000000),
    .qpll1lockdetclk_in(4'H0),
    .qpll1locken_in(4'HF),
    .qpll1pd_in(qpll1pd_in),
    .qpll1refclksel_in(12'H249),
    .qpll1reset_in(qpll1reset_in),
    .qpllrsvd1_in(32'H00000000),
    .qpllrsvd2_in(20'H00000),
    .qpllrsvd3_in(20'H00000),
    .qpllrsvd4_in(32'H00000000),
    .rcalenb_in(4'HF),
    .sdm0data_in(100'H0000000000000000000000000),
    .sdm0reset_in(4'H0),
    .sdm0toggle_in(4'H0),
    .sdm0width_in(8'H00),
    .sdm1data_in(100'H0000000000000000000000000),
    .sdm1reset_in(4'H0),
    .sdm1toggle_in(4'H0),
    .sdm1width_in(8'H00),
    .tcongpi_in(1'B0),
    .tconpowerup_in(1'B0),
    .tconreset_in(1'B0),
    .tconrsvdin1_in(1'B0),
    .ubcfgstreamen_in(4'H0),
    .ubdo_in(64'H0000000000000000),
    .ubdrdy_in(4'H0),
    .ubenable_in(4'H0),
    .ubgpi_in(8'H00),
    .ubintr_in(8'H00),
    .ubiolmbrst_in(4'H0),
    .ubmbrst_in(4'H0),
    .ubmdmcapture_in(4'H0),
    .ubmdmdbgrst_in(4'H0),
    .ubmdmdbgupdate_in(4'H0),
    .ubmdmregen_in(16'H0000),
    .ubmdmshift_in(4'H0),
    .ubmdmsysrst_in(4'H0),
    .ubmdmtck_in(4'H0),
    .ubmdmtdi_in(4'H0),
    .drpdo_common_out(drpdo_common_out),
    .drprdy_common_out(drprdy_common_out),
    .pmarsvdout0_out(),
    .pmarsvdout1_out(),
    .qpll0fbclklost_out(),
    .qpll0lock_out(qpll0lock_out),
    .qpll0outclk_out(qpll0outclk_out),
    .qpll0outrefclk_out(qpll0outrefclk_out),
    .qpll0refclklost_out(),
    .qpll1fbclklost_out(),
    .qpll1lock_out(qpll1lock_out),
    .qpll1outclk_out(qpll1outclk_out),
    .qpll1outrefclk_out(qpll1outrefclk_out),
    .qpll1refclklost_out(),
    .qplldmonitor0_out(),
    .qplldmonitor1_out(),
    .refclkoutmonitor0_out(),
    .refclkoutmonitor1_out(),
    .rxrecclk0_sel_out(),
    .rxrecclk1_sel_out(),
    .rxrecclk0sel_out(),
    .rxrecclk1sel_out(),
    .sdm0finalout_out(),
    .sdm0testdata_out(),
    .sdm1finalout_out(),
    .sdm1testdata_out(),
    .tcongpo_out(),
    .tconrsvdout0_out(),
    .ubdaddr_out(),
    .ubden_out(),
    .ubdi_out(),
    .ubdwe_out(),
    .ubmdmtdo_out(),
    .ubrsvdout_out(),
    .ubtxuart_out(),
    .cdrstepdir_in(16'H0000),
    .cdrstepsq_in(16'H0000),
    .cdrstepsx_in(16'H0000),
    .cfgreset_in(16'H0000),
    .clkrsvd0_in(16'H0000),
    .clkrsvd1_in(16'H0000),
    .cpllfreqlock_in(cpllfreqlock_in),
    .cplllockdetclk_in(16'H0000),
    .cplllocken_in(16'HFFFF),
    .cpllpd_in(cpllpd_in),
    .cpllrefclksel_in(48'H249249249249),
    .cpllreset_in(cpllreset_in),
    .dmonfiforeset_in(dmonfiforeset_in),
    .dmonitorclk_in(dmonitorclk_in),
    .drpaddr_in(drpaddr_in),
    .drpclk_in(drpclk_in),
    .drpdi_in(drpdi_in),
    .drpen_in(drpen_in),
    .drprst_in(16'H0000),
    .drpwe_in(drpwe_in),
    .elpcaldvorwren_in(1'B0),
    .elpcalpaorwren_in(1'B0),
    .evoddphicaldone_in(1'B0),
    .evoddphicalstart_in(1'B0),
    .evoddphidrden_in(1'B0),
    .evoddphidwren_in(1'B0),
    .evoddphixrden_in(1'B0),
    .evoddphixwren_in(1'B0),
    .eyescanmode_in(1'B0),
    .eyescanreset_in(eyescanreset_in),
    .eyescantrigger_in(16'H0000),
    .freqos_in(16'H0000),
    .gtgrefclk_in(16'H0000),
    .gthrxn_in(1'B0),
    .gthrxp_in(1'B0),
    .gtnorthrefclk0_in(16'H0000),
    .gtnorthrefclk1_in(16'H0000),
    .gtrefclk0_in(gtrefclk0_in),
    .gtrefclk1_in(16'H0000),
    .gtresetsel_in(1'B0),
    .gtrsvd_in(256'H0000000000000000000000000000000000000000000000000000000000000000),
    .gtrxreset_in(gtrxreset_in),
    .gtrxresetsel_in(16'H0000),
    .gtsouthrefclk0_in(16'H0000),
    .gtsouthrefclk1_in(16'H0000),
    .gttxreset_in(gttxreset_in),
    .gttxresetsel_in(16'H0000),
    .incpctrl_in(16'H0000),
    .gtyrxn_in(gtyrxn_in),
    .gtyrxp_in(gtyrxp_in),
    .loopback_in(loopback_in),
    .looprsvd_in(1'B0),
    .lpbkrxtxseren_in(1'B0),
    .lpbktxrxseren_in(1'B0),
    .pcieeqrxeqadaptdone_in(pcieeqrxeqadaptdone_in),
    .pcierstidle_in(pcierstidle_in),
    .pciersttxsyncstart_in(pciersttxsyncstart_in),
    .pcieuserratedone_in(pcieuserratedone_in),
    .pcsrsvdin_in(256'H0000000000000000000000000000000000000000000000000000000000000000),
    .pcsrsvdin2_in(1'B0),
    .pmarsvdin_in(1'B0),
    .qpll0clk_in(16'H0000),
    .qpll0freqlock_in(qpll0freqlock_in),
    .qpll0refclk_in(16'H0000),
    .qpll1clk_in(16'H0000),
    .qpll1freqlock_in(qpll1freqlock_in),
    .qpll1refclk_in(16'H0000),
    .resetovrd_in(resetovrd_in),
    .rstclkentx_in(1'B0),
    .rx8b10ben_in(rx8b10ben_in),
    .rxafecfoken_in(16'HFFFF),
    .rxbufreset_in(rxbufreset_in),
    .rxcdrfreqreset_in(rxcdrfreqreset_in),
    .rxcdrhold_in(rxcdrhold_in),
    .rxcdrovrden_in(16'H0000),
    .rxcdrreset_in(rxcdrreset_in),
    .rxcdrresetrsv_in(1'B0),
    .rxchbonden_in(16'H0000),
    .rxchbondi_in(80'H00000000000000000000),
    .rxchbondlevel_in(48'H000000000000),
    .rxchbondmaster_in(16'H0000),
    .rxchbondslave_in(16'H0000),
    .rxckcalreset_in(16'H0000),
    .rxckcalstart_in(112'H0000000000000000000000000000),
    .rxcommadeten_in(rxcommadeten_in),
    .rxdfeagcctrl_in(1'B0),
    .rxdccforcestart_in(1'B0),
    .rxdfeagchold_in(rxdfeagchold_in),
    .rxdfeagcovrden_in(16'H0000),
    .rxdfecfokfcnum_in(64'HDDDDDDDDDDDDDDDD),
    .rxdfecfokfen_in(16'H0000),
    .rxdfecfokfpulse_in(16'H0000),
    .rxdfecfokhold_in(rxdfecfokhold_in),
    .rxdfecfokovren_in(16'H0000),
    .rxdfekhhold_in(rxdfekhhold_in),
    .rxdfekhovrden_in(16'H0000),
    .rxdfelfhold_in(rxdfelfhold_in),
    .rxdfelfovrden_in(16'H0000),
    .rxdfelpmreset_in(rxdfelpmreset_in),
    .rxdfetap10hold_in(rxdfetap10hold_in),
    .rxdfetap10ovrden_in(16'H0000),
    .rxdfetap11hold_in(rxdfetap11hold_in),
    .rxdfetap11ovrden_in(16'H0000),
    .rxdfetap12hold_in(rxdfetap12hold_in),
    .rxdfetap12ovrden_in(16'H0000),
    .rxdfetap13hold_in(rxdfetap13hold_in),
    .rxdfetap13ovrden_in(16'H0000),
    .rxdfetap14hold_in(rxdfetap14hold_in),
    .rxdfetap14ovrden_in(16'H0000),
    .rxdfetap15hold_in(rxdfetap15hold_in),
    .rxdfetap15ovrden_in(16'H0000),
    .rxdfetap2hold_in(rxdfetap2hold_in),
    .rxdfetap2ovrden_in(16'H0000),
    .rxdfetap3hold_in(rxdfetap3hold_in),
    .rxdfetap3ovrden_in(16'H0000),
    .rxdfetap4hold_in(rxdfetap4hold_in),
    .rxdfetap4ovrden_in(16'H0000),
    .rxdfetap5hold_in(rxdfetap5hold_in),
    .rxdfetap5ovrden_in(16'H0000),
    .rxdfetap6hold_in(rxdfetap6hold_in),
    .rxdfetap6ovrden_in(16'H0000),
    .rxdfetap7hold_in(rxdfetap7hold_in),
    .rxdfetap7ovrden_in(16'H0000),
    .rxdfetap8hold_in(rxdfetap8hold_in),
    .rxdfetap8ovrden_in(16'H0000),
    .rxdfetap9hold_in(rxdfetap9hold_in),
    .rxdfetap9ovrden_in(16'H0000),
    .rxdfeuthold_in(rxdfeuthold_in),
    .rxdfeutovrden_in(16'H0000),
    .rxdfevphold_in(rxdfevphold_in),
    .rxdfevpovrden_in(16'H0000),
    .rxdfevsen_in(1'B0),
    .rxdfexyden_in(16'HFFFF),
    .rxdlybypass_in(16'HFFFF),
    .rxdlyen_in(16'H0000),
    .rxdlyovrden_in(16'H0000),
    .rxdlysreset_in(16'H0000),
    .rxelecidlemode_in(32'H00000000),
    .rxeqtraining_in(16'H0000),
    .rxgearboxslip_in(16'H0000),
    .rxlatclk_in(16'H0000),
    .rxlpmen_in(rxlpmen_in),
    .rxlpmgchold_in(rxlpmgchold_in),
    .rxlpmgcovrden_in(16'H0000),
    .rxlpmhfhold_in(rxlpmhfhold_in),
    .rxlpmhfovrden_in(16'H0000),
    .rxlpmlfhold_in(rxlpmlfhold_in),
    .rxlpmlfklovrden_in(16'H0000),
    .rxlpmoshold_in(rxlpmoshold_in),
    .rxlpmosovrden_in(16'H0000),
    .rxmcommaalignen_in(rxmcommaalignen_in),
    .rxmonitorsel_in(32'H00000000),
    .rxoobreset_in(16'H0000),
    .rxoscalreset_in(16'H0000),
    .rxoshold_in(rxoshold_in),
    .rxosintcfg_in(1'B0),
    .rxosinten_in(1'B0),
    .rxosinthold_in(1'B0),
    .rxosintovrden_in(1'B0),
    .rxosintstrobe_in(1'B0),
    .rxosinttestovrden_in(1'B0),
    .rxosovrden_in(16'H0000),
    .rxoutclksel_in(48'H492492492492),
    .rxpcommaalignen_in(rxpcommaalignen_in),
    .rxpcsreset_in(rxpcsreset_in),
    .rxpd_in(rxpd_in),
    .rxphalign_in(16'H0000),
    .rxphalignen_in(16'H0000),
    .rxphdlypd_in(16'H0000),
    .rxphdlyreset_in(16'H0000),
    .rxphovrden_in(1'B0),
    .rxpllclksel_in(32'HAAAAAAAA),
    .rxpmareset_in(rxpmareset_in),
    .rxpolarity_in(rxpolarity_in),
    .rxprbscntreset_in(rxprbscntreset_in),
    .rxprbssel_in(rxprbssel_in),
    .rxprogdivreset_in(rxprogdivreset_in),
    .rxqpien_in(1'B0),
    .rxrate_in(rxrate_in),
    .rxratemode_in(rxratemode_in),
    .rxslide_in(rxslide_in),
    .rxslipoutclk_in(16'H0000),
    .rxslippma_in(16'H0000),
    .rxsyncallin_in(16'H0000),
    .rxsyncin_in(16'H0000),
    .rxsyncmode_in(16'H0000),
    .rxsysclksel_in(32'HFFFFFFFF),
    .rxtermination_in(rxtermination_in),
    .rxuserrdy_in(rxuserrdy_in),
    .rxusrclk_in(rxusrclk_in),
    .rxusrclk2_in(rxusrclk2_in),
    .sigvalidclk_in(16'H0000),
    .tstin_in(320'H00000000000000000000000000000000000000000000000000000000000000000000000000000000),
    .tx8b10bbypass_in(128'H00000000000000000000000000000000),
    .tx8b10ben_in(tx8b10ben_in),
    .txbufdiffctrl_in(1'B0),
    .txcominit_in(16'H0000),
    .txcomsas_in(16'H0000),
    .txcomwake_in(16'H0000),
    .txctrl0_in(txctrl0_in),
    .txctrl1_in(txctrl1_in),
    .txctrl2_in(txctrl2_in),
    .txdata_in(txdata_in),
    .txdataextendrsvd_in(128'H00000000000000000000000000000000),
    .txdccforcestart_in(16'H0000),
    .txdccreset_in(16'H0000),
    .txdeemph_in(txdeemph_in),
    .txdetectrx_in(txdetectrx_in),
    .txdiffctrl_in(txdiffctrl_in),
    .txdiffpd_in(1'B0),
    .txdlybypass_in(txdlybypass_in),
    .txdlyen_in(txdlyen_in),
    .txdlyhold_in(txdlyhold_in),
    .txdlyovrden_in(txdlyovrden_in),
    .txdlysreset_in(txdlysreset_in),
    .txdlyupdown_in(txdlyupdown_in),
    .txelecidle_in(txelecidle_in),
    .txelforcestart_in(1'B0),
    .txheader_in(96'H000000000000000000000000),
    .txinhibit_in(16'H0000),
    .txlatclk_in(16'H0000),
    .txlfpstreset_in(16'H0000),
    .txlfpsu2lpexit_in(16'H0000),
    .txlfpsu3wake_in(16'H0000),
    .txmaincursor_in(txmaincursor_in),
    .txmargin_in(txmargin_in),
    .txmuxdcdexhold_in(16'H0000),
    .txmuxdcdorwren_in(16'H0000),
    .txoneszeros_in(16'H0000),
    .txoutclksel_in(txoutclksel_in),
    .txpcsreset_in(txpcsreset_in),
    .txpd_in(txpd_in),
    .txpdelecidlemode_in(16'H0000),
    .txphalign_in(txphalign_in),
    .txphalignen_in(txphalignen_in),
    .txphdlypd_in(txphdlypd_in),
    .txphdlyreset_in(txphdlyreset_in),
    .txphdlytstclk_in(txphdlytstclk_in),
    .txphinit_in(txphinit_in),
    .txphovrden_in(txphovrden_in),
    .txpippmen_in(16'H0000),
    .txpippmovrden_in(16'H0000),
    .txpippmpd_in(16'HFFFF),
    .txpippmsel_in(16'H0000),
    .txpippmstepsize_in(80'H00000000000000000000),
    .txpisopd_in(16'H0000),
    .txpllclksel_in(32'HAAAAAAAA),
    .txpmareset_in(txpmareset_in),
    .txpolarity_in(16'H0000),
    .txpostcursor_in(txpostcursor_in),
    .txpostcursorinv_in(1'B0),
    .txprbsforceerr_in(txprbsforceerr_in),
    .txprbssel_in(txprbssel_in),
    .txprecursor_in(txprecursor_in),
    .txprecursorinv_in(1'B0),
    .txprogdivreset_in(txprogdivreset_in),
    .txqpibiasen_in(1'B0),
    .txqpistrongpdown_in(1'B0),
    .txqpiweakpup_in(1'B0),
    .txrate_in(txrate_in),
    .txratemode_in(16'H0000),
    .txsequence_in(112'H0000000000000000000000000000),
    .txswing_in(txswing_in),
    .txsyncallin_in(txsyncallin_in),
    .txsyncin_in(txsyncin_in),
    .txsyncmode_in(txsyncmode_in),
    .txsysclksel_in(32'HFFFFFFFF),
    .txuserrdy_in(txuserrdy_in),
    .txusrclk_in(txusrclk_in),
    .txusrclk2_in(txusrclk2_in),
    .bufgtce_out(bufgtce_out),
    .bufgtcemask_out(bufgtcemask_out),
    .bufgtdiv_out(bufgtdiv_out),
    .bufgtreset_out(bufgtreset_out),
    .bufgtrstmask_out(bufgtrstmask_out),
    .cpllfbclklost_out(),
    .cplllock_out(cplllock_out),
    .cpllrefclklost_out(),
    .dmonitorout_out(dmonitorout_out),
    .dmonitoroutclk_out(),
    .drpdo_out(drpdo_out),
    .drprdy_out(drprdy_out),
    .eyescandataerror_out(),
    .gthtxn_out(),
    .gthtxp_out(),
    .gtpowergood_out(gtpowergood_out),
    .gtrefclkmonitor_out(),
    .gtytxn_out(gtytxn_out),
    .gtytxp_out(gtytxp_out),
    .pcierategen3_out(pcierategen3_out),
    .pcierateidle_out(pcierateidle_out),
    .pcierateqpllpd_out(pcierateqpllpd_out),
    .pcierateqpllreset_out(pcierateqpllreset_out),
    .pciesynctxsyncdone_out(pciesynctxsyncdone_out),
    .pcieusergen3rdy_out(pcieusergen3rdy_out),
    .pcieuserphystatusrst_out(pcieuserphystatusrst_out),
    .pcieuserratestart_out(pcieuserratestart_out),
    .pcsrsvdout_out(),
    .phystatus_out(phystatus_out),
    .pinrsrvdas_out(),
    .powerpresent_out(),
    .resetexception_out(),
    .rxbufstatus_out(rxbufstatus_out),
    .rxbyteisaligned_out(rxbyteisaligned_out),
    .rxbyterealign_out(rxbyterealign_out),
    .rxcdrlock_out(rxcdrlock_out),
    .rxcdrphdone_out(),
    .rxchanbondseq_out(),
    .rxchanisaligned_out(),
    .rxchanrealign_out(),
    .rxchbondo_out(),
    .rxckcaldone_out(),
    .rxclkcorcnt_out(rxclkcorcnt_out),
    .rxcominitdet_out(),
    .rxcommadet_out(rxcommadet_out),
    .rxcomsasdet_out(),
    .rxcomwakedet_out(),
    .rxctrl0_out(rxctrl0_out),
    .rxctrl1_out(rxctrl1_out),
    .rxctrl2_out(rxctrl2_out),
    .rxctrl3_out(rxctrl3_out),
    .rxdata_out(rxdata_out),
    .rxdataextendrsvd_out(),
    .rxdatavalid_out(),
    .rxdlysresetdone_out(rxdlysresetdone_out),
    .rxelecidle_out(rxelecidle_out),
    .rxheader_out(),
    .rxheadervalid_out(),
    .rxlfpstresetdet_out(),
    .rxlfpsu2lpexitdet_out(),
    .rxlfpsu3wakedet_out(),
    .rxmonitorout_out(),
    .rxosintdone_out(),
    .rxosintstarted_out(),
    .rxosintstrobedone_out(),
    .rxosintstrobestarted_out(),
    .rxoutclk_out(rxoutclk_out),
    .rxoutclkfabric_out(rxoutclkfabric_out),
    .rxoutclkpcs_out(rxoutclkpcs_out),
    .rxphaligndone_out(rxphaligndone_out),
    .rxphalignerr_out(),
    .rxpmaresetdone_out(rxpmaresetdone_out),
    .rxprbserr_out(rxprbserr_out),
    .rxprbslocked_out(rxprbslocked_out),
    .rxprgdivresetdone_out(),
    .rxqpisenn_out(),
    .rxqpisenp_out(),
    .rxratedone_out(rxratedone_out),
    .rxrecclkout_out(rxrecclkout_out),
    .rxresetdone_out(rxresetdone_out),
    .rxsliderdy_out(),
    .rxslipdone_out(),
    .rxslipoutclkrdy_out(),
    .rxslippmardy_out(),
    .rxstartofseq_out(),
    .rxstatus_out(rxstatus_out),
    .rxsyncdone_out(rxsyncdone_out),
    .rxsyncout_out(),
    .rxvalid_out(rxvalid_out),
    .txbufstatus_out(),
    .txcomfinish_out(),
    .txdccdone_out(),
    .txdlysresetdone_out(txdlysresetdone_out),
    .txoutclk_out(txoutclk_out),
    .txoutclkfabric_out(txoutclkfabric_out),
    .txoutclkpcs_out(txoutclkpcs_out),
    .txphaligndone_out(txphaligndone_out),
    .txphinitdone_out(txphinitdone_out),
    .txpmaresetdone_out(txpmaresetdone_out),
    .txprgdivresetdone_out(txprgdivresetdone_out),
    .txqpisenn_out(),
    .txqpisenp_out(),
    .txratedone_out(),
    .txresetdone_out(txresetdone_out),
    .txsyncdone_out(txsyncdone_out),
    .txsyncout_out(txsyncout_out)
  );
endmodule
