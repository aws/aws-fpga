//*****************************************************************************
// (c) Copyright 2013 - 2014 Xilinx, Inc. All rights reserved.
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
//*****************************************************************************
//   ____  ____
//  /   /\/   /
// /___/  \  /    Vendor             : Xilinx
// \   \   \/     Version            : 1.1
//  \   \         Application        : MIG
//  /   /         Filename           : ddr4_phy_v2_2_0_xiphy_bitslice_wrapper.sv
// /___/   /\     Date Last Modified : $Date: 2015/04/23 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : XiPHY
// Purpose          :
//                   ddr4_phy_v2_2_0_xiphy_bitslice_wrapper module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ps / 1ps

module ddr4_phy_v2_2_0_xiphy_bitslice_wrapper #(
   parameter           FIFO_SYNC_MODE       = "FALSE",    //Synchronous read/write clocks (TRUE, FALSE)
   parameter           ENABLE_PRE_EMPHASIS  = "FALSE",    //Pre-emphasis output 
   parameter integer   RX_DATA_WIDTH        = 8,          //8,4,1 bit interface
   parameter           RX_DATA_TYPE         = "DATA",     //DATA, CLOCK, DATA_AND_CLOCK, NONE
   parameter           RX_DELAY_FORMAT      = "TIME",     //TIME (mc_fixed_dly_ratio = (2*9)*(1000000/REFCLK_FREQ/DELAY_VAL), COUNT (mc_fixed_delay_ratio={9'b0, DELAY_VAL}) 
   parameter           RX_DELAY_TYPE        = "FIXED",    //FIXED, VAR_LOAD, VARIABLE
   parameter integer   RX_DELAY_VAL         = 0,          //0 to 1250 ps
   parameter real      RX_REFCLK_FREQ       = 300.0,      //300-2667 MHz    
   parameter           RX_UPDATE_MODE       = "ASYNC",    //ASYNC (mc_le_manual=0,mc_le_async=1), SYNC(mc_le_manual=0,mc_le_sync=0), MANUAL (mc_le_manual=1,mc_le_async=0)
   parameter integer   TX_DATA_WIDTH        = 8,          //8,4,1 bit interface
   parameter           TX_DELAY_TYPE        = "FIXED",    //FIXED, VAR_LOAD, VARIABLE
   parameter real      TX_REFCLK_FREQ       = 300.0,      //300-2667 MHz
   parameter           TX_UPDATE_MODE       = "ASYNC",    //ASYNC (mc_le_manual=0,mc_le_async=1), SYNC(mc_le_manual=0,mc_le_sync=0), MANUAL (mc_le_manual=1,mc_le_async=0)
   parameter integer   TX_DELAY_VAL         = 0,          //0 to 1250 ps 
   parameter           INIT                 = 1'b0,       //Init value of Tx Bitslice Oserdes
   parameter           TBYTE_CTL            = "TBYTE_IN", //From Tristate bitslice (TBYTE_IN) or Fabric (T) to IOB T input
   parameter           TX_DELAY_FORMAT      = "TIME",     //TIME (mc_fixed_dly_ratio = (2*9)*(1000000/REFCLK_FREQ/DELAY_VAL), COUNT (mc_fixed_delay_ratio={9'b0, DELAY_VAL})
   parameter           TX_OUTPUT_PHASE_90   = "FALSE",    //Delay DQ phase by 90 against write DQS
   parameter           NATIVE_ODELAY_BYPASS = "FALSE",    // Bypass ODELAY 
   parameter           SIM_DEVICE           = "ULTRASCALE"
) (
//RX
input          rx_ce,              // idelay ce
input          rx_clk,             // idelay clk
input          rx_inc,             // idelay inc
input          rx_ld,              // idelay ld
input   [8:0]  rx_cntvaluein,      // idelay cntvaluein
output  [8:0]  rx_cntvalueout,     // RX cntvalueout
input          rx_d,               // Data from IOB
//output         rx_dqs_out,         // RX dqs clk output to control
output  [7:0]  rx_q,               // RX paralled data out
input          rx_rst_dly,         // idelay reset
input          rx_rst,             // iserdes rst
input          rx_en_vtc,          // idelay en vtc
//input   [2:0]  rx_nib_ctrl_in,     // ribbon cable input bus from BS control {rx_clk_p, rx_clk_n, rx_ctrl_clk} 

//Ribbon Cable Per Bitslice Input Bus from BS Control  
input   [39:0] rx_bit_ctrl_in,     // per bitslice ribbon cable input bus from BS control 
//{rx_clk_p, rx_clk_n, rx_ctrl_clk, rx_bs_reset, ctl2bs_rx_recalibrate_en, ctl2bs_rx_ddr_en_dq, ctl2bs_rx_ddr_en_dqs, ctl2bs_fifo_bypass, rx_ctrl_ce, rx_ctrl_inc, rx_ctrl_ld, rx_ctrl_dly[8:0], rx_dcc[3:0]} 

//Ribbon Cable Per Bitslice Output Bus to BS Control 
output  [39:0] rx_bit_ctrl_out,    // per bitslice ribbon cable output bus to BS control 
//{rx_q[7], rx_q[3], bs2ctl_idelay_fixed_dly_ratio[17:0], bs2ctl_idelay_delay_format, bs2ctl_rx_recalibrate_en, bs2ctl_rx_ddr_en_dq, bs2ctl_rx_ddr_en_dqs, rx_vtc_ready, rx_dqs_out, rx_cntvalueout[8:0]} 

//TX
input          tx_ce,              // odelay ce
input          tx_clk,             // odelay clk
input          tx_inc,             // odelay inc
input          tx_ld,              // odelay load
input  [8:0]   tx_cntvaluein,      // odelay cntvaluein
output [8:0]   tx_cntvalueout,     // TX cntvalue output
input  [7:0]   tx_d,               // from fabric data
output         tx_q,               // TX serialized q output
input          tx_rst_dly,         // odelay reset active high
input          tx_rst,             // oserdes rst
input          tx_t,               // oserdes t input
output         tx_t_out,           // TX OSERDES T output
input          tx_tbyte_in,        // oserdes tbyte_in 
input          tx_en_vtc,          // odelay enable vtc
//input   [3:0]  tx_nib_ctrl_in,     // ribbon cable input bus from BS control {tx_ddr_clk, tx_div2_clk, tx_div4_clk, tx_ctrl_clk} 

//Ribbon Cable Per Bitslice Input Bus from BS Control  
input   [39:0] tx_bit_ctrl_in,     // per bitslice ribbon cable input bus from BS control 
//{tx_div4_clk, tx_div2_clk, tx_ddr_clk, tx_wl_train, ctl2bs_tx_ddr_phase_sel, tx_bs_reset, tx_mux_360_p_sel, tx_mux_360_n_sel, tx_mux_720_p0_sel, tx_mux_720_p1_sel, tx_mux_720_p2_sel, tx_mux_720_p3_sel, 
//tx_toggle_div2_sel, ctl2bs_dynamic_mode_en, tx_ctrl_ce, tx_ctrl_inc, tx_ctrl_ld, tx_ctrl_dly[8:0], tx_ctrl_clk} 

//Ribbon Cable Per Bitslice Output Bus to BS Control 
output  [39:0] tx_bit_ctrl_out,    // per bitslice ribbon cable output bus to BS control 
//{bs2ctl_tx_ddr_phase_sel, bs2ctl_odelay_fixed_dly_ratio[17:0], bs2ctl_odelay_delay_format, tx_vtc_ready, tx_cntvalueout[8:0]} 

//FIFO
input          clb2phy_fifo_clk,  // ififo clk from fabric
input          clb2phy_fifo_rden,   // RX ififo renable from fabric 
output         phy2clb_fifo_empty,  // RX ififo empty flag to fabric
output         phy2clb_fifo_wrclk   // RX ififo wrclk`

);

`ifdef ULTRASCALE_PHY_BLH
B_RXTX_BITSLICE #(
`else
RXTX_BITSLICE #(
`endif
   .FIFO_SYNC_MODE       (FIFO_SYNC_MODE),   //Synchronous read/write clocks (TRUE, FALSE)
   .INIT                 (INIT),             //Init value of Tx Bitslice Oserdes 
   .ENABLE_PRE_EMPHASIS  (ENABLE_PRE_EMPHASIS),     //Pre-emphasis output enabled
   .RX_DATA_TYPE         (RX_DATA_TYPE),     //DATA, CLOCK, DATA_AND_CLOCK, NONE
   .RX_DATA_WIDTH        (RX_DATA_WIDTH),    //8,4,1
   .RX_DELAY_FORMAT      (RX_DELAY_FORMAT),  //TIME,COUNT
   .RX_DELAY_TYPE        (RX_DELAY_TYPE),    //FIXED, VAR_LOAD, VARIABLE
   .RX_DELAY_VALUE       (RX_DELAY_VAL),     //0 to 1250 ps
   .RX_REFCLK_FREQUENCY  (RX_REFCLK_FREQ),   //300-2667
   .RX_UPDATE_MODE       (RX_UPDATE_MODE),   //ASYNC, MANUAL
   .TBYTE_CTL            (TBYTE_CTL),        //TBYTE_IN, T
   .TX_DATA_WIDTH        (TX_DATA_WIDTH),    
   .TX_DELAY_FORMAT      (TX_DELAY_FORMAT),  
   .TX_DELAY_TYPE        (TX_DELAY_TYPE),    
   .TX_DELAY_VALUE       (TX_DELAY_VAL),     
   .TX_REFCLK_FREQUENCY  (TX_REFCLK_FREQ),   
   .TX_UPDATE_MODE       (TX_UPDATE_MODE),   
   .TX_OUTPUT_PHASE_90   (TX_OUTPUT_PHASE_90),//Delay DQ phase by 90
`ifndef ULTRASCALE_PHY_BLH
   .SIM_DEVICE           (SIM_DEVICE),
`endif
   .NATIVE_ODELAY_BYPASS (NATIVE_ODELAY_BYPASS)
) 
xiphy_rxtx_bitslice
(
// RX
   .RX_CE                   (rx_ce),
   .RX_CLK                  (rx_clk),            // clk to idelay
   .RX_INC                  (rx_inc),
   .RX_LOAD                 (rx_ld),
   .RX_CNTVALUEIN           (rx_cntvaluein),
   .RX_CNTVALUEOUT          (rx_cntvalueout), 
   .DATAIN                  (rx_d),
   .Q                       (rx_q),
   .RX_RST                  (rx_rst),
   .RX_RST_DLY              (rx_rst_dly),
   .RX_EN_VTC               (rx_en_vtc),
   //.RX_NIB_CTRL_IN          (rx_nib_ctrl_in),     
   .RX_BIT_CTRL_IN          (rx_bit_ctrl_in),     
   .RX_BIT_CTRL_OUT         (rx_bit_ctrl_out),  
//TX
   .TX_CE                   (tx_ce),
   .TX_CLK                  (tx_clk),
   .TX_INC                  (tx_inc),
   .TX_LOAD                 (tx_ld),
   .TX_CNTVALUEIN           (tx_cntvaluein),
   .TX_CNTVALUEOUT          (tx_cntvalueout),
   .D                       (tx_d),
   .O                       (tx_q),
   .TX_RST_DLY              (tx_rst_dly),
   .TX_RST                  (tx_rst),
   .T                       (tx_t),
   .T_OUT                   (tx_t_out),
   .TBYTE_IN                (tx_tbyte_in),
   .TX_EN_VTC               (tx_en_vtc),
   //.TX_NIB_CTRL_IN          (tx_nib_ctrl_in),
   .TX_BIT_CTRL_IN          (tx_bit_ctrl_in),
   .TX_BIT_CTRL_OUT         (tx_bit_ctrl_out),
//FIFO
   .FIFO_RD_CLK             (clb2phy_fifo_clk), 
   .FIFO_RD_EN              (clb2phy_fifo_rden),
   .FIFO_EMPTY              (phy2clb_fifo_empty),
   .FIFO_WRCLK_OUT          (phy2clb_fifo_wrclk) 
);

endmodule

