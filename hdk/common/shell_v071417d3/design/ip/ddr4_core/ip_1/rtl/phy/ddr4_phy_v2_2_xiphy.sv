/******************************************************************************
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
******************************************************************************/
//   ____  ____
//  /   /\/   /
// /___/  \  /    Vendor             : Xilinx
// \   \   \/     Version            : 1.1
//  \   \         Application        : MIG
//  /   /         Filename           : ddr4_phy_v2_2_0_xiphy.sv
// /___/   /\     Date Last Modified : $Date: 2015/04/23 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                    ddr4_phy_v2_2_0_xiphy module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ps/1ps

module ddr4_phy_v2_2_0_xiphy #(
    parameter integer BYTES                           = 7
   ,parameter integer DBYTES                          = 4
   ,parameter         TBYTE_CTL                       = "TBYTE_IN"
   ,parameter         DELAY_TYPE                      = "FIXED"
   ,parameter         DELAY_FORMAT                    = "TIME"
   ,parameter         UPDATE_MODE                     = "ASYNC"
   ,parameter         PLLCLK_SRC                      = 1'b0
   ,parameter  [13*BYTES-1:0] FIFO_SYNC_MODE          = {(13*BYTES){1'b0}}
   ,parameter   [1:0] DIV_MODE                        = 2'b00
   ,parameter   [1:0] REFCLK_SRC                      = 2'b00
   ,parameter   [1:0] CTRL_CLK                        = 2'b11
   ,parameter  [45*BYTES-1:0] GCLK_SRC                = {(45*BYTES){1'b0}}
   ,parameter  [15*BYTES-1:0] INIT                    = {(15*BYTES){1'b0}}
   ,parameter  [15*BYTES-1:0] RX_DATA_TYPE            = {(15*BYTES){1'b0}}
   ,parameter  [13*BYTES-1:0] TX_OUTPUT_PHASE_90      = {(13*BYTES){1'b0}}
   ,parameter  [13*BYTES-1:0] RXTX_BITSLICE_EN        = {(13*BYTES){1'b0}}   
   ,parameter   [2*BYTES-1:0] TRI_OUTPUT_PHASE_90     = {(2*BYTES){1'b0}}
   ,parameter  [13*BYTES-1:0] NATIVE_ODELAY_BYPASS    = {(13*BYTES){1'b0}}
   ,parameter   [2*BYTES-1:0] EN_OTHER_PCLK           = {(2*BYTES){1'b0}}
   ,parameter   [2*BYTES-1:0] EN_OTHER_NCLK           = {(2*BYTES){1'b0}}
   ,parameter   [2*BYTES-1:0] SERIAL_MODE             = {(2*BYTES){1'b0}}
   ,parameter   [2*BYTES-1:0] RX_CLK_PHASE_P          = {(2*BYTES){1'b0}}
   ,parameter   [2*BYTES-1:0] RX_CLK_PHASE_N          = {(2*BYTES){1'b0}}
   ,parameter   [2*BYTES-1:0] INV_RXCLK               = {(2*BYTES){1'b0}}
   ,parameter   [2*BYTES-1:0] TX_GATING               = {(2*BYTES){1'b0}}
   ,parameter   [2*BYTES-1:0] RX_GATING               = {(2*BYTES){1'b1}}
   ,parameter   [2*BYTES-1:0] EN_CLK_TO_EXT_NORTH     = {(2*BYTES){1'b0}}
   ,parameter   [2*BYTES-1:0] EN_CLK_TO_EXT_SOUTH     = {(2*BYTES){1'b0}}
   ,parameter integer RX_DELAY_VAL             [12:0] = '{0,0,0,0,0,0,0,0,0,0,0,0,0}
   ,parameter integer TX_DELAY_VAL             [12:0] = '{0,0,0,0,0,0,0,0,0,0,0,0,0}
   ,parameter integer TRI_DELAY_VAL             [1:0] = '{0, 0}
   ,parameter integer READ_IDLE_COUNT           [1:0] = '{31, 31}
   ,parameter integer ROUNDING_FACTOR           [1:0] = '{16, 16}
   ,parameter integer DATA_WIDTH                      = 8
   ,parameter real    REFCLK_FREQ                     = 300.0
   ,parameter  [13*BYTES-1:0] DCI_SRC                 = {(BYTES*13){1'b0}}
   ,parameter   [2*BYTES-1:0] EN_DYN_ODLY_MODE        = {(BYTES*2){1'b0}}
   ,parameter   [2*BYTES-1:0] SELF_CALIBRATE          = {(2*BYTES){1'b0}}
   ,parameter   [2*BYTES-1:0] IDLY_VT_TRACK           = {(2*BYTES){1'b1}}
   ,parameter   [2*BYTES-1:0] ODLY_VT_TRACK           = {(2*BYTES){1'b1}}
   ,parameter   [2*BYTES-1:0] QDLY_VT_TRACK           = {(2*BYTES){1'b1}}
   ,parameter   [2*BYTES-1:0] RXGATE_EXTEND           = {(2*BYTES){1'b0}}
   ,parameter         DRAM_TYPE                       = "DDR4"
   ,parameter         SIM_DEVICE                      = "ULTRASCALE"
)(
   // global clocks
    input [BYTES-1:0]  pll_clk0
   ,input [BYTES-1:0]  pll_clk1
   ,input [5:0]            gclk_in

   ,output  [BYTES*16-1:0] riu2clb_rd_data
   ,output   [BYTES*1-1:0] riu2clb_valid
   ,output  [BYTES*13-1:0] phy2clb_fifo_empty
   ,output   [BYTES*2-1:0] phy2rclk_ss_divclk
   ,output   [BYTES*8-1:0] phy2clb_rd_dq0
   ,output   [BYTES*8-1:0] phy2clb_rd_dq1
   ,output   [BYTES*8-1:0] phy2clb_rd_dq2
   ,output   [BYTES*8-1:0] phy2clb_rd_dq3
   ,output   [BYTES*8-1:0] phy2clb_rd_dq4
   ,output   [BYTES*8-1:0] phy2clb_rd_dq5
   ,output   [BYTES*8-1:0] phy2clb_rd_dq6
   ,output   [BYTES*8-1:0] phy2clb_rd_dq7
   ,output   [BYTES*8-1:0] phy2clb_rd_dq8
   ,output   [BYTES*8-1:0] phy2clb_rd_dq9
   ,output   [BYTES*8-1:0] phy2clb_rd_dq10
   ,output   [BYTES*8-1:0] phy2clb_rd_dq11
   ,output   [BYTES*8-1:0] phy2clb_rd_dq12
   ,output [BYTES*117-1:0] phy2clb_idelay_cntvalueout
   ,output [BYTES*117-1:0] phy2clb_odelay_cntvalueout
   ,output  [BYTES*18-1:0] phy2clb_tristate_odelay_cntvalueout
   ,output   [BYTES*1-1:0] phy2clb_fixdly_rdy_upp
   ,output   [BYTES*1-1:0] phy2clb_fixdly_rdy_low
   ,output   [BYTES*1-1:0] clk_to_ext_north_upp
   ,output   [BYTES*1-1:0] clk_to_ext_south_upp
   ,output   [BYTES*1-1:0] clk_to_ext_north_low
   ,output   [BYTES*1-1:0] clk_to_ext_south_low
   ,output   [BYTES*1-1:0] phy2clb_phy_rdy_upp
   ,output   [BYTES*1-1:0] phy2clb_phy_rdy_low
   ,output  [BYTES*13-1:0] phy2iob_q_out_byte
   ,output  [BYTES*13-1:0] phy2iob_odt_out_byte
   ,output  [BYTES*13-1:0] phy2iob_t

   ,input  [BYTES*13-1:0] clb2phy_fifo_clk
   ,input   [BYTES*1-1:0] clb2phy_ctrl_clk_upp
   ,input   [BYTES*1-1:0] clb2phy_ctrl_clk_low
   ,input   [BYTES*1-1:0] clb2phy_ref_clk_upp
   ,input   [BYTES*1-1:0] clb2phy_ref_clk_low
   ,input   [BYTES*1-1:0] clb2phy_ctrl_rst_upp
   ,input   [BYTES*1-1:0] clb2phy_ctrl_rst_low
   ,input   [BYTES*2-1:0] clb2phy_txbit_tri_rst
   ,input  [BYTES*13-1:0] clb2phy_txbit_rst
   ,input  [BYTES*13-1:0] clb2phy_rxbit_rst
   ,input   [BYTES*8-1:0] clb2phy_wr_dq0
   ,input   [BYTES*8-1:0] clb2phy_wr_dq1
   ,input   [BYTES*8-1:0] clb2phy_wr_dq2
   ,input   [BYTES*8-1:0] clb2phy_wr_dq3
   ,input   [BYTES*8-1:0] clb2phy_wr_dq4
   ,input   [BYTES*8-1:0] clb2phy_wr_dq5
   ,input   [BYTES*8-1:0] clb2phy_wr_dq6
   ,input   [BYTES*8-1:0] clb2phy_wr_dq7
   ,input   [BYTES*8-1:0] clb2phy_wr_dq8
   ,input   [BYTES*8-1:0] clb2phy_wr_dq9
   ,input   [BYTES*8-1:0] clb2phy_wr_dq10
   ,input   [BYTES*8-1:0] clb2phy_wr_dq11
   ,input   [BYTES*8-1:0] clb2phy_wr_dq12
   ,input   [BYTES*4-1:0] clb2phy_t_b_upp
   ,input   [BYTES*4-1:0] clb2phy_t_b_low
   ,input   [BYTES*4-1:0] clb2phy_rden_upp
   ,input   [BYTES*4-1:0] clb2phy_rden_low
   ,input   [BYTES*6-1:0] clb2riu_addr
   ,input  [BYTES*16-1:0] clb2riu_wr_data
   ,input   [BYTES*1-1:0] clb2riu_wr_en
   ,input   [BYTES*1-1:0] clb2riu_nibble_sel_upp
   ,input   [BYTES*1-1:0] clb2riu_nibble_sel_low
   ,input  [BYTES*13-1:0] clb2phy_fifo_rden
   ,input  [BYTES*13-1:0] clb2phy_idelay_rst
   ,input  [BYTES*13-1:0] clb2phy_idelay_ce
   ,input  [BYTES*13-1:0] clb2phy_idelay_inc
   ,input  [BYTES*13-1:0] clb2phy_idelay_ld
   ,input [BYTES*117-1:0] clb2phy_idelay_cntvaluein
   ,input  [BYTES*13-1:0] clb2phy_odelay_rst
   ,input  [BYTES*13-1:0] clb2phy_odelay_ce
   ,input  [BYTES*13-1:0] clb2phy_odelay_inc
   ,input  [BYTES*13-1:0] clb2phy_odelay_ld
   ,input [BYTES*117-1:0] clb2phy_odelay_cntvaluein
   ,input  [BYTES*13-1:0] clb2phy_t_txbit
   ,input  [BYTES*13-1:0] clb2phy_tristate_odelay_rst
   ,input   [BYTES*2-1:0] clb2phy_tristate_odelay_ce
   ,input   [BYTES*2-1:0] clb2phy_tristate_odelay_inc
   ,input   [BYTES*2-1:0] clb2phy_tristate_odelay_ld
   ,input  [BYTES*18-1:0] clb2phy_tristate_odelay_cntvaluein
   ,input   [BYTES*4-1:0] clb2phy_wrcs0_upp
   ,input   [BYTES*4-1:0] clb2phy_wrcs1_upp
   ,input   [BYTES*4-1:0] clb2phy_wrcs0_low
   ,input   [BYTES*4-1:0] clb2phy_wrcs1_low
   ,input   [BYTES*4-1:0] clb2phy_rdcs0_upp
   ,input   [BYTES*4-1:0] clb2phy_rdcs1_upp
   ,input   [BYTES*4-1:0] clb2phy_rdcs0_low
   ,input   [BYTES*4-1:0] clb2phy_rdcs1_low
   ,input   [BYTES*1-1:0] clk_from_ext_low
   ,input   [BYTES*1-1:0] clk_from_ext_upp
   ,input  [BYTES*13-1:0] clb2phy_idelay_en_vtc
   ,input  [BYTES*13-1:0] clb2phy_odelay_en_vtc
   ,input   [BYTES*2-1:0] clb2phy_odelay_tristate_en_vtc
   ,input   [BYTES*1-1:0] clb2phy_dlyctl_en_vtc_upp
   ,input   [BYTES*1-1:0] clb2phy_dlyctl_en_vtc_low
   ,input  [BYTES*13-1:0] iob2phy_d_in_byte
   ,input   [BYTES*7-1:0] clb2phy_odt_upp
   ,input   [BYTES*7-1:0] clb2phy_odt_low
);

wire [BYTES*1-1:0] phy2clb_phy_rdy_upp_lcl;
wire [BYTES*1-1:0] phy2clb_phy_rdy_low_lcl;
wire [BYTES*1-1:0] phy2clb_fixdly_rdy_upp_lcl;
wire [BYTES*1-1:0] phy2clb_fixdly_rdy_low_lcl;
wire [BYTES*1-1:0] riu2clb_valid_lcl;

wire [BYTES-1:0] bisc_start_in;
wire [BYTES-1:0] bisc_stop_in;
wire [BYTES-1:0] bisc_start_out;
wire [BYTES-1:0] bisc_stop_out;

genvar i;

generate
   for (i = 0; i < BYTES; i = i + 1) begin : byte_num
     if(|RXTX_BITSLICE_EN[i*13+:13]) begin : xiphy_byte_wrapper
      ddr4_phy_v2_2_0_xiphy_byte_wrapper #(
          .ENABLE_PRE_EMPHASIS ((DRAM_TYPE == "DDR4") ? "TRUE" : "FALSE")
         ,.DATA_WIDTH          (DATA_WIDTH)
         ,.REFCLK_FREQ         (REFCLK_FREQ)
         ,.TBYTE_CTL           (TBYTE_CTL)
         ,.DELAY_TYPE          (DELAY_TYPE)
         ,.PLLCLK_SRC          (PLLCLK_SRC)
         ,.GCLK_SRC            (GCLK_SRC[i*45+:45])
         ,.INIT                (INIT[i*15+:15])
         ,.RX_DATA_TYPE        (RX_DATA_TYPE[i*15+:15])
         ,.RX_DELAY_VAL        (RX_DELAY_VAL)
         ,.TX_DELAY_VAL        (TX_DELAY_VAL)
         ,.TRI_DELAY_VAL       (TRI_DELAY_VAL)
         ,.RXTX_BITSLICE_EN    (RXTX_BITSLICE_EN[i*13+:13])
         ,.TX_OUTPUT_PHASE_90  (TX_OUTPUT_PHASE_90[i*13+:13])
         ,.TRI_OUTPUT_PHASE_90 (TRI_OUTPUT_PHASE_90[i*2+:2])
         ,.NATIVE_ODELAY_BYPASS (NATIVE_ODELAY_BYPASS[i*13+:13])
         ,.FIFO_SYNC_MODE      (FIFO_SYNC_MODE[i*13+:13])
         ,.EN_OTHER_PCLK       (EN_OTHER_PCLK[i*2+:2])
         ,.EN_OTHER_NCLK       (EN_OTHER_NCLK[i*2+:2])
         ,.SERIAL_MODE         (SERIAL_MODE[i*2+:2])
         ,.RX_CLK_PHASE_P      (RX_CLK_PHASE_P[i*2+:2])
         ,.RX_CLK_PHASE_N      (RX_CLK_PHASE_N[i*2+:2])
         ,.INV_RXCLK           (INV_RXCLK[i*2+:2])
         ,.TX_GATING           (TX_GATING[i*2+:2])
         ,.RX_GATING           (RX_GATING[i*2+:2])
         ,.READ_IDLE_COUNT     (READ_IDLE_COUNT)
         ,.DIV_MODE            (DIV_MODE)
         ,.REFCLK_SRC          (REFCLK_SRC)
         ,.ROUNDING_FACTOR     (ROUNDING_FACTOR)
         ,.CTRL_CLK            (CTRL_CLK)
         ,.EN_CLK_TO_EXT_NORTH (EN_CLK_TO_EXT_NORTH[i*2+:2])
         ,.EN_CLK_TO_EXT_SOUTH (EN_CLK_TO_EXT_SOUTH[i*2+:2])
         ,.DELAY_FORMAT        (DELAY_FORMAT)
         ,.UPDATE_MODE         (UPDATE_MODE)
         ,.DCI_SRC             (DCI_SRC[i*13+:13])
         ,.EN_DYN_ODLY_MODE    (EN_DYN_ODLY_MODE[i*2+:2])
         ,.SELF_CALIBRATE      (SELF_CALIBRATE[i*2+:2])
         ,.IDLY_VT_TRACK       (IDLY_VT_TRACK[i*2+:2])
         ,.ODLY_VT_TRACK       (ODLY_VT_TRACK[i*2+:2])
         ,.QDLY_VT_TRACK       (QDLY_VT_TRACK[i*2+:2])
         ,.RXGATE_EXTEND       (RXGATE_EXTEND[i*2+:2])
         ,.SIM_DEVICE          (SIM_DEVICE)
      ) u_xiphy_byte_wrapper (
          .phy2iob_q_out_byte                  (phy2iob_q_out_byte[i*13+:13])
         ,.phy2iob_odt_out_byte                (phy2iob_odt_out_byte[i*13+:13])
         ,.phy2iob_t                           (phy2iob_t[i*13+:13])

         ,.iob2phy_d_in_byte                   (iob2phy_d_in_byte[i*13+:13])

         ,.clb2phy_fifo_clk                    (clb2phy_fifo_clk[i*13+:13])

         ,.clb2phy_ctrl_clk_upp                (clb2phy_ctrl_clk_upp[i])
         ,.clb2phy_ctrl_clk_low                (clb2phy_ctrl_clk_low[i])
         ,.clb2phy_ref_clk_upp                 (clb2phy_ref_clk_upp[i])
         ,.clb2phy_ref_clk_low                 (clb2phy_ref_clk_low[i])

         ,.clb2phy_ctrl_rst_upp                (clb2phy_ctrl_rst_upp[i])
         ,.clb2phy_ctrl_rst_low                (clb2phy_ctrl_rst_low[i])
         ,.clb2phy_txbit_tri_rst               (clb2phy_txbit_tri_rst[i*2+:2])
         ,.clb2phy_txbit_rst                   (clb2phy_txbit_rst[i*13+:13])
         ,.clb2phy_rxbit_rst                   (clb2phy_rxbit_rst[i*13+:13])

         ,.pll_clk0                            (pll_clk0[i])
         ,.pll_clk1                            (pll_clk1[i])
         ,.gclk_in                             (gclk_in)

         ,.clb2phy_wr_dq0                      (clb2phy_wr_dq0[i*8+:8])
         ,.clb2phy_wr_dq1                      (clb2phy_wr_dq1[i*8+:8])
         ,.clb2phy_wr_dq2                      (clb2phy_wr_dq2[i*8+:8])
         ,.clb2phy_wr_dq3                      (clb2phy_wr_dq3[i*8+:8])
         ,.clb2phy_wr_dq4                      (clb2phy_wr_dq4[i*8+:8])
         ,.clb2phy_wr_dq5                      (clb2phy_wr_dq5[i*8+:8])
         ,.clb2phy_wr_dq6                      (clb2phy_wr_dq6[i*8+:8])
         ,.clb2phy_wr_dq7                      (clb2phy_wr_dq7[i*8+:8])
         ,.clb2phy_wr_dq8                      (clb2phy_wr_dq8[i*8+:8])
         ,.clb2phy_wr_dq9                      (clb2phy_wr_dq9[i*8+:8])
         ,.clb2phy_wr_dq10                     (clb2phy_wr_dq10[i*8+:8])
         ,.clb2phy_wr_dq11                     (clb2phy_wr_dq11[i*8+:8])
         ,.clb2phy_wr_dq12                     (clb2phy_wr_dq12[i*8+:8])

         ,.clb2phy_t_b_upp                     (clb2phy_t_b_upp[i*4+:4])
         ,.clb2phy_t_b_low                     (clb2phy_t_b_low[i*4+:4])

         ,.clb2phy_rden_upp                    (clb2phy_rden_upp[i*4+:4])
         ,.clb2phy_rden_low                    (clb2phy_rden_low[i*4+:4])

         ,.clb2riu_addr                        (clb2riu_addr[i*6+:6])
         ,.clb2riu_wr_data                     (clb2riu_wr_data[i*16+:16])
         ,.clb2riu_wr_en                       (clb2riu_wr_en[i])
         ,.riu2clb_rd_data                     (riu2clb_rd_data[i*16+:16])
         ,.riu2clb_valid                       (riu2clb_valid_lcl[i])
         ,.clb2riu_nibble_sel_upp              (clb2riu_nibble_sel_upp[i])
         ,.clb2riu_nibble_sel_low              (clb2riu_nibble_sel_low[i])

         ,.clb2phy_fifo_rden                   (clb2phy_fifo_rden[i*13+:13])
         ,.phy2clb_fifo_empty                  (phy2clb_fifo_empty[i*13+:13])

         ,.phy2rclk_ss_divclk                  (phy2rclk_ss_divclk[i*2+1:i*2])

         ,.phy2clb_rd_dq0                      (phy2clb_rd_dq0[i*8+7:i*8])
         ,.phy2clb_rd_dq1                      (phy2clb_rd_dq1[i*8+7:i*8])
         ,.phy2clb_rd_dq2                      (phy2clb_rd_dq2[i*8+7:i*8])
         ,.phy2clb_rd_dq3                      (phy2clb_rd_dq3[i*8+7:i*8])
         ,.phy2clb_rd_dq4                      (phy2clb_rd_dq4[i*8+7:i*8])
         ,.phy2clb_rd_dq5                      (phy2clb_rd_dq5[i*8+7:i*8])
         ,.phy2clb_rd_dq6                      (phy2clb_rd_dq6[i*8+7:i*8])
         ,.phy2clb_rd_dq7                      (phy2clb_rd_dq7[i*8+7:i*8])
         ,.phy2clb_rd_dq8                      (phy2clb_rd_dq8[i*8+7:i*8])
         ,.phy2clb_rd_dq9                      (phy2clb_rd_dq9[i*8+7:i*8])
         ,.phy2clb_rd_dq10                     (phy2clb_rd_dq10[i*8+7:i*8])
         ,.phy2clb_rd_dq11                     (phy2clb_rd_dq11[i*8+7:i*8])
         ,.phy2clb_rd_dq12                     (phy2clb_rd_dq12[i*8+7:i*8])

         ,.clb2phy_idelay_rst                  (clb2phy_idelay_rst[i*13+:13])
         ,.clb2phy_idelay_ce                   (clb2phy_idelay_ce[i*13+:13])
         ,.clb2phy_idelay_inc                  (clb2phy_idelay_inc[i*13+:13])
         ,.clb2phy_idelay_ld                   (clb2phy_idelay_ld[i*13+:13])
         ,.clb2phy_idelay_cntvaluein           (clb2phy_idelay_cntvaluein[i*117+:117])
         ,.phy2clb_idelay_cntvalueout          (phy2clb_idelay_cntvalueout[i*117+:117])

         ,.clb2phy_odelay_rst                  (clb2phy_odelay_rst[i*13+:13])
         ,.clb2phy_odelay_ce                   (clb2phy_odelay_ce[i*13+:13])
         ,.clb2phy_odelay_inc                  (clb2phy_odelay_inc[i*13+:13])
         ,.clb2phy_odelay_ld                   (clb2phy_odelay_ld[i*13+:13])
         ,.clb2phy_odelay_cntvaluein           (clb2phy_odelay_cntvaluein[i*117+:117])
         ,.phy2clb_odelay_cntvalueout          (phy2clb_odelay_cntvalueout[i*117+:117])

         ,.clb2phy_t_txbit                     (clb2phy_t_txbit[i*13+:13])

         ,.clb2phy_tristate_odelay_rst         (clb2phy_tristate_odelay_rst[i*2+:2])
         ,.clb2phy_tristate_odelay_ce          (clb2phy_tristate_odelay_ce[i*2+:2])
         ,.clb2phy_tristate_odelay_inc         (clb2phy_tristate_odelay_inc[i*2+:2])
         ,.clb2phy_tristate_odelay_ld          (clb2phy_tristate_odelay_ld[i*2+:2])
         ,.clb2phy_tristate_odelay_cntvaluein  (clb2phy_tristate_odelay_cntvaluein[i*18+:18])
         ,.phy2clb_tristate_odelay_cntvalueout (phy2clb_tristate_odelay_cntvalueout[i*18+:18])

         ,.clb2phy_wrcs0_upp                   (clb2phy_wrcs0_upp[i*4+:4])
         ,.clb2phy_wrcs1_upp                   (clb2phy_wrcs1_upp[i*4+:4])
         ,.clb2phy_wrcs0_low                   (clb2phy_wrcs0_low[i*4+:4])
         ,.clb2phy_wrcs1_low                   (clb2phy_wrcs1_low[i*4+:4])
         ,.clb2phy_rdcs0_upp                   (clb2phy_rdcs0_upp[i*4+:4])
         ,.clb2phy_rdcs1_upp                   (clb2phy_rdcs1_upp[i*4+:4])
         ,.clb2phy_rdcs0_low                   (clb2phy_rdcs0_low[i*4+:4])
         ,.clb2phy_rdcs1_low                   (clb2phy_rdcs1_low[i*4+:4])

         ,.phy2clb_fixdly_rdy_upp              (phy2clb_fixdly_rdy_upp_lcl[i])
         ,.phy2clb_fixdly_rdy_low              (phy2clb_fixdly_rdy_low_lcl[i])

         ,.clk_from_ext_low                    (clk_from_ext_low[i])
         ,.clk_from_ext_upp                    (clk_from_ext_upp[i])
         ,.clk_to_ext_north_upp                (clk_to_ext_north_upp[i])
         ,.clk_to_ext_south_upp                (clk_to_ext_south_upp[i])
         ,.clk_to_ext_north_low                (clk_to_ext_north_low[i])
         ,.clk_to_ext_south_low                (clk_to_ext_south_low[i])

         ,.clb2phy_idelay_en_vtc               (clb2phy_idelay_en_vtc[i*13+:13])
         ,.clb2phy_odelay_en_vtc               (clb2phy_odelay_en_vtc[i*13+:13])
         ,.clb2phy_odelay_tristate_en_vtc      (clb2phy_odelay_tristate_en_vtc[i*2+:2])

         ,.clb2phy_dlyctl_en_vtc_upp           (clb2phy_dlyctl_en_vtc_upp[i])
         ,.clb2phy_dlyctl_en_vtc_low           (clb2phy_dlyctl_en_vtc_low[i])
         ,.phy2clb_phy_rdy_upp                 (phy2clb_phy_rdy_upp_lcl[i])
         ,.phy2clb_phy_rdy_low                 (phy2clb_phy_rdy_low_lcl[i])

         ,.clb2phy_odt_upp                     (clb2phy_odt_upp[i*7+:7])
         ,.clb2phy_odt_low                     (clb2phy_odt_low[i*7+:7])

       `ifdef BISC_CHAIN_EN
         ,.bisc_start_in                       (bisc_start_in[i])
         ,.bisc_start_out                      (bisc_start_out[i])
         ,.bisc_stop_in                        (bisc_stop_in[i])
         ,.bisc_stop_out                       (bisc_stop_out[i])
       `endif
     );

    // Skip bytes
    end else begin
      `ifdef BISC_CHAIN_EN
        assign bisc_start_out[i] = bisc_start_in[i];
        assign bisc_stop_out[i]  = bisc_stop_in[i];
      `endif
    end

    `ifdef BISC_CHAIN_EN
      // For 0th BYTE, bisc_start_in has to be driven by bisc_stop_out
      if (i == 0) begin: byte0_bisc_start
        assign bisc_start_in[i] = bisc_stop_out[i];
      end else begin: other_bytes_bisc_start
        assign bisc_start_in[i] = bisc_start_out[i-1];
      end
      
      // For the last BYTE, bisc_stop_in has to be driven by 1
      if (i == (BYTES-1)) begin: byte0_bisc_stop
        assign bisc_stop_in[i] = 1;
      end else begin: other_bytes_bisc_stop
        assign bisc_stop_in[i] = bisc_stop_out[i+1];
      end
    `endif

    assign phy2clb_fixdly_rdy_low[i] = (|RXTX_BITSLICE_EN[i*13+:6])   ? phy2clb_fixdly_rdy_low_lcl[i] : 1'b1;
    assign phy2clb_fixdly_rdy_upp[i] = (|RXTX_BITSLICE_EN[i*13+6+:7]) ? phy2clb_fixdly_rdy_upp_lcl[i] : 1'b1;
    assign phy2clb_phy_rdy_low[i]    = (|RXTX_BITSLICE_EN[i*13+:6])   ? phy2clb_phy_rdy_low_lcl[i] : 1'b1;
    assign phy2clb_phy_rdy_upp[i]    = (|RXTX_BITSLICE_EN[i*13+6+:7]) ? phy2clb_phy_rdy_upp_lcl[i] : 1'b1;
    assign riu2clb_valid[i]          = (|RXTX_BITSLICE_EN[i*13+:13])  ? riu2clb_valid_lcl[i] : 1'b1;
  end
endgenerate

endmodule



