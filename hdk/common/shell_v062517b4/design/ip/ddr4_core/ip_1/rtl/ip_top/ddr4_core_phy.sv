

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
// DO NOT MODIFY THIS FILE.
//
//
// IP VLNV: xilinx.com:ip:mig_ddrx_phy:2.1
// IP Revision: 1
//******************************************************************************/
//   ____  ____
//  /   /\/   /
// /___/  \  /    Vendor             : Xilinx
// \   \   \/     Version            : 2.1
//  \   \         Application        : MIG
//  /   /         Filename           : ddr4_core_phy.sv
// /___/   /\     Date Last Modified : $Date: 2017/02/27 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4_SDRAM
// Purpose          :
//                   ddr4_core_phy module
// Reference        :
// Revision History :
//*****************************************************************************


`timescale 1ns/1ps

(* CHECK_LICENSE_TYPE = "phy1,dummy_model,{}" *)
(* DowngradeIPIdentifiedWarnings = "yes" *)
(* PROBE_PROHIBIT="TRUE" *)

module ddr4_core_phy (
  input                                           sys_clk_p,
  input                                           sys_clk_n,
  input                                           mmcm_lock,
  input                                           pllGate,
  input                                           div_clk,
  input                                           div_clk_rst,
  input                                           riu_clk,
  input                                           riu_clk_rst,
  output                                          pll_lock,
  output                                          sys_clk_in,
  output                                          mmcm_clk_in,
  output                                          ddr4_act_n,
  output  [16:0]                                  ddr4_adr,
  output  [1:0]                                   ddr4_ba,
  output  [1:0]                                   ddr4_bg,
  output  [0:0]                                   ddr4_c,
  output                                          ddr4_parity,
  output  [0:0]                                   ddr4_cke,
  output  [0:0]                                   ddr4_odt,
  output  [0:0]                                   ddr4_cs_n,
  output  [0:0]                                   ddr4_ck_t,
  output  [0:0]                                   ddr4_ck_c,
  output                                          ddr4_reset_n,
  inout  [8:0]                                     ddr4_dm_dbi_n,
  inout  [71:0]                                    ddr4_dq,
  inout  [17:0]                                    ddr4_dqs_c,
  inout  [17:0]                                    ddr4_dqs_t,
  input  [7:0]                                 mcal_CK_t,
  input  [7:0]                                 mcal_CK_c,
  input  [7 : 0]                                  mcal_ACT_n,
  input  [7:0]                                    mcal_CAS_n,
  input  [7:0]                                    mcal_RAS_n,
  input  [7:0]                                    mcal_WE_n,
  input  [135:0]                                  mcal_ADR,
  input  [15:0]                                   mcal_BA,
  input  [15:0]                                    mcal_BG,
  input  [7:0]                                  mcal_C,
  input  [7:0]                                    mcal_CKE,
  input  [7:0]                                    mcal_CS_n,
  input  [7:0]                                    mcal_ODT,
  input  [7 : 0]                                  mcal_PAR,

  input  [71:0]                                     ch0_mcal_DMOut_n,
  input  [575:0]                                 ch0_mcal_DQOut,
  input  [7:0]                                    ch0_mcal_DQSOut,
  input  [35:0]                                     ch0_mcal_clb2phy_rden_upp,
  input  [35:0]                                     ch0_mcal_clb2phy_rden_low,
  input  [35:0]                                     ch0_mcal_clb2phy_wrcs0_upp,
  input  [35:0]                                     ch0_mcal_clb2phy_wrcs1_upp,
  input  [35:0]                                     ch0_mcal_clb2phy_wrcs0_low,
  input  [35:0]                                     ch0_mcal_clb2phy_wrcs1_low,
  input  [35:0]                                     ch0_mcal_clb2phy_rdcs0_upp,
  input  [35:0]                                     ch0_mcal_clb2phy_rdcs1_upp,
  input  [35:0]                                     ch0_mcal_clb2phy_rdcs0_low,
  input  [35:0]                                     ch0_mcal_clb2phy_rdcs1_low,
  input  [62:0]                                     ch0_mcal_clb2phy_odt_upp,
  input  [62:0]                                     ch0_mcal_clb2phy_odt_low,
  input  [35:0]                                     ch0_mcal_clb2phy_t_b_low,
  input  [35:0]                                     ch0_mcal_clb2phy_t_b_upp,

  input  [62:0]                                     mcal_rd_vref_value,

  input  [71:0]                                     ch1_mcal_DMOut_n,
  input  [575:0]                                   ch1_mcal_DQOut,
  input  [7:0]                                    ch1_mcal_DQSOut,
  input  [35:0]                                     ch1_mcal_clb2phy_rden_upp,
  input  [35:0]                                     ch1_mcal_clb2phy_rden_low,
  input  [35:0]                                     ch1_mcal_clb2phy_wrcs0_upp,
  input  [35:0]                                     ch1_mcal_clb2phy_wrcs1_upp,
  input  [35:0]                                     ch1_mcal_clb2phy_wrcs0_low,
  input  [35:0]                                     ch1_mcal_clb2phy_wrcs1_low,
  input  [35:0]                                     ch1_mcal_clb2phy_rdcs0_upp,
  input  [35:0]                                     ch1_mcal_clb2phy_rdcs1_upp,
  input  [35:0]                                     ch1_mcal_clb2phy_rdcs0_low,
  input  [35:0]                                     ch1_mcal_clb2phy_rdcs1_low,
  input  [62:0]                                     ch1_mcal_clb2phy_odt_upp,
  input  [62:0]                                     ch1_mcal_clb2phy_odt_low,
  input  [35:0]                                     ch1_mcal_clb2phy_t_b_low,
  input  [35:0]                                     ch1_mcal_clb2phy_t_b_upp,

  input  [116:0]                                   ch0_mcal_clb2phy_fifo_rden,
  input  [116:0]                                   ch1_mcal_clb2phy_fifo_rden,

  output [71:0]                                    mcal_DMIn_n,
  output [575:0]                                  mcal_DQIn,

  output 	                                      phy_ready_riuclk,
  output 	                                      bisc_complete_riuclk,
  output [7:0]                                    phy2clb_rd_dq_bits,
  input  [8:0]                                    bisc_byte,

  input [7:0]                                     cal_RESET_n,
  input	                                          en_vtc_riuclk,
  input	                                          ub_rst_out_riuclk,
// PHY <> cal RIU
  output  [15:0]                                  riu2clb_vld_read_data,
  output [7:0]                                    riu_nibble_8,
  output 	[5:0]                                 riu_addr_cal,
  output [20-1:0]                                 riu2clb_valid_riuclk, // max number of bytes possible 
   
  input                                           io_addr_strobe_clb2riu_riuclk,
  input [31:0]                                    io_address_riuclk,
  input [31:0]                                    io_write_data_riuclk,
  input                                           io_write_strobe_riuclk,

  output [19:0]                                   phy2clb_fixdly_rdy_low_riuclk,
  output [19:0]                                   phy2clb_fixdly_rdy_upp_riuclk,
  output [19:0]                                   phy2clb_phy_rdy_upp_riuclk,
  output [19:0]                                   phy2clb_phy_rdy_low_riuclk,
  output  [511:0]                                 dbg_bus 
);


ddr4_core_phy_ddr4
   inst (
    .sys_clk_p                  (sys_clk_p),
    .sys_clk_n                  (sys_clk_n),
    .mmcm_lock                  (mmcm_lock),
    .pllGate                    (pllGate),
    .div_clk                    (div_clk),
    .div_clk_rst                (div_clk_rst),
    .riu_clk                    (riu_clk),
    .riu_clk_rst                (riu_clk_rst),
    .pll_lock                   (pll_lock),
    .sys_clk_in                 (sys_clk_in),
    .mmcm_clk_in                (mmcm_clk_in),
    .ddr4_act_n                 (ddr4_act_n),
    .ddr4_adr                   (ddr4_adr),
    .ddr4_ba                    (ddr4_ba),
    .ddr4_bg                    (ddr4_bg),
    .ddr4_c                     (ddr4_c),
    .ddr4_parity                (ddr4_parity),
    .ddr4_cke                   (ddr4_cke),
    .ddr4_odt                   (ddr4_odt),
    .ddr4_cs_n                  (ddr4_cs_n),
    .ddr4_ck_t                  (ddr4_ck_t),
    .ddr4_ck_c                  (ddr4_ck_c),
    .ddr4_reset_n               (ddr4_reset_n),
    .ddr4_dm_dbi_n              (ddr4_dm_dbi_n),
    .ddr4_dq                    (ddr4_dq),
    .ddr4_dqs_c                 (ddr4_dqs_c),
    .ddr4_dqs_t                 (ddr4_dqs_t),

    .mcal_CK_t                  (mcal_CK_t),
    .mcal_CK_c                  (mcal_CK_c),
    .mcal_ACT_n                 (mcal_ACT_n),
    .mcal_RAS_n                 (mcal_RAS_n),
    .mcal_CAS_n                 (mcal_CAS_n),
    .mcal_WE_n                  (mcal_WE_n),
    .mcal_ADR                   (mcal_ADR),
    .mcal_BA                    (mcal_BA),
    .mcal_BG                    (mcal_BG),
    .mcal_C                     (mcal_C), 
    .mcal_CKE                   (mcal_CKE),
    .mcal_CS_n                  (mcal_CS_n),
    .mcal_ODT                   (mcal_ODT),
    .mcal_PAR                   (mcal_PAR),

    .ch0_mcal_DMOut_n                (ch0_mcal_DMOut_n),
    .ch0_mcal_DQOut                  (ch0_mcal_DQOut),
    .ch0_mcal_DQSOut                 (ch0_mcal_DQSOut),
    .ch0_mcal_clb2phy_rden_upp       (ch0_mcal_clb2phy_rden_upp),
    .ch0_mcal_clb2phy_rden_low       (ch0_mcal_clb2phy_rden_low),
    .ch0_mcal_clb2phy_wrcs0_upp      (ch0_mcal_clb2phy_wrcs0_upp),
    .ch0_mcal_clb2phy_wrcs1_upp      (ch0_mcal_clb2phy_wrcs1_upp),
    .ch0_mcal_clb2phy_wrcs0_low      (ch0_mcal_clb2phy_wrcs0_low),
    .ch0_mcal_clb2phy_wrcs1_low      (ch0_mcal_clb2phy_wrcs1_low),
    .ch0_mcal_clb2phy_rdcs0_upp      (ch0_mcal_clb2phy_rdcs0_upp),
    .ch0_mcal_clb2phy_rdcs1_upp      (ch0_mcal_clb2phy_rdcs1_upp),
    .ch0_mcal_clb2phy_rdcs0_low      (ch0_mcal_clb2phy_rdcs0_low),
    .ch0_mcal_clb2phy_rdcs1_low      (ch0_mcal_clb2phy_rdcs1_low),
    .ch0_mcal_clb2phy_odt_upp        (ch0_mcal_clb2phy_odt_upp),
    .ch0_mcal_clb2phy_odt_low        (ch0_mcal_clb2phy_odt_low),
    .ch0_mcal_clb2phy_t_b_upp        (ch0_mcal_clb2phy_t_b_upp),
    .ch0_mcal_clb2phy_t_b_low        (ch0_mcal_clb2phy_t_b_low),

     .mcal_rd_vref_value              (mcal_rd_vref_value),

    .ch1_mcal_DMOut_n                (ch1_mcal_DMOut_n),
    .ch1_mcal_DQOut                  (ch1_mcal_DQOut),
    .ch1_mcal_DQSOut                 (ch1_mcal_DQSOut),
    .ch1_mcal_clb2phy_rden_upp       (ch1_mcal_clb2phy_rden_upp),
    .ch1_mcal_clb2phy_rden_low       (ch1_mcal_clb2phy_rden_low),
    .ch1_mcal_clb2phy_wrcs0_upp      (ch1_mcal_clb2phy_wrcs0_upp),
    .ch1_mcal_clb2phy_wrcs1_upp      (ch1_mcal_clb2phy_wrcs1_upp),
    .ch1_mcal_clb2phy_wrcs0_low      (ch1_mcal_clb2phy_wrcs0_low),
    .ch1_mcal_clb2phy_wrcs1_low      (ch1_mcal_clb2phy_wrcs1_low),
    .ch1_mcal_clb2phy_rdcs0_upp      (ch1_mcal_clb2phy_rdcs0_upp),
    .ch1_mcal_clb2phy_rdcs1_upp      (ch1_mcal_clb2phy_rdcs1_upp),
    .ch1_mcal_clb2phy_rdcs0_low      (ch1_mcal_clb2phy_rdcs0_low),
    .ch1_mcal_clb2phy_rdcs1_low      (ch1_mcal_clb2phy_rdcs1_low),
    .ch1_mcal_clb2phy_odt_upp        (ch1_mcal_clb2phy_odt_upp),
    .ch1_mcal_clb2phy_odt_low        (ch1_mcal_clb2phy_odt_low),
    .ch1_mcal_clb2phy_t_b_upp        (ch1_mcal_clb2phy_t_b_upp),
    .ch1_mcal_clb2phy_t_b_low        (ch1_mcal_clb2phy_t_b_low),

    .ch0_mcal_clb2phy_fifo_rden      (ch0_mcal_clb2phy_fifo_rden),
    .ch1_mcal_clb2phy_fifo_rden      (ch1_mcal_clb2phy_fifo_rden),

    .mcal_DMIn_n                     (mcal_DMIn_n),
    .mcal_DQIn                       (mcal_DQIn),

    .phy_ready_riuclk                (phy_ready_riuclk),
    .bisc_complete_riuclk            (bisc_complete_riuclk),
    .phy2clb_rd_dq_bits              (phy2clb_rd_dq_bits),
    .bisc_byte                       (bisc_byte),

    .cal_RESET_n                     (cal_RESET_n),
    .en_vtc_riuclk                   (en_vtc_riuclk),
    .ub_rst_out_riuclk               (ub_rst_out_riuclk),
    .riu2clb_vld_read_data           (riu2clb_vld_read_data),
    .riu_nibble_8                    (riu_nibble_8),
    .riu_addr_cal                    (riu_addr_cal),
    .riu2clb_valid_riuclk            (riu2clb_valid_riuclk),

    .io_addr_strobe_clb2riu_riuclk   (io_addr_strobe_clb2riu_riuclk),
    .io_address_riuclk               (io_address_riuclk),
    .io_write_data_riuclk            (io_write_data_riuclk),
    .io_write_strobe_riuclk          (io_write_strobe_riuclk),

    .phy2clb_fixdly_rdy_low_riuclk   (phy2clb_fixdly_rdy_low_riuclk),
    .phy2clb_fixdly_rdy_upp_riuclk   (phy2clb_fixdly_rdy_upp_riuclk),
    .phy2clb_phy_rdy_low_riuclk      (phy2clb_phy_rdy_low_riuclk),
    .phy2clb_phy_rdy_upp_riuclk      (phy2clb_phy_rdy_upp_riuclk),
    .dbg_bus                         (dbg_bus)
  );
endmodule
