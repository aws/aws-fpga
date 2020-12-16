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
//  /   /         Filename           : ddr4_v2_2_10_cal_pi.sv
// /___/   /\     Date Last Modified : $Date: 2015/04/23 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                   ddr4_v2_2_10_cal_pi module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ns/100ps

module ddr4_v2_2_10_cal_pi # (parameter
    DBAW = 5
   ,DBYTES = 4
   ,DBYTES_PI = 4
   ,MEM = "DDR4"
   ,DM_DBI = "DM_NODBI"
   ,RL = 11
   ,WL = 9
   ,RANKS = 1
   ,RDSTAGES = 0
   ,EARLY_WR_DATA = "OFF"
   ,EXTRA_CMD_DELAY  = 0
   ,ECC           = "OFF"
   ,TCQ = 0.1
   ,SLOT0_CONFIG   = 8'b0000_0001 // Slot0 Physical configuration
   ,SLOT1_CONFIG   = 8'b0000_0000 // Slot1 Physical configuration
   ,SLOT0_FUNC_CS  = 8'b0000_0001 // Slot0 Functional chipselect
   ,SLOT1_FUNC_CS  = 8'b0000_0000 // Slot1 Functional chipselect
   
   ,REG_CTRL       = "OFF" // RDIMM register control
)(
    input clk
   ,input rst

   ,output [DBYTES*4-1:0] mc_clb2phy_rden_low
   ,output [DBYTES*4-1:0] mc_clb2phy_rden_upp
   ,output [DBYTES*7-1:0] mcal_clb2phy_odt_low
   ,output [DBYTES*7-1:0] mcal_clb2phy_odt_upp

   ,input          [1:0] casSlot
   ,input                mccasSlot2
   ,input                rdCAS
   ,input                calrdCAS
   ,input                cal_clear_fifo_rden
   ,input                mcrdCAS
   ,input                wrCAS
   ,input                calwrCAS
   ,input                mcwrCAS
   ,input [DBYTES*6-1:0]  lowCL0
   ,input [DBYTES*6-1:0]  lowCL1
   ,input [DBYTES*6-1:0]  lowCL2
   ,input [DBYTES*6-1:0]  lowCL3
   ,input [DBYTES*6-1:0]  uppCL0
   ,input [DBYTES*6-1:0]  uppCL1
   ,input [DBYTES*6-1:0]  uppCL2
   ,input [DBYTES*6-1:0]  uppCL3
   ,input [6:0]          max_rd_lat
   ,input          [1:0] winRank
   ,input          [1:0] calRank
   ,input          [1:0] mcwinRank

  

   ,output [DBYTES*13-1:0] mc_clb2phy_fifo_rden_nxt
   ,output [DBYTES*4-1:0]   mc_clb2phy_rdcs0_upp
   ,output [DBYTES*4-1:0]   mc_clb2phy_rdcs1_upp
   ,output [DBYTES*4-1:0]   mc_clb2phy_rdcs0_low
   ,output [DBYTES*4-1:0]   mc_clb2phy_rdcs1_low
   ,output [DBYTES*4-1:0]   mc_clb2phy_t_b_upp
   ,output [DBYTES*4-1:0]   mc_clb2phy_t_b_low
   ,output [DBYTES*4-1:0]   mc_clb2phy_wrcs0_upp
   ,output [DBYTES*4-1:0]   mc_clb2phy_wrcs1_upp
   ,output [DBYTES*4-1:0]   mc_clb2phy_wrcs0_low
   ,output [DBYTES*4-1:0]   mc_clb2phy_wrcs1_low

   ,output       [DBAW-1:0] rdDataAddr
   ,output                  rdDataEn
   ,output                  rdDataEnd
   ,output                  rdInj
   ,output                  rdRmw

   ,input   [DBYTES*8-1:0] mcal_DMIn_n
   ,input                  winInjTxn
   ,input                  winRmw
   ,input       [DBAW-1:0] winBuf

   ,output   [DBYTES*8-1:0] mcal_DMOut_n
   ,output [DBYTES*8*8-1:0] mcal_DQOut
   ,output            [7:0] mcal_DQSOut
   ,output       [DBAW-1:0] wrDataAddr
   ,output                  wrDataEn

   ,input [DBYTES*8*8-1:0] DQOut
   ,input   [DBYTES*8-1:0] DMOut

   ,input     [DBYTES-1:0]  cal_oe_dis_low
   ,input     [DBYTES-1:0]  cal_oe_dis_upp
   ,input                  calDone
);

(* keep = "TRUE" *) reg rst_r1;

always @(posedge clk)
  rst_r1 <= rst;
   
assign mcal_clb2phy_odt_low = 'b0;
assign mcal_clb2phy_odt_upp = 'b0;

genvar bnum;
generate

   for (bnum = 0; bnum < DBYTES; bnum++) begin:rdEn
      ddr4_v2_2_10_cal_rd_en #(
          .RANKS (RANKS)
         ,.RL  (RL)
         ,.EXTRA_CMD_DELAY      (EXTRA_CMD_DELAY)
         ,.TCQ (TCQ)
      )u_ddr_mc_rd_en_upp (
          .clk             (clk)
         ,.rst             (rst_r1)
      
         ,.mc_clb2phy_rden  (mc_clb2phy_rden_upp[bnum*4+:4])
         ,.mc_clb2phy_rdcs0 (mc_clb2phy_rdcs0_upp[bnum*4+:4])
         ,.mc_clb2phy_rdcs1 (mc_clb2phy_rdcs1_upp[bnum*4+:4])
      
         ,.casSlot         (casSlot)
         ,.mccasSlot2      (mccasSlot2)
         ,.rdCAS           (rdCAS)
         ,.calrdCAS        (calrdCAS)
         ,.mcrdCAS         (mcrdCAS)
         ,.mCL0            (uppCL0[6*bnum+:6])
         ,.mCL1            (uppCL1[6*bnum+:6])
         ,.mCL2            (uppCL2[6*bnum+:6])
         ,.mCL3            (uppCL3[6*bnum+:6])
         ,.winRank         (winRank)
         ,.calRank         (calRank)
         ,.mcwinRank       (mcwinRank)
         ,.calDone         (calDone)
      );
      
      ddr4_v2_2_10_cal_rd_en #(
          .RANKS (RANKS)
         ,.RL  (RL)
         ,.EXTRA_CMD_DELAY      (EXTRA_CMD_DELAY)
         ,.TCQ (TCQ)
      )u_ddr_mc_rd_en_low(
          .clk             (clk)
         ,.rst             (rst_r1)
      
         ,.mc_clb2phy_rden (mc_clb2phy_rden_low[bnum*4+:4])
         ,.mc_clb2phy_rdcs0 (mc_clb2phy_rdcs0_low[bnum*4+:4])
         ,.mc_clb2phy_rdcs1 (mc_clb2phy_rdcs1_low[bnum*4+:4])
      
         ,.casSlot         (casSlot)
         ,.mccasSlot2      (mccasSlot2)
         ,.rdCAS           (rdCAS)
         ,.calrdCAS        (calrdCAS)
         ,.mcrdCAS         (mcrdCAS)
         ,.mCL0            (lowCL0[6*bnum+:6])
         ,.mCL1            (lowCL1[6*bnum+:6])
         ,.mCL2            (lowCL2[6*bnum+:6])
         ,.mCL3            (lowCL3[6*bnum+:6])
         ,.winRank         (winRank)
         ,.calRank         (calRank)
         ,.mcwinRank       (mcwinRank)
         ,.calDone         (calDone)
      );
   end

endgenerate



ddr4_v2_2_10_cal_read #(
    .DBYTES            (DBYTES)
   ,.DBAW             (DBAW)
   ,.RL               (RL)
   ,.EXTRA_CMD_DELAY  (EXTRA_CMD_DELAY)
   ,.TCQ              (TCQ)
) u_ddr_mc_read (
    .clk                  (clk)
   ,.rst                  (rst_r1)

   ,.mc_clb2phy_fifo_rden_nxt (mc_clb2phy_fifo_rden_nxt)
   ,.rdDataAddr           (rdDataAddr)
   ,.rdDataEn             (rdDataEn)
   ,.rdDataEnd            (rdDataEnd)
   ,.rdInj                (rdInj)
   ,.rdRmw                (rdRmw)
   
   ,.mcrdCAS              (mcrdCAS)
   ,.calrdCAS             (calrdCAS)
   ,.cal_clear_fifo_rden  (cal_clear_fifo_rden)
   ,.calDone              (calDone)
   ,.winInjTxn            (winInjTxn)
   ,.winRmw               (winRmw)
   ,.winBuf               (winBuf)
   ,.max_rd_lat           (max_rd_lat)
); 
   

ddr4_v2_2_10_cal_write #(     
    .DBYTES  (DBYTES)
   ,.DBAW   (DBAW)
   ,.MEM    (MEM)
   ,.RANKS  (RANKS)
   ,.DM_DBI (DM_DBI)
   ,.WL     (WL)
   ,.EARLY_WR_DATA (EARLY_WR_DATA)
   ,.EXTRA_CMD_DELAY      (EXTRA_CMD_DELAY)
   ,.ECC                  (ECC)
   ,.TCQ    (TCQ)
)u_ddr_mc_write(
    .clk (clk)
   ,.rst (rst_r1)

   ,.mc_clb2phy_wrcs0_upp (mc_clb2phy_wrcs0_upp)
   ,.mc_clb2phy_wrcs1_upp (mc_clb2phy_wrcs1_upp)
   ,.mc_clb2phy_wrcs0_low (mc_clb2phy_wrcs0_low)
   ,.mc_clb2phy_wrcs1_low (mc_clb2phy_wrcs1_low)
   ,.mc_clb2phy_t_b_upp   (mc_clb2phy_t_b_upp)
   ,.mc_clb2phy_t_b_low   (mc_clb2phy_t_b_low)
   ,.mcal_DMOut_n         (mcal_DMOut_n)
   ,.mcal_DQOut           (mcal_DQOut)
   ,.mcal_DQSOut          (mcal_DQSOut)
   ,.wrDataAddr           (wrDataAddr)
   ,.wrDataEn             (wrDataEn)

   ,.casSlot              (casSlot)
   ,.mccasSlot2           (mccasSlot2)
   ,.winBuf               (winBuf)
   ,.winRank              (winRank)
   ,.calRank              (calRank)
   ,.mcwinRank            (mcwinRank)
   ,.wrCAS                (wrCAS)
   ,.calwrCAS             (calwrCAS)
   ,.mcwrCAS              (mcwrCAS)
   ,.DQOut                (DQOut)
   ,.DMOut                (DMOut)
   ,.cal_oe_dis_low       (cal_oe_dis_low)
   ,.cal_oe_dis_upp       (cal_oe_dis_upp)
   ,.calDone              (calDone)
);

endmodule


