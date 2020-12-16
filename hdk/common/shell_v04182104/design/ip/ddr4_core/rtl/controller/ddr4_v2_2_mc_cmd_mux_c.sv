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
//  /   /         Filename           : ddr4_v2_2_10_mc_cmd_mux_c.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                   ddr4_v2_2_10_mc_cmd_mux_c module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ns/100ps

module ddr4_v2_2_10_mc_cmd_mux_c # (parameter
    COLBITS = 10
   ,RKBITS = 2
   ,RANK_SLAB = 4
   ,LR_WIDTH = 1
   ,DBAW = 5
)(
    output reg         [1:0] winBank
   ,output reg    [DBAW-1:0] winBuf
   ,output reg               winInjTxn
   ,output reg               winRmw
   ,output reg               winAP
   ,output reg [COLBITS-1:0] winCol
   ,output reg         [1:0] winGroup
   ,output reg [LR_WIDTH-1:0]winLRank
   ,output reg  [RKBITS-1:0] winRank
   ,output reg               winSize

   ,input           [7:0] cmdBank
   ,input    [DBAW*4-1:0] cmdBuf
   ,input           [3:0] cmdInjTxn
   ,input           [3:0] cmdRmw
   ,input           [3:0] cmdAP
   ,input [4*COLBITS-1:0] cmdCol // spyglass disable W498
   ,input           [7:0] cmdGroup
   ,input [4*LR_WIDTH-1:0]cmdLRank
   ,input  [RKBITS*4-1:0] cmdRank
   ,input           [3:0] cmdSize

   ,input  [3:0] sel
);

always @(*) casez (sel)
   4'bzzz1: begin
      winBank = cmdBank[0*2+:2];
      winBuf = cmdBuf[0*DBAW+:DBAW];
      winInjTxn = cmdInjTxn[0];
      winRmw    = cmdRmw[0];
      winAP = cmdAP[0] & ~cmdRmw[0];
      winCol = {cmdCol[(0*COLBITS+3)+:COLBITS-3], cmdSize[0] ? 1'b0 : cmdCol[0*COLBITS+2], 1'b0, cmdInjTxn[0]};
      winGroup = cmdGroup[0*2+:2];
      winLRank = cmdLRank[0*LR_WIDTH+:LR_WIDTH];
      winRank = cmdRank[0*RKBITS+:RKBITS];
      winSize = cmdSize[0];
   end
   4'bzz1z: begin
      winBank = cmdBank[1*2+:2];
      winBuf = cmdBuf[1*DBAW+:DBAW];
      winInjTxn = cmdInjTxn[1];
      winRmw    = cmdRmw[1];
      winAP = cmdAP[1] & ~cmdRmw[1];
      winCol = {cmdCol[(1*COLBITS+3)+:COLBITS-3], cmdSize[1] ? 1'b0 : cmdCol[1*COLBITS+2], 1'b0, cmdInjTxn[1]};
      winGroup = cmdGroup[1*2+:2];
      winLRank = cmdLRank[1*LR_WIDTH+:LR_WIDTH];
      winRank = cmdRank[1*RKBITS+:RKBITS];
      winSize = cmdSize[1];
   end
   4'bz1zz: begin
      winBank = cmdBank[2*2+:2];
      winBuf = cmdBuf[2*DBAW+:DBAW];
      winInjTxn = cmdInjTxn[2];
      winRmw    = cmdRmw[2];
      winAP = cmdAP[2] & ~cmdRmw[2];
      winCol = {cmdCol[(2*COLBITS+3)+:COLBITS-3], cmdSize[2] ? 1'b0 : cmdCol[2*COLBITS+2], 1'b0, cmdInjTxn[2]};
      winGroup = cmdGroup[2*2+:2];
      winLRank = cmdLRank[2*LR_WIDTH+:LR_WIDTH];
      winRank = cmdRank[2*RKBITS+:RKBITS];
      winSize = cmdSize[2];
   end
   4'b1zzz: begin
      winBank = cmdBank[3*2+:2];
      winBuf = cmdBuf[3*DBAW+:DBAW];
      winInjTxn = cmdInjTxn[3];
      winRmw    = cmdRmw[3];
      winAP = cmdAP[3] & ~cmdRmw[3];
      winCol = {cmdCol[(3*COLBITS+3)+:COLBITS-3], cmdSize[3] ? 1'b0 : cmdCol[3*COLBITS+2], 1'b0, cmdInjTxn[3]};
      winGroup = cmdGroup[3*2+:2];
      winLRank = cmdLRank[3*LR_WIDTH+:LR_WIDTH];
      winRank = cmdRank[3*RKBITS+:RKBITS];
      winSize = cmdSize[3];
   end
   default: begin
      winBank = 'x;
      winBuf = 'x;
      winInjTxn = 1'b0;
      winRmw    = 1'b0;
      winAP = 1'bx;
      winCol = 'x;
      winGroup = 'x;
      winLRank = 'x;
      winRank = 'x;
      winSize = 'x;
   end
endcase

endmodule


