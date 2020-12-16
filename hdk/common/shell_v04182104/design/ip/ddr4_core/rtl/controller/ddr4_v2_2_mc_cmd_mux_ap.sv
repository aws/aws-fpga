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
//  /   /         Filename           : ddr4_v2_2_10_mc_cmd_mux_ap.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                   ddr4_v2_2_10_mc_cmd_mux_ap module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ns/100ps

module ddr4_v2_2_10_mc_cmd_mux_ap # (parameter
    ABITS = 18
   ,RKBITS = 2
   ,RANK_SLAB = 4
   ,LR_WIDTH = 1
)(
    output reg       [1:0] winBank
   ,output reg       [1:0] winGroup
   ,output reg [LR_WIDTH-1:0] winLRank
   ,output reg   [RKBITS-1:0] winRank
   ,output reg [ABITS-1:0] winRow

   ,input         [3:0] sel
   ,input         [7:0] cmdBank
   ,input         [7:0] cmdGroup
   ,input [4*LR_WIDTH-1:0] cmdLRank
   ,input   [RKBITS*4-1:0] cmdRank
   ,input [4*ABITS-1:0] cmdRow
);

always @(*) casez (sel)
   4'bzzz1: begin
      winBank = cmdBank[1:0];
      winGroup = cmdGroup[1:0];
      winLRank = cmdLRank[0*LR_WIDTH+:LR_WIDTH];
      winRank = cmdRank[RKBITS*1-1:RKBITS*0];
      winRow = cmdRow[0*ABITS+:ABITS];
   end
   4'bzz1z: begin
      winBank = cmdBank[3:2];
      winGroup = cmdGroup[3:2];
      winLRank = cmdLRank[1*LR_WIDTH+:LR_WIDTH];
      winRank = cmdRank[RKBITS*2-1:RKBITS*1];
      winRow = cmdRow[1*ABITS+:ABITS];
   end
   4'bz1zz: begin
      winBank = cmdBank[5:4];
      winGroup = cmdGroup[5:4];
      winLRank = cmdLRank[2*LR_WIDTH+:LR_WIDTH];
      winRank = cmdRank[RKBITS*3-1:RKBITS*2];
      winRow = cmdRow[2*ABITS+:ABITS];
   end
   4'b1zzz: begin
      winBank = cmdBank[7:6];
      winGroup = cmdGroup[7:6];
      winLRank = cmdLRank[3*LR_WIDTH+:LR_WIDTH];
      winRank = cmdRank[RKBITS*4-1:RKBITS*3];
      winRow = cmdRow[3*ABITS+:ABITS];
   end
   default: begin
      winBank = 'x;
      winGroup = 'x;
      winLRank = 'x;
      winRank = 'x;
      winRow = 'x;
   end
endcase

endmodule


