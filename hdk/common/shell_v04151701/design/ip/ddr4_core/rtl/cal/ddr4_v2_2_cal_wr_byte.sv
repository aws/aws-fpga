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
//  /   /         Filename           : ddr4_v2_2_0_cal_wr_byte.sv
// /___/   /\     Date Last Modified : $Date: 2015/04/23 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                   ddr4_v2_2_0_cal_wr_byte module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ns/100ps

module ddr4_v2_2_0_cal_wr_byte #
  (
   parameter TCQ = 0.1
   )
   (
    input clk
   ,input rst

   ,output  [7:0] mcal_DMOut_n
   ,output [63:0] mcal_DQOut

   ,input [63:0] DQOut
   ,input  [7:0] DMOut
   ,input        wrDataVal
   ,input  [2:1] wrOffset
);

genvar bNum;
generate
   for (bNum = 0; bNum <= 7; bNum++) begin:genBit
      ddr4_v2_2_0_cal_wr_bit #
        (
         .TCQ   (TCQ)
         )
        u_ddr_mc_wr_bit (
          .clk (clk)
         ,.rst (rst)

         ,.mcal_DOut (mcal_DQOut[bNum*8+:8])

         ,.DQOut     (DQOut[bNum*8+:8])
         ,.wrDataVal (wrDataVal)
         ,.wrOffset  (wrOffset)
      );
   end
endgenerate

ddr4_v2_2_0_cal_wr_bit #
  (
   .TCQ   (TCQ)
   )
 
  u_ddr_mc_wr_dm (
    .clk (clk)
   ,.rst (rst)

   ,.mcal_DOut (mcal_DMOut_n)

   ,.DQOut     (DMOut)
   ,.wrDataVal (wrDataVal)
   ,.wrOffset  (wrOffset)
);

endmodule


