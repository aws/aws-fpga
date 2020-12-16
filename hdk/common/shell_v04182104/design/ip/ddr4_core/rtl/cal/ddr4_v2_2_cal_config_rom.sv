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
//  /   /         Filename           : ddr4_v2_2_10_cal_config_rom.sv
// /___/   /\     Date Last Modified : $Date: 2015/04/23 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                   ddr4_v2_2_10_cal_config_rom module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ps/1ps
 
module ddr4_v2_2_10_cal_config_rom #
  ( parameter MEM0 = 32'h0000,
    parameter MEM1 = 32'h0000,
    parameter MEM2 = 32'h0000,
    parameter MEM3 = 32'h0000,
    parameter MEM4 = 32'h0000,
    parameter MEM5 = 32'h0000,
    parameter MEM6 = 32'h0000,
    parameter MEM7 = 32'h0000,
    parameter MEM8 = 32'h0000,
    parameter MEM9 = 32'h0000,
    parameter MEM10 = 32'h0000,
    parameter MEM11 = 32'h0000,
    parameter MEM12 = 32'h0000,
    parameter MEM13 = 32'h0000,
    parameter MEM14 = 32'h0000,
    parameter MEM15 = 32'h0000,
    parameter MEM16 = 32'h0000,
    parameter MEM17 = 32'h0000,
    parameter MEM18 = 32'h0000,
    parameter MEM19 = 32'h0000,
    parameter MEM20 = 32'h0000,
    parameter MEM21 = 32'h0000,
    parameter MEM22 = 32'h0000,
    parameter MEM23 = 32'h0000,
    parameter MEM24 = 32'h0000,
    parameter MEM25 = 32'h0000,
    parameter MEM26 = 32'h0000,
    parameter MEM27 = 32'h0000,
    parameter MEM28 = 32'h0000,
    parameter MEM29 = 32'h0000,
    parameter MEM30 = 32'h0000,
    parameter MEM31 = 32'h0000,
    parameter MEM32 = 32'h0000,
    parameter MEM33 = 32'h0000,
    parameter MEM34 = 32'h0000,
    parameter MEM35 = 32'h0000,
    parameter MEM36 = 32'h0000,
    parameter MEM37 = 32'h0000,
    parameter MEM38 = 32'h0000,
    parameter MEM39 = 32'h0000,
    parameter MEM40 = 32'h0000,
    parameter MEM41 = 32'h0000,
    parameter MEM42 = 32'h0000,
    parameter MEM43 = 32'h0000,
    parameter MEM44 = 32'h0000,
    parameter MEM45 = 32'h0000,
    parameter MEM46 = 32'h0000,
    parameter MEM47 = 32'h0000,
    parameter MEM48 = 32'h0000,
    parameter MEM49 = 32'h0000,
    parameter MEM50 = 32'h0000,
    parameter MEM51 = 32'h0000,
    parameter MEM52 = 32'h0000,
    parameter MEM53 = 32'h0000,
    parameter MEM54 = 32'h0000,
    parameter MEM55 = 32'h0000,
    parameter MEM56 = 32'h0000,
    parameter MEM57 = 32'h0000,
    parameter MEM58 = 32'h0000,
    parameter MEM59 = 32'h0000,
    parameter MEM60 = 32'h0000,
    parameter MEM61 = 32'h0000,
    parameter MEM62 = 32'h0000,
    parameter MEM63 = 32'h0000,
    parameter DATA_WIDTH = 32,
    parameter ADDR_WIDTH = 6 , // DEPTH = 64, ADDR_WIDTH = 6; 
    parameter DEPTH = 64
    

  )
  (

   input                        clk_i,
   input  [ADDR_WIDTH - 1:0]                      rd_addr,
   output reg [DATA_WIDTH -1:0] dout_o
  );
   





    wire   [DATA_WIDTH - 1:0]  mem[0:DEPTH - 1]; 
    reg    [ADDR_WIDTH - 1:0]  rd_addr_reg;
/*
parameter mif_file = "stimulus.mif";  
initial
begin
    $readmemb(mif_file,mem, 0, DATA_WIDTH);
end
*/

// content formats
//        {burst length, instruction, address}
assign mem[0]  = MEM0; 
assign mem[1]  = MEM1; 
assign mem[2]  = MEM2; 
assign mem[3]  = MEM3; 
assign mem[4]  = MEM4; 
assign mem[5]  = MEM5; 
assign mem[6]  = MEM6; 
assign mem[7]  = MEM7; 
assign mem[8]  = MEM8; 
assign mem[9]  = MEM9; 
assign mem[10] = MEM10;
assign mem[11] = MEM11;
assign mem[12] = MEM12;
assign mem[13] = MEM13;
assign mem[14] = MEM14;
assign mem[15] = MEM15;
assign mem[16] = MEM16;
assign mem[17] = MEM17;
assign mem[18] = MEM18;
assign mem[19] = MEM19;
assign mem[20] = MEM20;
assign mem[21] = MEM21;
assign mem[22] = MEM22;
assign mem[23] = MEM23;
assign mem[24] = MEM24;
assign mem[25] = MEM25;
assign mem[26] = MEM26;
assign mem[27] = MEM27;
assign mem[28] = MEM28;
assign mem[29] = MEM29;
assign mem[30] = MEM30;
assign mem[31] = MEM31;
assign mem[32] = MEM32;
assign mem[33] = MEM33;
assign mem[34] = MEM34;
assign mem[35] = MEM35;
assign mem[36] = MEM36;
assign mem[37] = MEM37;
assign mem[38] = MEM38;
assign mem[39] = MEM39;
assign mem[40] = MEM40;
assign mem[41] = MEM41;
assign mem[42] = MEM42;
assign mem[43] = MEM43;
assign mem[44] = MEM44;
assign mem[45] = MEM45;
assign mem[46] = MEM46;
assign mem[47] = MEM47;
assign mem[48] = MEM48;
assign mem[49] = MEM49;
assign mem[50] = MEM50;
assign mem[51] = MEM51;
assign mem[52] = MEM52;
assign mem[53] = MEM53;
assign mem[54] = MEM54;
assign mem[55] = MEM55;
assign mem[56] = MEM56;
assign mem[57] = MEM57;
assign mem[58] = MEM58;
assign mem[59] = MEM59;
assign mem[60] = MEM60;
assign mem[61] = MEM61;
assign mem[62] = MEM62;
assign mem[63] = MEM63;


always @ (posedge clk_i)
begin
  dout_o  <= mem[rd_addr];
end

endmodule

