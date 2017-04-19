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
//  /   /         Filename           : ddr4_v2_2_0_mc_arb_p.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                   ddr4_v2_2_0_mc_arb_p module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ns/100ps

module ddr4_v2_2_0_mc_arb_p #(parameter TCQ = 0.1 
)(
    input        clk
   ,input        rst

   ,output reg [3:0] winPort

   ,input  [3:0] req
);

function [1:0] findWin;
   input       last;
   input [1:0] reqs;
casez (reqs)
   2'b01: findWin = 2'b01;
   2'b10: findWin = 2'b10;
   2'b11: findWin = last ? 2'b01 : 2'b10;
   default: findWin = 2'b00;
endcase
endfunction

// regs
reg       last;
reg       last10;
reg       last32;

// wire-regs
reg [1:0] winner;
reg [1:0] w10;
reg [1:0] w32;
reg [3:0] win3210;

always @(*) begin
   w10 = findWin(last10, req[1:0]);
   w32 = findWin(last32, req[3:2]);
   winner = findWin(last, {|req[3:2], |req[1:0]});
   casez (winner)
      2'b01:   win3210 = {2'b00, w10};
      2'b10:   win3210 = {w32, 2'b00};
      default: win3210 = 4'b0000;
   endcase
end

always @(posedge clk) if (rst) begin
   last <= 1'b0;
   last10 <= 1'b0;
   last32 <= 1'b0;
   winPort <= 4'b0;
end else begin:arbing
   casez (win3210)
      4'bzzz1: begin
         last <= #TCQ 1'b0;
         last10 <= #TCQ 1'b0;
         winPort <= #TCQ win3210;
      end
      4'bzz1z: begin
         last <= #TCQ 1'b0;
         last10 <= #TCQ 1'b1;
         winPort <= #TCQ win3210;
      end
      4'bz1zz: begin
         last <= #TCQ 1'b1;
         last32 <= #TCQ 1'b0;
         winPort <= #TCQ win3210;
      end
      4'b1zzz: begin
         last <= #TCQ 1'b1;
         last32 <= #TCQ 1'b1;
         winPort <= #TCQ win3210;
      end
      default: winPort <= #TCQ 4'b0000;
   endcase
end

endmodule


