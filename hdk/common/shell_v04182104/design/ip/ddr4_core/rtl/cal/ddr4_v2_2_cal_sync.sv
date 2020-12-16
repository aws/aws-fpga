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
//  /   /         Filename           : ddr4_v2_2_10_cal_sync.sv
// /___/   /\     Date Last Modified : $Date: 2015/01/22 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                   ddr4_v2_2_10_cal_sync module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ps/1ps

module ddr4_v2_2_10_cal_sync #(
   parameter        SYNC_MTBF               = 2
   ,parameter       WIDTH                   = 8
   ,parameter       INSERT_DELAY            = 0
   ,parameter       MAX_DELAY               = 3000
   ,parameter       TCQ                     = 100
)(
   input                          clk
   ,input [WIDTH-1:0]             data_in
   ,output [WIDTH-1:0]            data_out
);

genvar wd;
generate
  for (wd=0; wd<WIDTH; wd=wd+1) begin : SYNC
    (* dont_touch = "true" *) (* ASYNC_REG = "TRUE" *) reg [SYNC_MTBF-1:0] sync_reg;

    reg data_in_delayed = 1'b0;

    wire sync_in = INSERT_DELAY ? data_in_delayed : data_in[wd];

    assign data_out[wd] = sync_reg[SYNC_MTBF-1];

    always @(posedge clk) begin
      sync_reg <= #TCQ {sync_reg[0+:SYNC_MTBF-1], sync_in};
    end

    //synopsys translate_off
      integer DELAY_VAL = $urandom_range(0,MAX_DELAY);

      always @(*) data_in_delayed <= #(DELAY_VAL) data_in[wd];
    //synopsys translate_on

  end
endgenerate

endmodule

