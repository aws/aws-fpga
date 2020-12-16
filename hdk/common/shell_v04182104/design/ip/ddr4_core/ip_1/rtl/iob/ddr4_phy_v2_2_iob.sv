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
//  /   /         Filename           : ddr4_phy_v2_2_0_iob.sv
// /___/   /\     Date Last Modified : $Date: 2015/04/23 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                   ddr4_phy_v2_2_0_iob module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ps/1ps

// The ddr4_phy_v2_2_0_iob represents the IO part of the design. It encompasses all the bytes in
// the design. This module instantiates all the bytes through a generate statement.
// See the ddr4_phy_v2_2_0_iob_byte.v module for explanation of the parameter meaning.

module ddr4_phy_v2_2_0_iob # (
    parameter integer BYTES              = 7
   ,parameter [39*BYTES-1:0] IOBTYPE     = {(BYTES*39){1'b0}}
   ,parameter DQS_BIAS                   = "TRUE"
   ,parameter DRAM_TYPE                  = "DDR3"
   ,parameter EN_LVAUX                   = "FALSE"
   ,parameter BANK_TYPE                  = "HP_IO"
   ,parameter USE_DYNAMIC_DCI            = 1
)(
    output [BYTES*13-1:0] iob2phy_d_in_byte

   ,inout [BYTES*13-1:0] iob_pin

   ,input [BYTES*13-1:0] phy2iob_q_out_byte
   ,input [BYTES*13-1:0] phy2iob_odt_out_byte
   ,input [BYTES*13-1:0] phy2iob_t
   ,input [BYTES*7-1:0] mcal_rd_vref_value
);

genvar byteNum;
generate
   for (byteNum = 0; byteNum < BYTES; byteNum = byteNum+1) begin:genByte
      ddr4_phy_v2_2_0_iob_byte #(.IOBTYPE(IOBTYPE[byteNum*39+38:byteNum*39]), .DQS_BIAS(DQS_BIAS), .DRAM_TYPE(DRAM_TYPE), .EN_LVAUX(EN_LVAUX), .BANK_TYPE(BANK_TYPE), .USE_DYNAMIC_DCI(USE_DYNAMIC_DCI)) u_ddr_iob_byte (
          .iob2phy_d_in_byte    (iob2phy_d_in_byte[byteNum*13+12:byteNum*13])

         ,.iob_pin              (iob_pin[byteNum*13+12:byteNum*13])

         ,.phy2iob_q_out_byte   (phy2iob_q_out_byte[byteNum*13+12:byteNum*13])
         ,.phy2iob_odt_out_byte (phy2iob_odt_out_byte[byteNum*13+12:byteNum*13])
         ,.phy2iob_t            (phy2iob_t[byteNum*13+12:byteNum*13])
         ,.fpga_vref_tune (mcal_rd_vref_value[byteNum*7+6:byteNum*7])
      );
   end
endgenerate

endmodule


