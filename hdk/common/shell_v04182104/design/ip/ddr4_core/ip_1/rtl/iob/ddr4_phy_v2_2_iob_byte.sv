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
//  /   /         Filename           : ddr4_phy_v2_2_0_iob_byte.sv
// /___/   /\     Date Last Modified : $Date: 2015/04/23 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                   ddr4_phy_v2_2_0_iob_byte module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ps/1ps

// There are 13 bits, numbered 12:0 in a byte. Of these, 11:0 may be differential
// pairs. The IOBTYPE mask indicates which ones of these are diffrential pairs and also
// if they are inputs or outputs.

// each group of 3 bits designates the io type. these are ordered as dio
// (d-differential, i-input, o-output)
//  dio     Meaning
//  000     Unused pin
//  001     Single ended output
//  010     Single ended input
//  011     Single ended IO
//  100     Unused pin
//  101     Differential Output
//  110     Diffrential Input
//  111     Diffrential INOUT

// IOBTYPE pin pair 
// 0         0-1
// 1         2-3
// 2         4-5
// 3         6-7
// 4         8-9
// 5         10-11
//           12 is always single ended

module ddr4_phy_v2_2_0_iob_byte # (parameter
    IOBTYPE = 39'b0 // default is pins are not used
   ,DQS_BIAS = "TRUE"
   ,DRAM_TYPE  = "DDR3"
   ,EN_LVAUX = "FALSE"
   ,BANK_TYPE  = "HP_IO"
   ,USE_DYNAMIC_DCI= 1
)(
    output [13-1:0] iob2phy_d_in_byte

   ,inout [13-1:0] iob_pin      // spyglass disable W495

   ,input [13-1:0] phy2iob_q_out_byte
   ,input [13-1:0] phy2iob_odt_out_byte
   ,input [13-1:0] phy2iob_t
   ,input [6:0] fpga_vref_tune
);

    wire Vref;
    generate
     if (DRAM_TYPE  == "DDR4" && EN_LVAUX == "FALSE") begin 
            if (IOBTYPE[20:18] == 3'b111) begin: genVref
               HPIO_VREF #(.VREF_CNTR("FABRIC_RANGE1")) u_hpio_vref
         	(
         	 .FABRIC_VREF_TUNE (fpga_vref_tune),
         	 .VREF (Vref)
         	 );
            end
     end
    endgenerate
genvar bitNum;
generate
   for (bitNum = 0; bitNum < 13; bitNum = bitNum+1) begin: genBuf
      case (IOBTYPE[bitNum*3+:3])
         3'b001: begin
            OBUF OBUF(
                .I(phy2iob_q_out_byte[bitNum])
               ,.O(iob_pin[bitNum])
            );
            assign iob2phy_d_in_byte[bitNum] = '0;
         end
         3'b010: begin
            IBUF IBUF(
                .O(iob2phy_d_in_byte[bitNum])
               ,.I(iob_pin[bitNum])
            );
         end
         3'b011: begin
           if (DRAM_TYPE  == "DDR4") begin
            if (EN_LVAUX == "TRUE") begin 
              IOBUFE3 IOBUF(
                  .I(phy2iob_q_out_byte[bitNum])
                 ,.T(phy2iob_t[bitNum])
                 ,.O(iob2phy_d_in_byte[bitNum])
                 ,.IO(iob_pin[bitNum])
                 ,.OSC_EN (1'b0)
                 ,.OSC (4'b0000)
                 ,.DCITERMDISABLE ((USE_DYNAMIC_DCI == 1) ? phy2iob_odt_out_byte[bitNum] : 1'b0)
                 ,.IBUFDISABLE (1'b0)
              );
            end
            else begin 
              IOBUFE3 IOBUF(
                  .I(phy2iob_q_out_byte[bitNum])
                 ,.T(phy2iob_t[bitNum])
                 ,.O(iob2phy_d_in_byte[bitNum])
                 ,.IO(iob_pin[bitNum])
                 ,.VREF (Vref)
                 ,.OSC_EN (1'b0)
                 ,.OSC (4'b0000)
                 ,.DCITERMDISABLE ((USE_DYNAMIC_DCI == 1) ? phy2iob_odt_out_byte[bitNum] : 1'b0)
                 ,.IBUFDISABLE (1'b0)
              );
            end
           end
           else begin
              if (BANK_TYPE == "HP_IO") begin
                IOBUFE3 IOBUF(
                  .I(phy2iob_q_out_byte[bitNum])
                 ,.T(phy2iob_t[bitNum])
                 ,.O(iob2phy_d_in_byte[bitNum])
                 ,.IO(iob_pin[bitNum])
                 ,.VREF (1'b0)
                 ,.OSC_EN (1'b0)
                 ,.OSC (4'b0000)
                 ,.DCITERMDISABLE ((USE_DYNAMIC_DCI == 1) ? phy2iob_odt_out_byte[bitNum] : 1'b0)
                 ,.IBUFDISABLE (1'b0)
                 );
              end else if (BANK_TYPE == "HR_IO") begin
                IOBUF_INTERMDISABLE # (
                .SIM_DEVICE ("ULTRASCALE")
                )
                IOBUF(
                  .I(phy2iob_q_out_byte[bitNum])
                 ,.T(phy2iob_t[bitNum])
                 ,.O(iob2phy_d_in_byte[bitNum])
                 ,.IO(iob_pin[bitNum])
                 ,.INTERMDISABLE ((USE_DYNAMIC_DCI == 1) ? phy2iob_odt_out_byte[bitNum] : 1'b0)
                 ,.IBUFDISABLE (1'b0)
                 );
              end else begin
                IOBUF IOBUF(
                  .I(phy2iob_q_out_byte[bitNum])
                 ,.T(phy2iob_t[bitNum])
                 ,.O(iob2phy_d_in_byte[bitNum])
                 ,.IO(iob_pin[bitNum])
                 );
              end
           end
         end
         3'b101: if (bitNum % 2 == 0) begin // generate for even only
            OBUFDS OBUFDS(
                .I(phy2iob_q_out_byte[bitNum])
               ,.O(iob_pin[bitNum])
               ,.OB(iob_pin[bitNum+1])
            );
            assign iob2phy_d_in_byte[bitNum] = '0;
         end
         3'b110: if (bitNum % 2 == 0) begin
            IBUFDS #(.DQS_BIAS(DQS_BIAS)) IBUFDS(
                .O(iob2phy_d_in_byte[bitNum])
               ,.I(iob_pin[bitNum])
               ,.IB(iob_pin[bitNum+1])
            );
         end
         3'b111: if (bitNum % 2 == 0) begin
            IOBUFDS #(.DQS_BIAS(DQS_BIAS))  IO_BUFDS(
                .I(phy2iob_q_out_byte[bitNum])
               ,.T(phy2iob_t[bitNum])
               ,.O(iob2phy_d_in_byte[bitNum])
               ,.IO(iob_pin[bitNum])
               ,.IOB(iob_pin[bitNum+1])
            );
         end
         default: begin
            // No IO buffer!
         end
      endcase
   end
endgenerate

endmodule


