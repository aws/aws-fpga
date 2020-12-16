//*****************************************************************************
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
//*****************************************************************************
//   ____  ____
//  /   /\/   /
// /___/  \  /    Vendor                : Xilinx
// \   \   \/     Version               : 1.1
//  \   \         Application           : MIG
//  /   /         Filename              : ddr4_v2_2_10_mc_ecc_buf.v
// /___/   /\     Date Last Modified    : $Date$
// \   \  /  \    Date Created          : Tue May 13 2014
//  \___\/\___\
//
//Device            : UltraScale
//Design Name       : DDR4 SDRAM & DDR3 SDRAM
//Purpose           :
//                   ddr4_v2_2_10_mc_ecc_buf module
//Reference         :
//Revision History  :
//*****************************************************************************

`timescale 1ns/100ps

module ddr4_v2_2_10_mc_ecc_buf
  #(
    parameter TCQ = 100,
    parameter PAYLOAD_WIDTH          = 64,
    parameter DATA_BUF_ADDR_WIDTH    = 5,
    parameter DATA_BUF_OFFSET_WIDTH  = 1,
    parameter DATA_WIDTH             = 64,
    parameter nCK_PER_CLK             = 4
   )
   (
    /*AUTOARG*/
  // Outputs
  rd_merge_data,
  // Inputs
  clk, rst, rd_data_addr, rd_data_offset, wr_data_addr,
  wr_data_offset, rd_data, wr_ecc_buf
  );

  input clk;
  input rst;

  // RMW architecture supports only 16 data buffer entries.
  // Allow DATA_BUF_ADDR_WIDTH to be greater than 4, but
  // assume the upper bits are used for tagging.

  input [DATA_BUF_ADDR_WIDTH-1:0] rd_data_addr;
  input [DATA_BUF_OFFSET_WIDTH-1:0] rd_data_offset;
  wire [4:0] buf_wr_addr;

  input [DATA_BUF_ADDR_WIDTH-1:0] wr_data_addr;
  input [DATA_BUF_OFFSET_WIDTH-1:0] wr_data_offset;
  reg [4:0] buf_rd_addr_r;

  generate
    if (DATA_BUF_ADDR_WIDTH >= 4) begin : ge_4_addr_bits
      always @(posedge clk)  
        buf_rd_addr_r <= #TCQ{wr_data_addr[3:0], wr_data_offset};
      assign buf_wr_addr = {rd_data_addr[3:0], rd_data_offset};
    end
    else begin : lt_4_addr_bits
      always @(posedge clk) 
        buf_rd_addr_r <= #TCQ{{4-DATA_BUF_ADDR_WIDTH{1'b0}},
                               wr_data_addr[DATA_BUF_ADDR_WIDTH-1:0],
                               wr_data_offset};
      assign buf_wr_addr = {{4-DATA_BUF_ADDR_WIDTH{1'b0}},
                            rd_data_addr[DATA_BUF_ADDR_WIDTH-1:0], 
                            rd_data_offset};
    end
  endgenerate

  input [2*nCK_PER_CLK*PAYLOAD_WIDTH-1:0] rd_data;
  reg [2*nCK_PER_CLK*DATA_WIDTH-1:0] payload;
  integer h;
  always @(/*AS*/rd_data)
    for (h=0; h<2*nCK_PER_CLK; h=h+1)
      payload[h*DATA_WIDTH+:DATA_WIDTH] = 
        rd_data[h*PAYLOAD_WIDTH+:DATA_WIDTH];

  input wr_ecc_buf;
  localparam BUF_WIDTH = 2*nCK_PER_CLK*DATA_WIDTH;
  localparam FULL_RAM_CNT = (BUF_WIDTH/6);
  localparam REMAINDER = BUF_WIDTH % 6;
  localparam RAM_CNT = FULL_RAM_CNT + ((REMAINDER == 0 ) ? 0 : 1);
  localparam RAM_WIDTH = (RAM_CNT*6);
  wire [RAM_WIDTH-1:0] buf_out_data;
  generate
    begin : ram_buf
      wire [RAM_WIDTH-1:0] buf_in_data;
      if (REMAINDER == 0)
        assign buf_in_data = payload;
      else
        assign buf_in_data = {{6-REMAINDER{1'b0}}, payload};

      genvar i;
      for (i=0; i<RAM_CNT; i=i+1) begin : rd_buffer_ram
        RAM32M
          #(.INIT_A(64'h0000000000000000),
            .INIT_B(64'h0000000000000000),
            .INIT_C(64'h0000000000000000),
            .INIT_D(64'h0000000000000000)
          ) RAM32M0 (
            .DOA(buf_out_data[((i*6)+4)+:2]),
            .DOB(buf_out_data[((i*6)+2)+:2]),
            .DOC(buf_out_data[((i*6)+0)+:2]),
            .DOD(),
            .DIA(buf_in_data[((i*6)+4)+:2]),
            .DIB(buf_in_data[((i*6)+2)+:2]),
            .DIC(buf_in_data[((i*6)+0)+:2]),
            .DID(2'b0),
            .ADDRA(buf_rd_addr_r),
            .ADDRB(buf_rd_addr_r),
            .ADDRC(buf_rd_addr_r),
            .ADDRD(buf_wr_addr),
            .WE(wr_ecc_buf),
            .WCLK(clk)
           );
      end // block: rd_buffer_ram
    end
  endgenerate

  output wire [2*nCK_PER_CLK*DATA_WIDTH-1:0] rd_merge_data;
  assign rd_merge_data = buf_out_data[2*nCK_PER_CLK*DATA_WIDTH-1:0];


endmodule

