//-----------------------------------------------------------------------------
//
// (c) Copyright 2012-2012 Xilinx, Inc. All rights reserved.
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
//-----------------------------------------------------------------------------
//
// Project    : The Xilinx PCI Express DMA 
// File       : dma_fifo_wrap.v
// Version    : $IpVersion 
//-----------------------------------------------------------------------------
`include "xdma_axi4mm_axi_bridge.vh"
module xdma_v3_0_2_fifo_wrap
#(
  parameter DATA_WIDTH = 256,
  parameter ECC_ENABLE = 1,
  parameter AXI4MM_ULTRA = 0
  )
(
			input 			  clk,
			input 			  reset_n,
			input 			  WrEn,
			input 			  RdEn,
			input [DATA_WIDTH-1:0] 	  DataIn,
			input [DATA_WIDTH/8-1:0]  ParityIn,
			output [DATA_WIDTH-1:0]   DataOut,
			output [DATA_WIDTH/8-1:0] ParityOut,
			output 			  empty,
			output 			  full,
			output 			  almost_full,
			output 			  dbiterr
			);

   wire [DATA_WIDTH/64-1:0]    full_wire;
   wire [DATA_WIDTH/64-1:0]    almost_full_wire;
   wire [DATA_WIDTH/64-1:0]    empty_wire;
   wire [DATA_WIDTH-1:0]       DataOut_wire;
   wire [DATA_WIDTH/8-1:0]       ParityOut_wire;
   wire [DATA_WIDTH/64-1:0] 	 dbiterr_wire;
   
   assign DataOut = DataOut_wire;
   assign ParityOut = ParityOut_wire;
   assign dbiterr = |dbiterr_wire;
   assign full = full_wire[0];
   assign empty = empty_wire[0];
   assign almost_full = almost_full_wire[0];

   localparam MEM_CNT = DATA_WIDTH/64;

   genvar 			 memcnt;
   generate
      for(memcnt=0;memcnt<MEM_CNT;memcnt=memcnt+1) begin : fifo_gen_64B_eccparity
	 if(ECC_ENABLE==1) begin
	    assign ParityOut_wire[(memcnt*8)+:8] = 8'h0;
	    if(AXI4MM_ULTRA==1)
	      xdma_0_fifo_generator_64_ecc_ult u_fifo(
					.clk(clk),
					.srst(~reset_n),
					.din(DataIn[(memcnt*64)+:64]),
					.wr_en(WrEn),
					.rd_en(RdEn),
					.dout(DataOut_wire[(memcnt*64)+:64]),
					.full(full_wire[memcnt]),
					.empty(empty_wire[memcnt]),
					.prog_full(almost_full_wire[memcnt]),
					.wr_rst_busy(),
					.rd_rst_busy(),
					.dbiterr(dbiterr_wire[memcnt])
					);
	    else
	      xdma_0_fifo_generator_64_ecc_v7 u_fifo(
					.clk(clk),
					.rst(~reset_n),
					.din(DataIn[(memcnt*64)+:64]),
					.wr_en(WrEn),
					.rd_en(RdEn),
					.dout(DataOut_wire[(memcnt*64)+:64]),
					.full(full_wire[memcnt]),
					.empty(empty_wire[memcnt]),
					.almost_full(almost_full_wire[memcnt]),
					.dbiterr(dbiterr_wire[memcnt])
					);
	    
	 end else begin // if (ECC_ENABLE==1)
	    assign dbiterr_wire[memcnt] = 1'b0;
	    if(AXI4MM_ULTRA==1)
	      xdma_0_fifo_generator_64_parity_ult u_fifo(
					       .clk(clk),
					       .srst(~reset_n),
					       .din({ParityIn[(memcnt*8)+:8],DataIn[(memcnt*64)+:64]}),
					       .wr_en(WrEn),
					       .rd_en(RdEn),
					       .dout({ParityOut_wire[(memcnt*8)+:8],DataOut_wire[(memcnt*64)+:64]}),
					       .full(full_wire[memcnt]),
					       .empty(empty_wire[memcnt]),
					       .wr_rst_busy(),
					       .rd_rst_busy(),
					       .prog_full(almost_full_wire[memcnt])
					       );
	    else
	      xdma_0_fifo_generator_64_parity_v7 u_fifo(
					       .clk(clk),
					       .srst(~reset_n),
					       .din({ParityIn[(memcnt*8)+:8],DataIn[(memcnt*64)+:64]}),
					       .wr_en(WrEn),
					       .rd_en(RdEn),
					       .dout({ParityOut_wire[(memcnt*8)+:8],DataOut_wire[(memcnt*64)+:64]}),
					       .full(full_wire[memcnt]),
					       .empty(empty_wire[memcnt]),
					       .almost_full(almost_full_wire[memcnt])
					       );
	 end
      end
   endgenerate

endmodule // axi4mm_fifo_wrap

