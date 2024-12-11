
//-----------------------------------------------------------------------------
//
// (c) Copyright 2020-2024 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and
// international copyright and other intellectual property
// laws.
//
// DISCLAIMER
// This disclaimer is not a license and does not grant any
// rights to the materials distributed herewith. Except as
// otherwise provided in a valid license issued to you by
// AMD, and to the maximum extent permitted by applicable
// law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// WITH ALL FAULTS, AND AMD HEREBY DISCLAIMS ALL WARRANTIES
// AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// (2) AMD shall not be liable (whether in contract or tort,
// including negligence, or under any other theory of
// related to, arising under or in connection with these
// materials, including for any direct, or any indirect,
// special, incidental, or consequential loss or damage
// (including loss of data, profits, goodwill, or any type of
// loss or damage suffered as a result of any action brought
// by a third party) even if such damage or loss was
// reasonably foreseeable or AMD had been advised of the
// possibility of the same.
//
// CRITICAL APPLICATIONS
// AMD products are not designed or intended to be fail-
// safe, or for use in any application requiring fail-safe
// performance, such as life-support or safety devices or
// systems, Class III medical devices, nuclear facilities,
// applications related to the deployment of airbags, or any
// other applications that could lead to death, personal
// injury, or severe property or environmental damage
// (individually and collectively, "Critical
// Applications"). Customer assumes the sole risk and
// liability of any use of AMD products in Critical
// Applications, subject only to applicable laws and
// regulations governing limitations on product liability.
//
// THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// PART OF THIS FILE AT ALL TIMES.
//
//-----------------------------------------------------------------------------
//
// Project    : The Xilinx PCI Express DMA 
// File       : pcie_bridge_ep_dma_bram_wrap_2048.sv
// Version    : 4.1
//-----------------------------------------------------------------------------

`ifndef DMA_BRAM_WRAP_2048_SV
`define DMA_BRAM_WRAP_2048_SV

`include "xdma_axi4mm_axi_bridge.vh"
`include "dma_defines.vh"
`include "dma_defines.svh"

module xdma_v4_1_29_dma_bram_wrap_2048
#(
  parameter DATA_WIDTH = 256,
  parameter AXI4MM_ULTRA = 0,
  parameter ECC_ENABLE	= 0,
  parameter OUTPUT_REG = 0
  )
(
 input clkin,
 input [DATA_WIDTH-1:0]   DataIn,
 input [DATA_WIDTH/8-1:0] ParityIn,
 input [DATA_WIDTH/8-1:0] wrEn,
 input rdEn,
 input [10:0] AddrIn,
 input [10:0] AddrOut,
 output [DATA_WIDTH-1:0] DataOut,
 output			 DbeOut,
 output [DATA_WIDTH/8-1:0] ParityOut
 );


localparam	MEM_CNT		= (DATA_WIDTH / 64)+((DATA_WIDTH%64) != 0);
   
wire [DATA_WIDTH/64-1:0] dbiterr_wire;
assign			 DbeOut = (ECC_ENABLE) ? |dbiterr_wire : 1'b0;
genvar 		    memcnt;
generate
	for(memcnt=0;memcnt<MEM_CNT;memcnt=memcnt+1) 
	begin
		if (OUTPUT_REG == 0) 
				if (ECC_ENABLE == 0)
	      			xdma_v4_1_29_blk_mem_64_noreg_be_2048 u_buffermem(
					     .clka(clkin),
					     .wea(wrEn[memcnt*64/8+:8]),
					     .ena(1'b1),
					     .addra(AddrIn),
					     .dina({ParityIn[(memcnt*8)+7],DataIn[(memcnt*64+56)+:8],
					     	    ParityIn[(memcnt*8)+6],DataIn[(memcnt*64+48)+:8],
					     	    ParityIn[(memcnt*8)+5],DataIn[(memcnt*64+40)+:8],
					     	    ParityIn[(memcnt*8)+4],DataIn[(memcnt*64+32)+:8],
					     	    ParityIn[(memcnt*8)+3],DataIn[(memcnt*64+24)+:8],
					     	    ParityIn[(memcnt*8)+2],DataIn[(memcnt*64+16)+:8],
					     	    ParityIn[(memcnt*8)+1],DataIn[(memcnt*64+8 )+:8],
					     	    ParityIn[(memcnt*8)+0],DataIn[(memcnt*64+0)+:8]}),
					     .clkb(clkin),
					     .enb (rdEn),
					     .addrb(AddrOut),
					     .doutb({ParityOut[(memcnt*8)+7],DataOut[(memcnt*64+56)+:8],
					     	    ParityOut[(memcnt*8)+6],DataOut[(memcnt*64+48)+:8],
					     	    ParityOut[(memcnt*8)+5],DataOut[(memcnt*64+40)+:8],
					     	    ParityOut[(memcnt*8)+4],DataOut[(memcnt*64+32)+:8],
					     	    ParityOut[(memcnt*8)+3],DataOut[(memcnt*64+24)+:8],
					     	    ParityOut[(memcnt*8)+2],DataOut[(memcnt*64+16)+:8],
					     	    ParityOut[(memcnt*8)+1],DataOut[(memcnt*64+8)+:8],
					     	    ParityOut[(memcnt*8)+0],DataOut[(memcnt*64+0)+:8]})
					     );
				else 
	      			xdma_v4_1_29_blk_mem_64_noreg_ecc u_buffermem(
					.clka(clkin),
					.wea(wrEn[0]),
					.ena(1'b1),
					.addra(AddrIn),
					.dina(DataIn[(memcnt*64)+:64]),
					.clkb(clkin),
					.enb (rdEn),
					.addrb(AddrOut),
					.doutb(DataOut[(memcnt*64)+:64]),
					.dbiterr(dbiterr_wire[memcnt])
				);
	    	else
				if (ECC_ENABLE == 0)
	      			xdma_v4_1_29_blk_mem_64_reg_be u_buffermem(
					     .clka(clkin),
					     .ena(1'b1),
					     .wea(wrEn[memcnt*64/8+:8]),
					     .addra(AddrIn),
					     .dina({ParityIn[(memcnt*8)+7],DataIn[(memcnt*64+56)+:8],
					     	    ParityIn[(memcnt*8)+6],DataIn[(memcnt*64+48)+:8],
					     	    ParityIn[(memcnt*8)+5],DataIn[(memcnt*64+40)+:8],
					     	    ParityIn[(memcnt*8)+4],DataIn[(memcnt*64+32)+:8],
					     	    ParityIn[(memcnt*8)+3],DataIn[(memcnt*64+24)+:8],
					     	    ParityIn[(memcnt*8)+2],DataIn[(memcnt*64+16)+:8],
					     	    ParityIn[(memcnt*8)+1],DataIn[(memcnt*64+8)+:8],
					     	    ParityIn[(memcnt*8)+0],DataIn[(memcnt*64+0)+:8]}),
					     .clkb(clkin),
					     .enb (rdEn),
					     .addrb(AddrOut),
					     .doutb({ParityOut[(memcnt*8)+7],DataOut[(memcnt*64+56)+:8],
					     	    ParityOut[(memcnt*8)+6],DataOut[(memcnt*64+48)+:8],
					     	    ParityOut[(memcnt*8)+5],DataOut[(memcnt*64+40)+:8],
					     	    ParityOut[(memcnt*8)+4],DataOut[(memcnt*64+32)+:8],
					     	    ParityOut[(memcnt*8)+3],DataOut[(memcnt*64+24)+:8],
					     	    ParityOut[(memcnt*8)+2],DataOut[(memcnt*64+16)+:8],
					     	    ParityOut[(memcnt*8)+1],DataOut[(memcnt*64+8)+:8],
					     	    ParityOut[(memcnt*8)+0],DataOut[(memcnt*64+0)+:8]})
					     );
				else 
	      			xdma_v4_1_29_blk_mem_64_reg_ecc u_buffermem(
					.clka(clkin),
					.wea(wrEn[0]),
					.ena(1'b1),
					.addra(AddrIn),
					.dina(DataIn[(memcnt*64)+:64]),
					.clkb(clkin),
					.enb (rdEn),
					.addrb(AddrOut),
					.doutb(DataOut[(memcnt*64)+:64]),
					.dbiterr(dbiterr_wire[memcnt])
				);
	end
   endgenerate
   
endmodule

`endif

