
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
// File       : pcie_bridge_rc_dma_bram_wrap.sv
// Version    : 4.1
//-----------------------------------------------------------------------------

`ifndef DMA_BRAM_WRAP_SV
`define DMA_BRAM_WRAP_SV

`include "xdma_axi4mm_axi_bridge.vh"
`include "dma_defines.vh"
`include "dma_defines.svh"

module xdma_v4_1_29_dma_bram_wrap
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
 input [8:0] AddrIn,
 input [8:0] AddrOut,
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
	      			xdma_v4_1_29_blk_mem_64_noreg_be u_buffermem(
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

module xdma_v4_1_29_dma_fifo_64x512_wrap
#(
	parameter			ADR_WIDTH_A	= 9,
	parameter			DAT_WIDTH_A	= 128,
	parameter			ADR_WIDTH_B	= 10,
	parameter			DAT_WIDTH_B	= 64,
	parameter			ULTRA		= 0,
	parameter			ECC_ENABLE	= 0
)
(
	input				CLK_IN,			// Clock
	
	input	[ADR_WIDTH_A-1:0]	WP_IN,			// Write pointer
	input				WR_IN,			// Write
	input	[DAT_WIDTH_A-1:0]	DAT_IN,			// Write data

	// Output
	input	[ADR_WIDTH_B-1:0]	RP_IN,			// Read Pointer 
	output	[DAT_WIDTH_B-1:0]	DAT_OUT,		// Read data

	output				DBE_OUT
);

localparam NUM_BRAM 	= (1 << (ADR_WIDTH_A-9)) * DAT_WIDTH_A/64;
localparam WIDTH_RATIO  = DAT_WIDTH_A/64;
localparam WP_LSB 	= ADR_WIDTH_A - 9;
localparam RP_LSB	= $clog2(NUM_BRAM);

(* KEEP = "TRUE" *) logic	[NUM_BRAM-1:0] [DAT_WIDTH_B-1:0]	dout;

genvar i;

logic	[NUM_BRAM-1:0]	bram_wr;
logic	[8:0]		bram_wp;
logic	[NUM_BRAM-1:0]	dbe;
logic			dbe_or;

 
	generate
		if (WP_LSB >= 1)
			assign	bram_wr = {WIDTH_RATIO{WR_IN}} << (WIDTH_RATIO * WP_IN[WP_LSB-1:0]);
		else
			assign  bram_wr = {WIDTH_RATIO{WR_IN}};
	endgenerate
 
	assign	bram_wp = WP_IN[WP_LSB +: 9];
 

	generate for (i = 0; i < NUM_BRAM; i = i+1)
	begin: ramw
			xdma_v4_1_29_dma_bram_wrap #(
				.DATA_WIDTH(64),
				.AXI4MM_ULTRA(ULTRA),
				.OUTPUT_REG(1))
				bram (
				.clkin(CLK_IN),
				.wrEn ({8{bram_wr[i]}}),
				.rdEn (1'b1),
				.AddrIn (9'h0 | bram_wp),
				.DataIn (DAT_IN[(i%WIDTH_RATIO)*DAT_WIDTH_B+: DAT_WIDTH_B]),
				.AddrOut(9'h0 | RP_IN[ADR_WIDTH_B-1:RP_LSB]),
				.DataOut(dout[i]),
				.DbeOut(),
				.ParityIn(8'h0), // FIXME
				.ParityOut()    // FIXME
			);
	end
	endgenerate

	generate
		if (RP_LSB >= 1)
		begin
			(* KEEP = "TRUE" *) logic	[RP_LSB-1:0]	rp_sel;
			(* KEEP = "TRUE" *) logic	[RP_LSB-1:0]	rp_sel_ff;
			always @(posedge CLK_IN)
			begin
				rp_sel <= RP_IN[RP_LSB-1:0];
				rp_sel_ff <= rp_sel;
			end
			
			assign DAT_OUT = dout[rp_sel_ff];
		end
		else
		begin
			assign DAT_OUT = dout;
		end
	endgenerate

	generate
	if (ECC_ENABLE)
	begin
		always @(posedge CLK_IN)
		begin
				dbe_or <= |dbe;
		end
	end
	else
	begin
		assign dbe_or = 1'b0;
	end
	endgenerate

	assign DBE_OUT = dbe_or;
	
endmodule
`ifdef DMA_FIFO_128X512
module xdma_v4_1_29_dma_fifo_128x512_wrap
#(
	parameter			ADR_WIDTH_A	= 9,
	parameter			DAT_WIDTH_A	= 128,
	parameter			ADR_WIDTH_B	= 10,
	parameter			DAT_WIDTH_B	= 128,
	parameter			ULTRA		= 0,
	parameter			ECC_ENABLE	= 0
)
(
	input				CLK_IN,			// Clock
	
	input	[ADR_WIDTH_A-1:0]	WP_IN,			// Write pointer
	input				WR_IN,			// Write
	input	[DAT_WIDTH_A-1:0]	DAT_IN,			// Write data

	// Output
	input	[ADR_WIDTH_B-1:0]	RP_IN,			// Read Pointer 
	output	[DAT_WIDTH_B-1:0]	DAT_OUT,		// Read data

	output				DBE_OUT
);
// For 64 bit dp, ADR_WIDTH_A == 10, else ADR_WIDTH_A == 9
localparam NUM_BRAM 	= (1 << (ADR_WIDTH_A-9)) * DAT_WIDTH_A/128;
localparam WIDTH_RATIO  = (DAT_WIDTH == 64) ? 1 : DAT_WIDTH_A/128;
localparam WP_LSB 	= ADR_WIDTH_A - 9;
localparam RP_LSB	= $clog2(NUM_BRAM);

(* KEEP = "TRUE" *) logic	[NUM_BRAM-1:0] [DAT_WIDTH_B-1:0]	dout;

genvar i;

logic	[NUM_BRAM-1:0]	bram_wr;
logic	[8:0]		bram_wp;
logic	[NUM_BRAM-1:0]	dbe;
logic			dbe_or;

 
	generate
		if (WP_LSB >= 1)
			assign	bram_wr = {WIDTH_RATIO{WR_IN}} << (WIDTH_RATIO * WP_IN[WP_LSB-1:0]);
		else
			assign  bram_wr = {WIDTH_RATIO{WR_IN}};
	endgenerate
 
	assign	bram_wp = WP_IN[WP_LSB +: 9];
 

	generate for (i = 0; i < NUM_BRAM; i = i+1)
	begin: ramw
			xdma_v4_1_29_dma_bram_wrap #(
				.DATA_WIDTH(128),
				.AXI4MM_ULTRA(ULTRA),
				.OUTPUT_REG(1))
				bram (
				.clkin(CLK_IN),
				.wrEn ({16{bram_wr[i]}}),
				.rdEn (1'b1),
				.AddrIn (9'h0 | bram_wp),
				.DataIn (DAT_IN[(i%WIDTH_RATIO)*DAT_WIDTH_B+: DAT_WIDTH_B]),
				.AddrOut(9'h0 | RP_IN[ADR_WIDTH_B-1:RP_LSB]),
				.DataOut(dout[i]),
				.ParityIn(8'h0), // FIXME
				.ParityOut()    // FIXME
			);
	end
	endgenerate

	generate
		if (RP_LSB >= 1)
		begin
			(* KEEP = "TRUE" *) logic	[RP_LSB-1:0]	rp_sel;
			(* KEEP = "TRUE" *) logic	[RP_LSB-1:0]	rp_sel_ff;
			always @(posedge CLK_IN)
			begin
				rp_sel <= RP_IN[RP_LSB-1:0];
				rp_sel_ff <= rp_sel;
			end
			
			assign DAT_OUT = dout[rp_sel_ff];
		end
		else
		begin
			assign DAT_OUT = dout;
		end
	endgenerate

	generate
	if (ECC_ENABLE)
	begin
		always @(posedge CLK_IN)
		begin
				dbe_or <= |dbe;
		end
	end
	else
	begin
		assign dbe_or = 1'b0;
	end
	endgenerate

	assign DBE_OUT = dbe_or;
	
endmodule
`endif

module xdma_v4_1_29_mem_simple_dport_bram
  #(parameter MEM_W=128,
    parameter ADR_W=9,
    parameter RDT_FFOUT=1		// rdt flop-out
  ) (
  input                   clk,
  input                   we,
  input       [ADR_W-1:0] wad,
  input       [MEM_W-1:0] wdt,
  input                   re,
  input       [ADR_W-1:0] rad,
  output wire [MEM_W-1:0] rdt
);

localparam MEM_D = 2**ADR_W;

(* ram_style = "block" *) reg [MEM_W-1:0] the_bram [MEM_D-1:0];
reg  [MEM_W-1:0] bram_rdt;
reg  [MEM_W-1:0] bram_rdt_r;

// WR
always @(posedge clk) begin
  if (we) begin
    the_bram[wad] <= wdt;
  end
end
// RD
always @(posedge clk) begin
  if (re) begin
    bram_rdt <= the_bram[rad];
  end
  bram_rdt_r <= bram_rdt;
end

generate
  if (RDT_FFOUT == 1) begin
    assign rdt = bram_rdt_r;
  end
  else begin
    assign rdt = bram_rdt;
  end
endgenerate

endmodule
`endif

