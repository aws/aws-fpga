//Copyright 1986-2017 Xilinx, Inc. All Rights Reserved.
//--------------------------------------------------------------------------------
//Tool Version: Vivado v.2017.1_sdxop (lin64) Build 1933108 Fri Jul 14 11:54:19 MDT 2017
//Date        : Thu Jul 27 11:56:31 2017
//Host        : ip-10-206-21-53 running 64-bit CentOS release 6.5 (Final)
//Command     : generate_target bd_uram.bd
//Design      : bd_uram
//Purpose     : IP block netlist
//--------------------------------------------------------------------------------
`timescale 1 ps / 1 ps

(* CORE_GENERATION_INFO = "bd_uram,IP_Integrator,{x_ipVendor=xilinx.com,x_ipLibrary=BlockDiagram,x_ipName=bd_uram,x_ipVersion=1.00.a,x_ipLanguage=VERILOG,numBlks=2,numReposBlks=2,numNonXlnxBlks=0,numHierBlks=0,maxHierDepth=0,numSysgenBlks=0,numHlsBlks=0,numHdlrefBlks=0,numPkgbdBlks=0,bdsource=USER,synth_mode=Global}" *) (* HW_HANDOFF = "bd_uram.hwdef" *) 
module bd_uram
   (URAM_PORTA_1_addr,
    URAM_PORTA_1_clk,
    URAM_PORTA_1_din,
    URAM_PORTA_1_en,
    URAM_PORTA_1_we,
    URAM_PORTA_addr,
    URAM_PORTA_clk,
    URAM_PORTA_din,
    URAM_PORTA_en,
    URAM_PORTA_we,
    URAM_PORTB_1_addr,
    URAM_PORTB_1_clk,
    URAM_PORTB_1_dout,
    URAM_PORTB_1_en,
    URAM_PORTB_addr,
    URAM_PORTB_clk,
    URAM_PORTB_dout,
    URAM_PORTB_en);
  input [19:0]URAM_PORTA_1_addr;
  input URAM_PORTA_1_clk;
  input [31:0]URAM_PORTA_1_din;
  input URAM_PORTA_1_en;
  input [0:0]URAM_PORTA_1_we;
  input [19:0]URAM_PORTA_addr;
  input URAM_PORTA_clk;
  input [31:0]URAM_PORTA_din;
  input URAM_PORTA_en;
  input [0:0]URAM_PORTA_we;
  input [19:0]URAM_PORTB_1_addr;
  input URAM_PORTB_1_clk;
  output [31:0]URAM_PORTB_1_dout;
  input URAM_PORTB_1_en;
  input [19:0]URAM_PORTB_addr;
  input URAM_PORTB_clk;
  output [31:0]URAM_PORTB_dout;
  input URAM_PORTB_en;

  wire [19:0]BRAM_PORTA_1_1_ADDR;
  wire BRAM_PORTA_1_1_CLK;
  wire [31:0]BRAM_PORTA_1_1_DIN;
  wire BRAM_PORTA_1_1_EN;
  wire [0:0]BRAM_PORTA_1_1_WE;
  wire [19:0]BRAM_PORTA_1_ADDR;
  wire BRAM_PORTA_1_CLK;
  wire [31:0]BRAM_PORTA_1_DIN;
  wire BRAM_PORTA_1_EN;
  wire [0:0]BRAM_PORTA_1_WE;
  wire [19:0]BRAM_PORTB_1_1_ADDR;
  wire BRAM_PORTB_1_1_CLK;
  wire [31:0]BRAM_PORTB_1_1_DOUT;
  wire BRAM_PORTB_1_1_EN;
  wire [19:0]BRAM_PORTB_1_ADDR;
  wire BRAM_PORTB_1_CLK;
  wire [31:0]BRAM_PORTB_1_DOUT;
  wire BRAM_PORTB_1_EN;

  assign BRAM_PORTA_1_1_ADDR = URAM_PORTA_1_addr[19:0];
  assign BRAM_PORTA_1_1_CLK = URAM_PORTA_1_clk;
  assign BRAM_PORTA_1_1_DIN = URAM_PORTA_1_din[31:0];
  assign BRAM_PORTA_1_1_EN = URAM_PORTA_1_en;
  assign BRAM_PORTA_1_1_WE = URAM_PORTA_1_we[0];
  assign BRAM_PORTA_1_ADDR = URAM_PORTA_addr[19:0];
  assign BRAM_PORTA_1_CLK = URAM_PORTA_clk;
  assign BRAM_PORTA_1_DIN = URAM_PORTA_din[31:0];
  assign BRAM_PORTA_1_EN = URAM_PORTA_en;
  assign BRAM_PORTA_1_WE = URAM_PORTA_we[0];
  assign BRAM_PORTB_1_1_ADDR = URAM_PORTB_1_addr[19:0];
  assign BRAM_PORTB_1_1_CLK = URAM_PORTB_1_clk;
  assign BRAM_PORTB_1_1_EN = URAM_PORTB_1_en;
  assign BRAM_PORTB_1_ADDR = URAM_PORTB_addr[19:0];
  assign BRAM_PORTB_1_CLK = URAM_PORTB_clk;
  assign BRAM_PORTB_1_EN = URAM_PORTB_en;
  assign URAM_PORTB_1_dout[31:0] = BRAM_PORTB_1_1_DOUT;
  assign URAM_PORTB_dout[31:0] = BRAM_PORTB_1_DOUT;
  bd_uram_blk_mem_gen_0_0 blk_mem_gen_0
       (.addra(BRAM_PORTA_1_ADDR),
        .addrb(BRAM_PORTB_1_ADDR),
        .clka(BRAM_PORTA_1_CLK),
        .clkb(BRAM_PORTB_1_CLK),
        .dina(BRAM_PORTA_1_DIN),
        .doutb(BRAM_PORTB_1_DOUT),
        .ena(BRAM_PORTA_1_EN),
        .enb(BRAM_PORTB_1_EN),
        .wea(BRAM_PORTA_1_WE));
  bd_uram_blk_mem_gen_1_0 blk_mem_gen_1
       (.addra(BRAM_PORTA_1_1_ADDR),
        .addrb(BRAM_PORTB_1_1_ADDR),
        .clka(BRAM_PORTA_1_1_CLK),
        .clkb(BRAM_PORTB_1_1_CLK),
        .dina(BRAM_PORTA_1_1_DIN),
        .doutb(BRAM_PORTB_1_1_DOUT),
        .ena(BRAM_PORTA_1_1_EN),
        .enb(BRAM_PORTB_1_1_EN),
        .wea(BRAM_PORTA_1_1_WE));
endmodule
