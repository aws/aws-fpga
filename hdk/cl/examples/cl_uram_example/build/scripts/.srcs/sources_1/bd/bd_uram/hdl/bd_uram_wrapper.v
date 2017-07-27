//Copyright 1986-2017 Xilinx, Inc. All Rights Reserved.
//--------------------------------------------------------------------------------
//Tool Version: Vivado v.2017.1_sdxop (lin64) Build 1933108 Fri Jul 14 11:54:19 MDT 2017
//Date        : Thu Jul 27 11:56:31 2017
//Host        : ip-10-206-21-53 running 64-bit CentOS release 6.5 (Final)
//Command     : generate_target bd_uram_wrapper.bd
//Design      : bd_uram_wrapper
//Purpose     : IP block netlist
//--------------------------------------------------------------------------------
`timescale 1 ps / 1 ps

module bd_uram_wrapper
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

  wire [19:0]URAM_PORTA_1_addr;
  wire URAM_PORTA_1_clk;
  wire [31:0]URAM_PORTA_1_din;
  wire URAM_PORTA_1_en;
  wire [0:0]URAM_PORTA_1_we;
  wire [19:0]URAM_PORTA_addr;
  wire URAM_PORTA_clk;
  wire [31:0]URAM_PORTA_din;
  wire URAM_PORTA_en;
  wire [0:0]URAM_PORTA_we;
  wire [19:0]URAM_PORTB_1_addr;
  wire URAM_PORTB_1_clk;
  wire [31:0]URAM_PORTB_1_dout;
  wire URAM_PORTB_1_en;
  wire [19:0]URAM_PORTB_addr;
  wire URAM_PORTB_clk;
  wire [31:0]URAM_PORTB_dout;
  wire URAM_PORTB_en;

  bd_uram bd_uram_i
       (.URAM_PORTA_1_addr(URAM_PORTA_1_addr),
        .URAM_PORTA_1_clk(URAM_PORTA_1_clk),
        .URAM_PORTA_1_din(URAM_PORTA_1_din),
        .URAM_PORTA_1_en(URAM_PORTA_1_en),
        .URAM_PORTA_1_we(URAM_PORTA_1_we),
        .URAM_PORTA_addr(URAM_PORTA_addr),
        .URAM_PORTA_clk(URAM_PORTA_clk),
        .URAM_PORTA_din(URAM_PORTA_din),
        .URAM_PORTA_en(URAM_PORTA_en),
        .URAM_PORTA_we(URAM_PORTA_we),
        .URAM_PORTB_1_addr(URAM_PORTB_1_addr),
        .URAM_PORTB_1_clk(URAM_PORTB_1_clk),
        .URAM_PORTB_1_dout(URAM_PORTB_1_dout),
        .URAM_PORTB_1_en(URAM_PORTB_1_en),
        .URAM_PORTB_addr(URAM_PORTB_addr),
        .URAM_PORTB_clk(URAM_PORTB_clk),
        .URAM_PORTB_dout(URAM_PORTB_dout),
        .URAM_PORTB_en(URAM_PORTB_en));
endmodule
