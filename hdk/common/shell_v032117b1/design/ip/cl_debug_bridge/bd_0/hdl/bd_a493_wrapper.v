//Copyright 1986-2016 Xilinx, Inc. All Rights Reserved.
//--------------------------------------------------------------------------------
//Tool Version: Vivado v.2016.4_sdx (lin64) Build 1752585 Wed Jan 18 17:34:57 MST 2017
//Date        : Wed Feb  1 14:13:30 2017
//Host        : ip-10-206-21-184 running 64-bit CentOS release 6.5 (Final)
//Command     : generate_target bd_a493_wrapper.bd
//Design      : bd_a493_wrapper
//Purpose     : IP block netlist
//--------------------------------------------------------------------------------
`timescale 1 ps / 1 ps

module bd_a493_wrapper
   (bscanid,
    capture,
    clk,
    drck,
    reset,
    runtest,
    sel,
    shift,
    tck,
    tdi,
    tdo,
    tms,
    update);
  output [31:0]bscanid;
  input capture;
  input clk;
  input drck;
  input reset;
  input runtest;
  input sel;
  input shift;
  input tck;
  input tdi;
  output tdo;
  input tms;
  input update;

  wire [31:0]bscanid;
  wire capture;
  wire clk;
  wire drck;
  wire reset;
  wire runtest;
  wire sel;
  wire shift;
  wire tck;
  wire tdi;
  wire tdo;
  wire tms;
  wire update;

  bd_a493 bd_a493_i
       (.bscanid(bscanid),
        .capture(capture),
        .clk(clk),
        .drck(drck),
        .reset(reset),
        .runtest(runtest),
        .sel(sel),
        .shift(shift),
        .tck(tck),
        .tdi(tdi),
        .tdo(tdo),
        .tms(tms),
        .update(update));
endmodule
