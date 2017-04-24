//Copyright 1986-2017 Xilinx, Inc. All Rights Reserved.
//--------------------------------------------------------------------------------
//Tool Version: Vivado v.2017.1 (lin64) Build 1836722 Wed Apr  5 18:59:43 MDT 2017
//Date        : Mon Apr 10 16:28:26 2017
//Host        : ip-10-206-21-124 running 64-bit CentOS release 6.5 (Final)
//Command     : generate_target bd_a493_wrapper.bd
//Design      : bd_a493_wrapper
//Purpose     : IP block netlist
//--------------------------------------------------------------------------------
`timescale 1 ps / 1 ps

module bd_a493_wrapper
   (S_BSCAN_VEC_bscanid,
    S_BSCAN_VEC_capture,
    S_BSCAN_VEC_drck,
    S_BSCAN_VEC_reset,
    S_BSCAN_VEC_runtest,
    S_BSCAN_VEC_sel,
    S_BSCAN_VEC_shift,
    S_BSCAN_VEC_tck,
    S_BSCAN_VEC_tdi,
    S_BSCAN_VEC_tdo,
    S_BSCAN_VEC_tms,
    S_BSCAN_VEC_update,
    clk);
  output [31:0]S_BSCAN_VEC_bscanid;
  input S_BSCAN_VEC_capture;
  input S_BSCAN_VEC_drck;
  input S_BSCAN_VEC_reset;
  input S_BSCAN_VEC_runtest;
  input S_BSCAN_VEC_sel;
  input S_BSCAN_VEC_shift;
  input S_BSCAN_VEC_tck;
  input S_BSCAN_VEC_tdi;
  output S_BSCAN_VEC_tdo;
  input S_BSCAN_VEC_tms;
  input S_BSCAN_VEC_update;
  input clk;

  wire [31:0]S_BSCAN_VEC_bscanid;
  wire S_BSCAN_VEC_capture;
  wire S_BSCAN_VEC_drck;
  wire S_BSCAN_VEC_reset;
  wire S_BSCAN_VEC_runtest;
  wire S_BSCAN_VEC_sel;
  wire S_BSCAN_VEC_shift;
  wire S_BSCAN_VEC_tck;
  wire S_BSCAN_VEC_tdi;
  wire S_BSCAN_VEC_tdo;
  wire S_BSCAN_VEC_tms;
  wire S_BSCAN_VEC_update;
  wire clk;

  bd_a493 bd_a493_i
       (.S_BSCAN_VEC_bscanid(S_BSCAN_VEC_bscanid),
        .S_BSCAN_VEC_capture(S_BSCAN_VEC_capture),
        .S_BSCAN_VEC_drck(S_BSCAN_VEC_drck),
        .S_BSCAN_VEC_reset(S_BSCAN_VEC_reset),
        .S_BSCAN_VEC_runtest(S_BSCAN_VEC_runtest),
        .S_BSCAN_VEC_sel(S_BSCAN_VEC_sel),
        .S_BSCAN_VEC_shift(S_BSCAN_VEC_shift),
        .S_BSCAN_VEC_tck(S_BSCAN_VEC_tck),
        .S_BSCAN_VEC_tdi(S_BSCAN_VEC_tdi),
        .S_BSCAN_VEC_tdo(S_BSCAN_VEC_tdo),
        .S_BSCAN_VEC_tms(S_BSCAN_VEC_tms),
        .S_BSCAN_VEC_update(S_BSCAN_VEC_update),
        .clk(clk));
endmodule
