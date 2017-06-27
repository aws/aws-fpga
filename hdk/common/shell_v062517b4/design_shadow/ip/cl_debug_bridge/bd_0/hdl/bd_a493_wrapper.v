//Copyright 1986-2017 Xilinx, Inc. All Rights Reserved.
//--------------------------------------------------------------------------------
//Tool Version: Vivado v.2017.1_sdxop (lin64) Build 1910123 Thu Jun 15 20:45:13 MDT 2017
//Date        : Wed Jun 21 15:25:45 2017
//Host        : ip-10-206-21-124 running 64-bit CentOS release 6.5 (Final)
//Command     : generate_target bd_a493_wrapper.bd
//Design      : bd_a493_wrapper
//Purpose     : IP block netlist
//--------------------------------------------------------------------------------
`timescale 1 ps / 1 ps

module bd_a493_wrapper
   (S_BSCAN_bscanid_en,
    S_BSCAN_capture,
    S_BSCAN_drck,
    S_BSCAN_reset,
    S_BSCAN_runtest,
    S_BSCAN_sel,
    S_BSCAN_shift,
    S_BSCAN_tck,
    S_BSCAN_tdi,
    S_BSCAN_tdo,
    S_BSCAN_tms,
    S_BSCAN_update,
    clk);
  input S_BSCAN_bscanid_en;
  input S_BSCAN_capture;
  input S_BSCAN_drck;
  input S_BSCAN_reset;
  input S_BSCAN_runtest;
  input S_BSCAN_sel;
  input S_BSCAN_shift;
  input S_BSCAN_tck;
  input S_BSCAN_tdi;
  output S_BSCAN_tdo;
  input S_BSCAN_tms;
  input S_BSCAN_update;
  input clk;

  wire S_BSCAN_bscanid_en;
  wire S_BSCAN_capture;
  wire S_BSCAN_drck;
  wire S_BSCAN_reset;
  wire S_BSCAN_runtest;
  wire S_BSCAN_sel;
  wire S_BSCAN_shift;
  wire S_BSCAN_tck;
  wire S_BSCAN_tdi;
  wire S_BSCAN_tdo;
  wire S_BSCAN_tms;
  wire S_BSCAN_update;
  wire clk;

  bd_a493 bd_a493_i
       (.S_BSCAN_bscanid_en(S_BSCAN_bscanid_en),
        .S_BSCAN_capture(S_BSCAN_capture),
        .S_BSCAN_drck(S_BSCAN_drck),
        .S_BSCAN_reset(S_BSCAN_reset),
        .S_BSCAN_runtest(S_BSCAN_runtest),
        .S_BSCAN_sel(S_BSCAN_sel),
        .S_BSCAN_shift(S_BSCAN_shift),
        .S_BSCAN_tck(S_BSCAN_tck),
        .S_BSCAN_tdi(S_BSCAN_tdi),
        .S_BSCAN_tdo(S_BSCAN_tdo),
        .S_BSCAN_tms(S_BSCAN_tms),
        .S_BSCAN_update(S_BSCAN_update),
        .clk(clk));
endmodule
