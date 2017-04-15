//Copyright 1986-2016 Xilinx, Inc. All Rights Reserved.
//--------------------------------------------------------------------------------
//Tool Version: Vivado v.2016.4_sdx (lin64) Build 1752585 Wed Jan 18 17:34:57 MST 2017
//Date        : Wed Feb  1 14:13:30 2017
//Host        : ip-10-206-21-184 running 64-bit CentOS release 6.5 (Final)
//Command     : generate_target bd_a493.bd
//Design      : bd_a493
//Purpose     : IP block netlist
//--------------------------------------------------------------------------------
`timescale 1 ps / 1 ps

(* CORE_GENERATION_INFO = "bd_a493,IP_Integrator,{x_ipVendor=xilinx.com,x_ipLibrary=BlockDiagram,x_ipName=bd_a493,x_ipVersion=1.00.a,x_ipLanguage=VERILOG,numBlks=2,numReposBlks=2,numNonXlnxBlks=0,numHierBlks=0,maxHierDepth=0,numSysgenBlks=0,numHlsBlks=0,numHdlrefBlks=0,numPkgbdBlks=0,bdsource=SBD,synth_mode=Global}" *) (* HW_HANDOFF = "cl_debug_bridge.hwdef" *) 
module bd_a493
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

  wire capture_1;
  wire clk_1;
  wire drck_1;
  wire [31:0]lut_buffer_bscanid_o;
  wire lut_buffer_tdo_o;
  wire reset_1;
  wire runtest_1;
  wire sel_1;
  wire shift_1;
  wire tck_1;
  wire tdi_1;
  wire tms_1;
  wire update_1;
  wire [31:0]xsdbm_bscanid;
  wire xsdbm_tdo;

  assign bscanid[31:0] = lut_buffer_bscanid_o;
  assign capture_1 = capture;
  assign clk_1 = clk;
  assign drck_1 = drck;
  assign reset_1 = reset;
  assign runtest_1 = runtest;
  assign sel_1 = sel;
  assign shift_1 = shift;
  assign tck_1 = tck;
  assign tdi_1 = tdi;
  assign tdo = lut_buffer_tdo_o;
  assign tms_1 = tms;
  assign update_1 = update;
  bd_a493_lut_buffer_0 lut_buffer
       (.bscanid_i(xsdbm_bscanid),
        .bscanid_o(lut_buffer_bscanid_o),
        .tdo_i(xsdbm_tdo),
        .tdo_o(lut_buffer_tdo_o));
  bd_a493_xsdbm_0 xsdbm
       (.bscanid(xsdbm_bscanid),
        .capture(capture_1),
        .clk(clk_1),
        .drck(drck_1),
        .reset(reset_1),
        .runtest(runtest_1),
        .sel(sel_1),
        .shift(shift_1),
        .tck(tck_1),
        .tdi(tdi_1),
        .tdo(xsdbm_tdo),
        .tms(tms_1),
        .update(update_1));
endmodule
