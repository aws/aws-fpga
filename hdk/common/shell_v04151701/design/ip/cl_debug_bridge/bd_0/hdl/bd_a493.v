//Copyright 1986-2017 Xilinx, Inc. All Rights Reserved.
//--------------------------------------------------------------------------------
//Tool Version: Vivado v.2017.1 (lin64) Build 1836722 Wed Apr  5 18:59:43 MDT 2017
//Date        : Mon Apr 10 16:28:26 2017
//Host        : ip-10-206-21-124 running 64-bit CentOS release 6.5 (Final)
//Command     : generate_target bd_a493.bd
//Design      : bd_a493
//Purpose     : IP block netlist
//--------------------------------------------------------------------------------
`timescale 1 ps / 1 ps

(* CORE_GENERATION_INFO = "bd_a493,IP_Integrator,{x_ipVendor=xilinx.com,x_ipLibrary=BlockDiagram,x_ipName=bd_a493,x_ipVersion=1.00.a,x_ipLanguage=VERILOG,numBlks=2,numReposBlks=2,numNonXlnxBlks=0,numHierBlks=0,maxHierDepth=0,numSysgenBlks=0,numHlsBlks=0,numHdlrefBlks=0,numPkgbdBlks=0,bdsource=SBD,synth_mode=OOC_per_IP}" *) (* HW_HANDOFF = "cl_debug_bridge.hwdef" *) 
module bd_a493
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

  wire [31:0]S_BSCAN_VEC_1_BSCANID;
  wire S_BSCAN_VEC_1_CAPTURE;
  wire S_BSCAN_VEC_1_DRCK;
  wire S_BSCAN_VEC_1_RESET;
  wire S_BSCAN_VEC_1_RUNTEST;
  wire S_BSCAN_VEC_1_SEL;
  wire S_BSCAN_VEC_1_SHIFT;
  wire S_BSCAN_VEC_1_TCK;
  wire S_BSCAN_VEC_1_TDI;
  wire S_BSCAN_VEC_1_TDO;
  wire S_BSCAN_VEC_1_TMS;
  wire S_BSCAN_VEC_1_UPDATE;
  wire clk_1;
  wire [31:0]lut_buffer_m_bscan_vec_BSCANID;
  wire lut_buffer_m_bscan_vec_CAPTURE;
  wire lut_buffer_m_bscan_vec_DRCK;
  wire lut_buffer_m_bscan_vec_RESET;
  wire lut_buffer_m_bscan_vec_RUNTEST;
  wire lut_buffer_m_bscan_vec_SEL;
  wire lut_buffer_m_bscan_vec_SHIFT;
  wire lut_buffer_m_bscan_vec_TCK;
  wire lut_buffer_m_bscan_vec_TDI;
  wire lut_buffer_m_bscan_vec_TDO;
  wire lut_buffer_m_bscan_vec_TMS;
  wire lut_buffer_m_bscan_vec_UPDATE;

  assign S_BSCAN_VEC_1_CAPTURE = S_BSCAN_VEC_capture;
  assign S_BSCAN_VEC_1_DRCK = S_BSCAN_VEC_drck;
  assign S_BSCAN_VEC_1_RESET = S_BSCAN_VEC_reset;
  assign S_BSCAN_VEC_1_RUNTEST = S_BSCAN_VEC_runtest;
  assign S_BSCAN_VEC_1_SEL = S_BSCAN_VEC_sel;
  assign S_BSCAN_VEC_1_SHIFT = S_BSCAN_VEC_shift;
  assign S_BSCAN_VEC_1_TCK = S_BSCAN_VEC_tck;
  assign S_BSCAN_VEC_1_TDI = S_BSCAN_VEC_tdi;
  assign S_BSCAN_VEC_1_TMS = S_BSCAN_VEC_tms;
  assign S_BSCAN_VEC_1_UPDATE = S_BSCAN_VEC_update;
  assign S_BSCAN_VEC_bscanid[31:0] = S_BSCAN_VEC_1_BSCANID;
  assign S_BSCAN_VEC_tdo = S_BSCAN_VEC_1_TDO;
  assign clk_1 = clk;
  bd_a493_lut_buffer_0 lut_buffer
       (.bscanid_i(lut_buffer_m_bscan_vec_BSCANID),
        .bscanid_o(S_BSCAN_VEC_1_BSCANID),
        .capture_i(S_BSCAN_VEC_1_CAPTURE),
        .capture_o(lut_buffer_m_bscan_vec_CAPTURE),
        .drck_i(S_BSCAN_VEC_1_DRCK),
        .drck_o(lut_buffer_m_bscan_vec_DRCK),
        .reset_i(S_BSCAN_VEC_1_RESET),
        .reset_o(lut_buffer_m_bscan_vec_RESET),
        .runtest_i(S_BSCAN_VEC_1_RUNTEST),
        .runtest_o(lut_buffer_m_bscan_vec_RUNTEST),
        .sel_i(S_BSCAN_VEC_1_SEL),
        .sel_o(lut_buffer_m_bscan_vec_SEL),
        .shift_i(S_BSCAN_VEC_1_SHIFT),
        .shift_o(lut_buffer_m_bscan_vec_SHIFT),
        .tck_i(S_BSCAN_VEC_1_TCK),
        .tck_o(lut_buffer_m_bscan_vec_TCK),
        .tdi_i(S_BSCAN_VEC_1_TDI),
        .tdi_o(lut_buffer_m_bscan_vec_TDI),
        .tdo_i(lut_buffer_m_bscan_vec_TDO),
        .tdo_o(S_BSCAN_VEC_1_TDO),
        .tms_i(S_BSCAN_VEC_1_TMS),
        .tms_o(lut_buffer_m_bscan_vec_TMS),
        .update_i(S_BSCAN_VEC_1_UPDATE),
        .update_o(lut_buffer_m_bscan_vec_UPDATE));
  bd_a493_xsdbm_0 xsdbm
       (.bscanid(lut_buffer_m_bscan_vec_BSCANID),
        .capture(lut_buffer_m_bscan_vec_CAPTURE),
        .clk(clk_1),
        .drck(lut_buffer_m_bscan_vec_DRCK),
        .reset(lut_buffer_m_bscan_vec_RESET),
        .runtest(lut_buffer_m_bscan_vec_RUNTEST),
        .sel(lut_buffer_m_bscan_vec_SEL),
        .shift(lut_buffer_m_bscan_vec_SHIFT),
        .tck(lut_buffer_m_bscan_vec_TCK),
        .tdi(lut_buffer_m_bscan_vec_TDI),
        .tdo(lut_buffer_m_bscan_vec_TDO),
        .tms(lut_buffer_m_bscan_vec_TMS),
        .update(lut_buffer_m_bscan_vec_UPDATE));
endmodule
