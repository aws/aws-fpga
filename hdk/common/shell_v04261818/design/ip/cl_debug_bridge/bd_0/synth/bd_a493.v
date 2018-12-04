//Copyright 1986-2017 Xilinx, Inc. All Rights Reserved.
//--------------------------------------------------------------------------------
//Command: generate_target bd_a493.bd
//Design : bd_a493
//Purpose: IP block netlist
//--------------------------------------------------------------------------------
`timescale 1 ps / 1 ps

(* CORE_GENERATION_INFO = "bd_a493,IP_Integrator,{x_ipVendor=xilinx.com,x_ipLibrary=BlockDiagram,x_ipName=bd_a493,x_ipVersion=1.00.a,x_ipLanguage=VERILOG,numBlks=2,numReposBlks=2,numNonXlnxBlks=0,numHierBlks=0,maxHierDepth=0,numSysgenBlks=0,numHlsBlks=0,numHdlrefBlks=0,numPkgbdBlks=0,bdsource=SBD,synth_mode=OOC_per_IP}" *) (* HW_HANDOFF = "cl_debug_bridge.hwdef" *) 
module bd_a493
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
  (* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 S_BSCAN BSCANID_EN" *) input S_BSCAN_bscanid_en;
  (* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 S_BSCAN CAPTURE" *) input S_BSCAN_capture;
  (* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 S_BSCAN DRCK" *) input S_BSCAN_drck;
  (* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 S_BSCAN RESET" *) input S_BSCAN_reset;
  (* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 S_BSCAN RUNTEST" *) input S_BSCAN_runtest;
  (* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 S_BSCAN SEL" *) input S_BSCAN_sel;
  (* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 S_BSCAN SHIFT" *) input S_BSCAN_shift;
  (* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 S_BSCAN TCK" *) input S_BSCAN_tck;
  (* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 S_BSCAN TDI" *) input S_BSCAN_tdi;
  (* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 S_BSCAN TDO" *) output S_BSCAN_tdo;
  (* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 S_BSCAN TMS" *) input S_BSCAN_tms;
  (* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 S_BSCAN UPDATE" *) input S_BSCAN_update;
  (* X_INTERFACE_INFO = "xilinx.com:signal:clock:1.0 CLK.CLK CLK" *) (* X_INTERFACE_PARAMETER = "XIL_INTERFACENAME CLK.CLK, FREQ_HZ 100000000, PHASE 0.000" *) input clk;

  wire S_BSCAN_1_BSCANID_EN;
  wire S_BSCAN_1_CAPTURE;
  wire S_BSCAN_1_DRCK;
  wire S_BSCAN_1_RESET;
  wire S_BSCAN_1_RUNTEST;
  wire S_BSCAN_1_SEL;
  wire S_BSCAN_1_SHIFT;
  wire S_BSCAN_1_TCK;
  wire S_BSCAN_1_TDI;
  wire S_BSCAN_1_TDO;
  wire S_BSCAN_1_TMS;
  wire S_BSCAN_1_UPDATE;
  wire clk_1;
  wire lut_buffer_m_bscan_BSCANID_EN;
  wire lut_buffer_m_bscan_CAPTURE;
  wire lut_buffer_m_bscan_DRCK;
  wire lut_buffer_m_bscan_RESET;
  wire lut_buffer_m_bscan_RUNTEST;
  wire lut_buffer_m_bscan_SEL;
  wire lut_buffer_m_bscan_SHIFT;
  wire lut_buffer_m_bscan_TCK;
  wire lut_buffer_m_bscan_TDI;
  wire lut_buffer_m_bscan_TDO;
  wire lut_buffer_m_bscan_TMS;
  wire lut_buffer_m_bscan_UPDATE;

  assign S_BSCAN_1_BSCANID_EN = S_BSCAN_bscanid_en;
  assign S_BSCAN_1_CAPTURE = S_BSCAN_capture;
  assign S_BSCAN_1_DRCK = S_BSCAN_drck;
  assign S_BSCAN_1_RESET = S_BSCAN_reset;
  assign S_BSCAN_1_RUNTEST = S_BSCAN_runtest;
  assign S_BSCAN_1_SEL = S_BSCAN_sel;
  assign S_BSCAN_1_SHIFT = S_BSCAN_shift;
  assign S_BSCAN_1_TCK = S_BSCAN_tck;
  assign S_BSCAN_1_TDI = S_BSCAN_tdi;
  assign S_BSCAN_1_TMS = S_BSCAN_tms;
  assign S_BSCAN_1_UPDATE = S_BSCAN_update;
  assign S_BSCAN_tdo = S_BSCAN_1_TDO;
  assign clk_1 = clk;
  bd_a493_lut_buffer_0 lut_buffer
       (.bscanid_en_i(S_BSCAN_1_BSCANID_EN),
        .bscanid_en_o(lut_buffer_m_bscan_BSCANID_EN),
        .capture_i(S_BSCAN_1_CAPTURE),
        .capture_o(lut_buffer_m_bscan_CAPTURE),
        .drck_i(S_BSCAN_1_DRCK),
        .drck_o(lut_buffer_m_bscan_DRCK),
        .reset_i(S_BSCAN_1_RESET),
        .reset_o(lut_buffer_m_bscan_RESET),
        .runtest_i(S_BSCAN_1_RUNTEST),
        .runtest_o(lut_buffer_m_bscan_RUNTEST),
        .sel_i(S_BSCAN_1_SEL),
        .sel_o(lut_buffer_m_bscan_SEL),
        .shift_i(S_BSCAN_1_SHIFT),
        .shift_o(lut_buffer_m_bscan_SHIFT),
        .tck_i(S_BSCAN_1_TCK),
        .tck_o(lut_buffer_m_bscan_TCK),
        .tdi_i(S_BSCAN_1_TDI),
        .tdi_o(lut_buffer_m_bscan_TDI),
        .tdo_i(lut_buffer_m_bscan_TDO),
        .tdo_o(S_BSCAN_1_TDO),
        .tms_i(S_BSCAN_1_TMS),
        .tms_o(lut_buffer_m_bscan_TMS),
        .update_i(S_BSCAN_1_UPDATE),
        .update_o(lut_buffer_m_bscan_UPDATE));
  bd_a493_xsdbm_0 xsdbm
       (.bscanid_en(lut_buffer_m_bscan_BSCANID_EN),
        .capture(lut_buffer_m_bscan_CAPTURE),
        .clk(clk_1),
        .drck(lut_buffer_m_bscan_DRCK),
        .reset(lut_buffer_m_bscan_RESET),
        .runtest(lut_buffer_m_bscan_RUNTEST),
        .sel(lut_buffer_m_bscan_SEL),
        .shift(lut_buffer_m_bscan_SHIFT),
        .tck(lut_buffer_m_bscan_TCK),
        .tdi(lut_buffer_m_bscan_TDI),
        .tdo(lut_buffer_m_bscan_TDO),
        .tms(lut_buffer_m_bscan_TMS),
        .update(lut_buffer_m_bscan_UPDATE));
endmodule
