// Copyright 1986-2016 Xilinx, Inc. All Rights Reserved.
// --------------------------------------------------------------------------------
// Tool Version: Vivado v.2016.4_sdx (lin64) Build 1765467 Wed Feb  1 13:16:54 MST 2017
// Date        : Wed Feb 22 13:13:33 2017
// Host        : ip-10-206-20-105 running 64-bit CentOS release 6.5 (Final)
// Command     : write_verilog -force -mode synth_stub -rename_top cl_axi_interconnect_m02_regslice_0 -prefix
//               cl_axi_interconnect_m02_regslice_0_ cl_axi_interconnect_s00_regslice_0_stub.v
// Design      : cl_axi_interconnect_s00_regslice_0
// Purpose     : Stub declaration of top-level module interface
// Device      : xcvu9p-flgb2104-2-i-es2
// --------------------------------------------------------------------------------

// This empty module with port declaration file causes synthesis tools to infer a black box for IP.
// The synthesis directives are for Synopsys Synplify support to prevent IO buffer insertion.
// Please paste the declaration into a Verilog source file or add the file as an additional source.
(* X_CORE_INFO = "axi_register_slice_v2_1_11_axi_register_slice,Vivado 2016.4_sdx" *)
module cl_axi_interconnect_m02_regslice_0(aclk, aresetn, s_axi_awid, s_axi_awaddr, 
  s_axi_awlen, s_axi_awsize, s_axi_awburst, s_axi_awlock, s_axi_awcache, s_axi_awprot, 
  s_axi_awregion, s_axi_awqos, s_axi_awvalid, s_axi_awready, s_axi_wdata, s_axi_wstrb, 
  s_axi_wlast, s_axi_wvalid, s_axi_wready, s_axi_bid, s_axi_bresp, s_axi_bvalid, s_axi_bready, 
  s_axi_arid, s_axi_araddr, s_axi_arlen, s_axi_arsize, s_axi_arburst, s_axi_arlock, 
  s_axi_arcache, s_axi_arprot, s_axi_arregion, s_axi_arqos, s_axi_arvalid, s_axi_arready, 
  s_axi_rid, s_axi_rdata, s_axi_rresp, s_axi_rlast, s_axi_rvalid, s_axi_rready, m_axi_awid, 
  m_axi_awaddr, m_axi_awlen, m_axi_awsize, m_axi_awburst, m_axi_awlock, m_axi_awcache, 
  m_axi_awprot, m_axi_awregion, m_axi_awqos, m_axi_awvalid, m_axi_awready, m_axi_wdata, 
  m_axi_wstrb, m_axi_wlast, m_axi_wvalid, m_axi_wready, m_axi_bid, m_axi_bresp, m_axi_bvalid, 
  m_axi_bready, m_axi_arid, m_axi_araddr, m_axi_arlen, m_axi_arsize, m_axi_arburst, 
  m_axi_arlock, m_axi_arcache, m_axi_arprot, m_axi_arregion, m_axi_arqos, m_axi_arvalid, 
  m_axi_arready, m_axi_rid, m_axi_rdata, m_axi_rresp, m_axi_rlast, m_axi_rvalid, m_axi_rready)
/* synthesis syn_black_box black_box_pad_pin="aclk,aresetn,s_axi_awid[5:0],s_axi_awaddr[63:0],s_axi_awlen[7:0],s_axi_awsize[2:0],s_axi_awburst[1:0],s_axi_awlock[0:0],s_axi_awcache[3:0],s_axi_awprot[2:0],s_axi_awregion[3:0],s_axi_awqos[3:0],s_axi_awvalid,s_axi_awready,s_axi_wdata[511:0],s_axi_wstrb[63:0],s_axi_wlast,s_axi_wvalid,s_axi_wready,s_axi_bid[5:0],s_axi_bresp[1:0],s_axi_bvalid,s_axi_bready,s_axi_arid[5:0],s_axi_araddr[63:0],s_axi_arlen[7:0],s_axi_arsize[2:0],s_axi_arburst[1:0],s_axi_arlock[0:0],s_axi_arcache[3:0],s_axi_arprot[2:0],s_axi_arregion[3:0],s_axi_arqos[3:0],s_axi_arvalid,s_axi_arready,s_axi_rid[5:0],s_axi_rdata[511:0],s_axi_rresp[1:0],s_axi_rlast,s_axi_rvalid,s_axi_rready,m_axi_awid[5:0],m_axi_awaddr[63:0],m_axi_awlen[7:0],m_axi_awsize[2:0],m_axi_awburst[1:0],m_axi_awlock[0:0],m_axi_awcache[3:0],m_axi_awprot[2:0],m_axi_awregion[3:0],m_axi_awqos[3:0],m_axi_awvalid,m_axi_awready,m_axi_wdata[511:0],m_axi_wstrb[63:0],m_axi_wlast,m_axi_wvalid,m_axi_wready,m_axi_bid[5:0],m_axi_bresp[1:0],m_axi_bvalid,m_axi_bready,m_axi_arid[5:0],m_axi_araddr[63:0],m_axi_arlen[7:0],m_axi_arsize[2:0],m_axi_arburst[1:0],m_axi_arlock[0:0],m_axi_arcache[3:0],m_axi_arprot[2:0],m_axi_arregion[3:0],m_axi_arqos[3:0],m_axi_arvalid,m_axi_arready,m_axi_rid[5:0],m_axi_rdata[511:0],m_axi_rresp[1:0],m_axi_rlast,m_axi_rvalid,m_axi_rready" */;
  input aclk;
  input aresetn;
  input [5:0]s_axi_awid;
  input [63:0]s_axi_awaddr;
  input [7:0]s_axi_awlen;
  input [2:0]s_axi_awsize;
  input [1:0]s_axi_awburst;
  input [0:0]s_axi_awlock;
  input [3:0]s_axi_awcache;
  input [2:0]s_axi_awprot;
  input [3:0]s_axi_awregion;
  input [3:0]s_axi_awqos;
  input s_axi_awvalid;
  output s_axi_awready;
  input [511:0]s_axi_wdata;
  input [63:0]s_axi_wstrb;
  input s_axi_wlast;
  input s_axi_wvalid;
  output s_axi_wready;
  output [5:0]s_axi_bid;
  output [1:0]s_axi_bresp;
  output s_axi_bvalid;
  input s_axi_bready;
  input [5:0]s_axi_arid;
  input [63:0]s_axi_araddr;
  input [7:0]s_axi_arlen;
  input [2:0]s_axi_arsize;
  input [1:0]s_axi_arburst;
  input [0:0]s_axi_arlock;
  input [3:0]s_axi_arcache;
  input [2:0]s_axi_arprot;
  input [3:0]s_axi_arregion;
  input [3:0]s_axi_arqos;
  input s_axi_arvalid;
  output s_axi_arready;
  output [5:0]s_axi_rid;
  output [511:0]s_axi_rdata;
  output [1:0]s_axi_rresp;
  output s_axi_rlast;
  output s_axi_rvalid;
  input s_axi_rready;
  output [5:0]m_axi_awid;
  output [63:0]m_axi_awaddr;
  output [7:0]m_axi_awlen;
  output [2:0]m_axi_awsize;
  output [1:0]m_axi_awburst;
  output [0:0]m_axi_awlock;
  output [3:0]m_axi_awcache;
  output [2:0]m_axi_awprot;
  output [3:0]m_axi_awregion;
  output [3:0]m_axi_awqos;
  output m_axi_awvalid;
  input m_axi_awready;
  output [511:0]m_axi_wdata;
  output [63:0]m_axi_wstrb;
  output m_axi_wlast;
  output m_axi_wvalid;
  input m_axi_wready;
  input [5:0]m_axi_bid;
  input [1:0]m_axi_bresp;
  input m_axi_bvalid;
  output m_axi_bready;
  output [5:0]m_axi_arid;
  output [63:0]m_axi_araddr;
  output [7:0]m_axi_arlen;
  output [2:0]m_axi_arsize;
  output [1:0]m_axi_arburst;
  output [0:0]m_axi_arlock;
  output [3:0]m_axi_arcache;
  output [2:0]m_axi_arprot;
  output [3:0]m_axi_arregion;
  output [3:0]m_axi_arqos;
  output m_axi_arvalid;
  input m_axi_arready;
  input [5:0]m_axi_rid;
  input [511:0]m_axi_rdata;
  input [1:0]m_axi_rresp;
  input m_axi_rlast;
  input m_axi_rvalid;
  output m_axi_rready;
endmodule
