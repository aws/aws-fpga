//Copyright 1986-2022 Xilinx, Inc. All Rights Reserved.
//Copyright 2022-2024 Advanced Micro Devices, Inc. All Rights Reserved.
//--------------------------------------------------------------------------------
//Tool Version: Vivado v.2024.1 (lin64) Build 5076996 Wed May 22 18:36:09 MDT 2024
//Date        : Thu Jul 18 12:03:36 2024
//Host        : c7-c5-24xl-0 running 64-bit CentOS Linux release 7.9.2009 (Core)
//Command     : generate_target cl_axi_sc_1x1.bd
//Design      : cl_axi_sc_1x1
//Purpose     : IP block netlist
//--------------------------------------------------------------------------------
`timescale 1 ps / 1 ps

(* CORE_GENERATION_INFO = "cl_axi_sc_1x1,IP_Integrator,{x_ipVendor=xilinx.com,x_ipLibrary=BlockDiagram,x_ipName=cl_axi_sc_1x1,x_ipVersion=1.00.a,x_ipLanguage=VERILOG,numBlks=1,numReposBlks=1,numNonXlnxBlks=0,numHierBlks=0,maxHierDepth=0,numSysgenBlks=0,numHlsBlks=0,numHdlrefBlks=0,numPkgbdBlks=0,bdsource=USER,synth_mode=None}" *) (* HW_HANDOFF = "cl_axi_sc_1x1.hwdef" *) 
module cl_axi_sc_1x1
   (AXI3_araddr,
    AXI3_arburst,
    AXI3_arcache,
    AXI3_arlen,
    AXI3_arlock,
    AXI3_arprot,
    AXI3_arqos,
    AXI3_arready,
    AXI3_arsize,
    AXI3_arvalid,
    AXI3_awaddr,
    AXI3_awburst,
    AXI3_awcache,
    AXI3_awlen,
    AXI3_awlock,
    AXI3_awprot,
    AXI3_awqos,
    AXI3_awready,
    AXI3_awsize,
    AXI3_awvalid,
    AXI3_bready,
    AXI3_bresp,
    AXI3_bvalid,
    AXI3_rdata,
    AXI3_rlast,
    AXI3_rready,
    AXI3_rresp,
    AXI3_rvalid,
    AXI3_wdata,
    AXI3_wlast,
    AXI3_wready,
    AXI3_wstrb,
    AXI3_wvalid,
    AXI4_araddr,
    AXI4_arburst,
    AXI4_arcache,
    AXI4_arid,
    AXI4_arlen,
    AXI4_arlock,
    AXI4_arprot,
    AXI4_arqos,
    AXI4_arready,
    AXI4_arsize,
    AXI4_arvalid,
    AXI4_awaddr,
    AXI4_awburst,
    AXI4_awcache,
    AXI4_awid,
    AXI4_awlen,
    AXI4_awlock,
    AXI4_awprot,
    AXI4_awqos,
    AXI4_awready,
    AXI4_awsize,
    AXI4_awvalid,
    AXI4_bid,
    AXI4_bready,
    AXI4_bresp,
    AXI4_bvalid,
    AXI4_rdata,
    AXI4_rid,
    AXI4_rlast,
    AXI4_rready,
    AXI4_rresp,
    AXI4_rvalid,
    AXI4_wdata,
    AXI4_wlast,
    AXI4_wready,
    AXI4_wstrb,
    AXI4_wvalid,
    aclk_250,
    aclk_450,
    aresetn_250);
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 ARADDR" *) (* X_INTERFACE_PARAMETER = "XIL_INTERFACENAME AXI3, ADDR_WIDTH 64, ARUSER_WIDTH 0, AWUSER_WIDTH 0, BUSER_WIDTH 0, CLK_DOMAIN cl_axi_sc_1x1_aclk_450, DATA_WIDTH 256, FREQ_HZ 450000000, HAS_BRESP 1, HAS_BURST 0, HAS_CACHE 1, HAS_LOCK 0, HAS_PROT 0, HAS_QOS 0, HAS_REGION 0, HAS_RRESP 1, HAS_WSTRB 1, ID_WIDTH 0, INSERT_VIP 0, MAX_BURST_LENGTH 16, NUM_READ_OUTSTANDING 64, NUM_READ_THREADS 1, NUM_WRITE_OUTSTANDING 64, NUM_WRITE_THREADS 1, PHASE 0.0, PROTOCOL AXI3, READ_WRITE_MODE READ_WRITE, RUSER_BITS_PER_BYTE 0, RUSER_WIDTH 0, SUPPORTS_NARROW_BURST 0, WUSER_BITS_PER_BYTE 0, WUSER_WIDTH 0" *) output [63:0]AXI3_araddr;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 ARBURST" *) output [1:0]AXI3_arburst;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 ARCACHE" *) output [3:0]AXI3_arcache;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 ARLEN" *) output [3:0]AXI3_arlen;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 ARLOCK" *) output [1:0]AXI3_arlock;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 ARPROT" *) output [2:0]AXI3_arprot;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 ARQOS" *) output [3:0]AXI3_arqos;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 ARREADY" *) input AXI3_arready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 ARSIZE" *) output [2:0]AXI3_arsize;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 ARVALID" *) output AXI3_arvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 AWADDR" *) output [63:0]AXI3_awaddr;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 AWBURST" *) output [1:0]AXI3_awburst;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 AWCACHE" *) output [3:0]AXI3_awcache;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 AWLEN" *) output [3:0]AXI3_awlen;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 AWLOCK" *) output [1:0]AXI3_awlock;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 AWPROT" *) output [2:0]AXI3_awprot;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 AWQOS" *) output [3:0]AXI3_awqos;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 AWREADY" *) input AXI3_awready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 AWSIZE" *) output [2:0]AXI3_awsize;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 AWVALID" *) output AXI3_awvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 BREADY" *) output AXI3_bready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 BRESP" *) input [1:0]AXI3_bresp;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 BVALID" *) input AXI3_bvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 RDATA" *) input [255:0]AXI3_rdata;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 RLAST" *) input AXI3_rlast;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 RREADY" *) output AXI3_rready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 RRESP" *) input [1:0]AXI3_rresp;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 RVALID" *) input AXI3_rvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 WDATA" *) output [255:0]AXI3_wdata;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 WLAST" *) output AXI3_wlast;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 WREADY" *) input AXI3_wready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 WSTRB" *) output [31:0]AXI3_wstrb;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI3 WVALID" *) output AXI3_wvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 ARADDR" *) (* X_INTERFACE_PARAMETER = "XIL_INTERFACENAME AXI4, ADDR_WIDTH 64, ARUSER_WIDTH 0, AWUSER_WIDTH 0, BUSER_WIDTH 0, CLK_DOMAIN cl_axi_sc_1x1_aclk_250, DATA_WIDTH 512, FREQ_HZ 250000000, HAS_BRESP 1, HAS_BURST 0, HAS_CACHE 1, HAS_LOCK 0, HAS_PROT 0, HAS_QOS 0, HAS_REGION 0, HAS_RRESP 1, HAS_WSTRB 1, ID_WIDTH 16, INSERT_VIP 0, MAX_BURST_LENGTH 64, NUM_READ_OUTSTANDING 32, NUM_READ_THREADS 1, NUM_WRITE_OUTSTANDING 32, NUM_WRITE_THREADS 1, PHASE 0.0, PROTOCOL AXI4, READ_WRITE_MODE READ_WRITE, RUSER_BITS_PER_BYTE 0, RUSER_WIDTH 0, SUPPORTS_NARROW_BURST 0, WUSER_BITS_PER_BYTE 0, WUSER_WIDTH 0" *) input [63:0]AXI4_araddr;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 ARBURST" *) input [1:0]AXI4_arburst;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 ARCACHE" *) input [3:0]AXI4_arcache;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 ARID" *) input [15:0]AXI4_arid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 ARLEN" *) input [7:0]AXI4_arlen;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 ARLOCK" *) input [0:0]AXI4_arlock;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 ARPROT" *) input [2:0]AXI4_arprot;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 ARQOS" *) input [3:0]AXI4_arqos;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 ARREADY" *) output AXI4_arready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 ARSIZE" *) input [2:0]AXI4_arsize;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 ARVALID" *) input AXI4_arvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 AWADDR" *) input [63:0]AXI4_awaddr;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 AWBURST" *) input [1:0]AXI4_awburst;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 AWCACHE" *) input [3:0]AXI4_awcache;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 AWID" *) input [15:0]AXI4_awid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 AWLEN" *) input [7:0]AXI4_awlen;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 AWLOCK" *) input [0:0]AXI4_awlock;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 AWPROT" *) input [2:0]AXI4_awprot;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 AWQOS" *) input [3:0]AXI4_awqos;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 AWREADY" *) output AXI4_awready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 AWSIZE" *) input [2:0]AXI4_awsize;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 AWVALID" *) input AXI4_awvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 BID" *) output [15:0]AXI4_bid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 BREADY" *) input AXI4_bready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 BRESP" *) output [1:0]AXI4_bresp;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 BVALID" *) output AXI4_bvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 RDATA" *) output [511:0]AXI4_rdata;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 RID" *) output [15:0]AXI4_rid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 RLAST" *) output AXI4_rlast;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 RREADY" *) input AXI4_rready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 RRESP" *) output [1:0]AXI4_rresp;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 RVALID" *) output AXI4_rvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 WDATA" *) input [511:0]AXI4_wdata;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 WLAST" *) input AXI4_wlast;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 WREADY" *) output AXI4_wready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 WSTRB" *) input [63:0]AXI4_wstrb;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 AXI4 WVALID" *) input AXI4_wvalid;
  (* X_INTERFACE_INFO = "xilinx.com:signal:clock:1.0 CLK.ACLK_250 CLK" *) (* X_INTERFACE_PARAMETER = "XIL_INTERFACENAME CLK.ACLK_250, ASSOCIATED_BUSIF AXI4, ASSOCIATED_RESET aresetn_250, CLK_DOMAIN cl_axi_sc_1x1_aclk_250, FREQ_HZ 250000000, FREQ_TOLERANCE_HZ 0, INSERT_VIP 0, PHASE 0.0" *) input aclk_250;
  (* X_INTERFACE_INFO = "xilinx.com:signal:clock:1.0 CLK.ACLK_450 CLK" *) (* X_INTERFACE_PARAMETER = "XIL_INTERFACENAME CLK.ACLK_450, ASSOCIATED_BUSIF AXI3, CLK_DOMAIN cl_axi_sc_1x1_aclk_450, FREQ_HZ 450000000, FREQ_TOLERANCE_HZ 0, INSERT_VIP 0, PHASE 0.0" *) input aclk_450;
  (* X_INTERFACE_INFO = "xilinx.com:signal:reset:1.0 RST.ARESETN_250 RST" *) (* X_INTERFACE_PARAMETER = "XIL_INTERFACENAME RST.ARESETN_250, INSERT_VIP 0, POLARITY ACTIVE_LOW" *) input aresetn_250;

  wire [63:0]AXI4_1_ARADDR;
  wire [1:0]AXI4_1_ARBURST;
  wire [3:0]AXI4_1_ARCACHE;
  wire [15:0]AXI4_1_ARID;
  wire [7:0]AXI4_1_ARLEN;
  wire [0:0]AXI4_1_ARLOCK;
  wire [2:0]AXI4_1_ARPROT;
  wire [3:0]AXI4_1_ARQOS;
  wire AXI4_1_ARREADY;
  wire [2:0]AXI4_1_ARSIZE;
  wire AXI4_1_ARVALID;
  wire [63:0]AXI4_1_AWADDR;
  wire [1:0]AXI4_1_AWBURST;
  wire [3:0]AXI4_1_AWCACHE;
  wire [15:0]AXI4_1_AWID;
  wire [7:0]AXI4_1_AWLEN;
  wire [0:0]AXI4_1_AWLOCK;
  wire [2:0]AXI4_1_AWPROT;
  wire [3:0]AXI4_1_AWQOS;
  wire AXI4_1_AWREADY;
  wire [2:0]AXI4_1_AWSIZE;
  wire AXI4_1_AWVALID;
  wire [15:0]AXI4_1_BID;
  wire AXI4_1_BREADY;
  wire [1:0]AXI4_1_BRESP;
  wire AXI4_1_BVALID;
  wire [511:0]AXI4_1_RDATA;
  wire [15:0]AXI4_1_RID;
  wire AXI4_1_RLAST;
  wire AXI4_1_RREADY;
  wire [1:0]AXI4_1_RRESP;
  wire AXI4_1_RVALID;
  wire [511:0]AXI4_1_WDATA;
  wire AXI4_1_WLAST;
  wire AXI4_1_WREADY;
  wire [63:0]AXI4_1_WSTRB;
  wire AXI4_1_WVALID;
  wire aclk_250_1;
  wire aclk_450_1;
  wire aresetn_0_1;
  wire [63:0]smartconnect_0_M00_AXI_ARADDR;
  wire [1:0]smartconnect_0_M00_AXI_ARBURST;
  wire [3:0]smartconnect_0_M00_AXI_ARCACHE;
  wire [3:0]smartconnect_0_M00_AXI_ARLEN;
  wire [1:0]smartconnect_0_M00_AXI_ARLOCK;
  wire [2:0]smartconnect_0_M00_AXI_ARPROT;
  wire [3:0]smartconnect_0_M00_AXI_ARQOS;
  wire smartconnect_0_M00_AXI_ARREADY;
  wire [2:0]smartconnect_0_M00_AXI_ARSIZE;
  wire smartconnect_0_M00_AXI_ARVALID;
  wire [63:0]smartconnect_0_M00_AXI_AWADDR;
  wire [1:0]smartconnect_0_M00_AXI_AWBURST;
  wire [3:0]smartconnect_0_M00_AXI_AWCACHE;
  wire [3:0]smartconnect_0_M00_AXI_AWLEN;
  wire [1:0]smartconnect_0_M00_AXI_AWLOCK;
  wire [2:0]smartconnect_0_M00_AXI_AWPROT;
  wire [3:0]smartconnect_0_M00_AXI_AWQOS;
  wire smartconnect_0_M00_AXI_AWREADY;
  wire [2:0]smartconnect_0_M00_AXI_AWSIZE;
  wire smartconnect_0_M00_AXI_AWVALID;
  wire smartconnect_0_M00_AXI_BREADY;
  wire [1:0]smartconnect_0_M00_AXI_BRESP;
  wire smartconnect_0_M00_AXI_BVALID;
  wire [255:0]smartconnect_0_M00_AXI_RDATA;
  wire smartconnect_0_M00_AXI_RLAST;
  wire smartconnect_0_M00_AXI_RREADY;
  wire [1:0]smartconnect_0_M00_AXI_RRESP;
  wire smartconnect_0_M00_AXI_RVALID;
  wire [255:0]smartconnect_0_M00_AXI_WDATA;
  wire smartconnect_0_M00_AXI_WLAST;
  wire smartconnect_0_M00_AXI_WREADY;
  wire [31:0]smartconnect_0_M00_AXI_WSTRB;
  wire smartconnect_0_M00_AXI_WVALID;

  assign AXI3_araddr[63:0] = smartconnect_0_M00_AXI_ARADDR;
  assign AXI3_arburst[1:0] = smartconnect_0_M00_AXI_ARBURST;
  assign AXI3_arcache[3:0] = smartconnect_0_M00_AXI_ARCACHE;
  assign AXI3_arlen[3:0] = smartconnect_0_M00_AXI_ARLEN;
  assign AXI3_arlock[1:0] = smartconnect_0_M00_AXI_ARLOCK;
  assign AXI3_arprot[2:0] = smartconnect_0_M00_AXI_ARPROT;
  assign AXI3_arqos[3:0] = smartconnect_0_M00_AXI_ARQOS;
  assign AXI3_arsize[2:0] = smartconnect_0_M00_AXI_ARSIZE;
  assign AXI3_arvalid = smartconnect_0_M00_AXI_ARVALID;
  assign AXI3_awaddr[63:0] = smartconnect_0_M00_AXI_AWADDR;
  assign AXI3_awburst[1:0] = smartconnect_0_M00_AXI_AWBURST;
  assign AXI3_awcache[3:0] = smartconnect_0_M00_AXI_AWCACHE;
  assign AXI3_awlen[3:0] = smartconnect_0_M00_AXI_AWLEN;
  assign AXI3_awlock[1:0] = smartconnect_0_M00_AXI_AWLOCK;
  assign AXI3_awprot[2:0] = smartconnect_0_M00_AXI_AWPROT;
  assign AXI3_awqos[3:0] = smartconnect_0_M00_AXI_AWQOS;
  assign AXI3_awsize[2:0] = smartconnect_0_M00_AXI_AWSIZE;
  assign AXI3_awvalid = smartconnect_0_M00_AXI_AWVALID;
  assign AXI3_bready = smartconnect_0_M00_AXI_BREADY;
  assign AXI3_rready = smartconnect_0_M00_AXI_RREADY;
  assign AXI3_wdata[255:0] = smartconnect_0_M00_AXI_WDATA;
  assign AXI3_wlast = smartconnect_0_M00_AXI_WLAST;
  assign AXI3_wstrb[31:0] = smartconnect_0_M00_AXI_WSTRB;
  assign AXI3_wvalid = smartconnect_0_M00_AXI_WVALID;
  assign AXI4_1_ARADDR = AXI4_araddr[63:0];
  assign AXI4_1_ARBURST = AXI4_arburst[1:0];
  assign AXI4_1_ARCACHE = AXI4_arcache[3:0];
  assign AXI4_1_ARID = AXI4_arid[15:0];
  assign AXI4_1_ARLEN = AXI4_arlen[7:0];
  assign AXI4_1_ARLOCK = AXI4_arlock[0];
  assign AXI4_1_ARPROT = AXI4_arprot[2:0];
  assign AXI4_1_ARQOS = AXI4_arqos[3:0];
  assign AXI4_1_ARSIZE = AXI4_arsize[2:0];
  assign AXI4_1_ARVALID = AXI4_arvalid;
  assign AXI4_1_AWADDR = AXI4_awaddr[63:0];
  assign AXI4_1_AWBURST = AXI4_awburst[1:0];
  assign AXI4_1_AWCACHE = AXI4_awcache[3:0];
  assign AXI4_1_AWID = AXI4_awid[15:0];
  assign AXI4_1_AWLEN = AXI4_awlen[7:0];
  assign AXI4_1_AWLOCK = AXI4_awlock[0];
  assign AXI4_1_AWPROT = AXI4_awprot[2:0];
  assign AXI4_1_AWQOS = AXI4_awqos[3:0];
  assign AXI4_1_AWSIZE = AXI4_awsize[2:0];
  assign AXI4_1_AWVALID = AXI4_awvalid;
  assign AXI4_1_BREADY = AXI4_bready;
  assign AXI4_1_RREADY = AXI4_rready;
  assign AXI4_1_WDATA = AXI4_wdata[511:0];
  assign AXI4_1_WLAST = AXI4_wlast;
  assign AXI4_1_WSTRB = AXI4_wstrb[63:0];
  assign AXI4_1_WVALID = AXI4_wvalid;
  assign AXI4_arready = AXI4_1_ARREADY;
  assign AXI4_awready = AXI4_1_AWREADY;
  assign AXI4_bid[15:0] = AXI4_1_BID;
  assign AXI4_bresp[1:0] = AXI4_1_BRESP;
  assign AXI4_bvalid = AXI4_1_BVALID;
  assign AXI4_rdata[511:0] = AXI4_1_RDATA;
  assign AXI4_rid[15:0] = AXI4_1_RID;
  assign AXI4_rlast = AXI4_1_RLAST;
  assign AXI4_rresp[1:0] = AXI4_1_RRESP;
  assign AXI4_rvalid = AXI4_1_RVALID;
  assign AXI4_wready = AXI4_1_WREADY;
  assign aclk_250_1 = aclk_250;
  assign aclk_450_1 = aclk_450;
  assign aresetn_0_1 = aresetn_250;
  assign smartconnect_0_M00_AXI_ARREADY = AXI3_arready;
  assign smartconnect_0_M00_AXI_AWREADY = AXI3_awready;
  assign smartconnect_0_M00_AXI_BRESP = AXI3_bresp[1:0];
  assign smartconnect_0_M00_AXI_BVALID = AXI3_bvalid;
  assign smartconnect_0_M00_AXI_RDATA = AXI3_rdata[255:0];
  assign smartconnect_0_M00_AXI_RLAST = AXI3_rlast;
  assign smartconnect_0_M00_AXI_RRESP = AXI3_rresp[1:0];
  assign smartconnect_0_M00_AXI_RVALID = AXI3_rvalid;
  assign smartconnect_0_M00_AXI_WREADY = AXI3_wready;
  cl_axi_sc_1x1_smartconnect_0_0 smartconnect_0
       (.M00_AXI_araddr(smartconnect_0_M00_AXI_ARADDR),
        .M00_AXI_arburst(smartconnect_0_M00_AXI_ARBURST),
        .M00_AXI_arcache(smartconnect_0_M00_AXI_ARCACHE),
        .M00_AXI_arlen(smartconnect_0_M00_AXI_ARLEN),
        .M00_AXI_arlock(smartconnect_0_M00_AXI_ARLOCK),
        .M00_AXI_arprot(smartconnect_0_M00_AXI_ARPROT),
        .M00_AXI_arqos(smartconnect_0_M00_AXI_ARQOS),
        .M00_AXI_arready(smartconnect_0_M00_AXI_ARREADY),
        .M00_AXI_arsize(smartconnect_0_M00_AXI_ARSIZE),
        .M00_AXI_arvalid(smartconnect_0_M00_AXI_ARVALID),
        .M00_AXI_awaddr(smartconnect_0_M00_AXI_AWADDR),
        .M00_AXI_awburst(smartconnect_0_M00_AXI_AWBURST),
        .M00_AXI_awcache(smartconnect_0_M00_AXI_AWCACHE),
        .M00_AXI_awlen(smartconnect_0_M00_AXI_AWLEN),
        .M00_AXI_awlock(smartconnect_0_M00_AXI_AWLOCK),
        .M00_AXI_awprot(smartconnect_0_M00_AXI_AWPROT),
        .M00_AXI_awqos(smartconnect_0_M00_AXI_AWQOS),
        .M00_AXI_awready(smartconnect_0_M00_AXI_AWREADY),
        .M00_AXI_awsize(smartconnect_0_M00_AXI_AWSIZE),
        .M00_AXI_awvalid(smartconnect_0_M00_AXI_AWVALID),
        .M00_AXI_bready(smartconnect_0_M00_AXI_BREADY),
        .M00_AXI_bresp(smartconnect_0_M00_AXI_BRESP),
        .M00_AXI_bvalid(smartconnect_0_M00_AXI_BVALID),
        .M00_AXI_rdata(smartconnect_0_M00_AXI_RDATA),
        .M00_AXI_rlast(smartconnect_0_M00_AXI_RLAST),
        .M00_AXI_rready(smartconnect_0_M00_AXI_RREADY),
        .M00_AXI_rresp(smartconnect_0_M00_AXI_RRESP),
        .M00_AXI_rvalid(smartconnect_0_M00_AXI_RVALID),
        .M00_AXI_wdata(smartconnect_0_M00_AXI_WDATA),
        .M00_AXI_wlast(smartconnect_0_M00_AXI_WLAST),
        .M00_AXI_wready(smartconnect_0_M00_AXI_WREADY),
        .M00_AXI_wstrb(smartconnect_0_M00_AXI_WSTRB),
        .M00_AXI_wvalid(smartconnect_0_M00_AXI_WVALID),
        .S00_AXI_araddr(AXI4_1_ARADDR),
        .S00_AXI_arburst(AXI4_1_ARBURST),
        .S00_AXI_arcache(AXI4_1_ARCACHE),
        .S00_AXI_arid(AXI4_1_ARID),
        .S00_AXI_arlen(AXI4_1_ARLEN),
        .S00_AXI_arlock(AXI4_1_ARLOCK),
        .S00_AXI_arprot(AXI4_1_ARPROT),
        .S00_AXI_arqos(AXI4_1_ARQOS),
        .S00_AXI_arready(AXI4_1_ARREADY),
        .S00_AXI_arsize(AXI4_1_ARSIZE),
        .S00_AXI_arvalid(AXI4_1_ARVALID),
        .S00_AXI_awaddr(AXI4_1_AWADDR),
        .S00_AXI_awburst(AXI4_1_AWBURST),
        .S00_AXI_awcache(AXI4_1_AWCACHE),
        .S00_AXI_awid(AXI4_1_AWID),
        .S00_AXI_awlen(AXI4_1_AWLEN),
        .S00_AXI_awlock(AXI4_1_AWLOCK),
        .S00_AXI_awprot(AXI4_1_AWPROT),
        .S00_AXI_awqos(AXI4_1_AWQOS),
        .S00_AXI_awready(AXI4_1_AWREADY),
        .S00_AXI_awsize(AXI4_1_AWSIZE),
        .S00_AXI_awvalid(AXI4_1_AWVALID),
        .S00_AXI_bid(AXI4_1_BID),
        .S00_AXI_bready(AXI4_1_BREADY),
        .S00_AXI_bresp(AXI4_1_BRESP),
        .S00_AXI_bvalid(AXI4_1_BVALID),
        .S00_AXI_rdata(AXI4_1_RDATA),
        .S00_AXI_rid(AXI4_1_RID),
        .S00_AXI_rlast(AXI4_1_RLAST),
        .S00_AXI_rready(AXI4_1_RREADY),
        .S00_AXI_rresp(AXI4_1_RRESP),
        .S00_AXI_rvalid(AXI4_1_RVALID),
        .S00_AXI_wdata(AXI4_1_WDATA),
        .S00_AXI_wlast(AXI4_1_WLAST),
        .S00_AXI_wready(AXI4_1_WREADY),
        .S00_AXI_wstrb(AXI4_1_WSTRB),
        .S00_AXI_wvalid(AXI4_1_WVALID),
        .aclk(aclk_250_1),
        .aclk1(aclk_450_1),
        .aresetn(aresetn_0_1));
endmodule
