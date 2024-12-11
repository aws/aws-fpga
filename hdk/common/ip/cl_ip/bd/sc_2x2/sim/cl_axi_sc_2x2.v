//Copyright 1986-2022 Xilinx, Inc. All Rights Reserved.
//Copyright 2022-2024 Advanced Micro Devices, Inc. All Rights Reserved.
//--------------------------------------------------------------------------------
//Tool Version: Vivado v.2023.2.2 (lin64) Build 4126759 Thu Feb  8 23:52:05 MST 2024
//Date        : Thu Jun 27 07:55:23 2024
//Host        : xsjgd1 running 64-bit Red Hat Enterprise Linux release 8.2 (Ootpa)
//Command     : generate_target cl_axi_sc_2x2.bd
//Design      : cl_axi_sc_2x2
//Purpose     : IP block netlist
//--------------------------------------------------------------------------------
`timescale 1 ps / 1 ps

(* CORE_GENERATION_INFO = "cl_axi_sc_2x2,IP_Integrator,{x_ipVendor=xilinx.com,x_ipLibrary=BlockDiagram,x_ipName=cl_axi_sc_2x2,x_ipVersion=1.00.a,x_ipLanguage=VERILOG,numBlks=3,numReposBlks=3,numNonXlnxBlks=0,numHierBlks=0,maxHierDepth=0,numSysgenBlks=0,numHlsBlks=0,numHdlrefBlks=0,numPkgbdBlks=0,bdsource=USER,synth_mode=None}" *) (* HW_HANDOFF = "cl_axi_sc_2x2.hwdef" *) 
module cl_axi_sc_2x2
   (ATG_araddr,
    ATG_arburst,
    ATG_arcache,
    ATG_arid,
    ATG_arlen,
    ATG_arlock,
    ATG_arprot,
    ATG_arqos,
    ATG_arready,
    ATG_arregion,
    ATG_arsize,
    ATG_arvalid,
    ATG_awaddr,
    ATG_awburst,
    ATG_awcache,
    ATG_awid,
    ATG_awlen,
    ATG_awlock,
    ATG_awprot,
    ATG_awqos,
    ATG_awready,
    ATG_awregion,
    ATG_awsize,
    ATG_awvalid,
    ATG_bid,
    ATG_bready,
    ATG_bresp,
    ATG_bvalid,
    ATG_rdata,
    ATG_rid,
    ATG_rlast,
    ATG_rready,
    ATG_rresp,
    ATG_rvalid,
    ATG_wdata,
    ATG_wlast,
    ATG_wready,
    ATG_wstrb,
    ATG_wvalid,
    DDRA_araddr,
    DDRA_arburst,
    DDRA_arcache,
    DDRA_arlen,
    DDRA_arlock,
    DDRA_arprot,
    DDRA_arqos,
    DDRA_arready,
    DDRA_arsize,
    DDRA_arvalid,
    DDRA_awaddr,
    DDRA_awburst,
    DDRA_awcache,
    DDRA_awlen,
    DDRA_awlock,
    DDRA_awprot,
    DDRA_awqos,
    DDRA_awready,
    DDRA_awsize,
    DDRA_awvalid,
    DDRA_bready,
    DDRA_bresp,
    DDRA_bvalid,
    DDRA_rdata,
    DDRA_rlast,
    DDRA_rready,
    DDRA_rresp,
    DDRA_rvalid,
    DDRA_wdata,
    DDRA_wlast,
    DDRA_wready,
    DDRA_wstrb,
    DDRA_wvalid,
    DDRB_araddr,
    DDRB_arburst,
    DDRB_arcache,
    DDRB_arlen,
    DDRB_arlock,
    DDRB_arprot,
    DDRB_arqos,
    DDRB_arready,
    DDRB_arsize,
    DDRB_arvalid,
    DDRB_awaddr,
    DDRB_awburst,
    DDRB_awcache,
    DDRB_awlen,
    DDRB_awlock,
    DDRB_awprot,
    DDRB_awqos,
    DDRB_awready,
    DDRB_awsize,
    DDRB_awvalid,
    DDRB_bready,
    DDRB_bresp,
    DDRB_bvalid,
    DDRB_rdata,
    DDRB_rlast,
    DDRB_rready,
    DDRB_rresp,
    DDRB_rvalid,
    DDRB_wdata,
    DDRB_wlast,
    DDRB_wready,
    DDRB_wstrb,
    DDRB_wvalid,
    XDMA_araddr,
    XDMA_arburst,
    XDMA_arcache,
    XDMA_arid,
    XDMA_arlen,
    XDMA_arlock,
    XDMA_arprot,
    XDMA_arqos,
    XDMA_arready,
    XDMA_arregion,
    XDMA_arsize,
    XDMA_arvalid,
    XDMA_awaddr,
    XDMA_awburst,
    XDMA_awcache,
    XDMA_awid,
    XDMA_awlen,
    XDMA_awlock,
    XDMA_awprot,
    XDMA_awqos,
    XDMA_awready,
    XDMA_awregion,
    XDMA_awsize,
    XDMA_awvalid,
    XDMA_bid,
    XDMA_bready,
    XDMA_bresp,
    XDMA_bvalid,
    XDMA_rdata,
    XDMA_rid,
    XDMA_rlast,
    XDMA_rready,
    XDMA_rresp,
    XDMA_rvalid,
    XDMA_wdata,
    XDMA_wlast,
    XDMA_wready,
    XDMA_wstrb,
    XDMA_wvalid,
    aclk_250,
    aresetn_250);
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG ARADDR" *) (* X_INTERFACE_PARAMETER = "XIL_INTERFACENAME ATG, ADDR_WIDTH 64, ARUSER_WIDTH 0, AWUSER_WIDTH 0, BUSER_WIDTH 0, CLK_DOMAIN cl_axi_sc_2x2_aclk_250, DATA_WIDTH 512, FREQ_HZ 100000000, HAS_BRESP 1, HAS_BURST 0, HAS_CACHE 1, HAS_LOCK 1, HAS_PROT 1, HAS_QOS 1, HAS_REGION 1, HAS_RRESP 1, HAS_WSTRB 1, ID_WIDTH 0, INSERT_VIP 0, MAX_BURST_LENGTH 64, NUM_READ_OUTSTANDING 32, NUM_READ_THREADS 1, NUM_WRITE_OUTSTANDING 32, NUM_WRITE_THREADS 1, PHASE 0.0, PROTOCOL AXI4, READ_WRITE_MODE READ_WRITE, RUSER_BITS_PER_BYTE 0, RUSER_WIDTH 0, SUPPORTS_NARROW_BURST 0, WUSER_BITS_PER_BYTE 0, WUSER_WIDTH 0" *) input [63:0]ATG_araddr;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG ARBURST" *) input [1:0]ATG_arburst;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG ARCACHE" *) input [3:0]ATG_arcache;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG ARID" *) input [15:0]ATG_arid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG ARLEN" *) input [7:0]ATG_arlen;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG ARLOCK" *) input [0:0]ATG_arlock;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG ARPROT" *) input [2:0]ATG_arprot;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG ARQOS" *) input [3:0]ATG_arqos;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG ARREADY" *) output ATG_arready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG ARREGION" *) input [3:0]ATG_arregion;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG ARSIZE" *) input [2:0]ATG_arsize;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG ARVALID" *) input ATG_arvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG AWADDR" *) input [63:0]ATG_awaddr;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG AWBURST" *) input [1:0]ATG_awburst;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG AWCACHE" *) input [3:0]ATG_awcache;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG AWID" *) input [15:0]ATG_awid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG AWLEN" *) input [7:0]ATG_awlen;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG AWLOCK" *) input [0:0]ATG_awlock;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG AWPROT" *) input [2:0]ATG_awprot;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG AWQOS" *) input [3:0]ATG_awqos;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG AWREADY" *) output ATG_awready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG AWREGION" *) input [3:0]ATG_awregion;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG AWSIZE" *) input [2:0]ATG_awsize;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG AWVALID" *) input ATG_awvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG BID" *) output [15:0]ATG_bid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG BREADY" *) input ATG_bready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG BRESP" *) output [1:0]ATG_bresp;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG BVALID" *) output ATG_bvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG RDATA" *) output [511:0]ATG_rdata;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG RID" *) output [15:0]ATG_rid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG RLAST" *) output ATG_rlast;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG RREADY" *) input ATG_rready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG RRESP" *) output [1:0]ATG_rresp;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG RVALID" *) output ATG_rvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG WDATA" *) input [511:0]ATG_wdata;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG WLAST" *) input ATG_wlast;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG WREADY" *) output ATG_wready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG WSTRB" *) input [63:0]ATG_wstrb;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 ATG WVALID" *) input ATG_wvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA ARADDR" *) (* X_INTERFACE_PARAMETER = "XIL_INTERFACENAME DDRA, ADDR_WIDTH 64, ARUSER_WIDTH 0, AWUSER_WIDTH 0, BUSER_WIDTH 0, CLK_DOMAIN cl_axi_sc_2x2_aclk_250, DATA_WIDTH 512, FREQ_HZ 100000000, HAS_BRESP 1, HAS_BURST 0, HAS_CACHE 1, HAS_LOCK 1, HAS_PROT 1, HAS_QOS 1, HAS_REGION 0, HAS_RRESP 1, HAS_WSTRB 1, ID_WIDTH 0, INSERT_VIP 0, MAX_BURST_LENGTH 64, NUM_READ_OUTSTANDING 16, NUM_READ_THREADS 1, NUM_WRITE_OUTSTANDING 16, NUM_WRITE_THREADS 1, PHASE 0.0, PROTOCOL AXI4, READ_WRITE_MODE READ_WRITE, RUSER_BITS_PER_BYTE 0, RUSER_WIDTH 0, SUPPORTS_NARROW_BURST 0, WUSER_BITS_PER_BYTE 0, WUSER_WIDTH 0" *) output [63:0]DDRA_araddr;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA ARBURST" *) output [1:0]DDRA_arburst;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA ARCACHE" *) output [3:0]DDRA_arcache;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA ARLEN" *) output [7:0]DDRA_arlen;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA ARLOCK" *) output [0:0]DDRA_arlock;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA ARPROT" *) output [2:0]DDRA_arprot;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA ARQOS" *) output [3:0]DDRA_arqos;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA ARREADY" *) input DDRA_arready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA ARSIZE" *) output [2:0]DDRA_arsize;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA ARVALID" *) output DDRA_arvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA AWADDR" *) output [63:0]DDRA_awaddr;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA AWBURST" *) output [1:0]DDRA_awburst;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA AWCACHE" *) output [3:0]DDRA_awcache;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA AWLEN" *) output [7:0]DDRA_awlen;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA AWLOCK" *) output [0:0]DDRA_awlock;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA AWPROT" *) output [2:0]DDRA_awprot;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA AWQOS" *) output [3:0]DDRA_awqos;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA AWREADY" *) input DDRA_awready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA AWSIZE" *) output [2:0]DDRA_awsize;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA AWVALID" *) output DDRA_awvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA BREADY" *) output DDRA_bready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA BRESP" *) input [1:0]DDRA_bresp;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA BVALID" *) input DDRA_bvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA RDATA" *) input [511:0]DDRA_rdata;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA RLAST" *) input DDRA_rlast;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA RREADY" *) output DDRA_rready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA RRESP" *) input [1:0]DDRA_rresp;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA RVALID" *) input DDRA_rvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA WDATA" *) output [511:0]DDRA_wdata;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA WLAST" *) output DDRA_wlast;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA WREADY" *) input DDRA_wready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA WSTRB" *) output [63:0]DDRA_wstrb;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRA WVALID" *) output DDRA_wvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB ARADDR" *) (* X_INTERFACE_PARAMETER = "XIL_INTERFACENAME DDRB, ADDR_WIDTH 64, ARUSER_WIDTH 0, AWUSER_WIDTH 0, BUSER_WIDTH 0, CLK_DOMAIN cl_axi_sc_2x2_aclk_250, DATA_WIDTH 512, FREQ_HZ 100000000, HAS_BRESP 1, HAS_BURST 0, HAS_CACHE 1, HAS_LOCK 1, HAS_PROT 1, HAS_QOS 1, HAS_REGION 0, HAS_RRESP 1, HAS_WSTRB 1, ID_WIDTH 0, INSERT_VIP 0, MAX_BURST_LENGTH 64, NUM_READ_OUTSTANDING 32, NUM_READ_THREADS 1, NUM_WRITE_OUTSTANDING 32, NUM_WRITE_THREADS 1, PHASE 0.0, PROTOCOL AXI4, READ_WRITE_MODE READ_WRITE, RUSER_BITS_PER_BYTE 0, RUSER_WIDTH 0, SUPPORTS_NARROW_BURST 0, WUSER_BITS_PER_BYTE 0, WUSER_WIDTH 0" *) output [63:0]DDRB_araddr;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB ARBURST" *) output [1:0]DDRB_arburst;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB ARCACHE" *) output [3:0]DDRB_arcache;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB ARLEN" *) output [7:0]DDRB_arlen;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB ARLOCK" *) output [0:0]DDRB_arlock;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB ARPROT" *) output [2:0]DDRB_arprot;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB ARQOS" *) output [3:0]DDRB_arqos;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB ARREADY" *) input DDRB_arready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB ARSIZE" *) output [2:0]DDRB_arsize;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB ARVALID" *) output DDRB_arvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB AWADDR" *) output [63:0]DDRB_awaddr;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB AWBURST" *) output [1:0]DDRB_awburst;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB AWCACHE" *) output [3:0]DDRB_awcache;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB AWLEN" *) output [7:0]DDRB_awlen;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB AWLOCK" *) output [0:0]DDRB_awlock;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB AWPROT" *) output [2:0]DDRB_awprot;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB AWQOS" *) output [3:0]DDRB_awqos;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB AWREADY" *) input DDRB_awready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB AWSIZE" *) output [2:0]DDRB_awsize;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB AWVALID" *) output DDRB_awvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB BREADY" *) output DDRB_bready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB BRESP" *) input [1:0]DDRB_bresp;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB BVALID" *) input DDRB_bvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB RDATA" *) input [511:0]DDRB_rdata;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB RLAST" *) input DDRB_rlast;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB RREADY" *) output DDRB_rready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB RRESP" *) input [1:0]DDRB_rresp;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB RVALID" *) input DDRB_rvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB WDATA" *) output [511:0]DDRB_wdata;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB WLAST" *) output DDRB_wlast;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB WREADY" *) input DDRB_wready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB WSTRB" *) output [63:0]DDRB_wstrb;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 DDRB WVALID" *) output DDRB_wvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA ARADDR" *) (* X_INTERFACE_PARAMETER = "XIL_INTERFACENAME XDMA, ADDR_WIDTH 64, ARUSER_WIDTH 0, AWUSER_WIDTH 0, BUSER_WIDTH 0, CLK_DOMAIN cl_axi_sc_2x2_aclk_250, DATA_WIDTH 512, FREQ_HZ 100000000, HAS_BRESP 1, HAS_BURST 0, HAS_CACHE 1, HAS_LOCK 1, HAS_PROT 1, HAS_QOS 1, HAS_REGION 1, HAS_RRESP 1, HAS_WSTRB 1, ID_WIDTH 16, INSERT_VIP 0, MAX_BURST_LENGTH 64, NUM_READ_OUTSTANDING 64, NUM_READ_THREADS 4, NUM_WRITE_OUTSTANDING 32, NUM_WRITE_THREADS 4, PHASE 0.0, PROTOCOL AXI4, READ_WRITE_MODE READ_WRITE, RUSER_BITS_PER_BYTE 0, RUSER_WIDTH 0, SUPPORTS_NARROW_BURST 0, WUSER_BITS_PER_BYTE 0, WUSER_WIDTH 0" *) input [63:0]XDMA_araddr;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA ARBURST" *) input [1:0]XDMA_arburst;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA ARCACHE" *) input [3:0]XDMA_arcache;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA ARID" *) input [15:0]XDMA_arid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA ARLEN" *) input [7:0]XDMA_arlen;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA ARLOCK" *) input [0:0]XDMA_arlock;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA ARPROT" *) input [2:0]XDMA_arprot;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA ARQOS" *) input [3:0]XDMA_arqos;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA ARREADY" *) output XDMA_arready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA ARREGION" *) input [3:0]XDMA_arregion;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA ARSIZE" *) input [2:0]XDMA_arsize;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA ARVALID" *) input XDMA_arvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA AWADDR" *) input [63:0]XDMA_awaddr;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA AWBURST" *) input [1:0]XDMA_awburst;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA AWCACHE" *) input [3:0]XDMA_awcache;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA AWID" *) input [15:0]XDMA_awid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA AWLEN" *) input [7:0]XDMA_awlen;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA AWLOCK" *) input [0:0]XDMA_awlock;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA AWPROT" *) input [2:0]XDMA_awprot;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA AWQOS" *) input [3:0]XDMA_awqos;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA AWREADY" *) output XDMA_awready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA AWREGION" *) input [3:0]XDMA_awregion;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA AWSIZE" *) input [2:0]XDMA_awsize;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA AWVALID" *) input XDMA_awvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA BID" *) output [15:0]XDMA_bid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA BREADY" *) input XDMA_bready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA BRESP" *) output [1:0]XDMA_bresp;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA BVALID" *) output XDMA_bvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA RDATA" *) output [511:0]XDMA_rdata;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA RID" *) output [15:0]XDMA_rid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA RLAST" *) output XDMA_rlast;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA RREADY" *) input XDMA_rready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA RRESP" *) output [1:0]XDMA_rresp;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA RVALID" *) output XDMA_rvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA WDATA" *) input [511:0]XDMA_wdata;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA WLAST" *) input XDMA_wlast;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA WREADY" *) output XDMA_wready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA WSTRB" *) input [63:0]XDMA_wstrb;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 XDMA WVALID" *) input XDMA_wvalid;
  (* X_INTERFACE_INFO = "xilinx.com:signal:clock:1.0 CLK.ACLK_250 CLK" *) (* X_INTERFACE_PARAMETER = "XIL_INTERFACENAME CLK.ACLK_250, ASSOCIATED_BUSIF DDRA:XDMA:ATG:DDRB, ASSOCIATED_RESET aresetn_250, CLK_DOMAIN cl_axi_sc_2x2_aclk_250, FREQ_HZ 100000000, FREQ_TOLERANCE_HZ 0, INSERT_VIP 0, PHASE 0.0" *) input aclk_250;
  (* X_INTERFACE_INFO = "xilinx.com:signal:reset:1.0 RST.ARESETN_250 RST" *) (* X_INTERFACE_PARAMETER = "XIL_INTERFACENAME RST.ARESETN_250, INSERT_VIP 0, POLARITY ACTIVE_LOW" *) input aresetn_250;

  wire [63:0]ATG_1_ARADDR;
  wire [1:0]ATG_1_ARBURST;
  wire [3:0]ATG_1_ARCACHE;
  wire [15:0]ATG_1_ARID;
  wire [7:0]ATG_1_ARLEN;
  wire [0:0]ATG_1_ARLOCK;
  wire [2:0]ATG_1_ARPROT;
  wire [3:0]ATG_1_ARQOS;
  wire ATG_1_ARREADY;
  wire [3:0]ATG_1_ARREGION;
  wire [2:0]ATG_1_ARSIZE;
  wire ATG_1_ARVALID;
  wire [63:0]ATG_1_AWADDR;
  wire [1:0]ATG_1_AWBURST;
  wire [3:0]ATG_1_AWCACHE;
  wire [15:0]ATG_1_AWID;
  wire [7:0]ATG_1_AWLEN;
  wire [0:0]ATG_1_AWLOCK;
  wire [2:0]ATG_1_AWPROT;
  wire [3:0]ATG_1_AWQOS;
  wire ATG_1_AWREADY;
  wire [3:0]ATG_1_AWREGION;
  wire [2:0]ATG_1_AWSIZE;
  wire ATG_1_AWVALID;
  wire [15:0]ATG_1_BID;
  wire ATG_1_BREADY;
  wire [1:0]ATG_1_BRESP;
  wire ATG_1_BVALID;
  wire [511:0]ATG_1_RDATA;
  wire [15:0]ATG_1_RID;
  wire ATG_1_RLAST;
  wire ATG_1_RREADY;
  wire [1:0]ATG_1_RRESP;
  wire ATG_1_RVALID;
  wire [511:0]ATG_1_WDATA;
  wire ATG_1_WLAST;
  wire ATG_1_WREADY;
  wire [63:0]ATG_1_WSTRB;
  wire ATG_1_WVALID;
  wire [63:0]XDMA_1_ARADDR;
  wire [1:0]XDMA_1_ARBURST;
  wire [3:0]XDMA_1_ARCACHE;
  wire [15:0]XDMA_1_ARID;
  wire [7:0]XDMA_1_ARLEN;
  wire [0:0]XDMA_1_ARLOCK;
  wire [2:0]XDMA_1_ARPROT;
  wire [3:0]XDMA_1_ARQOS;
  wire XDMA_1_ARREADY;
  wire [3:0]XDMA_1_ARREGION;
  wire [2:0]XDMA_1_ARSIZE;
  wire XDMA_1_ARVALID;
  wire [63:0]XDMA_1_AWADDR;
  wire [1:0]XDMA_1_AWBURST;
  wire [3:0]XDMA_1_AWCACHE;
  wire [15:0]XDMA_1_AWID;
  wire [7:0]XDMA_1_AWLEN;
  wire [0:0]XDMA_1_AWLOCK;
  wire [2:0]XDMA_1_AWPROT;
  wire [3:0]XDMA_1_AWQOS;
  wire XDMA_1_AWREADY;
  wire [3:0]XDMA_1_AWREGION;
  wire [2:0]XDMA_1_AWSIZE;
  wire XDMA_1_AWVALID;
  wire [15:0]XDMA_1_BID;
  wire XDMA_1_BREADY;
  wire [1:0]XDMA_1_BRESP;
  wire XDMA_1_BVALID;
  wire [511:0]XDMA_1_RDATA;
  wire [15:0]XDMA_1_RID;
  wire XDMA_1_RLAST;
  wire XDMA_1_RREADY;
  wire [1:0]XDMA_1_RRESP;
  wire XDMA_1_RVALID;
  wire [511:0]XDMA_1_WDATA;
  wire XDMA_1_WLAST;
  wire XDMA_1_WREADY;
  wire [63:0]XDMA_1_WSTRB;
  wire XDMA_1_WVALID;
  wire aclk_0_1;
  wire aresetn_0_1;
  wire [63:0]fifo_generator_atg_M_AXI_ARADDR;
  wire [1:0]fifo_generator_atg_M_AXI_ARBURST;
  wire [3:0]fifo_generator_atg_M_AXI_ARCACHE;
  wire [15:0]fifo_generator_atg_M_AXI_ARID;
  wire [7:0]fifo_generator_atg_M_AXI_ARLEN;
  wire [0:0]fifo_generator_atg_M_AXI_ARLOCK;
  wire [2:0]fifo_generator_atg_M_AXI_ARPROT;
  wire [3:0]fifo_generator_atg_M_AXI_ARQOS;
  wire fifo_generator_atg_M_AXI_ARREADY;
  wire [2:0]fifo_generator_atg_M_AXI_ARSIZE;
  wire fifo_generator_atg_M_AXI_ARVALID;
  wire [63:0]fifo_generator_atg_M_AXI_AWADDR;
  wire [1:0]fifo_generator_atg_M_AXI_AWBURST;
  wire [3:0]fifo_generator_atg_M_AXI_AWCACHE;
  wire [15:0]fifo_generator_atg_M_AXI_AWID;
  wire [7:0]fifo_generator_atg_M_AXI_AWLEN;
  wire [0:0]fifo_generator_atg_M_AXI_AWLOCK;
  wire [2:0]fifo_generator_atg_M_AXI_AWPROT;
  wire [3:0]fifo_generator_atg_M_AXI_AWQOS;
  wire fifo_generator_atg_M_AXI_AWREADY;
  wire [2:0]fifo_generator_atg_M_AXI_AWSIZE;
  wire fifo_generator_atg_M_AXI_AWVALID;
  wire [15:0]fifo_generator_atg_M_AXI_BID;
  wire fifo_generator_atg_M_AXI_BREADY;
  wire [1:0]fifo_generator_atg_M_AXI_BRESP;
  wire fifo_generator_atg_M_AXI_BVALID;
  wire [511:0]fifo_generator_atg_M_AXI_RDATA;
  wire [15:0]fifo_generator_atg_M_AXI_RID;
  wire fifo_generator_atg_M_AXI_RLAST;
  wire fifo_generator_atg_M_AXI_RREADY;
  wire [1:0]fifo_generator_atg_M_AXI_RRESP;
  wire fifo_generator_atg_M_AXI_RVALID;
  wire [511:0]fifo_generator_atg_M_AXI_WDATA;
  wire fifo_generator_atg_M_AXI_WLAST;
  wire fifo_generator_atg_M_AXI_WREADY;
  wire [63:0]fifo_generator_atg_M_AXI_WSTRB;
  wire fifo_generator_atg_M_AXI_WVALID;
  wire [63:0]fifo_generator_xdma_M_AXI_ARADDR;
  wire [1:0]fifo_generator_xdma_M_AXI_ARBURST;
  wire [3:0]fifo_generator_xdma_M_AXI_ARCACHE;
  wire [15:0]fifo_generator_xdma_M_AXI_ARID;
  wire [7:0]fifo_generator_xdma_M_AXI_ARLEN;
  wire [0:0]fifo_generator_xdma_M_AXI_ARLOCK;
  wire [2:0]fifo_generator_xdma_M_AXI_ARPROT;
  wire [3:0]fifo_generator_xdma_M_AXI_ARQOS;
  wire fifo_generator_xdma_M_AXI_ARREADY;
  wire [2:0]fifo_generator_xdma_M_AXI_ARSIZE;
  wire fifo_generator_xdma_M_AXI_ARVALID;
  wire [63:0]fifo_generator_xdma_M_AXI_AWADDR;
  wire [1:0]fifo_generator_xdma_M_AXI_AWBURST;
  wire [3:0]fifo_generator_xdma_M_AXI_AWCACHE;
  wire [15:0]fifo_generator_xdma_M_AXI_AWID;
  wire [7:0]fifo_generator_xdma_M_AXI_AWLEN;
  wire [0:0]fifo_generator_xdma_M_AXI_AWLOCK;
  wire [2:0]fifo_generator_xdma_M_AXI_AWPROT;
  wire [3:0]fifo_generator_xdma_M_AXI_AWQOS;
  wire fifo_generator_xdma_M_AXI_AWREADY;
  wire [2:0]fifo_generator_xdma_M_AXI_AWSIZE;
  wire fifo_generator_xdma_M_AXI_AWVALID;
  wire [15:0]fifo_generator_xdma_M_AXI_BID;
  wire fifo_generator_xdma_M_AXI_BREADY;
  wire [1:0]fifo_generator_xdma_M_AXI_BRESP;
  wire fifo_generator_xdma_M_AXI_BVALID;
  wire [511:0]fifo_generator_xdma_M_AXI_RDATA;
  wire [15:0]fifo_generator_xdma_M_AXI_RID;
  wire fifo_generator_xdma_M_AXI_RLAST;
  wire fifo_generator_xdma_M_AXI_RREADY;
  wire [1:0]fifo_generator_xdma_M_AXI_RRESP;
  wire fifo_generator_xdma_M_AXI_RVALID;
  wire [511:0]fifo_generator_xdma_M_AXI_WDATA;
  wire fifo_generator_xdma_M_AXI_WLAST;
  wire fifo_generator_xdma_M_AXI_WREADY;
  wire [63:0]fifo_generator_xdma_M_AXI_WSTRB;
  wire fifo_generator_xdma_M_AXI_WVALID;
  wire [63:0]smartconnect_0_M00_AXI_ARADDR;
  wire [1:0]smartconnect_0_M00_AXI_ARBURST;
  wire [3:0]smartconnect_0_M00_AXI_ARCACHE;
  wire [7:0]smartconnect_0_M00_AXI_ARLEN;
  wire [0:0]smartconnect_0_M00_AXI_ARLOCK;
  wire [2:0]smartconnect_0_M00_AXI_ARPROT;
  wire [3:0]smartconnect_0_M00_AXI_ARQOS;
  wire smartconnect_0_M00_AXI_ARREADY;
  wire [2:0]smartconnect_0_M00_AXI_ARSIZE;
  wire smartconnect_0_M00_AXI_ARVALID;
  wire [63:0]smartconnect_0_M00_AXI_AWADDR;
  wire [1:0]smartconnect_0_M00_AXI_AWBURST;
  wire [3:0]smartconnect_0_M00_AXI_AWCACHE;
  wire [7:0]smartconnect_0_M00_AXI_AWLEN;
  wire [0:0]smartconnect_0_M00_AXI_AWLOCK;
  wire [2:0]smartconnect_0_M00_AXI_AWPROT;
  wire [3:0]smartconnect_0_M00_AXI_AWQOS;
  wire smartconnect_0_M00_AXI_AWREADY;
  wire [2:0]smartconnect_0_M00_AXI_AWSIZE;
  wire smartconnect_0_M00_AXI_AWVALID;
  wire smartconnect_0_M00_AXI_BREADY;
  wire [1:0]smartconnect_0_M00_AXI_BRESP;
  wire smartconnect_0_M00_AXI_BVALID;
  wire [511:0]smartconnect_0_M00_AXI_RDATA;
  wire smartconnect_0_M00_AXI_RLAST;
  wire smartconnect_0_M00_AXI_RREADY;
  wire [1:0]smartconnect_0_M00_AXI_RRESP;
  wire smartconnect_0_M00_AXI_RVALID;
  wire [511:0]smartconnect_0_M00_AXI_WDATA;
  wire smartconnect_0_M00_AXI_WLAST;
  wire smartconnect_0_M00_AXI_WREADY;
  wire [63:0]smartconnect_0_M00_AXI_WSTRB;
  wire smartconnect_0_M00_AXI_WVALID;
  wire [63:0]smartconnect_0_M01_AXI_ARADDR;
  wire [1:0]smartconnect_0_M01_AXI_ARBURST;
  wire [3:0]smartconnect_0_M01_AXI_ARCACHE;
  wire [7:0]smartconnect_0_M01_AXI_ARLEN;
  wire [0:0]smartconnect_0_M01_AXI_ARLOCK;
  wire [2:0]smartconnect_0_M01_AXI_ARPROT;
  wire [3:0]smartconnect_0_M01_AXI_ARQOS;
  wire smartconnect_0_M01_AXI_ARREADY;
  wire [2:0]smartconnect_0_M01_AXI_ARSIZE;
  wire smartconnect_0_M01_AXI_ARVALID;
  wire [63:0]smartconnect_0_M01_AXI_AWADDR;
  wire [1:0]smartconnect_0_M01_AXI_AWBURST;
  wire [3:0]smartconnect_0_M01_AXI_AWCACHE;
  wire [7:0]smartconnect_0_M01_AXI_AWLEN;
  wire [0:0]smartconnect_0_M01_AXI_AWLOCK;
  wire [2:0]smartconnect_0_M01_AXI_AWPROT;
  wire [3:0]smartconnect_0_M01_AXI_AWQOS;
  wire smartconnect_0_M01_AXI_AWREADY;
  wire [2:0]smartconnect_0_M01_AXI_AWSIZE;
  wire smartconnect_0_M01_AXI_AWVALID;
  wire smartconnect_0_M01_AXI_BREADY;
  wire [1:0]smartconnect_0_M01_AXI_BRESP;
  wire smartconnect_0_M01_AXI_BVALID;
  wire [511:0]smartconnect_0_M01_AXI_RDATA;
  wire smartconnect_0_M01_AXI_RLAST;
  wire smartconnect_0_M01_AXI_RREADY;
  wire [1:0]smartconnect_0_M01_AXI_RRESP;
  wire smartconnect_0_M01_AXI_RVALID;
  wire [511:0]smartconnect_0_M01_AXI_WDATA;
  wire smartconnect_0_M01_AXI_WLAST;
  wire smartconnect_0_M01_AXI_WREADY;
  wire [63:0]smartconnect_0_M01_AXI_WSTRB;
  wire smartconnect_0_M01_AXI_WVALID;

  assign ATG_1_ARADDR = ATG_araddr[63:0];
  assign ATG_1_ARBURST = ATG_arburst[1:0];
  assign ATG_1_ARCACHE = ATG_arcache[3:0];
  assign ATG_1_ARID = ATG_arid[15:0];
  assign ATG_1_ARLEN = ATG_arlen[7:0];
  assign ATG_1_ARLOCK = ATG_arlock[0];
  assign ATG_1_ARPROT = ATG_arprot[2:0];
  assign ATG_1_ARQOS = ATG_arqos[3:0];
  assign ATG_1_ARREGION = ATG_arregion[3:0];
  assign ATG_1_ARSIZE = ATG_arsize[2:0];
  assign ATG_1_ARVALID = ATG_arvalid;
  assign ATG_1_AWADDR = ATG_awaddr[63:0];
  assign ATG_1_AWBURST = ATG_awburst[1:0];
  assign ATG_1_AWCACHE = ATG_awcache[3:0];
  assign ATG_1_AWID = ATG_awid[15:0];
  assign ATG_1_AWLEN = ATG_awlen[7:0];
  assign ATG_1_AWLOCK = ATG_awlock[0];
  assign ATG_1_AWPROT = ATG_awprot[2:0];
  assign ATG_1_AWQOS = ATG_awqos[3:0];
  assign ATG_1_AWREGION = ATG_awregion[3:0];
  assign ATG_1_AWSIZE = ATG_awsize[2:0];
  assign ATG_1_AWVALID = ATG_awvalid;
  assign ATG_1_BREADY = ATG_bready;
  assign ATG_1_RREADY = ATG_rready;
  assign ATG_1_WDATA = ATG_wdata[511:0];
  assign ATG_1_WLAST = ATG_wlast;
  assign ATG_1_WSTRB = ATG_wstrb[63:0];
  assign ATG_1_WVALID = ATG_wvalid;
  assign ATG_arready = ATG_1_ARREADY;
  assign ATG_awready = ATG_1_AWREADY;
  assign ATG_bid[15:0] = ATG_1_BID;
  assign ATG_bresp[1:0] = ATG_1_BRESP;
  assign ATG_bvalid = ATG_1_BVALID;
  assign ATG_rdata[511:0] = ATG_1_RDATA;
  assign ATG_rid[15:0] = ATG_1_RID;
  assign ATG_rlast = ATG_1_RLAST;
  assign ATG_rresp[1:0] = ATG_1_RRESP;
  assign ATG_rvalid = ATG_1_RVALID;
  assign ATG_wready = ATG_1_WREADY;
  assign DDRA_araddr[63:0] = smartconnect_0_M00_AXI_ARADDR;
  assign DDRA_arburst[1:0] = smartconnect_0_M00_AXI_ARBURST;
  assign DDRA_arcache[3:0] = smartconnect_0_M00_AXI_ARCACHE;
  assign DDRA_arlen[7:0] = smartconnect_0_M00_AXI_ARLEN;
  assign DDRA_arlock[0] = smartconnect_0_M00_AXI_ARLOCK;
  assign DDRA_arprot[2:0] = smartconnect_0_M00_AXI_ARPROT;
  assign DDRA_arqos[3:0] = smartconnect_0_M00_AXI_ARQOS;
  assign DDRA_arsize[2:0] = smartconnect_0_M00_AXI_ARSIZE;
  assign DDRA_arvalid = smartconnect_0_M00_AXI_ARVALID;
  assign DDRA_awaddr[63:0] = smartconnect_0_M00_AXI_AWADDR;
  assign DDRA_awburst[1:0] = smartconnect_0_M00_AXI_AWBURST;
  assign DDRA_awcache[3:0] = smartconnect_0_M00_AXI_AWCACHE;
  assign DDRA_awlen[7:0] = smartconnect_0_M00_AXI_AWLEN;
  assign DDRA_awlock[0] = smartconnect_0_M00_AXI_AWLOCK;
  assign DDRA_awprot[2:0] = smartconnect_0_M00_AXI_AWPROT;
  assign DDRA_awqos[3:0] = smartconnect_0_M00_AXI_AWQOS;
  assign DDRA_awsize[2:0] = smartconnect_0_M00_AXI_AWSIZE;
  assign DDRA_awvalid = smartconnect_0_M00_AXI_AWVALID;
  assign DDRA_bready = smartconnect_0_M00_AXI_BREADY;
  assign DDRA_rready = smartconnect_0_M00_AXI_RREADY;
  assign DDRA_wdata[511:0] = smartconnect_0_M00_AXI_WDATA;
  assign DDRA_wlast = smartconnect_0_M00_AXI_WLAST;
  assign DDRA_wstrb[63:0] = smartconnect_0_M00_AXI_WSTRB;
  assign DDRA_wvalid = smartconnect_0_M00_AXI_WVALID;
  assign DDRB_araddr[63:0] = smartconnect_0_M01_AXI_ARADDR;
  assign DDRB_arburst[1:0] = smartconnect_0_M01_AXI_ARBURST;
  assign DDRB_arcache[3:0] = smartconnect_0_M01_AXI_ARCACHE;
  assign DDRB_arlen[7:0] = smartconnect_0_M01_AXI_ARLEN;
  assign DDRB_arlock[0] = smartconnect_0_M01_AXI_ARLOCK;
  assign DDRB_arprot[2:0] = smartconnect_0_M01_AXI_ARPROT;
  assign DDRB_arqos[3:0] = smartconnect_0_M01_AXI_ARQOS;
  assign DDRB_arsize[2:0] = smartconnect_0_M01_AXI_ARSIZE;
  assign DDRB_arvalid = smartconnect_0_M01_AXI_ARVALID;
  assign DDRB_awaddr[63:0] = smartconnect_0_M01_AXI_AWADDR;
  assign DDRB_awburst[1:0] = smartconnect_0_M01_AXI_AWBURST;
  assign DDRB_awcache[3:0] = smartconnect_0_M01_AXI_AWCACHE;
  assign DDRB_awlen[7:0] = smartconnect_0_M01_AXI_AWLEN;
  assign DDRB_awlock[0] = smartconnect_0_M01_AXI_AWLOCK;
  assign DDRB_awprot[2:0] = smartconnect_0_M01_AXI_AWPROT;
  assign DDRB_awqos[3:0] = smartconnect_0_M01_AXI_AWQOS;
  assign DDRB_awsize[2:0] = smartconnect_0_M01_AXI_AWSIZE;
  assign DDRB_awvalid = smartconnect_0_M01_AXI_AWVALID;
  assign DDRB_bready = smartconnect_0_M01_AXI_BREADY;
  assign DDRB_rready = smartconnect_0_M01_AXI_RREADY;
  assign DDRB_wdata[511:0] = smartconnect_0_M01_AXI_WDATA;
  assign DDRB_wlast = smartconnect_0_M01_AXI_WLAST;
  assign DDRB_wstrb[63:0] = smartconnect_0_M01_AXI_WSTRB;
  assign DDRB_wvalid = smartconnect_0_M01_AXI_WVALID;
  assign XDMA_1_ARADDR = XDMA_araddr[63:0];
  assign XDMA_1_ARBURST = XDMA_arburst[1:0];
  assign XDMA_1_ARCACHE = XDMA_arcache[3:0];
  assign XDMA_1_ARID = XDMA_arid[15:0];
  assign XDMA_1_ARLEN = XDMA_arlen[7:0];
  assign XDMA_1_ARLOCK = XDMA_arlock[0];
  assign XDMA_1_ARPROT = XDMA_arprot[2:0];
  assign XDMA_1_ARQOS = XDMA_arqos[3:0];
  assign XDMA_1_ARREGION = XDMA_arregion[3:0];
  assign XDMA_1_ARSIZE = XDMA_arsize[2:0];
  assign XDMA_1_ARVALID = XDMA_arvalid;
  assign XDMA_1_AWADDR = XDMA_awaddr[63:0];
  assign XDMA_1_AWBURST = XDMA_awburst[1:0];
  assign XDMA_1_AWCACHE = XDMA_awcache[3:0];
  assign XDMA_1_AWID = XDMA_awid[15:0];
  assign XDMA_1_AWLEN = XDMA_awlen[7:0];
  assign XDMA_1_AWLOCK = XDMA_awlock[0];
  assign XDMA_1_AWPROT = XDMA_awprot[2:0];
  assign XDMA_1_AWQOS = XDMA_awqos[3:0];
  assign XDMA_1_AWREGION = XDMA_awregion[3:0];
  assign XDMA_1_AWSIZE = XDMA_awsize[2:0];
  assign XDMA_1_AWVALID = XDMA_awvalid;
  assign XDMA_1_BREADY = XDMA_bready;
  assign XDMA_1_RREADY = XDMA_rready;
  assign XDMA_1_WDATA = XDMA_wdata[511:0];
  assign XDMA_1_WLAST = XDMA_wlast;
  assign XDMA_1_WSTRB = XDMA_wstrb[63:0];
  assign XDMA_1_WVALID = XDMA_wvalid;
  assign XDMA_arready = XDMA_1_ARREADY;
  assign XDMA_awready = XDMA_1_AWREADY;
  assign XDMA_bid[15:0] = XDMA_1_BID;
  assign XDMA_bresp[1:0] = XDMA_1_BRESP;
  assign XDMA_bvalid = XDMA_1_BVALID;
  assign XDMA_rdata[511:0] = XDMA_1_RDATA;
  assign XDMA_rid[15:0] = XDMA_1_RID;
  assign XDMA_rlast = XDMA_1_RLAST;
  assign XDMA_rresp[1:0] = XDMA_1_RRESP;
  assign XDMA_rvalid = XDMA_1_RVALID;
  assign XDMA_wready = XDMA_1_WREADY;
  assign aclk_0_1 = aclk_250;
  assign aresetn_0_1 = aresetn_250;
  assign smartconnect_0_M00_AXI_ARREADY = DDRA_arready;
  assign smartconnect_0_M00_AXI_AWREADY = DDRA_awready;
  assign smartconnect_0_M00_AXI_BRESP = DDRA_bresp[1:0];
  assign smartconnect_0_M00_AXI_BVALID = DDRA_bvalid;
  assign smartconnect_0_M00_AXI_RDATA = DDRA_rdata[511:0];
  assign smartconnect_0_M00_AXI_RLAST = DDRA_rlast;
  assign smartconnect_0_M00_AXI_RRESP = DDRA_rresp[1:0];
  assign smartconnect_0_M00_AXI_RVALID = DDRA_rvalid;
  assign smartconnect_0_M00_AXI_WREADY = DDRA_wready;
  assign smartconnect_0_M01_AXI_ARREADY = DDRB_arready;
  assign smartconnect_0_M01_AXI_AWREADY = DDRB_awready;
  assign smartconnect_0_M01_AXI_BRESP = DDRB_bresp[1:0];
  assign smartconnect_0_M01_AXI_BVALID = DDRB_bvalid;
  assign smartconnect_0_M01_AXI_RDATA = DDRB_rdata[511:0];
  assign smartconnect_0_M01_AXI_RLAST = DDRB_rlast;
  assign smartconnect_0_M01_AXI_RRESP = DDRB_rresp[1:0];
  assign smartconnect_0_M01_AXI_RVALID = DDRB_rvalid;
  assign smartconnect_0_M01_AXI_WREADY = DDRB_wready;
  cl_axi_sc_2x2_fifo_generator_xdma_0 fifo_generator_atg
       (.m_axi_araddr(fifo_generator_atg_M_AXI_ARADDR),
        .m_axi_arburst(fifo_generator_atg_M_AXI_ARBURST),
        .m_axi_arcache(fifo_generator_atg_M_AXI_ARCACHE),
        .m_axi_arid(fifo_generator_atg_M_AXI_ARID),
        .m_axi_arlen(fifo_generator_atg_M_AXI_ARLEN),
        .m_axi_arlock(fifo_generator_atg_M_AXI_ARLOCK),
        .m_axi_arprot(fifo_generator_atg_M_AXI_ARPROT),
        .m_axi_arqos(fifo_generator_atg_M_AXI_ARQOS),
        .m_axi_arready(fifo_generator_atg_M_AXI_ARREADY),
        .m_axi_arsize(fifo_generator_atg_M_AXI_ARSIZE),
        .m_axi_arvalid(fifo_generator_atg_M_AXI_ARVALID),
        .m_axi_awaddr(fifo_generator_atg_M_AXI_AWADDR),
        .m_axi_awburst(fifo_generator_atg_M_AXI_AWBURST),
        .m_axi_awcache(fifo_generator_atg_M_AXI_AWCACHE),
        .m_axi_awid(fifo_generator_atg_M_AXI_AWID),
        .m_axi_awlen(fifo_generator_atg_M_AXI_AWLEN),
        .m_axi_awlock(fifo_generator_atg_M_AXI_AWLOCK),
        .m_axi_awprot(fifo_generator_atg_M_AXI_AWPROT),
        .m_axi_awqos(fifo_generator_atg_M_AXI_AWQOS),
        .m_axi_awready(fifo_generator_atg_M_AXI_AWREADY),
        .m_axi_awsize(fifo_generator_atg_M_AXI_AWSIZE),
        .m_axi_awvalid(fifo_generator_atg_M_AXI_AWVALID),
        .m_axi_bid(fifo_generator_atg_M_AXI_BID),
        .m_axi_bready(fifo_generator_atg_M_AXI_BREADY),
        .m_axi_bresp(fifo_generator_atg_M_AXI_BRESP),
        .m_axi_bvalid(fifo_generator_atg_M_AXI_BVALID),
        .m_axi_rdata(fifo_generator_atg_M_AXI_RDATA),
        .m_axi_rid(fifo_generator_atg_M_AXI_RID),
        .m_axi_rlast(fifo_generator_atg_M_AXI_RLAST),
        .m_axi_rready(fifo_generator_atg_M_AXI_RREADY),
        .m_axi_rresp(fifo_generator_atg_M_AXI_RRESP),
        .m_axi_rvalid(fifo_generator_atg_M_AXI_RVALID),
        .m_axi_wdata(fifo_generator_atg_M_AXI_WDATA),
        .m_axi_wlast(fifo_generator_atg_M_AXI_WLAST),
        .m_axi_wready(fifo_generator_atg_M_AXI_WREADY),
        .m_axi_wstrb(fifo_generator_atg_M_AXI_WSTRB),
        .m_axi_wvalid(fifo_generator_atg_M_AXI_WVALID),
        .s_aclk(aclk_0_1),
        .s_aresetn(aresetn_0_1),
        .s_axi_araddr(ATG_1_ARADDR),
        .s_axi_arburst(ATG_1_ARBURST),
        .s_axi_arcache(ATG_1_ARCACHE),
        .s_axi_arid(ATG_1_ARID),
        .s_axi_arlen(ATG_1_ARLEN),
        .s_axi_arlock(ATG_1_ARLOCK),
        .s_axi_arprot(ATG_1_ARPROT),
        .s_axi_arqos(ATG_1_ARQOS),
        .s_axi_arready(ATG_1_ARREADY),
        .s_axi_arregion(ATG_1_ARREGION),
        .s_axi_arsize(ATG_1_ARSIZE),
        .s_axi_arvalid(ATG_1_ARVALID),
        .s_axi_awaddr(ATG_1_AWADDR),
        .s_axi_awburst(ATG_1_AWBURST),
        .s_axi_awcache(ATG_1_AWCACHE),
        .s_axi_awid(ATG_1_AWID),
        .s_axi_awlen(ATG_1_AWLEN),
        .s_axi_awlock(ATG_1_AWLOCK),
        .s_axi_awprot(ATG_1_AWPROT),
        .s_axi_awqos(ATG_1_AWQOS),
        .s_axi_awready(ATG_1_AWREADY),
        .s_axi_awregion(ATG_1_AWREGION),
        .s_axi_awsize(ATG_1_AWSIZE),
        .s_axi_awvalid(ATG_1_AWVALID),
        .s_axi_bid(ATG_1_BID),
        .s_axi_bready(ATG_1_BREADY),
        .s_axi_bresp(ATG_1_BRESP),
        .s_axi_bvalid(ATG_1_BVALID),
        .s_axi_rdata(ATG_1_RDATA),
        .s_axi_rid(ATG_1_RID),
        .s_axi_rlast(ATG_1_RLAST),
        .s_axi_rready(ATG_1_RREADY),
        .s_axi_rresp(ATG_1_RRESP),
        .s_axi_rvalid(ATG_1_RVALID),
        .s_axi_wdata(ATG_1_WDATA),
        .s_axi_wlast(ATG_1_WLAST),
        .s_axi_wready(ATG_1_WREADY),
        .s_axi_wstrb(ATG_1_WSTRB),
        .s_axi_wvalid(ATG_1_WVALID));
  cl_axi_sc_2x2_fifo_generator_0_0 fifo_generator_xdma
       (.m_axi_araddr(fifo_generator_xdma_M_AXI_ARADDR),
        .m_axi_arburst(fifo_generator_xdma_M_AXI_ARBURST),
        .m_axi_arcache(fifo_generator_xdma_M_AXI_ARCACHE),
        .m_axi_arid(fifo_generator_xdma_M_AXI_ARID),
        .m_axi_arlen(fifo_generator_xdma_M_AXI_ARLEN),
        .m_axi_arlock(fifo_generator_xdma_M_AXI_ARLOCK),
        .m_axi_arprot(fifo_generator_xdma_M_AXI_ARPROT),
        .m_axi_arqos(fifo_generator_xdma_M_AXI_ARQOS),
        .m_axi_arready(fifo_generator_xdma_M_AXI_ARREADY),
        .m_axi_arsize(fifo_generator_xdma_M_AXI_ARSIZE),
        .m_axi_arvalid(fifo_generator_xdma_M_AXI_ARVALID),
        .m_axi_awaddr(fifo_generator_xdma_M_AXI_AWADDR),
        .m_axi_awburst(fifo_generator_xdma_M_AXI_AWBURST),
        .m_axi_awcache(fifo_generator_xdma_M_AXI_AWCACHE),
        .m_axi_awid(fifo_generator_xdma_M_AXI_AWID),
        .m_axi_awlen(fifo_generator_xdma_M_AXI_AWLEN),
        .m_axi_awlock(fifo_generator_xdma_M_AXI_AWLOCK),
        .m_axi_awprot(fifo_generator_xdma_M_AXI_AWPROT),
        .m_axi_awqos(fifo_generator_xdma_M_AXI_AWQOS),
        .m_axi_awready(fifo_generator_xdma_M_AXI_AWREADY),
        .m_axi_awsize(fifo_generator_xdma_M_AXI_AWSIZE),
        .m_axi_awvalid(fifo_generator_xdma_M_AXI_AWVALID),
        .m_axi_bid(fifo_generator_xdma_M_AXI_BID),
        .m_axi_bready(fifo_generator_xdma_M_AXI_BREADY),
        .m_axi_bresp(fifo_generator_xdma_M_AXI_BRESP),
        .m_axi_bvalid(fifo_generator_xdma_M_AXI_BVALID),
        .m_axi_rdata(fifo_generator_xdma_M_AXI_RDATA),
        .m_axi_rid(fifo_generator_xdma_M_AXI_RID),
        .m_axi_rlast(fifo_generator_xdma_M_AXI_RLAST),
        .m_axi_rready(fifo_generator_xdma_M_AXI_RREADY),
        .m_axi_rresp(fifo_generator_xdma_M_AXI_RRESP),
        .m_axi_rvalid(fifo_generator_xdma_M_AXI_RVALID),
        .m_axi_wdata(fifo_generator_xdma_M_AXI_WDATA),
        .m_axi_wlast(fifo_generator_xdma_M_AXI_WLAST),
        .m_axi_wready(fifo_generator_xdma_M_AXI_WREADY),
        .m_axi_wstrb(fifo_generator_xdma_M_AXI_WSTRB),
        .m_axi_wvalid(fifo_generator_xdma_M_AXI_WVALID),
        .s_aclk(aclk_0_1),
        .s_aresetn(aresetn_0_1),
        .s_axi_araddr(XDMA_1_ARADDR),
        .s_axi_arburst(XDMA_1_ARBURST),
        .s_axi_arcache(XDMA_1_ARCACHE),
        .s_axi_arid(XDMA_1_ARID),
        .s_axi_arlen(XDMA_1_ARLEN),
        .s_axi_arlock(XDMA_1_ARLOCK),
        .s_axi_arprot(XDMA_1_ARPROT),
        .s_axi_arqos(XDMA_1_ARQOS),
        .s_axi_arready(XDMA_1_ARREADY),
        .s_axi_arregion(XDMA_1_ARREGION),
        .s_axi_arsize(XDMA_1_ARSIZE),
        .s_axi_arvalid(XDMA_1_ARVALID),
        .s_axi_awaddr(XDMA_1_AWADDR),
        .s_axi_awburst(XDMA_1_AWBURST),
        .s_axi_awcache(XDMA_1_AWCACHE),
        .s_axi_awid(XDMA_1_AWID),
        .s_axi_awlen(XDMA_1_AWLEN),
        .s_axi_awlock(XDMA_1_AWLOCK),
        .s_axi_awprot(XDMA_1_AWPROT),
        .s_axi_awqos(XDMA_1_AWQOS),
        .s_axi_awready(XDMA_1_AWREADY),
        .s_axi_awregion(XDMA_1_AWREGION),
        .s_axi_awsize(XDMA_1_AWSIZE),
        .s_axi_awvalid(XDMA_1_AWVALID),
        .s_axi_bid(XDMA_1_BID),
        .s_axi_bready(XDMA_1_BREADY),
        .s_axi_bresp(XDMA_1_BRESP),
        .s_axi_bvalid(XDMA_1_BVALID),
        .s_axi_rdata(XDMA_1_RDATA),
        .s_axi_rid(XDMA_1_RID),
        .s_axi_rlast(XDMA_1_RLAST),
        .s_axi_rready(XDMA_1_RREADY),
        .s_axi_rresp(XDMA_1_RRESP),
        .s_axi_rvalid(XDMA_1_RVALID),
        .s_axi_wdata(XDMA_1_WDATA),
        .s_axi_wlast(XDMA_1_WLAST),
        .s_axi_wready(XDMA_1_WREADY),
        .s_axi_wstrb(XDMA_1_WSTRB),
        .s_axi_wvalid(XDMA_1_WVALID));
  cl_axi_sc_2x2_smartconnect_0_0 smartconnect_0
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
        .M01_AXI_araddr(smartconnect_0_M01_AXI_ARADDR),
        .M01_AXI_arburst(smartconnect_0_M01_AXI_ARBURST),
        .M01_AXI_arcache(smartconnect_0_M01_AXI_ARCACHE),
        .M01_AXI_arlen(smartconnect_0_M01_AXI_ARLEN),
        .M01_AXI_arlock(smartconnect_0_M01_AXI_ARLOCK),
        .M01_AXI_arprot(smartconnect_0_M01_AXI_ARPROT),
        .M01_AXI_arqos(smartconnect_0_M01_AXI_ARQOS),
        .M01_AXI_arready(smartconnect_0_M01_AXI_ARREADY),
        .M01_AXI_arsize(smartconnect_0_M01_AXI_ARSIZE),
        .M01_AXI_arvalid(smartconnect_0_M01_AXI_ARVALID),
        .M01_AXI_awaddr(smartconnect_0_M01_AXI_AWADDR),
        .M01_AXI_awburst(smartconnect_0_M01_AXI_AWBURST),
        .M01_AXI_awcache(smartconnect_0_M01_AXI_AWCACHE),
        .M01_AXI_awlen(smartconnect_0_M01_AXI_AWLEN),
        .M01_AXI_awlock(smartconnect_0_M01_AXI_AWLOCK),
        .M01_AXI_awprot(smartconnect_0_M01_AXI_AWPROT),
        .M01_AXI_awqos(smartconnect_0_M01_AXI_AWQOS),
        .M01_AXI_awready(smartconnect_0_M01_AXI_AWREADY),
        .M01_AXI_awsize(smartconnect_0_M01_AXI_AWSIZE),
        .M01_AXI_awvalid(smartconnect_0_M01_AXI_AWVALID),
        .M01_AXI_bready(smartconnect_0_M01_AXI_BREADY),
        .M01_AXI_bresp(smartconnect_0_M01_AXI_BRESP),
        .M01_AXI_bvalid(smartconnect_0_M01_AXI_BVALID),
        .M01_AXI_rdata(smartconnect_0_M01_AXI_RDATA),
        .M01_AXI_rlast(smartconnect_0_M01_AXI_RLAST),
        .M01_AXI_rready(smartconnect_0_M01_AXI_RREADY),
        .M01_AXI_rresp(smartconnect_0_M01_AXI_RRESP),
        .M01_AXI_rvalid(smartconnect_0_M01_AXI_RVALID),
        .M01_AXI_wdata(smartconnect_0_M01_AXI_WDATA),
        .M01_AXI_wlast(smartconnect_0_M01_AXI_WLAST),
        .M01_AXI_wready(smartconnect_0_M01_AXI_WREADY),
        .M01_AXI_wstrb(smartconnect_0_M01_AXI_WSTRB),
        .M01_AXI_wvalid(smartconnect_0_M01_AXI_WVALID),
        .S00_AXI_araddr(fifo_generator_xdma_M_AXI_ARADDR),
        .S00_AXI_arburst(fifo_generator_xdma_M_AXI_ARBURST),
        .S00_AXI_arcache(fifo_generator_xdma_M_AXI_ARCACHE),
        .S00_AXI_arid(fifo_generator_xdma_M_AXI_ARID),
        .S00_AXI_arlen(fifo_generator_xdma_M_AXI_ARLEN),
        .S00_AXI_arlock(fifo_generator_xdma_M_AXI_ARLOCK),
        .S00_AXI_arprot(fifo_generator_xdma_M_AXI_ARPROT),
        .S00_AXI_arqos(fifo_generator_xdma_M_AXI_ARQOS),
        .S00_AXI_arready(fifo_generator_xdma_M_AXI_ARREADY),
        .S00_AXI_arsize(fifo_generator_xdma_M_AXI_ARSIZE),
        .S00_AXI_arvalid(fifo_generator_xdma_M_AXI_ARVALID),
        .S00_AXI_awaddr(fifo_generator_xdma_M_AXI_AWADDR),
        .S00_AXI_awburst(fifo_generator_xdma_M_AXI_AWBURST),
        .S00_AXI_awcache(fifo_generator_xdma_M_AXI_AWCACHE),
        .S00_AXI_awid(fifo_generator_xdma_M_AXI_AWID),
        .S00_AXI_awlen(fifo_generator_xdma_M_AXI_AWLEN),
        .S00_AXI_awlock(fifo_generator_xdma_M_AXI_AWLOCK),
        .S00_AXI_awprot(fifo_generator_xdma_M_AXI_AWPROT),
        .S00_AXI_awqos(fifo_generator_xdma_M_AXI_AWQOS),
        .S00_AXI_awready(fifo_generator_xdma_M_AXI_AWREADY),
        .S00_AXI_awsize(fifo_generator_xdma_M_AXI_AWSIZE),
        .S00_AXI_awvalid(fifo_generator_xdma_M_AXI_AWVALID),
        .S00_AXI_bid(fifo_generator_xdma_M_AXI_BID),
        .S00_AXI_bready(fifo_generator_xdma_M_AXI_BREADY),
        .S00_AXI_bresp(fifo_generator_xdma_M_AXI_BRESP),
        .S00_AXI_bvalid(fifo_generator_xdma_M_AXI_BVALID),
        .S00_AXI_rdata(fifo_generator_xdma_M_AXI_RDATA),
        .S00_AXI_rid(fifo_generator_xdma_M_AXI_RID),
        .S00_AXI_rlast(fifo_generator_xdma_M_AXI_RLAST),
        .S00_AXI_rready(fifo_generator_xdma_M_AXI_RREADY),
        .S00_AXI_rresp(fifo_generator_xdma_M_AXI_RRESP),
        .S00_AXI_rvalid(fifo_generator_xdma_M_AXI_RVALID),
        .S00_AXI_wdata(fifo_generator_xdma_M_AXI_WDATA),
        .S00_AXI_wlast(fifo_generator_xdma_M_AXI_WLAST),
        .S00_AXI_wready(fifo_generator_xdma_M_AXI_WREADY),
        .S00_AXI_wstrb(fifo_generator_xdma_M_AXI_WSTRB),
        .S00_AXI_wvalid(fifo_generator_xdma_M_AXI_WVALID),
        .S01_AXI_araddr(fifo_generator_atg_M_AXI_ARADDR),
        .S01_AXI_arburst(fifo_generator_atg_M_AXI_ARBURST),
        .S01_AXI_arcache(fifo_generator_atg_M_AXI_ARCACHE),
        .S01_AXI_arid(fifo_generator_atg_M_AXI_ARID),
        .S01_AXI_arlen(fifo_generator_atg_M_AXI_ARLEN),
        .S01_AXI_arlock(fifo_generator_atg_M_AXI_ARLOCK),
        .S01_AXI_arprot(fifo_generator_atg_M_AXI_ARPROT),
        .S01_AXI_arqos(fifo_generator_atg_M_AXI_ARQOS),
        .S01_AXI_arready(fifo_generator_atg_M_AXI_ARREADY),
        .S01_AXI_arsize(fifo_generator_atg_M_AXI_ARSIZE),
        .S01_AXI_arvalid(fifo_generator_atg_M_AXI_ARVALID),
        .S01_AXI_awaddr(fifo_generator_atg_M_AXI_AWADDR),
        .S01_AXI_awburst(fifo_generator_atg_M_AXI_AWBURST),
        .S01_AXI_awcache(fifo_generator_atg_M_AXI_AWCACHE),
        .S01_AXI_awid(fifo_generator_atg_M_AXI_AWID),
        .S01_AXI_awlen(fifo_generator_atg_M_AXI_AWLEN),
        .S01_AXI_awlock(fifo_generator_atg_M_AXI_AWLOCK),
        .S01_AXI_awprot(fifo_generator_atg_M_AXI_AWPROT),
        .S01_AXI_awqos(fifo_generator_atg_M_AXI_AWQOS),
        .S01_AXI_awready(fifo_generator_atg_M_AXI_AWREADY),
        .S01_AXI_awsize(fifo_generator_atg_M_AXI_AWSIZE),
        .S01_AXI_awvalid(fifo_generator_atg_M_AXI_AWVALID),
        .S01_AXI_bid(fifo_generator_atg_M_AXI_BID),
        .S01_AXI_bready(fifo_generator_atg_M_AXI_BREADY),
        .S01_AXI_bresp(fifo_generator_atg_M_AXI_BRESP),
        .S01_AXI_bvalid(fifo_generator_atg_M_AXI_BVALID),
        .S01_AXI_rdata(fifo_generator_atg_M_AXI_RDATA),
        .S01_AXI_rid(fifo_generator_atg_M_AXI_RID),
        .S01_AXI_rlast(fifo_generator_atg_M_AXI_RLAST),
        .S01_AXI_rready(fifo_generator_atg_M_AXI_RREADY),
        .S01_AXI_rresp(fifo_generator_atg_M_AXI_RRESP),
        .S01_AXI_rvalid(fifo_generator_atg_M_AXI_RVALID),
        .S01_AXI_wdata(fifo_generator_atg_M_AXI_WDATA),
        .S01_AXI_wlast(fifo_generator_atg_M_AXI_WLAST),
        .S01_AXI_wready(fifo_generator_atg_M_AXI_WREADY),
        .S01_AXI_wstrb(fifo_generator_atg_M_AXI_WSTRB),
        .S01_AXI_wvalid(fifo_generator_atg_M_AXI_WVALID),
        .aclk(aclk_0_1),
        .aresetn(aresetn_0_1));
endmodule
