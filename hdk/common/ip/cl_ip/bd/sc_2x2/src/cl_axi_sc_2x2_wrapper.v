//Copyright 1986-2022 Xilinx, Inc. All Rights Reserved.
//Copyright 2022-2024 Advanced Micro Devices, Inc. All Rights Reserved.
//--------------------------------------------------------------------------------
//Tool Version: Vivado v.2023.2.2 (lin64) Build 4126759 Thu Feb  8 23:52:05 MST 2024
//Date        : Thu Jun 27 07:24:48 2024
//Host        : xsjgd1 running 64-bit Red Hat Enterprise Linux release 8.2 (Ootpa)
//Command     : generate_target cl_axi_sc_2x2_wrapper.bd
//Design      : cl_axi_sc_2x2_wrapper
//Purpose     : IP block netlist
//--------------------------------------------------------------------------------
`timescale 1 ps / 1 ps

module cl_axi_sc_2x2_wrapper
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
  input [63:0]ATG_araddr;
  input [1:0]ATG_arburst;
  input [3:0]ATG_arcache;
  input [15:0]ATG_arid;
  input [7:0]ATG_arlen;
  input [0:0]ATG_arlock;
  input [2:0]ATG_arprot;
  input [3:0]ATG_arqos;
  output ATG_arready;
  input [3:0]ATG_arregion;
  input [2:0]ATG_arsize;
  input ATG_arvalid;
  input [63:0]ATG_awaddr;
  input [1:0]ATG_awburst;
  input [3:0]ATG_awcache;
  input [15:0]ATG_awid;
  input [7:0]ATG_awlen;
  input [0:0]ATG_awlock;
  input [2:0]ATG_awprot;
  input [3:0]ATG_awqos;
  output ATG_awready;
  input [3:0]ATG_awregion;
  input [2:0]ATG_awsize;
  input ATG_awvalid;
  output [15:0]ATG_bid;
  input ATG_bready;
  output [1:0]ATG_bresp;
  output ATG_bvalid;
  output [511:0]ATG_rdata;
  output [15:0]ATG_rid;
  output ATG_rlast;
  input ATG_rready;
  output [1:0]ATG_rresp;
  output ATG_rvalid;
  input [511:0]ATG_wdata;
  input ATG_wlast;
  output ATG_wready;
  input [63:0]ATG_wstrb;
  input ATG_wvalid;
  output [63:0]DDRA_araddr;
  output [1:0]DDRA_arburst;
  output [3:0]DDRA_arcache;
  output [7:0]DDRA_arlen;
  output [0:0]DDRA_arlock;
  output [2:0]DDRA_arprot;
  output [3:0]DDRA_arqos;
  input DDRA_arready;
  output [2:0]DDRA_arsize;
  output DDRA_arvalid;
  output [63:0]DDRA_awaddr;
  output [1:0]DDRA_awburst;
  output [3:0]DDRA_awcache;
  output [7:0]DDRA_awlen;
  output [0:0]DDRA_awlock;
  output [2:0]DDRA_awprot;
  output [3:0]DDRA_awqos;
  input DDRA_awready;
  output [2:0]DDRA_awsize;
  output DDRA_awvalid;
  output DDRA_bready;
  input [1:0]DDRA_bresp;
  input DDRA_bvalid;
  input [511:0]DDRA_rdata;
  input DDRA_rlast;
  output DDRA_rready;
  input [1:0]DDRA_rresp;
  input DDRA_rvalid;
  output [511:0]DDRA_wdata;
  output DDRA_wlast;
  input DDRA_wready;
  output [63:0]DDRA_wstrb;
  output DDRA_wvalid;
  output [63:0]DDRB_araddr;
  output [1:0]DDRB_arburst;
  output [3:0]DDRB_arcache;
  output [7:0]DDRB_arlen;
  output [0:0]DDRB_arlock;
  output [2:0]DDRB_arprot;
  output [3:0]DDRB_arqos;
  input DDRB_arready;
  output [2:0]DDRB_arsize;
  output DDRB_arvalid;
  output [63:0]DDRB_awaddr;
  output [1:0]DDRB_awburst;
  output [3:0]DDRB_awcache;
  output [7:0]DDRB_awlen;
  output [0:0]DDRB_awlock;
  output [2:0]DDRB_awprot;
  output [3:0]DDRB_awqos;
  input DDRB_awready;
  output [2:0]DDRB_awsize;
  output DDRB_awvalid;
  output DDRB_bready;
  input [1:0]DDRB_bresp;
  input DDRB_bvalid;
  input [511:0]DDRB_rdata;
  input DDRB_rlast;
  output DDRB_rready;
  input [1:0]DDRB_rresp;
  input DDRB_rvalid;
  output [511:0]DDRB_wdata;
  output DDRB_wlast;
  input DDRB_wready;
  output [63:0]DDRB_wstrb;
  output DDRB_wvalid;
  input [63:0]XDMA_araddr;
  input [1:0]XDMA_arburst;
  input [3:0]XDMA_arcache;
  input [15:0]XDMA_arid;
  input [7:0]XDMA_arlen;
  input [0:0]XDMA_arlock;
  input [2:0]XDMA_arprot;
  input [3:0]XDMA_arqos;
  output XDMA_arready;
  input [3:0]XDMA_arregion;
  input [2:0]XDMA_arsize;
  input XDMA_arvalid;
  input [63:0]XDMA_awaddr;
  input [1:0]XDMA_awburst;
  input [3:0]XDMA_awcache;
  input [15:0]XDMA_awid;
  input [7:0]XDMA_awlen;
  input [0:0]XDMA_awlock;
  input [2:0]XDMA_awprot;
  input [3:0]XDMA_awqos;
  output XDMA_awready;
  input [3:0]XDMA_awregion;
  input [2:0]XDMA_awsize;
  input XDMA_awvalid;
  output [15:0]XDMA_bid;
  input XDMA_bready;
  output [1:0]XDMA_bresp;
  output XDMA_bvalid;
  output [511:0]XDMA_rdata;
  output [15:0]XDMA_rid;
  output XDMA_rlast;
  input XDMA_rready;
  output [1:0]XDMA_rresp;
  output XDMA_rvalid;
  input [511:0]XDMA_wdata;
  input XDMA_wlast;
  output XDMA_wready;
  input [63:0]XDMA_wstrb;
  input XDMA_wvalid;
  input aclk_250;
  input aresetn_250;

  wire [63:0]ATG_araddr;
  wire [1:0]ATG_arburst;
  wire [3:0]ATG_arcache;
  wire [15:0]ATG_arid;
  wire [7:0]ATG_arlen;
  wire [0:0]ATG_arlock;
  wire [2:0]ATG_arprot;
  wire [3:0]ATG_arqos;
  wire ATG_arready;
  wire [3:0]ATG_arregion;
  wire [2:0]ATG_arsize;
  wire ATG_arvalid;
  wire [63:0]ATG_awaddr;
  wire [1:0]ATG_awburst;
  wire [3:0]ATG_awcache;
  wire [15:0]ATG_awid;
  wire [7:0]ATG_awlen;
  wire [0:0]ATG_awlock;
  wire [2:0]ATG_awprot;
  wire [3:0]ATG_awqos;
  wire ATG_awready;
  wire [3:0]ATG_awregion;
  wire [2:0]ATG_awsize;
  wire ATG_awvalid;
  wire [15:0]ATG_bid;
  wire ATG_bready;
  wire [1:0]ATG_bresp;
  wire ATG_bvalid;
  wire [511:0]ATG_rdata;
  wire [15:0]ATG_rid;
  wire ATG_rlast;
  wire ATG_rready;
  wire [1:0]ATG_rresp;
  wire ATG_rvalid;
  wire [511:0]ATG_wdata;
  wire ATG_wlast;
  wire ATG_wready;
  wire [63:0]ATG_wstrb;
  wire ATG_wvalid;
  wire [63:0]DDRA_araddr;
  wire [1:0]DDRA_arburst;
  wire [3:0]DDRA_arcache;
  wire [7:0]DDRA_arlen;
  wire [0:0]DDRA_arlock;
  wire [2:0]DDRA_arprot;
  wire [3:0]DDRA_arqos;
  wire DDRA_arready;
  wire [2:0]DDRA_arsize;
  wire DDRA_arvalid;
  wire [63:0]DDRA_awaddr;
  wire [1:0]DDRA_awburst;
  wire [3:0]DDRA_awcache;
  wire [7:0]DDRA_awlen;
  wire [0:0]DDRA_awlock;
  wire [2:0]DDRA_awprot;
  wire [3:0]DDRA_awqos;
  wire DDRA_awready;
  wire [2:0]DDRA_awsize;
  wire DDRA_awvalid;
  wire DDRA_bready;
  wire [1:0]DDRA_bresp;
  wire DDRA_bvalid;
  wire [511:0]DDRA_rdata;
  wire DDRA_rlast;
  wire DDRA_rready;
  wire [1:0]DDRA_rresp;
  wire DDRA_rvalid;
  wire [511:0]DDRA_wdata;
  wire DDRA_wlast;
  wire DDRA_wready;
  wire [63:0]DDRA_wstrb;
  wire DDRA_wvalid;
  wire [63:0]DDRB_araddr;
  wire [1:0]DDRB_arburst;
  wire [3:0]DDRB_arcache;
  wire [7:0]DDRB_arlen;
  wire [0:0]DDRB_arlock;
  wire [2:0]DDRB_arprot;
  wire [3:0]DDRB_arqos;
  wire DDRB_arready;
  wire [2:0]DDRB_arsize;
  wire DDRB_arvalid;
  wire [63:0]DDRB_awaddr;
  wire [1:0]DDRB_awburst;
  wire [3:0]DDRB_awcache;
  wire [7:0]DDRB_awlen;
  wire [0:0]DDRB_awlock;
  wire [2:0]DDRB_awprot;
  wire [3:0]DDRB_awqos;
  wire DDRB_awready;
  wire [2:0]DDRB_awsize;
  wire DDRB_awvalid;
  wire DDRB_bready;
  wire [1:0]DDRB_bresp;
  wire DDRB_bvalid;
  wire [511:0]DDRB_rdata;
  wire DDRB_rlast;
  wire DDRB_rready;
  wire [1:0]DDRB_rresp;
  wire DDRB_rvalid;
  wire [511:0]DDRB_wdata;
  wire DDRB_wlast;
  wire DDRB_wready;
  wire [63:0]DDRB_wstrb;
  wire DDRB_wvalid;
  wire [63:0]XDMA_araddr;
  wire [1:0]XDMA_arburst;
  wire [3:0]XDMA_arcache;
  wire [15:0]XDMA_arid;
  wire [7:0]XDMA_arlen;
  wire [0:0]XDMA_arlock;
  wire [2:0]XDMA_arprot;
  wire [3:0]XDMA_arqos;
  wire XDMA_arready;
  wire [3:0]XDMA_arregion;
  wire [2:0]XDMA_arsize;
  wire XDMA_arvalid;
  wire [63:0]XDMA_awaddr;
  wire [1:0]XDMA_awburst;
  wire [3:0]XDMA_awcache;
  wire [15:0]XDMA_awid;
  wire [7:0]XDMA_awlen;
  wire [0:0]XDMA_awlock;
  wire [2:0]XDMA_awprot;
  wire [3:0]XDMA_awqos;
  wire XDMA_awready;
  wire [3:0]XDMA_awregion;
  wire [2:0]XDMA_awsize;
  wire XDMA_awvalid;
  wire [15:0]XDMA_bid;
  wire XDMA_bready;
  wire [1:0]XDMA_bresp;
  wire XDMA_bvalid;
  wire [511:0]XDMA_rdata;
  wire [15:0]XDMA_rid;
  wire XDMA_rlast;
  wire XDMA_rready;
  wire [1:0]XDMA_rresp;
  wire XDMA_rvalid;
  wire [511:0]XDMA_wdata;
  wire XDMA_wlast;
  wire XDMA_wready;
  wire [63:0]XDMA_wstrb;
  wire XDMA_wvalid;
  wire aclk_250;
  wire aresetn_250;

  cl_axi_sc_2x2 cl_axi_sc_2x2_i
       (.ATG_araddr(ATG_araddr),
        .ATG_arburst(ATG_arburst),
        .ATG_arcache(ATG_arcache),
        .ATG_arid(ATG_arid),
        .ATG_arlen(ATG_arlen),
        .ATG_arlock(ATG_arlock),
        .ATG_arprot(ATG_arprot),
        .ATG_arqos(ATG_arqos),
        .ATG_arready(ATG_arready),
        .ATG_arregion(ATG_arregion),
        .ATG_arsize(ATG_arsize),
        .ATG_arvalid(ATG_arvalid),
        .ATG_awaddr(ATG_awaddr),
        .ATG_awburst(ATG_awburst),
        .ATG_awcache(ATG_awcache),
        .ATG_awid(ATG_awid),
        .ATG_awlen(ATG_awlen),
        .ATG_awlock(ATG_awlock),
        .ATG_awprot(ATG_awprot),
        .ATG_awqos(ATG_awqos),
        .ATG_awready(ATG_awready),
        .ATG_awregion(ATG_awregion),
        .ATG_awsize(ATG_awsize),
        .ATG_awvalid(ATG_awvalid),
        .ATG_bid(ATG_bid),
        .ATG_bready(ATG_bready),
        .ATG_bresp(ATG_bresp),
        .ATG_bvalid(ATG_bvalid),
        .ATG_rdata(ATG_rdata),
        .ATG_rid(ATG_rid),
        .ATG_rlast(ATG_rlast),
        .ATG_rready(ATG_rready),
        .ATG_rresp(ATG_rresp),
        .ATG_rvalid(ATG_rvalid),
        .ATG_wdata(ATG_wdata),
        .ATG_wlast(ATG_wlast),
        .ATG_wready(ATG_wready),
        .ATG_wstrb(ATG_wstrb),
        .ATG_wvalid(ATG_wvalid),
        .DDRA_araddr(DDRA_araddr),
        .DDRA_arburst(DDRA_arburst),
        .DDRA_arcache(DDRA_arcache),
        .DDRA_arlen(DDRA_arlen),
        .DDRA_arlock(DDRA_arlock),
        .DDRA_arprot(DDRA_arprot),
        .DDRA_arqos(DDRA_arqos),
        .DDRA_arready(DDRA_arready),
        .DDRA_arsize(DDRA_arsize),
        .DDRA_arvalid(DDRA_arvalid),
        .DDRA_awaddr(DDRA_awaddr),
        .DDRA_awburst(DDRA_awburst),
        .DDRA_awcache(DDRA_awcache),
        .DDRA_awlen(DDRA_awlen),
        .DDRA_awlock(DDRA_awlock),
        .DDRA_awprot(DDRA_awprot),
        .DDRA_awqos(DDRA_awqos),
        .DDRA_awready(DDRA_awready),
        .DDRA_awsize(DDRA_awsize),
        .DDRA_awvalid(DDRA_awvalid),
        .DDRA_bready(DDRA_bready),
        .DDRA_bresp(DDRA_bresp),
        .DDRA_bvalid(DDRA_bvalid),
        .DDRA_rdata(DDRA_rdata),
        .DDRA_rlast(DDRA_rlast),
        .DDRA_rready(DDRA_rready),
        .DDRA_rresp(DDRA_rresp),
        .DDRA_rvalid(DDRA_rvalid),
        .DDRA_wdata(DDRA_wdata),
        .DDRA_wlast(DDRA_wlast),
        .DDRA_wready(DDRA_wready),
        .DDRA_wstrb(DDRA_wstrb),
        .DDRA_wvalid(DDRA_wvalid),
        .DDRB_araddr(DDRB_araddr),
        .DDRB_arburst(DDRB_arburst),
        .DDRB_arcache(DDRB_arcache),
        .DDRB_arlen(DDRB_arlen),
        .DDRB_arlock(DDRB_arlock),
        .DDRB_arprot(DDRB_arprot),
        .DDRB_arqos(DDRB_arqos),
        .DDRB_arready(DDRB_arready),
        .DDRB_arsize(DDRB_arsize),
        .DDRB_arvalid(DDRB_arvalid),
        .DDRB_awaddr(DDRB_awaddr),
        .DDRB_awburst(DDRB_awburst),
        .DDRB_awcache(DDRB_awcache),
        .DDRB_awlen(DDRB_awlen),
        .DDRB_awlock(DDRB_awlock),
        .DDRB_awprot(DDRB_awprot),
        .DDRB_awqos(DDRB_awqos),
        .DDRB_awready(DDRB_awready),
        .DDRB_awsize(DDRB_awsize),
        .DDRB_awvalid(DDRB_awvalid),
        .DDRB_bready(DDRB_bready),
        .DDRB_bresp(DDRB_bresp),
        .DDRB_bvalid(DDRB_bvalid),
        .DDRB_rdata(DDRB_rdata),
        .DDRB_rlast(DDRB_rlast),
        .DDRB_rready(DDRB_rready),
        .DDRB_rresp(DDRB_rresp),
        .DDRB_rvalid(DDRB_rvalid),
        .DDRB_wdata(DDRB_wdata),
        .DDRB_wlast(DDRB_wlast),
        .DDRB_wready(DDRB_wready),
        .DDRB_wstrb(DDRB_wstrb),
        .DDRB_wvalid(DDRB_wvalid),
        .XDMA_araddr(XDMA_araddr),
        .XDMA_arburst(XDMA_arburst),
        .XDMA_arcache(XDMA_arcache),
        .XDMA_arid(XDMA_arid),
        .XDMA_arlen(XDMA_arlen),
        .XDMA_arlock(XDMA_arlock),
        .XDMA_arprot(XDMA_arprot),
        .XDMA_arqos(XDMA_arqos),
        .XDMA_arready(XDMA_arready),
        .XDMA_arregion(XDMA_arregion),
        .XDMA_arsize(XDMA_arsize),
        .XDMA_arvalid(XDMA_arvalid),
        .XDMA_awaddr(XDMA_awaddr),
        .XDMA_awburst(XDMA_awburst),
        .XDMA_awcache(XDMA_awcache),
        .XDMA_awid(XDMA_awid),
        .XDMA_awlen(XDMA_awlen),
        .XDMA_awlock(XDMA_awlock),
        .XDMA_awprot(XDMA_awprot),
        .XDMA_awqos(XDMA_awqos),
        .XDMA_awready(XDMA_awready),
        .XDMA_awregion(XDMA_awregion),
        .XDMA_awsize(XDMA_awsize),
        .XDMA_awvalid(XDMA_awvalid),
        .XDMA_bid(XDMA_bid),
        .XDMA_bready(XDMA_bready),
        .XDMA_bresp(XDMA_bresp),
        .XDMA_bvalid(XDMA_bvalid),
        .XDMA_rdata(XDMA_rdata),
        .XDMA_rid(XDMA_rid),
        .XDMA_rlast(XDMA_rlast),
        .XDMA_rready(XDMA_rready),
        .XDMA_rresp(XDMA_rresp),
        .XDMA_rvalid(XDMA_rvalid),
        .XDMA_wdata(XDMA_wdata),
        .XDMA_wlast(XDMA_wlast),
        .XDMA_wready(XDMA_wready),
        .XDMA_wstrb(XDMA_wstrb),
        .XDMA_wvalid(XDMA_wvalid),
        .aclk_250(aclk_250),
        .aresetn_250(aresetn_250));
endmodule
