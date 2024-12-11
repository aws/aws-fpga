//Copyright 1986-2022 Xilinx, Inc. All Rights Reserved.
//Copyright 2022-2024 Advanced Micro Devices, Inc. All Rights Reserved.
//--------------------------------------------------------------------------------
//Tool Version: Vivado v.2023.2.2 (lin64) Build 4126759 Thu Feb  8 23:52:05 MST 2024
//Date        : Fri Jun 28 10:57:23 2024
//Host        : xsjgd1 running 64-bit Red Hat Enterprise Linux release 8.2 (Ootpa)
//Command     : generate_target cl_axi_sc_1x1_wrapper.bd
//Design      : cl_axi_sc_1x1_wrapper
//Purpose     : IP block netlist
//--------------------------------------------------------------------------------
`timescale 1 ps / 1 ps

module cl_axi_sc_1x1_wrapper
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
  output [63:0]AXI3_araddr;
  output [1:0]AXI3_arburst;
  output [3:0]AXI3_arcache;
  output [3:0]AXI3_arlen;
  output [1:0]AXI3_arlock;
  output [2:0]AXI3_arprot;
  output [3:0]AXI3_arqos;
  input AXI3_arready;
  output [2:0]AXI3_arsize;
  output AXI3_arvalid;
  output [63:0]AXI3_awaddr;
  output [1:0]AXI3_awburst;
  output [3:0]AXI3_awcache;
  output [3:0]AXI3_awlen;
  output [1:0]AXI3_awlock;
  output [2:0]AXI3_awprot;
  output [3:0]AXI3_awqos;
  input AXI3_awready;
  output [2:0]AXI3_awsize;
  output AXI3_awvalid;
  output AXI3_bready;
  input [1:0]AXI3_bresp;
  input AXI3_bvalid;
  input [255:0]AXI3_rdata;
  input AXI3_rlast;
  output AXI3_rready;
  input [1:0]AXI3_rresp;
  input AXI3_rvalid;
  output [255:0]AXI3_wdata;
  output AXI3_wlast;
  input AXI3_wready;
  output [31:0]AXI3_wstrb;
  output AXI3_wvalid;
  input [63:0]AXI4_araddr;
  input [1:0]AXI4_arburst;
  input [3:0]AXI4_arcache;
  input [15:0]AXI4_arid;
  input [7:0]AXI4_arlen;
  input [0:0]AXI4_arlock;
  input [2:0]AXI4_arprot;
  input [3:0]AXI4_arqos;
  output AXI4_arready;
  input [2:0]AXI4_arsize;
  input AXI4_arvalid;
  input [63:0]AXI4_awaddr;
  input [1:0]AXI4_awburst;
  input [3:0]AXI4_awcache;
  input [15:0]AXI4_awid;
  input [7:0]AXI4_awlen;
  input [0:0]AXI4_awlock;
  input [2:0]AXI4_awprot;
  input [3:0]AXI4_awqos;
  output AXI4_awready;
  input [2:0]AXI4_awsize;
  input AXI4_awvalid;
  output [15:0]AXI4_bid;
  input AXI4_bready;
  output [1:0]AXI4_bresp;
  output AXI4_bvalid;
  output [511:0]AXI4_rdata;
  output [15:0]AXI4_rid;
  output AXI4_rlast;
  input AXI4_rready;
  output [1:0]AXI4_rresp;
  output AXI4_rvalid;
  input [511:0]AXI4_wdata;
  input AXI4_wlast;
  output AXI4_wready;
  input [63:0]AXI4_wstrb;
  input AXI4_wvalid;
  input aclk_250;
  input aclk_450;
  input aresetn_250;

  wire [63:0]AXI3_araddr;
  wire [1:0]AXI3_arburst;
  wire [3:0]AXI3_arcache;
  wire [3:0]AXI3_arlen;
  wire [1:0]AXI3_arlock;
  wire [2:0]AXI3_arprot;
  wire [3:0]AXI3_arqos;
  wire AXI3_arready;
  wire [2:0]AXI3_arsize;
  wire AXI3_arvalid;
  wire [63:0]AXI3_awaddr;
  wire [1:0]AXI3_awburst;
  wire [3:0]AXI3_awcache;
  wire [3:0]AXI3_awlen;
  wire [1:0]AXI3_awlock;
  wire [2:0]AXI3_awprot;
  wire [3:0]AXI3_awqos;
  wire AXI3_awready;
  wire [2:0]AXI3_awsize;
  wire AXI3_awvalid;
  wire AXI3_bready;
  wire [1:0]AXI3_bresp;
  wire AXI3_bvalid;
  wire [255:0]AXI3_rdata;
  wire AXI3_rlast;
  wire AXI3_rready;
  wire [1:0]AXI3_rresp;
  wire AXI3_rvalid;
  wire [255:0]AXI3_wdata;
  wire AXI3_wlast;
  wire AXI3_wready;
  wire [31:0]AXI3_wstrb;
  wire AXI3_wvalid;
  wire [63:0]AXI4_araddr;
  wire [1:0]AXI4_arburst;
  wire [3:0]AXI4_arcache;
  wire [15:0]AXI4_arid;
  wire [7:0]AXI4_arlen;
  wire [0:0]AXI4_arlock;
  wire [2:0]AXI4_arprot;
  wire [3:0]AXI4_arqos;
  wire AXI4_arready;
  wire [2:0]AXI4_arsize;
  wire AXI4_arvalid;
  wire [63:0]AXI4_awaddr;
  wire [1:0]AXI4_awburst;
  wire [3:0]AXI4_awcache;
  wire [15:0]AXI4_awid;
  wire [7:0]AXI4_awlen;
  wire [0:0]AXI4_awlock;
  wire [2:0]AXI4_awprot;
  wire [3:0]AXI4_awqos;
  wire AXI4_awready;
  wire [2:0]AXI4_awsize;
  wire AXI4_awvalid;
  wire [15:0]AXI4_bid;
  wire AXI4_bready;
  wire [1:0]AXI4_bresp;
  wire AXI4_bvalid;
  wire [511:0]AXI4_rdata;
  wire [15:0]AXI4_rid;
  wire AXI4_rlast;
  wire AXI4_rready;
  wire [1:0]AXI4_rresp;
  wire AXI4_rvalid;
  wire [511:0]AXI4_wdata;
  wire AXI4_wlast;
  wire AXI4_wready;
  wire [63:0]AXI4_wstrb;
  wire AXI4_wvalid;
  wire aclk_250;
  wire aclk_450;
  wire aresetn_250;

  cl_axi_sc_1x1 cl_axi_sc_1x1_i
       (.AXI3_araddr(AXI3_araddr),
        .AXI3_arburst(AXI3_arburst),
        .AXI3_arcache(AXI3_arcache),
        .AXI3_arlen(AXI3_arlen),
        .AXI3_arlock(AXI3_arlock),
        .AXI3_arprot(AXI3_arprot),
        .AXI3_arqos(AXI3_arqos),
        .AXI3_arready(AXI3_arready),
        .AXI3_arsize(AXI3_arsize),
        .AXI3_arvalid(AXI3_arvalid),
        .AXI3_awaddr(AXI3_awaddr),
        .AXI3_awburst(AXI3_awburst),
        .AXI3_awcache(AXI3_awcache),
        .AXI3_awlen(AXI3_awlen),
        .AXI3_awlock(AXI3_awlock),
        .AXI3_awprot(AXI3_awprot),
        .AXI3_awqos(AXI3_awqos),
        .AXI3_awready(AXI3_awready),
        .AXI3_awsize(AXI3_awsize),
        .AXI3_awvalid(AXI3_awvalid),
        .AXI3_bready(AXI3_bready),
        .AXI3_bresp(AXI3_bresp),
        .AXI3_bvalid(AXI3_bvalid),
        .AXI3_rdata(AXI3_rdata),
        .AXI3_rlast(AXI3_rlast),
        .AXI3_rready(AXI3_rready),
        .AXI3_rresp(AXI3_rresp),
        .AXI3_rvalid(AXI3_rvalid),
        .AXI3_wdata(AXI3_wdata),
        .AXI3_wlast(AXI3_wlast),
        .AXI3_wready(AXI3_wready),
        .AXI3_wstrb(AXI3_wstrb),
        .AXI3_wvalid(AXI3_wvalid),
        .AXI4_araddr(AXI4_araddr),
        .AXI4_arburst(AXI4_arburst),
        .AXI4_arcache(AXI4_arcache),
        .AXI4_arid(AXI4_arid),
        .AXI4_arlen(AXI4_arlen),
        .AXI4_arlock(AXI4_arlock),
        .AXI4_arprot(AXI4_arprot),
        .AXI4_arqos(AXI4_arqos),
        .AXI4_arready(AXI4_arready),
        .AXI4_arsize(AXI4_arsize),
        .AXI4_arvalid(AXI4_arvalid),
        .AXI4_awaddr(AXI4_awaddr),
        .AXI4_awburst(AXI4_awburst),
        .AXI4_awcache(AXI4_awcache),
        .AXI4_awid(AXI4_awid),
        .AXI4_awlen(AXI4_awlen),
        .AXI4_awlock(AXI4_awlock),
        .AXI4_awprot(AXI4_awprot),
        .AXI4_awqos(AXI4_awqos),
        .AXI4_awready(AXI4_awready),
        .AXI4_awsize(AXI4_awsize),
        .AXI4_awvalid(AXI4_awvalid),
        .AXI4_bid(AXI4_bid),
        .AXI4_bready(AXI4_bready),
        .AXI4_bresp(AXI4_bresp),
        .AXI4_bvalid(AXI4_bvalid),
        .AXI4_rdata(AXI4_rdata),
        .AXI4_rid(AXI4_rid),
        .AXI4_rlast(AXI4_rlast),
        .AXI4_rready(AXI4_rready),
        .AXI4_rresp(AXI4_rresp),
        .AXI4_rvalid(AXI4_rvalid),
        .AXI4_wdata(AXI4_wdata),
        .AXI4_wlast(AXI4_wlast),
        .AXI4_wready(AXI4_wready),
        .AXI4_wstrb(AXI4_wstrb),
        .AXI4_wvalid(AXI4_wvalid),
        .aclk_250(aclk_250),
        .aclk_450(aclk_450),
        .aresetn_250(aresetn_250));
endmodule
