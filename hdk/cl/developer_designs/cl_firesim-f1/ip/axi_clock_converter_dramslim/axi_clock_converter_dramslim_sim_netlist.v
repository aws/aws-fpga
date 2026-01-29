// Copyright 1986-2017 Xilinx, Inc. All Rights Reserved.
// --------------------------------------------------------------------------------
// Tool Version: Vivado v.2017.1 (lin64) Build 1846317 Fri Apr 14 18:54:47 MDT 2017
// Date        : Sat Jul  8 00:01:49 2017
// Host        : ip-172-31-17-184.ec2.internal running 64-bit CentOS Linux release 7.3.1611 (Core)
// Command     : write_verilog -force -mode funcsim
//               /home/centos/firesim_ip2/axi_clock_converter_dramslim/axi_clock_converter_dramslim_sim_netlist.v
// Design      : axi_clock_converter_dramslim
// Purpose     : This verilog netlist is a functional simulation representation of the design and should not be modified
//               or synthesized. This netlist cannot be used for SDF annotated simulation.
// Device      : xcvu9p-flgb2104-2-i
// --------------------------------------------------------------------------------
`timescale 1 ps / 1 ps

(* CHECK_LICENSE_TYPE = "axi_clock_converter_dramslim,axi_clock_converter_v2_1_11_axi_clock_converter,{}" *) (* DowngradeIPIdentifiedWarnings = "yes" *) (* X_CORE_INFO = "axi_clock_converter_v2_1_11_axi_clock_converter,Vivado 2017.1" *) 
(* NotValidForBitStream *)
module axi_clock_converter_dramslim
   (s_axi_aclk,
    s_axi_aresetn,
    s_axi_awid,
    s_axi_awaddr,
    s_axi_awlen,
    s_axi_awsize,
    s_axi_awburst,
    s_axi_awlock,
    s_axi_awcache,
    s_axi_awprot,
    s_axi_awregion,
    s_axi_awqos,
    s_axi_awvalid,
    s_axi_awready,
    s_axi_wdata,
    s_axi_wstrb,
    s_axi_wlast,
    s_axi_wvalid,
    s_axi_wready,
    s_axi_bid,
    s_axi_bresp,
    s_axi_bvalid,
    s_axi_bready,
    s_axi_arid,
    s_axi_araddr,
    s_axi_arlen,
    s_axi_arsize,
    s_axi_arburst,
    s_axi_arlock,
    s_axi_arcache,
    s_axi_arprot,
    s_axi_arregion,
    s_axi_arqos,
    s_axi_arvalid,
    s_axi_arready,
    s_axi_rid,
    s_axi_rdata,
    s_axi_rresp,
    s_axi_rlast,
    s_axi_rvalid,
    s_axi_rready,
    m_axi_aclk,
    m_axi_aresetn,
    m_axi_awid,
    m_axi_awaddr,
    m_axi_awlen,
    m_axi_awsize,
    m_axi_awburst,
    m_axi_awlock,
    m_axi_awcache,
    m_axi_awprot,
    m_axi_awregion,
    m_axi_awqos,
    m_axi_awvalid,
    m_axi_awready,
    m_axi_wdata,
    m_axi_wstrb,
    m_axi_wlast,
    m_axi_wvalid,
    m_axi_wready,
    m_axi_bid,
    m_axi_bresp,
    m_axi_bvalid,
    m_axi_bready,
    m_axi_arid,
    m_axi_araddr,
    m_axi_arlen,
    m_axi_arsize,
    m_axi_arburst,
    m_axi_arlock,
    m_axi_arcache,
    m_axi_arprot,
    m_axi_arregion,
    m_axi_arqos,
    m_axi_arvalid,
    m_axi_arready,
    m_axi_rid,
    m_axi_rdata,
    m_axi_rresp,
    m_axi_rlast,
    m_axi_rvalid,
    m_axi_rready);
  (* X_INTERFACE_INFO = "xilinx.com:signal:clock:1.0 SI_CLK CLK" *) input s_axi_aclk;
  (* X_INTERFACE_INFO = "xilinx.com:signal:reset:1.0 SI_RST RST" *) input s_axi_aresetn;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWID" *) input [15:0]s_axi_awid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWADDR" *) input [63:0]s_axi_awaddr;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWLEN" *) input [7:0]s_axi_awlen;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWSIZE" *) input [2:0]s_axi_awsize;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWBURST" *) input [1:0]s_axi_awburst;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWLOCK" *) input [0:0]s_axi_awlock;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWCACHE" *) input [3:0]s_axi_awcache;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWPROT" *) input [2:0]s_axi_awprot;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWREGION" *) input [3:0]s_axi_awregion;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWQOS" *) input [3:0]s_axi_awqos;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWVALID" *) input s_axi_awvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWREADY" *) output s_axi_awready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI WDATA" *) input [63:0]s_axi_wdata;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI WSTRB" *) input [7:0]s_axi_wstrb;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI WLAST" *) input s_axi_wlast;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI WVALID" *) input s_axi_wvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI WREADY" *) output s_axi_wready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI BID" *) output [15:0]s_axi_bid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI BRESP" *) output [1:0]s_axi_bresp;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI BVALID" *) output s_axi_bvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI BREADY" *) input s_axi_bready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARID" *) input [15:0]s_axi_arid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARADDR" *) input [63:0]s_axi_araddr;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARLEN" *) input [7:0]s_axi_arlen;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARSIZE" *) input [2:0]s_axi_arsize;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARBURST" *) input [1:0]s_axi_arburst;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARLOCK" *) input [0:0]s_axi_arlock;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARCACHE" *) input [3:0]s_axi_arcache;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARPROT" *) input [2:0]s_axi_arprot;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARREGION" *) input [3:0]s_axi_arregion;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARQOS" *) input [3:0]s_axi_arqos;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARVALID" *) input s_axi_arvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARREADY" *) output s_axi_arready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI RID" *) output [15:0]s_axi_rid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI RDATA" *) output [63:0]s_axi_rdata;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI RRESP" *) output [1:0]s_axi_rresp;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI RLAST" *) output s_axi_rlast;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI RVALID" *) output s_axi_rvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI RREADY" *) input s_axi_rready;
  (* X_INTERFACE_INFO = "xilinx.com:signal:clock:1.0 MI_CLK CLK" *) input m_axi_aclk;
  (* X_INTERFACE_INFO = "xilinx.com:signal:reset:1.0 MI_RST RST" *) input m_axi_aresetn;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWID" *) output [15:0]m_axi_awid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWADDR" *) output [63:0]m_axi_awaddr;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWLEN" *) output [7:0]m_axi_awlen;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWSIZE" *) output [2:0]m_axi_awsize;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWBURST" *) output [1:0]m_axi_awburst;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWLOCK" *) output [0:0]m_axi_awlock;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWCACHE" *) output [3:0]m_axi_awcache;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWPROT" *) output [2:0]m_axi_awprot;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWREGION" *) output [3:0]m_axi_awregion;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWQOS" *) output [3:0]m_axi_awqos;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWVALID" *) output m_axi_awvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWREADY" *) input m_axi_awready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI WDATA" *) output [63:0]m_axi_wdata;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI WSTRB" *) output [7:0]m_axi_wstrb;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI WLAST" *) output m_axi_wlast;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI WVALID" *) output m_axi_wvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI WREADY" *) input m_axi_wready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI BID" *) input [15:0]m_axi_bid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI BRESP" *) input [1:0]m_axi_bresp;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI BVALID" *) input m_axi_bvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI BREADY" *) output m_axi_bready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARID" *) output [15:0]m_axi_arid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARADDR" *) output [63:0]m_axi_araddr;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARLEN" *) output [7:0]m_axi_arlen;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARSIZE" *) output [2:0]m_axi_arsize;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARBURST" *) output [1:0]m_axi_arburst;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARLOCK" *) output [0:0]m_axi_arlock;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARCACHE" *) output [3:0]m_axi_arcache;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARPROT" *) output [2:0]m_axi_arprot;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARREGION" *) output [3:0]m_axi_arregion;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARQOS" *) output [3:0]m_axi_arqos;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARVALID" *) output m_axi_arvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARREADY" *) input m_axi_arready;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI RID" *) input [15:0]m_axi_rid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI RDATA" *) input [63:0]m_axi_rdata;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI RRESP" *) input [1:0]m_axi_rresp;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI RLAST" *) input m_axi_rlast;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI RVALID" *) input m_axi_rvalid;
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI RREADY" *) output m_axi_rready;

  wire m_axi_aclk;
  wire [63:0]m_axi_araddr;
  wire [1:0]m_axi_arburst;
  wire [3:0]m_axi_arcache;
  wire m_axi_aresetn;
  wire [15:0]m_axi_arid;
  wire [7:0]m_axi_arlen;
  wire [0:0]m_axi_arlock;
  wire [2:0]m_axi_arprot;
  wire [3:0]m_axi_arqos;
  wire m_axi_arready;
  wire [3:0]m_axi_arregion;
  wire [2:0]m_axi_arsize;
  wire m_axi_arvalid;
  wire [63:0]m_axi_awaddr;
  wire [1:0]m_axi_awburst;
  wire [3:0]m_axi_awcache;
  wire [15:0]m_axi_awid;
  wire [7:0]m_axi_awlen;
  wire [0:0]m_axi_awlock;
  wire [2:0]m_axi_awprot;
  wire [3:0]m_axi_awqos;
  wire m_axi_awready;
  wire [3:0]m_axi_awregion;
  wire [2:0]m_axi_awsize;
  wire m_axi_awvalid;
  wire [15:0]m_axi_bid;
  wire m_axi_bready;
  wire [1:0]m_axi_bresp;
  wire m_axi_bvalid;
  wire [63:0]m_axi_rdata;
  wire [15:0]m_axi_rid;
  wire m_axi_rlast;
  wire m_axi_rready;
  wire [1:0]m_axi_rresp;
  wire m_axi_rvalid;
  wire [63:0]m_axi_wdata;
  wire m_axi_wlast;
  wire m_axi_wready;
  wire [7:0]m_axi_wstrb;
  wire m_axi_wvalid;
  wire s_axi_aclk;
  wire [63:0]s_axi_araddr;
  wire [1:0]s_axi_arburst;
  wire [3:0]s_axi_arcache;
  wire s_axi_aresetn;
  wire [15:0]s_axi_arid;
  wire [7:0]s_axi_arlen;
  wire [0:0]s_axi_arlock;
  wire [2:0]s_axi_arprot;
  wire [3:0]s_axi_arqos;
  wire s_axi_arready;
  wire [3:0]s_axi_arregion;
  wire [2:0]s_axi_arsize;
  wire s_axi_arvalid;
  wire [63:0]s_axi_awaddr;
  wire [1:0]s_axi_awburst;
  wire [3:0]s_axi_awcache;
  wire [15:0]s_axi_awid;
  wire [7:0]s_axi_awlen;
  wire [0:0]s_axi_awlock;
  wire [2:0]s_axi_awprot;
  wire [3:0]s_axi_awqos;
  wire s_axi_awready;
  wire [3:0]s_axi_awregion;
  wire [2:0]s_axi_awsize;
  wire s_axi_awvalid;
  wire [15:0]s_axi_bid;
  wire s_axi_bready;
  wire [1:0]s_axi_bresp;
  wire s_axi_bvalid;
  wire [63:0]s_axi_rdata;
  wire [15:0]s_axi_rid;
  wire s_axi_rlast;
  wire s_axi_rready;
  wire [1:0]s_axi_rresp;
  wire s_axi_rvalid;
  wire [63:0]s_axi_wdata;
  wire s_axi_wlast;
  wire s_axi_wready;
  wire [7:0]s_axi_wstrb;
  wire s_axi_wvalid;
  wire [0:0]NLW_inst_m_axi_aruser_UNCONNECTED;
  wire [0:0]NLW_inst_m_axi_awuser_UNCONNECTED;
  wire [15:0]NLW_inst_m_axi_wid_UNCONNECTED;
  wire [0:0]NLW_inst_m_axi_wuser_UNCONNECTED;
  wire [0:0]NLW_inst_s_axi_buser_UNCONNECTED;
  wire [0:0]NLW_inst_s_axi_ruser_UNCONNECTED;

  (* C_ARADDR_RIGHT = "29" *) 
  (* C_ARADDR_WIDTH = "64" *) 
  (* C_ARBURST_RIGHT = "16" *) 
  (* C_ARBURST_WIDTH = "2" *) 
  (* C_ARCACHE_RIGHT = "11" *) 
  (* C_ARCACHE_WIDTH = "4" *) 
  (* C_ARID_RIGHT = "93" *) 
  (* C_ARID_WIDTH = "16" *) 
  (* C_ARLEN_RIGHT = "21" *) 
  (* C_ARLEN_WIDTH = "8" *) 
  (* C_ARLOCK_RIGHT = "15" *) 
  (* C_ARLOCK_WIDTH = "1" *) 
  (* C_ARPROT_RIGHT = "8" *) 
  (* C_ARPROT_WIDTH = "3" *) 
  (* C_ARQOS_RIGHT = "0" *) 
  (* C_ARQOS_WIDTH = "4" *) 
  (* C_ARREGION_RIGHT = "4" *) 
  (* C_ARREGION_WIDTH = "4" *) 
  (* C_ARSIZE_RIGHT = "18" *) 
  (* C_ARSIZE_WIDTH = "3" *) 
  (* C_ARUSER_RIGHT = "0" *) 
  (* C_ARUSER_WIDTH = "0" *) 
  (* C_AR_WIDTH = "109" *) 
  (* C_AWADDR_RIGHT = "29" *) 
  (* C_AWADDR_WIDTH = "64" *) 
  (* C_AWBURST_RIGHT = "16" *) 
  (* C_AWBURST_WIDTH = "2" *) 
  (* C_AWCACHE_RIGHT = "11" *) 
  (* C_AWCACHE_WIDTH = "4" *) 
  (* C_AWID_RIGHT = "93" *) 
  (* C_AWID_WIDTH = "16" *) 
  (* C_AWLEN_RIGHT = "21" *) 
  (* C_AWLEN_WIDTH = "8" *) 
  (* C_AWLOCK_RIGHT = "15" *) 
  (* C_AWLOCK_WIDTH = "1" *) 
  (* C_AWPROT_RIGHT = "8" *) 
  (* C_AWPROT_WIDTH = "3" *) 
  (* C_AWQOS_RIGHT = "0" *) 
  (* C_AWQOS_WIDTH = "4" *) 
  (* C_AWREGION_RIGHT = "4" *) 
  (* C_AWREGION_WIDTH = "4" *) 
  (* C_AWSIZE_RIGHT = "18" *) 
  (* C_AWSIZE_WIDTH = "3" *) 
  (* C_AWUSER_RIGHT = "0" *) 
  (* C_AWUSER_WIDTH = "0" *) 
  (* C_AW_WIDTH = "109" *) 
  (* C_AXI_ADDR_WIDTH = "64" *) 
  (* C_AXI_ARUSER_WIDTH = "1" *) 
  (* C_AXI_AWUSER_WIDTH = "1" *) 
  (* C_AXI_BUSER_WIDTH = "1" *) 
  (* C_AXI_DATA_WIDTH = "64" *) 
  (* C_AXI_ID_WIDTH = "16" *) 
  (* C_AXI_IS_ACLK_ASYNC = "1" *) 
  (* C_AXI_PROTOCOL = "0" *) 
  (* C_AXI_RUSER_WIDTH = "1" *) 
  (* C_AXI_SUPPORTS_READ = "1" *) 
  (* C_AXI_SUPPORTS_USER_SIGNALS = "0" *) 
  (* C_AXI_SUPPORTS_WRITE = "1" *) 
  (* C_AXI_WUSER_WIDTH = "1" *) 
  (* C_BID_RIGHT = "2" *) 
  (* C_BID_WIDTH = "16" *) 
  (* C_BRESP_RIGHT = "0" *) 
  (* C_BRESP_WIDTH = "2" *) 
  (* C_BUSER_RIGHT = "0" *) 
  (* C_BUSER_WIDTH = "0" *) 
  (* C_B_WIDTH = "18" *) 
  (* C_FAMILY = "virtexuplus" *) 
  (* C_FIFO_AR_WIDTH = "109" *) 
  (* C_FIFO_AW_WIDTH = "109" *) 
  (* C_FIFO_B_WIDTH = "18" *) 
  (* C_FIFO_R_WIDTH = "83" *) 
  (* C_FIFO_W_WIDTH = "73" *) 
  (* C_M_AXI_ACLK_RATIO = "2" *) 
  (* C_RDATA_RIGHT = "3" *) 
  (* C_RDATA_WIDTH = "64" *) 
  (* C_RID_RIGHT = "67" *) 
  (* C_RID_WIDTH = "16" *) 
  (* C_RLAST_RIGHT = "0" *) 
  (* C_RLAST_WIDTH = "1" *) 
  (* C_RRESP_RIGHT = "1" *) 
  (* C_RRESP_WIDTH = "2" *) 
  (* C_RUSER_RIGHT = "0" *) 
  (* C_RUSER_WIDTH = "0" *) 
  (* C_R_WIDTH = "83" *) 
  (* C_SYNCHRONIZER_STAGE = "3" *) 
  (* C_S_AXI_ACLK_RATIO = "1" *) 
  (* C_WDATA_RIGHT = "9" *) 
  (* C_WDATA_WIDTH = "64" *) 
  (* C_WID_RIGHT = "73" *) 
  (* C_WID_WIDTH = "0" *) 
  (* C_WLAST_RIGHT = "0" *) 
  (* C_WLAST_WIDTH = "1" *) 
  (* C_WSTRB_RIGHT = "1" *) 
  (* C_WSTRB_WIDTH = "8" *) 
  (* C_WUSER_RIGHT = "0" *) 
  (* C_WUSER_WIDTH = "0" *) 
  (* C_W_WIDTH = "73" *) 
  (* P_ACLK_RATIO = "2" *) 
  (* P_AXI3 = "1" *) 
  (* P_AXI4 = "0" *) 
  (* P_AXILITE = "2" *) 
  (* P_FULLY_REG = "1" *) 
  (* P_LIGHT_WT = "0" *) 
  (* P_LUTRAM_ASYNC = "12" *) 
  (* P_ROUNDING_OFFSET = "0" *) 
  (* P_SI_LT_MI = "1'b1" *) 
  (* downgradeipidentifiedwarnings = "yes" *) 
  axi_clock_converter_dramslim_axi_clock_converter_v2_1_11_axi_clock_converter inst
       (.m_axi_aclk(m_axi_aclk),
        .m_axi_araddr(m_axi_araddr),
        .m_axi_arburst(m_axi_arburst),
        .m_axi_arcache(m_axi_arcache),
        .m_axi_aresetn(m_axi_aresetn),
        .m_axi_arid(m_axi_arid),
        .m_axi_arlen(m_axi_arlen),
        .m_axi_arlock(m_axi_arlock),
        .m_axi_arprot(m_axi_arprot),
        .m_axi_arqos(m_axi_arqos),
        .m_axi_arready(m_axi_arready),
        .m_axi_arregion(m_axi_arregion),
        .m_axi_arsize(m_axi_arsize),
        .m_axi_aruser(NLW_inst_m_axi_aruser_UNCONNECTED[0]),
        .m_axi_arvalid(m_axi_arvalid),
        .m_axi_awaddr(m_axi_awaddr),
        .m_axi_awburst(m_axi_awburst),
        .m_axi_awcache(m_axi_awcache),
        .m_axi_awid(m_axi_awid),
        .m_axi_awlen(m_axi_awlen),
        .m_axi_awlock(m_axi_awlock),
        .m_axi_awprot(m_axi_awprot),
        .m_axi_awqos(m_axi_awqos),
        .m_axi_awready(m_axi_awready),
        .m_axi_awregion(m_axi_awregion),
        .m_axi_awsize(m_axi_awsize),
        .m_axi_awuser(NLW_inst_m_axi_awuser_UNCONNECTED[0]),
        .m_axi_awvalid(m_axi_awvalid),
        .m_axi_bid(m_axi_bid),
        .m_axi_bready(m_axi_bready),
        .m_axi_bresp(m_axi_bresp),
        .m_axi_buser(1'b0),
        .m_axi_bvalid(m_axi_bvalid),
        .m_axi_rdata(m_axi_rdata),
        .m_axi_rid(m_axi_rid),
        .m_axi_rlast(m_axi_rlast),
        .m_axi_rready(m_axi_rready),
        .m_axi_rresp(m_axi_rresp),
        .m_axi_ruser(1'b0),
        .m_axi_rvalid(m_axi_rvalid),
        .m_axi_wdata(m_axi_wdata),
        .m_axi_wid(NLW_inst_m_axi_wid_UNCONNECTED[15:0]),
        .m_axi_wlast(m_axi_wlast),
        .m_axi_wready(m_axi_wready),
        .m_axi_wstrb(m_axi_wstrb),
        .m_axi_wuser(NLW_inst_m_axi_wuser_UNCONNECTED[0]),
        .m_axi_wvalid(m_axi_wvalid),
        .s_axi_aclk(s_axi_aclk),
        .s_axi_araddr(s_axi_araddr),
        .s_axi_arburst(s_axi_arburst),
        .s_axi_arcache(s_axi_arcache),
        .s_axi_aresetn(s_axi_aresetn),
        .s_axi_arid(s_axi_arid),
        .s_axi_arlen(s_axi_arlen),
        .s_axi_arlock(s_axi_arlock),
        .s_axi_arprot(s_axi_arprot),
        .s_axi_arqos(s_axi_arqos),
        .s_axi_arready(s_axi_arready),
        .s_axi_arregion(s_axi_arregion),
        .s_axi_arsize(s_axi_arsize),
        .s_axi_aruser(1'b0),
        .s_axi_arvalid(s_axi_arvalid),
        .s_axi_awaddr(s_axi_awaddr),
        .s_axi_awburst(s_axi_awburst),
        .s_axi_awcache(s_axi_awcache),
        .s_axi_awid(s_axi_awid),
        .s_axi_awlen(s_axi_awlen),
        .s_axi_awlock(s_axi_awlock),
        .s_axi_awprot(s_axi_awprot),
        .s_axi_awqos(s_axi_awqos),
        .s_axi_awready(s_axi_awready),
        .s_axi_awregion(s_axi_awregion),
        .s_axi_awsize(s_axi_awsize),
        .s_axi_awuser(1'b0),
        .s_axi_awvalid(s_axi_awvalid),
        .s_axi_bid(s_axi_bid),
        .s_axi_bready(s_axi_bready),
        .s_axi_bresp(s_axi_bresp),
        .s_axi_buser(NLW_inst_s_axi_buser_UNCONNECTED[0]),
        .s_axi_bvalid(s_axi_bvalid),
        .s_axi_rdata(s_axi_rdata),
        .s_axi_rid(s_axi_rid),
        .s_axi_rlast(s_axi_rlast),
        .s_axi_rready(s_axi_rready),
        .s_axi_rresp(s_axi_rresp),
        .s_axi_ruser(NLW_inst_s_axi_ruser_UNCONNECTED[0]),
        .s_axi_rvalid(s_axi_rvalid),
        .s_axi_wdata(s_axi_wdata),
        .s_axi_wid({1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0}),
        .s_axi_wlast(s_axi_wlast),
        .s_axi_wready(s_axi_wready),
        .s_axi_wstrb(s_axi_wstrb),
        .s_axi_wuser(1'b0),
        .s_axi_wvalid(s_axi_wvalid));
endmodule

(* C_ARADDR_RIGHT = "29" *) (* C_ARADDR_WIDTH = "64" *) (* C_ARBURST_RIGHT = "16" *) 
(* C_ARBURST_WIDTH = "2" *) (* C_ARCACHE_RIGHT = "11" *) (* C_ARCACHE_WIDTH = "4" *) 
(* C_ARID_RIGHT = "93" *) (* C_ARID_WIDTH = "16" *) (* C_ARLEN_RIGHT = "21" *) 
(* C_ARLEN_WIDTH = "8" *) (* C_ARLOCK_RIGHT = "15" *) (* C_ARLOCK_WIDTH = "1" *) 
(* C_ARPROT_RIGHT = "8" *) (* C_ARPROT_WIDTH = "3" *) (* C_ARQOS_RIGHT = "0" *) 
(* C_ARQOS_WIDTH = "4" *) (* C_ARREGION_RIGHT = "4" *) (* C_ARREGION_WIDTH = "4" *) 
(* C_ARSIZE_RIGHT = "18" *) (* C_ARSIZE_WIDTH = "3" *) (* C_ARUSER_RIGHT = "0" *) 
(* C_ARUSER_WIDTH = "0" *) (* C_AR_WIDTH = "109" *) (* C_AWADDR_RIGHT = "29" *) 
(* C_AWADDR_WIDTH = "64" *) (* C_AWBURST_RIGHT = "16" *) (* C_AWBURST_WIDTH = "2" *) 
(* C_AWCACHE_RIGHT = "11" *) (* C_AWCACHE_WIDTH = "4" *) (* C_AWID_RIGHT = "93" *) 
(* C_AWID_WIDTH = "16" *) (* C_AWLEN_RIGHT = "21" *) (* C_AWLEN_WIDTH = "8" *) 
(* C_AWLOCK_RIGHT = "15" *) (* C_AWLOCK_WIDTH = "1" *) (* C_AWPROT_RIGHT = "8" *) 
(* C_AWPROT_WIDTH = "3" *) (* C_AWQOS_RIGHT = "0" *) (* C_AWQOS_WIDTH = "4" *) 
(* C_AWREGION_RIGHT = "4" *) (* C_AWREGION_WIDTH = "4" *) (* C_AWSIZE_RIGHT = "18" *) 
(* C_AWSIZE_WIDTH = "3" *) (* C_AWUSER_RIGHT = "0" *) (* C_AWUSER_WIDTH = "0" *) 
(* C_AW_WIDTH = "109" *) (* C_AXI_ADDR_WIDTH = "64" *) (* C_AXI_ARUSER_WIDTH = "1" *) 
(* C_AXI_AWUSER_WIDTH = "1" *) (* C_AXI_BUSER_WIDTH = "1" *) (* C_AXI_DATA_WIDTH = "64" *) 
(* C_AXI_ID_WIDTH = "16" *) (* C_AXI_IS_ACLK_ASYNC = "1" *) (* C_AXI_PROTOCOL = "0" *) 
(* C_AXI_RUSER_WIDTH = "1" *) (* C_AXI_SUPPORTS_READ = "1" *) (* C_AXI_SUPPORTS_USER_SIGNALS = "0" *) 
(* C_AXI_SUPPORTS_WRITE = "1" *) (* C_AXI_WUSER_WIDTH = "1" *) (* C_BID_RIGHT = "2" *) 
(* C_BID_WIDTH = "16" *) (* C_BRESP_RIGHT = "0" *) (* C_BRESP_WIDTH = "2" *) 
(* C_BUSER_RIGHT = "0" *) (* C_BUSER_WIDTH = "0" *) (* C_B_WIDTH = "18" *) 
(* C_FAMILY = "virtexuplus" *) (* C_FIFO_AR_WIDTH = "109" *) (* C_FIFO_AW_WIDTH = "109" *) 
(* C_FIFO_B_WIDTH = "18" *) (* C_FIFO_R_WIDTH = "83" *) (* C_FIFO_W_WIDTH = "73" *) 
(* C_M_AXI_ACLK_RATIO = "2" *) (* C_RDATA_RIGHT = "3" *) (* C_RDATA_WIDTH = "64" *) 
(* C_RID_RIGHT = "67" *) (* C_RID_WIDTH = "16" *) (* C_RLAST_RIGHT = "0" *) 
(* C_RLAST_WIDTH = "1" *) (* C_RRESP_RIGHT = "1" *) (* C_RRESP_WIDTH = "2" *) 
(* C_RUSER_RIGHT = "0" *) (* C_RUSER_WIDTH = "0" *) (* C_R_WIDTH = "83" *) 
(* C_SYNCHRONIZER_STAGE = "3" *) (* C_S_AXI_ACLK_RATIO = "1" *) (* C_WDATA_RIGHT = "9" *) 
(* C_WDATA_WIDTH = "64" *) (* C_WID_RIGHT = "73" *) (* C_WID_WIDTH = "0" *) 
(* C_WLAST_RIGHT = "0" *) (* C_WLAST_WIDTH = "1" *) (* C_WSTRB_RIGHT = "1" *) 
(* C_WSTRB_WIDTH = "8" *) (* C_WUSER_RIGHT = "0" *) (* C_WUSER_WIDTH = "0" *) 
(* C_W_WIDTH = "73" *) (* DowngradeIPIdentifiedWarnings = "yes" *) (* ORIG_REF_NAME = "axi_clock_converter_v2_1_11_axi_clock_converter" *) 
(* P_ACLK_RATIO = "2" *) (* P_AXI3 = "1" *) (* P_AXI4 = "0" *) 
(* P_AXILITE = "2" *) (* P_FULLY_REG = "1" *) (* P_LIGHT_WT = "0" *) 
(* P_LUTRAM_ASYNC = "12" *) (* P_ROUNDING_OFFSET = "0" *) (* P_SI_LT_MI = "1'b1" *) 
module axi_clock_converter_dramslim_axi_clock_converter_v2_1_11_axi_clock_converter
   (s_axi_aclk,
    s_axi_aresetn,
    s_axi_awid,
    s_axi_awaddr,
    s_axi_awlen,
    s_axi_awsize,
    s_axi_awburst,
    s_axi_awlock,
    s_axi_awcache,
    s_axi_awprot,
    s_axi_awregion,
    s_axi_awqos,
    s_axi_awuser,
    s_axi_awvalid,
    s_axi_awready,
    s_axi_wid,
    s_axi_wdata,
    s_axi_wstrb,
    s_axi_wlast,
    s_axi_wuser,
    s_axi_wvalid,
    s_axi_wready,
    s_axi_bid,
    s_axi_bresp,
    s_axi_buser,
    s_axi_bvalid,
    s_axi_bready,
    s_axi_arid,
    s_axi_araddr,
    s_axi_arlen,
    s_axi_arsize,
    s_axi_arburst,
    s_axi_arlock,
    s_axi_arcache,
    s_axi_arprot,
    s_axi_arregion,
    s_axi_arqos,
    s_axi_aruser,
    s_axi_arvalid,
    s_axi_arready,
    s_axi_rid,
    s_axi_rdata,
    s_axi_rresp,
    s_axi_rlast,
    s_axi_ruser,
    s_axi_rvalid,
    s_axi_rready,
    m_axi_aclk,
    m_axi_aresetn,
    m_axi_awid,
    m_axi_awaddr,
    m_axi_awlen,
    m_axi_awsize,
    m_axi_awburst,
    m_axi_awlock,
    m_axi_awcache,
    m_axi_awprot,
    m_axi_awregion,
    m_axi_awqos,
    m_axi_awuser,
    m_axi_awvalid,
    m_axi_awready,
    m_axi_wid,
    m_axi_wdata,
    m_axi_wstrb,
    m_axi_wlast,
    m_axi_wuser,
    m_axi_wvalid,
    m_axi_wready,
    m_axi_bid,
    m_axi_bresp,
    m_axi_buser,
    m_axi_bvalid,
    m_axi_bready,
    m_axi_arid,
    m_axi_araddr,
    m_axi_arlen,
    m_axi_arsize,
    m_axi_arburst,
    m_axi_arlock,
    m_axi_arcache,
    m_axi_arprot,
    m_axi_arregion,
    m_axi_arqos,
    m_axi_aruser,
    m_axi_arvalid,
    m_axi_arready,
    m_axi_rid,
    m_axi_rdata,
    m_axi_rresp,
    m_axi_rlast,
    m_axi_ruser,
    m_axi_rvalid,
    m_axi_rready);
  (* keep = "true" *) input s_axi_aclk;
  (* keep = "true" *) input s_axi_aresetn;
  input [15:0]s_axi_awid;
  input [63:0]s_axi_awaddr;
  input [7:0]s_axi_awlen;
  input [2:0]s_axi_awsize;
  input [1:0]s_axi_awburst;
  input [0:0]s_axi_awlock;
  input [3:0]s_axi_awcache;
  input [2:0]s_axi_awprot;
  input [3:0]s_axi_awregion;
  input [3:0]s_axi_awqos;
  input [0:0]s_axi_awuser;
  input s_axi_awvalid;
  output s_axi_awready;
  input [15:0]s_axi_wid;
  input [63:0]s_axi_wdata;
  input [7:0]s_axi_wstrb;
  input s_axi_wlast;
  input [0:0]s_axi_wuser;
  input s_axi_wvalid;
  output s_axi_wready;
  output [15:0]s_axi_bid;
  output [1:0]s_axi_bresp;
  output [0:0]s_axi_buser;
  output s_axi_bvalid;
  input s_axi_bready;
  input [15:0]s_axi_arid;
  input [63:0]s_axi_araddr;
  input [7:0]s_axi_arlen;
  input [2:0]s_axi_arsize;
  input [1:0]s_axi_arburst;
  input [0:0]s_axi_arlock;
  input [3:0]s_axi_arcache;
  input [2:0]s_axi_arprot;
  input [3:0]s_axi_arregion;
  input [3:0]s_axi_arqos;
  input [0:0]s_axi_aruser;
  input s_axi_arvalid;
  output s_axi_arready;
  output [15:0]s_axi_rid;
  output [63:0]s_axi_rdata;
  output [1:0]s_axi_rresp;
  output s_axi_rlast;
  output [0:0]s_axi_ruser;
  output s_axi_rvalid;
  input s_axi_rready;
  (* keep = "true" *) input m_axi_aclk;
  (* keep = "true" *) input m_axi_aresetn;
  output [15:0]m_axi_awid;
  output [63:0]m_axi_awaddr;
  output [7:0]m_axi_awlen;
  output [2:0]m_axi_awsize;
  output [1:0]m_axi_awburst;
  output [0:0]m_axi_awlock;
  output [3:0]m_axi_awcache;
  output [2:0]m_axi_awprot;
  output [3:0]m_axi_awregion;
  output [3:0]m_axi_awqos;
  output [0:0]m_axi_awuser;
  output m_axi_awvalid;
  input m_axi_awready;
  output [15:0]m_axi_wid;
  output [63:0]m_axi_wdata;
  output [7:0]m_axi_wstrb;
  output m_axi_wlast;
  output [0:0]m_axi_wuser;
  output m_axi_wvalid;
  input m_axi_wready;
  input [15:0]m_axi_bid;
  input [1:0]m_axi_bresp;
  input [0:0]m_axi_buser;
  input m_axi_bvalid;
  output m_axi_bready;
  output [15:0]m_axi_arid;
  output [63:0]m_axi_araddr;
  output [7:0]m_axi_arlen;
  output [2:0]m_axi_arsize;
  output [1:0]m_axi_arburst;
  output [0:0]m_axi_arlock;
  output [3:0]m_axi_arcache;
  output [2:0]m_axi_arprot;
  output [3:0]m_axi_arregion;
  output [3:0]m_axi_arqos;
  output [0:0]m_axi_aruser;
  output m_axi_arvalid;
  input m_axi_arready;
  input [15:0]m_axi_rid;
  input [63:0]m_axi_rdata;
  input [1:0]m_axi_rresp;
  input m_axi_rlast;
  input [0:0]m_axi_ruser;
  input m_axi_rvalid;
  output m_axi_rready;

  wire \<const0> ;
  wire async_conv_reset_n;
  (* RTL_KEEP = "true" *) wire m_axi_aclk;
  wire [63:0]m_axi_araddr;
  wire [1:0]m_axi_arburst;
  wire [3:0]m_axi_arcache;
  (* RTL_KEEP = "true" *) wire m_axi_aresetn;
  wire [15:0]m_axi_arid;
  wire [7:0]m_axi_arlen;
  wire [0:0]m_axi_arlock;
  wire [2:0]m_axi_arprot;
  wire [3:0]m_axi_arqos;
  wire m_axi_arready;
  wire [3:0]m_axi_arregion;
  wire [2:0]m_axi_arsize;
  wire m_axi_arvalid;
  wire [63:0]m_axi_awaddr;
  wire [1:0]m_axi_awburst;
  wire [3:0]m_axi_awcache;
  wire [15:0]m_axi_awid;
  wire [7:0]m_axi_awlen;
  wire [0:0]m_axi_awlock;
  wire [2:0]m_axi_awprot;
  wire [3:0]m_axi_awqos;
  wire m_axi_awready;
  wire [3:0]m_axi_awregion;
  wire [2:0]m_axi_awsize;
  wire m_axi_awvalid;
  wire [15:0]m_axi_bid;
  wire m_axi_bready;
  wire [1:0]m_axi_bresp;
  wire m_axi_bvalid;
  wire [63:0]m_axi_rdata;
  wire [15:0]m_axi_rid;
  wire m_axi_rlast;
  wire m_axi_rready;
  wire [1:0]m_axi_rresp;
  wire m_axi_rvalid;
  wire [63:0]m_axi_wdata;
  wire m_axi_wlast;
  wire m_axi_wready;
  wire [7:0]m_axi_wstrb;
  wire m_axi_wvalid;
  (* RTL_KEEP = "true" *) wire s_axi_aclk;
  wire [63:0]s_axi_araddr;
  wire [1:0]s_axi_arburst;
  wire [3:0]s_axi_arcache;
  (* RTL_KEEP = "true" *) wire s_axi_aresetn;
  wire [15:0]s_axi_arid;
  wire [7:0]s_axi_arlen;
  wire [0:0]s_axi_arlock;
  wire [2:0]s_axi_arprot;
  wire [3:0]s_axi_arqos;
  wire s_axi_arready;
  wire [3:0]s_axi_arregion;
  wire [2:0]s_axi_arsize;
  wire s_axi_arvalid;
  wire [63:0]s_axi_awaddr;
  wire [1:0]s_axi_awburst;
  wire [3:0]s_axi_awcache;
  wire [15:0]s_axi_awid;
  wire [7:0]s_axi_awlen;
  wire [0:0]s_axi_awlock;
  wire [2:0]s_axi_awprot;
  wire [3:0]s_axi_awqos;
  wire s_axi_awready;
  wire [3:0]s_axi_awregion;
  wire [2:0]s_axi_awsize;
  wire s_axi_awvalid;
  wire [15:0]s_axi_bid;
  wire s_axi_bready;
  wire [1:0]s_axi_bresp;
  wire s_axi_bvalid;
  wire [63:0]s_axi_rdata;
  wire [15:0]s_axi_rid;
  wire s_axi_rlast;
  wire s_axi_rready;
  wire [1:0]s_axi_rresp;
  wire s_axi_rvalid;
  wire [63:0]s_axi_wdata;
  wire s_axi_wlast;
  wire s_axi_wready;
  wire [7:0]s_axi_wstrb;
  wire s_axi_wvalid;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_almost_empty_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_almost_full_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_ar_dbiterr_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_ar_overflow_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_ar_prog_empty_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_ar_prog_full_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_ar_sbiterr_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_ar_underflow_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_aw_dbiterr_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_aw_overflow_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_aw_prog_empty_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_aw_prog_full_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_aw_sbiterr_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_aw_underflow_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_b_dbiterr_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_b_overflow_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_b_prog_empty_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_b_prog_full_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_b_sbiterr_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_b_underflow_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_r_dbiterr_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_r_overflow_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_r_prog_empty_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_r_prog_full_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_r_sbiterr_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_r_underflow_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_w_dbiterr_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_w_overflow_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_w_prog_empty_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_w_prog_full_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_w_sbiterr_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_w_underflow_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axis_dbiterr_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axis_overflow_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axis_prog_empty_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axis_prog_full_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axis_sbiterr_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axis_underflow_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_dbiterr_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_empty_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_full_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_m_axis_tlast_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_m_axis_tvalid_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_overflow_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_prog_empty_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_prog_full_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_rd_rst_busy_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_s_axis_tready_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_sbiterr_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_underflow_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_valid_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_wr_ack_UNCONNECTED ;
  wire \NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_wr_rst_busy_UNCONNECTED ;
  wire [4:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_ar_data_count_UNCONNECTED ;
  wire [4:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_ar_rd_data_count_UNCONNECTED ;
  wire [4:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_ar_wr_data_count_UNCONNECTED ;
  wire [4:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_aw_data_count_UNCONNECTED ;
  wire [4:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_aw_rd_data_count_UNCONNECTED ;
  wire [4:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_aw_wr_data_count_UNCONNECTED ;
  wire [4:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_b_data_count_UNCONNECTED ;
  wire [4:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_b_rd_data_count_UNCONNECTED ;
  wire [4:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_b_wr_data_count_UNCONNECTED ;
  wire [4:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_r_data_count_UNCONNECTED ;
  wire [4:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_r_rd_data_count_UNCONNECTED ;
  wire [4:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_r_wr_data_count_UNCONNECTED ;
  wire [4:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_w_data_count_UNCONNECTED ;
  wire [4:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_w_rd_data_count_UNCONNECTED ;
  wire [4:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_w_wr_data_count_UNCONNECTED ;
  wire [10:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axis_data_count_UNCONNECTED ;
  wire [10:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axis_rd_data_count_UNCONNECTED ;
  wire [10:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axis_wr_data_count_UNCONNECTED ;
  wire [9:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_data_count_UNCONNECTED ;
  wire [17:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_dout_UNCONNECTED ;
  wire [0:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_m_axi_aruser_UNCONNECTED ;
  wire [0:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_m_axi_awuser_UNCONNECTED ;
  wire [15:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_m_axi_wid_UNCONNECTED ;
  wire [0:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_m_axi_wuser_UNCONNECTED ;
  wire [7:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_m_axis_tdata_UNCONNECTED ;
  wire [0:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_m_axis_tdest_UNCONNECTED ;
  wire [0:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_m_axis_tid_UNCONNECTED ;
  wire [0:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_m_axis_tkeep_UNCONNECTED ;
  wire [0:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_m_axis_tstrb_UNCONNECTED ;
  wire [3:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_m_axis_tuser_UNCONNECTED ;
  wire [9:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_rd_data_count_UNCONNECTED ;
  wire [0:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_s_axi_buser_UNCONNECTED ;
  wire [0:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_s_axi_ruser_UNCONNECTED ;
  wire [9:0]\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_wr_data_count_UNCONNECTED ;

  assign m_axi_aruser[0] = \<const0> ;
  assign m_axi_awuser[0] = \<const0> ;
  assign m_axi_wid[15] = \<const0> ;
  assign m_axi_wid[14] = \<const0> ;
  assign m_axi_wid[13] = \<const0> ;
  assign m_axi_wid[12] = \<const0> ;
  assign m_axi_wid[11] = \<const0> ;
  assign m_axi_wid[10] = \<const0> ;
  assign m_axi_wid[9] = \<const0> ;
  assign m_axi_wid[8] = \<const0> ;
  assign m_axi_wid[7] = \<const0> ;
  assign m_axi_wid[6] = \<const0> ;
  assign m_axi_wid[5] = \<const0> ;
  assign m_axi_wid[4] = \<const0> ;
  assign m_axi_wid[3] = \<const0> ;
  assign m_axi_wid[2] = \<const0> ;
  assign m_axi_wid[1] = \<const0> ;
  assign m_axi_wid[0] = \<const0> ;
  assign m_axi_wuser[0] = \<const0> ;
  assign s_axi_buser[0] = \<const0> ;
  assign s_axi_ruser[0] = \<const0> ;
  GND GND
       (.G(\<const0> ));
  (* C_ADD_NGC_CONSTRAINT = "0" *) 
  (* C_APPLICATION_TYPE_AXIS = "0" *) 
  (* C_APPLICATION_TYPE_RACH = "0" *) 
  (* C_APPLICATION_TYPE_RDCH = "0" *) 
  (* C_APPLICATION_TYPE_WACH = "0" *) 
  (* C_APPLICATION_TYPE_WDCH = "0" *) 
  (* C_APPLICATION_TYPE_WRCH = "0" *) 
  (* C_AXIS_TDATA_WIDTH = "8" *) 
  (* C_AXIS_TDEST_WIDTH = "1" *) 
  (* C_AXIS_TID_WIDTH = "1" *) 
  (* C_AXIS_TKEEP_WIDTH = "1" *) 
  (* C_AXIS_TSTRB_WIDTH = "1" *) 
  (* C_AXIS_TUSER_WIDTH = "4" *) 
  (* C_AXIS_TYPE = "0" *) 
  (* C_AXI_ADDR_WIDTH = "64" *) 
  (* C_AXI_ARUSER_WIDTH = "1" *) 
  (* C_AXI_AWUSER_WIDTH = "1" *) 
  (* C_AXI_BUSER_WIDTH = "1" *) 
  (* C_AXI_DATA_WIDTH = "64" *) 
  (* C_AXI_ID_WIDTH = "16" *) 
  (* C_AXI_LEN_WIDTH = "8" *) 
  (* C_AXI_LOCK_WIDTH = "1" *) 
  (* C_AXI_RUSER_WIDTH = "1" *) 
  (* C_AXI_TYPE = "1" *) 
  (* C_AXI_WUSER_WIDTH = "1" *) 
  (* C_COMMON_CLOCK = "0" *) 
  (* C_COUNT_TYPE = "0" *) 
  (* C_DATA_COUNT_WIDTH = "10" *) 
  (* C_DEFAULT_VALUE = "BlankString" *) 
  (* C_DIN_WIDTH = "18" *) 
  (* C_DIN_WIDTH_AXIS = "1" *) 
  (* C_DIN_WIDTH_RACH = "109" *) 
  (* C_DIN_WIDTH_RDCH = "83" *) 
  (* C_DIN_WIDTH_WACH = "109" *) 
  (* C_DIN_WIDTH_WDCH = "73" *) 
  (* C_DIN_WIDTH_WRCH = "18" *) 
  (* C_DOUT_RST_VAL = "0" *) 
  (* C_DOUT_WIDTH = "18" *) 
  (* C_ENABLE_RLOCS = "0" *) 
  (* C_ENABLE_RST_SYNC = "1" *) 
  (* C_EN_SAFETY_CKT = "0" *) 
  (* C_ERROR_INJECTION_TYPE = "0" *) 
  (* C_ERROR_INJECTION_TYPE_AXIS = "0" *) 
  (* C_ERROR_INJECTION_TYPE_RACH = "0" *) 
  (* C_ERROR_INJECTION_TYPE_RDCH = "0" *) 
  (* C_ERROR_INJECTION_TYPE_WACH = "0" *) 
  (* C_ERROR_INJECTION_TYPE_WDCH = "0" *) 
  (* C_ERROR_INJECTION_TYPE_WRCH = "0" *) 
  (* C_FAMILY = "virtexuplus" *) 
  (* C_FULL_FLAGS_RST_VAL = "1" *) 
  (* C_HAS_ALMOST_EMPTY = "0" *) 
  (* C_HAS_ALMOST_FULL = "0" *) 
  (* C_HAS_AXIS_TDATA = "1" *) 
  (* C_HAS_AXIS_TDEST = "0" *) 
  (* C_HAS_AXIS_TID = "0" *) 
  (* C_HAS_AXIS_TKEEP = "0" *) 
  (* C_HAS_AXIS_TLAST = "0" *) 
  (* C_HAS_AXIS_TREADY = "1" *) 
  (* C_HAS_AXIS_TSTRB = "0" *) 
  (* C_HAS_AXIS_TUSER = "1" *) 
  (* C_HAS_AXI_ARUSER = "0" *) 
  (* C_HAS_AXI_AWUSER = "0" *) 
  (* C_HAS_AXI_BUSER = "0" *) 
  (* C_HAS_AXI_ID = "1" *) 
  (* C_HAS_AXI_RD_CHANNEL = "1" *) 
  (* C_HAS_AXI_RUSER = "0" *) 
  (* C_HAS_AXI_WR_CHANNEL = "1" *) 
  (* C_HAS_AXI_WUSER = "0" *) 
  (* C_HAS_BACKUP = "0" *) 
  (* C_HAS_DATA_COUNT = "0" *) 
  (* C_HAS_DATA_COUNTS_AXIS = "0" *) 
  (* C_HAS_DATA_COUNTS_RACH = "0" *) 
  (* C_HAS_DATA_COUNTS_RDCH = "0" *) 
  (* C_HAS_DATA_COUNTS_WACH = "0" *) 
  (* C_HAS_DATA_COUNTS_WDCH = "0" *) 
  (* C_HAS_DATA_COUNTS_WRCH = "0" *) 
  (* C_HAS_INT_CLK = "0" *) 
  (* C_HAS_MASTER_CE = "0" *) 
  (* C_HAS_MEMINIT_FILE = "0" *) 
  (* C_HAS_OVERFLOW = "0" *) 
  (* C_HAS_PROG_FLAGS_AXIS = "0" *) 
  (* C_HAS_PROG_FLAGS_RACH = "0" *) 
  (* C_HAS_PROG_FLAGS_RDCH = "0" *) 
  (* C_HAS_PROG_FLAGS_WACH = "0" *) 
  (* C_HAS_PROG_FLAGS_WDCH = "0" *) 
  (* C_HAS_PROG_FLAGS_WRCH = "0" *) 
  (* C_HAS_RD_DATA_COUNT = "0" *) 
  (* C_HAS_RD_RST = "0" *) 
  (* C_HAS_RST = "1" *) 
  (* C_HAS_SLAVE_CE = "0" *) 
  (* C_HAS_SRST = "0" *) 
  (* C_HAS_UNDERFLOW = "0" *) 
  (* C_HAS_VALID = "0" *) 
  (* C_HAS_WR_ACK = "0" *) 
  (* C_HAS_WR_DATA_COUNT = "0" *) 
  (* C_HAS_WR_RST = "0" *) 
  (* C_IMPLEMENTATION_TYPE = "0" *) 
  (* C_IMPLEMENTATION_TYPE_AXIS = "11" *) 
  (* C_IMPLEMENTATION_TYPE_RACH = "12" *) 
  (* C_IMPLEMENTATION_TYPE_RDCH = "12" *) 
  (* C_IMPLEMENTATION_TYPE_WACH = "12" *) 
  (* C_IMPLEMENTATION_TYPE_WDCH = "12" *) 
  (* C_IMPLEMENTATION_TYPE_WRCH = "12" *) 
  (* C_INIT_WR_PNTR_VAL = "0" *) 
  (* C_INTERFACE_TYPE = "2" *) 
  (* C_MEMORY_TYPE = "1" *) 
  (* C_MIF_FILE_NAME = "BlankString" *) 
  (* C_MSGON_VAL = "1" *) 
  (* C_OPTIMIZATION_MODE = "0" *) 
  (* C_OVERFLOW_LOW = "0" *) 
  (* C_POWER_SAVING_MODE = "0" *) 
  (* C_PRELOAD_LATENCY = "1" *) 
  (* C_PRELOAD_REGS = "0" *) 
  (* C_PRIM_FIFO_TYPE = "4kx4" *) 
  (* C_PRIM_FIFO_TYPE_AXIS = "512x36" *) 
  (* C_PRIM_FIFO_TYPE_RACH = "512x36" *) 
  (* C_PRIM_FIFO_TYPE_RDCH = "512x36" *) 
  (* C_PRIM_FIFO_TYPE_WACH = "512x36" *) 
  (* C_PRIM_FIFO_TYPE_WDCH = "512x36" *) 
  (* C_PRIM_FIFO_TYPE_WRCH = "512x36" *) 
  (* C_PROG_EMPTY_THRESH_ASSERT_VAL = "2" *) 
  (* C_PROG_EMPTY_THRESH_ASSERT_VAL_AXIS = "1021" *) 
  (* C_PROG_EMPTY_THRESH_ASSERT_VAL_RACH = "13" *) 
  (* C_PROG_EMPTY_THRESH_ASSERT_VAL_RDCH = "13" *) 
  (* C_PROG_EMPTY_THRESH_ASSERT_VAL_WACH = "13" *) 
  (* C_PROG_EMPTY_THRESH_ASSERT_VAL_WDCH = "13" *) 
  (* C_PROG_EMPTY_THRESH_ASSERT_VAL_WRCH = "13" *) 
  (* C_PROG_EMPTY_THRESH_NEGATE_VAL = "3" *) 
  (* C_PROG_EMPTY_TYPE = "0" *) 
  (* C_PROG_EMPTY_TYPE_AXIS = "0" *) 
  (* C_PROG_EMPTY_TYPE_RACH = "0" *) 
  (* C_PROG_EMPTY_TYPE_RDCH = "0" *) 
  (* C_PROG_EMPTY_TYPE_WACH = "0" *) 
  (* C_PROG_EMPTY_TYPE_WDCH = "0" *) 
  (* C_PROG_EMPTY_TYPE_WRCH = "0" *) 
  (* C_PROG_FULL_THRESH_ASSERT_VAL = "1022" *) 
  (* C_PROG_FULL_THRESH_ASSERT_VAL_AXIS = "1023" *) 
  (* C_PROG_FULL_THRESH_ASSERT_VAL_RACH = "15" *) 
  (* C_PROG_FULL_THRESH_ASSERT_VAL_RDCH = "15" *) 
  (* C_PROG_FULL_THRESH_ASSERT_VAL_WACH = "15" *) 
  (* C_PROG_FULL_THRESH_ASSERT_VAL_WDCH = "15" *) 
  (* C_PROG_FULL_THRESH_ASSERT_VAL_WRCH = "15" *) 
  (* C_PROG_FULL_THRESH_NEGATE_VAL = "1021" *) 
  (* C_PROG_FULL_TYPE = "0" *) 
  (* C_PROG_FULL_TYPE_AXIS = "0" *) 
  (* C_PROG_FULL_TYPE_RACH = "0" *) 
  (* C_PROG_FULL_TYPE_RDCH = "0" *) 
  (* C_PROG_FULL_TYPE_WACH = "0" *) 
  (* C_PROG_FULL_TYPE_WDCH = "0" *) 
  (* C_PROG_FULL_TYPE_WRCH = "0" *) 
  (* C_RACH_TYPE = "0" *) 
  (* C_RDCH_TYPE = "0" *) 
  (* C_RD_DATA_COUNT_WIDTH = "10" *) 
  (* C_RD_DEPTH = "1024" *) 
  (* C_RD_FREQ = "1" *) 
  (* C_RD_PNTR_WIDTH = "10" *) 
  (* C_REG_SLICE_MODE_AXIS = "0" *) 
  (* C_REG_SLICE_MODE_RACH = "0" *) 
  (* C_REG_SLICE_MODE_RDCH = "0" *) 
  (* C_REG_SLICE_MODE_WACH = "0" *) 
  (* C_REG_SLICE_MODE_WDCH = "0" *) 
  (* C_REG_SLICE_MODE_WRCH = "0" *) 
  (* C_SELECT_XPM = "0" *) 
  (* C_SYNCHRONIZER_STAGE = "3" *) 
  (* C_UNDERFLOW_LOW = "0" *) 
  (* C_USE_COMMON_OVERFLOW = "0" *) 
  (* C_USE_COMMON_UNDERFLOW = "0" *) 
  (* C_USE_DEFAULT_SETTINGS = "0" *) 
  (* C_USE_DOUT_RST = "1" *) 
  (* C_USE_ECC = "0" *) 
  (* C_USE_ECC_AXIS = "0" *) 
  (* C_USE_ECC_RACH = "0" *) 
  (* C_USE_ECC_RDCH = "0" *) 
  (* C_USE_ECC_WACH = "0" *) 
  (* C_USE_ECC_WDCH = "0" *) 
  (* C_USE_ECC_WRCH = "0" *) 
  (* C_USE_EMBEDDED_REG = "0" *) 
  (* C_USE_FIFO16_FLAGS = "0" *) 
  (* C_USE_FWFT_DATA_COUNT = "0" *) 
  (* C_USE_PIPELINE_REG = "0" *) 
  (* C_VALID_LOW = "0" *) 
  (* C_WACH_TYPE = "0" *) 
  (* C_WDCH_TYPE = "0" *) 
  (* C_WRCH_TYPE = "0" *) 
  (* C_WR_ACK_LOW = "0" *) 
  (* C_WR_DATA_COUNT_WIDTH = "10" *) 
  (* C_WR_DEPTH = "1024" *) 
  (* C_WR_DEPTH_AXIS = "1024" *) 
  (* C_WR_DEPTH_RACH = "16" *) 
  (* C_WR_DEPTH_RDCH = "16" *) 
  (* C_WR_DEPTH_WACH = "16" *) 
  (* C_WR_DEPTH_WDCH = "16" *) 
  (* C_WR_DEPTH_WRCH = "16" *) 
  (* C_WR_FREQ = "1" *) 
  (* C_WR_PNTR_WIDTH = "10" *) 
  (* C_WR_PNTR_WIDTH_AXIS = "10" *) 
  (* C_WR_PNTR_WIDTH_RACH = "4" *) 
  (* C_WR_PNTR_WIDTH_RDCH = "4" *) 
  (* C_WR_PNTR_WIDTH_WACH = "4" *) 
  (* C_WR_PNTR_WIDTH_WDCH = "4" *) 
  (* C_WR_PNTR_WIDTH_WRCH = "4" *) 
  (* C_WR_RESPONSE_LATENCY = "1" *) 
  axi_clock_converter_dramslim_fifo_generator_v13_1_4 \gen_clock_conv.gen_async_conv.asyncfifo_axi 
       (.almost_empty(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_almost_empty_UNCONNECTED ),
        .almost_full(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_almost_full_UNCONNECTED ),
        .axi_ar_data_count(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_ar_data_count_UNCONNECTED [4:0]),
        .axi_ar_dbiterr(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_ar_dbiterr_UNCONNECTED ),
        .axi_ar_injectdbiterr(1'b0),
        .axi_ar_injectsbiterr(1'b0),
        .axi_ar_overflow(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_ar_overflow_UNCONNECTED ),
        .axi_ar_prog_empty(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_ar_prog_empty_UNCONNECTED ),
        .axi_ar_prog_empty_thresh({1'b0,1'b0,1'b0,1'b0}),
        .axi_ar_prog_full(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_ar_prog_full_UNCONNECTED ),
        .axi_ar_prog_full_thresh({1'b0,1'b0,1'b0,1'b0}),
        .axi_ar_rd_data_count(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_ar_rd_data_count_UNCONNECTED [4:0]),
        .axi_ar_sbiterr(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_ar_sbiterr_UNCONNECTED ),
        .axi_ar_underflow(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_ar_underflow_UNCONNECTED ),
        .axi_ar_wr_data_count(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_ar_wr_data_count_UNCONNECTED [4:0]),
        .axi_aw_data_count(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_aw_data_count_UNCONNECTED [4:0]),
        .axi_aw_dbiterr(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_aw_dbiterr_UNCONNECTED ),
        .axi_aw_injectdbiterr(1'b0),
        .axi_aw_injectsbiterr(1'b0),
        .axi_aw_overflow(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_aw_overflow_UNCONNECTED ),
        .axi_aw_prog_empty(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_aw_prog_empty_UNCONNECTED ),
        .axi_aw_prog_empty_thresh({1'b0,1'b0,1'b0,1'b0}),
        .axi_aw_prog_full(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_aw_prog_full_UNCONNECTED ),
        .axi_aw_prog_full_thresh({1'b0,1'b0,1'b0,1'b0}),
        .axi_aw_rd_data_count(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_aw_rd_data_count_UNCONNECTED [4:0]),
        .axi_aw_sbiterr(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_aw_sbiterr_UNCONNECTED ),
        .axi_aw_underflow(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_aw_underflow_UNCONNECTED ),
        .axi_aw_wr_data_count(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_aw_wr_data_count_UNCONNECTED [4:0]),
        .axi_b_data_count(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_b_data_count_UNCONNECTED [4:0]),
        .axi_b_dbiterr(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_b_dbiterr_UNCONNECTED ),
        .axi_b_injectdbiterr(1'b0),
        .axi_b_injectsbiterr(1'b0),
        .axi_b_overflow(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_b_overflow_UNCONNECTED ),
        .axi_b_prog_empty(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_b_prog_empty_UNCONNECTED ),
        .axi_b_prog_empty_thresh({1'b0,1'b0,1'b0,1'b0}),
        .axi_b_prog_full(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_b_prog_full_UNCONNECTED ),
        .axi_b_prog_full_thresh({1'b0,1'b0,1'b0,1'b0}),
        .axi_b_rd_data_count(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_b_rd_data_count_UNCONNECTED [4:0]),
        .axi_b_sbiterr(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_b_sbiterr_UNCONNECTED ),
        .axi_b_underflow(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_b_underflow_UNCONNECTED ),
        .axi_b_wr_data_count(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_b_wr_data_count_UNCONNECTED [4:0]),
        .axi_r_data_count(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_r_data_count_UNCONNECTED [4:0]),
        .axi_r_dbiterr(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_r_dbiterr_UNCONNECTED ),
        .axi_r_injectdbiterr(1'b0),
        .axi_r_injectsbiterr(1'b0),
        .axi_r_overflow(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_r_overflow_UNCONNECTED ),
        .axi_r_prog_empty(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_r_prog_empty_UNCONNECTED ),
        .axi_r_prog_empty_thresh({1'b0,1'b0,1'b0,1'b0}),
        .axi_r_prog_full(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_r_prog_full_UNCONNECTED ),
        .axi_r_prog_full_thresh({1'b0,1'b0,1'b0,1'b0}),
        .axi_r_rd_data_count(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_r_rd_data_count_UNCONNECTED [4:0]),
        .axi_r_sbiterr(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_r_sbiterr_UNCONNECTED ),
        .axi_r_underflow(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_r_underflow_UNCONNECTED ),
        .axi_r_wr_data_count(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_r_wr_data_count_UNCONNECTED [4:0]),
        .axi_w_data_count(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_w_data_count_UNCONNECTED [4:0]),
        .axi_w_dbiterr(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_w_dbiterr_UNCONNECTED ),
        .axi_w_injectdbiterr(1'b0),
        .axi_w_injectsbiterr(1'b0),
        .axi_w_overflow(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_w_overflow_UNCONNECTED ),
        .axi_w_prog_empty(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_w_prog_empty_UNCONNECTED ),
        .axi_w_prog_empty_thresh({1'b0,1'b0,1'b0,1'b0}),
        .axi_w_prog_full(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_w_prog_full_UNCONNECTED ),
        .axi_w_prog_full_thresh({1'b0,1'b0,1'b0,1'b0}),
        .axi_w_rd_data_count(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_w_rd_data_count_UNCONNECTED [4:0]),
        .axi_w_sbiterr(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_w_sbiterr_UNCONNECTED ),
        .axi_w_underflow(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_w_underflow_UNCONNECTED ),
        .axi_w_wr_data_count(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axi_w_wr_data_count_UNCONNECTED [4:0]),
        .axis_data_count(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axis_data_count_UNCONNECTED [10:0]),
        .axis_dbiterr(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axis_dbiterr_UNCONNECTED ),
        .axis_injectdbiterr(1'b0),
        .axis_injectsbiterr(1'b0),
        .axis_overflow(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axis_overflow_UNCONNECTED ),
        .axis_prog_empty(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axis_prog_empty_UNCONNECTED ),
        .axis_prog_empty_thresh({1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0}),
        .axis_prog_full(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axis_prog_full_UNCONNECTED ),
        .axis_prog_full_thresh({1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0}),
        .axis_rd_data_count(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axis_rd_data_count_UNCONNECTED [10:0]),
        .axis_sbiterr(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axis_sbiterr_UNCONNECTED ),
        .axis_underflow(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axis_underflow_UNCONNECTED ),
        .axis_wr_data_count(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_axis_wr_data_count_UNCONNECTED [10:0]),
        .backup(1'b0),
        .backup_marker(1'b0),
        .clk(1'b0),
        .data_count(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_data_count_UNCONNECTED [9:0]),
        .dbiterr(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_dbiterr_UNCONNECTED ),
        .din({1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0}),
        .dout(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_dout_UNCONNECTED [17:0]),
        .empty(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_empty_UNCONNECTED ),
        .full(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_full_UNCONNECTED ),
        .injectdbiterr(1'b0),
        .injectsbiterr(1'b0),
        .int_clk(1'b0),
        .m_aclk(m_axi_aclk),
        .m_aclk_en(1'b1),
        .m_axi_araddr(m_axi_araddr),
        .m_axi_arburst(m_axi_arburst),
        .m_axi_arcache(m_axi_arcache),
        .m_axi_arid(m_axi_arid),
        .m_axi_arlen(m_axi_arlen),
        .m_axi_arlock(m_axi_arlock),
        .m_axi_arprot(m_axi_arprot),
        .m_axi_arqos(m_axi_arqos),
        .m_axi_arready(m_axi_arready),
        .m_axi_arregion(m_axi_arregion),
        .m_axi_arsize(m_axi_arsize),
        .m_axi_aruser(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_m_axi_aruser_UNCONNECTED [0]),
        .m_axi_arvalid(m_axi_arvalid),
        .m_axi_awaddr(m_axi_awaddr),
        .m_axi_awburst(m_axi_awburst),
        .m_axi_awcache(m_axi_awcache),
        .m_axi_awid(m_axi_awid),
        .m_axi_awlen(m_axi_awlen),
        .m_axi_awlock(m_axi_awlock),
        .m_axi_awprot(m_axi_awprot),
        .m_axi_awqos(m_axi_awqos),
        .m_axi_awready(m_axi_awready),
        .m_axi_awregion(m_axi_awregion),
        .m_axi_awsize(m_axi_awsize),
        .m_axi_awuser(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_m_axi_awuser_UNCONNECTED [0]),
        .m_axi_awvalid(m_axi_awvalid),
        .m_axi_bid(m_axi_bid),
        .m_axi_bready(m_axi_bready),
        .m_axi_bresp(m_axi_bresp),
        .m_axi_buser(1'b0),
        .m_axi_bvalid(m_axi_bvalid),
        .m_axi_rdata(m_axi_rdata),
        .m_axi_rid(m_axi_rid),
        .m_axi_rlast(m_axi_rlast),
        .m_axi_rready(m_axi_rready),
        .m_axi_rresp(m_axi_rresp),
        .m_axi_ruser(1'b0),
        .m_axi_rvalid(m_axi_rvalid),
        .m_axi_wdata(m_axi_wdata),
        .m_axi_wid(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_m_axi_wid_UNCONNECTED [15:0]),
        .m_axi_wlast(m_axi_wlast),
        .m_axi_wready(m_axi_wready),
        .m_axi_wstrb(m_axi_wstrb),
        .m_axi_wuser(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_m_axi_wuser_UNCONNECTED [0]),
        .m_axi_wvalid(m_axi_wvalid),
        .m_axis_tdata(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_m_axis_tdata_UNCONNECTED [7:0]),
        .m_axis_tdest(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_m_axis_tdest_UNCONNECTED [0]),
        .m_axis_tid(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_m_axis_tid_UNCONNECTED [0]),
        .m_axis_tkeep(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_m_axis_tkeep_UNCONNECTED [0]),
        .m_axis_tlast(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_m_axis_tlast_UNCONNECTED ),
        .m_axis_tready(1'b0),
        .m_axis_tstrb(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_m_axis_tstrb_UNCONNECTED [0]),
        .m_axis_tuser(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_m_axis_tuser_UNCONNECTED [3:0]),
        .m_axis_tvalid(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_m_axis_tvalid_UNCONNECTED ),
        .overflow(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_overflow_UNCONNECTED ),
        .prog_empty(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_prog_empty_UNCONNECTED ),
        .prog_empty_thresh({1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0}),
        .prog_empty_thresh_assert({1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0}),
        .prog_empty_thresh_negate({1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0}),
        .prog_full(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_prog_full_UNCONNECTED ),
        .prog_full_thresh({1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0}),
        .prog_full_thresh_assert({1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0}),
        .prog_full_thresh_negate({1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0}),
        .rd_clk(1'b0),
        .rd_data_count(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_rd_data_count_UNCONNECTED [9:0]),
        .rd_en(1'b0),
        .rd_rst(1'b0),
        .rd_rst_busy(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_rd_rst_busy_UNCONNECTED ),
        .rst(1'b0),
        .s_aclk(s_axi_aclk),
        .s_aclk_en(1'b1),
        .s_aresetn(async_conv_reset_n),
        .s_axi_araddr(s_axi_araddr),
        .s_axi_arburst(s_axi_arburst),
        .s_axi_arcache(s_axi_arcache),
        .s_axi_arid(s_axi_arid),
        .s_axi_arlen(s_axi_arlen),
        .s_axi_arlock(s_axi_arlock),
        .s_axi_arprot(s_axi_arprot),
        .s_axi_arqos(s_axi_arqos),
        .s_axi_arready(s_axi_arready),
        .s_axi_arregion(s_axi_arregion),
        .s_axi_arsize(s_axi_arsize),
        .s_axi_aruser(1'b0),
        .s_axi_arvalid(s_axi_arvalid),
        .s_axi_awaddr(s_axi_awaddr),
        .s_axi_awburst(s_axi_awburst),
        .s_axi_awcache(s_axi_awcache),
        .s_axi_awid(s_axi_awid),
        .s_axi_awlen(s_axi_awlen),
        .s_axi_awlock(s_axi_awlock),
        .s_axi_awprot(s_axi_awprot),
        .s_axi_awqos(s_axi_awqos),
        .s_axi_awready(s_axi_awready),
        .s_axi_awregion(s_axi_awregion),
        .s_axi_awsize(s_axi_awsize),
        .s_axi_awuser(1'b0),
        .s_axi_awvalid(s_axi_awvalid),
        .s_axi_bid(s_axi_bid),
        .s_axi_bready(s_axi_bready),
        .s_axi_bresp(s_axi_bresp),
        .s_axi_buser(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_s_axi_buser_UNCONNECTED [0]),
        .s_axi_bvalid(s_axi_bvalid),
        .s_axi_rdata(s_axi_rdata),
        .s_axi_rid(s_axi_rid),
        .s_axi_rlast(s_axi_rlast),
        .s_axi_rready(s_axi_rready),
        .s_axi_rresp(s_axi_rresp),
        .s_axi_ruser(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_s_axi_ruser_UNCONNECTED [0]),
        .s_axi_rvalid(s_axi_rvalid),
        .s_axi_wdata(s_axi_wdata),
        .s_axi_wid({1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0}),
        .s_axi_wlast(s_axi_wlast),
        .s_axi_wready(s_axi_wready),
        .s_axi_wstrb(s_axi_wstrb),
        .s_axi_wuser(1'b0),
        .s_axi_wvalid(s_axi_wvalid),
        .s_axis_tdata({1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0}),
        .s_axis_tdest(1'b0),
        .s_axis_tid(1'b0),
        .s_axis_tkeep(1'b0),
        .s_axis_tlast(1'b0),
        .s_axis_tready(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_s_axis_tready_UNCONNECTED ),
        .s_axis_tstrb(1'b0),
        .s_axis_tuser({1'b0,1'b0,1'b0,1'b0}),
        .s_axis_tvalid(1'b0),
        .sbiterr(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_sbiterr_UNCONNECTED ),
        .sleep(1'b0),
        .srst(1'b0),
        .underflow(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_underflow_UNCONNECTED ),
        .valid(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_valid_UNCONNECTED ),
        .wr_ack(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_wr_ack_UNCONNECTED ),
        .wr_clk(1'b0),
        .wr_data_count(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_wr_data_count_UNCONNECTED [9:0]),
        .wr_en(1'b0),
        .wr_rst(1'b0),
        .wr_rst_busy(\NLW_gen_clock_conv.gen_async_conv.asyncfifo_axi_wr_rst_busy_UNCONNECTED ));
  LUT2 #(
    .INIT(4'h8)) 
    \gen_clock_conv.gen_async_conv.asyncfifo_axi_i_1 
       (.I0(s_axi_aresetn),
        .I1(m_axi_aresetn),
        .O(async_conv_reset_n));
endmodule

(* ORIG_REF_NAME = "clk_x_pntrs" *) 
module axi_clock_converter_dramslim_clk_x_pntrs
   (out,
    ram_full_fb_i_reg,
    ram_full_fb_i_reg_0,
    ram_empty_i_reg,
    ram_empty_i_reg_0,
    ram_full_fb_i_reg_1,
    Q,
    \grstd1.grst_full.grst_f.rst_d3_reg ,
    \gic0.gc0.count_reg[2] ,
    \gc0.count_reg[2] ,
    \gic0.gc0.count_d2_reg[3] ,
    m_aclk,
    AR,
    s_aclk,
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ,
    \gc0.count_d1_reg[3] ,
    D,
    \Q_reg_reg[1] );
  output [3:0]out;
  output ram_full_fb_i_reg;
  output [0:0]ram_full_fb_i_reg_0;
  output ram_empty_i_reg;
  output [3:0]ram_empty_i_reg_0;
  input ram_full_fb_i_reg_1;
  input [3:0]Q;
  input \grstd1.grst_full.grst_f.rst_d3_reg ;
  input [2:0]\gic0.gc0.count_reg[2] ;
  input [2:0]\gc0.count_reg[2] ;
  input [3:0]\gic0.gc0.count_d2_reg[3] ;
  input m_aclk;
  input [0:0]AR;
  input s_aclk;
  input [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;
  input [0:0]\gc0.count_d1_reg[3] ;
  input [2:0]D;
  input [0:0]\Q_reg_reg[1] ;

  wire [0:0]AR;
  wire [2:0]D;
  wire [3:0]Q;
  wire [0:0]\Q_reg_reg[1] ;
  wire __0_n_0;
  wire __1_n_0;
  wire __2_n_0;
  wire [2:0]bin2gray;
  wire [0:0]\gc0.count_d1_reg[3] ;
  wire [2:0]\gc0.count_reg[2] ;
  wire [3:0]\gic0.gc0.count_d2_reg[3] ;
  wire [2:0]\gic0.gc0.count_reg[2] ;
  wire \gnxpm_cdc.gsync_stage[3].rd_stg_inst_n_4 ;
  wire \gnxpm_cdc.gsync_stage[3].wr_stg_inst_n_4 ;
  wire \gnxpm_cdc.rd_pntr_gc_reg_n_0_[0] ;
  wire \gnxpm_cdc.rd_pntr_gc_reg_n_0_[1] ;
  wire \gnxpm_cdc.rd_pntr_gc_reg_n_0_[2] ;
  wire \gnxpm_cdc.rd_pntr_gc_reg_n_0_[3] ;
  wire \gnxpm_cdc.wr_pntr_gc_reg_n_0_[0] ;
  wire \gnxpm_cdc.wr_pntr_gc_reg_n_0_[1] ;
  wire \gnxpm_cdc.wr_pntr_gc_reg_n_0_[2] ;
  wire \gnxpm_cdc.wr_pntr_gc_reg_n_0_[3] ;
  wire \grstd1.grst_full.grst_f.rst_d3_reg ;
  wire m_aclk;
  wire [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;
  wire [3:0]out;
  wire [2:0]p_23_out;
  wire [3:0]p_3_out;
  wire [3:0]p_4_out;
  wire [3:0]p_5_out;
  wire [3:0]p_6_out;
  wire [3:0]p_8_out;
  wire ram_empty_i_reg;
  wire [3:0]ram_empty_i_reg_0;
  wire ram_full_fb_i_reg;
  wire [0:0]ram_full_fb_i_reg_0;
  wire ram_full_fb_i_reg_1;
  wire ram_full_i_i_2_n_0;
  wire ram_full_i_i_4_n_0;
  wire s_aclk;

  LUT3 #(
    .INIT(8'h96)) 
    __0
       (.I0(out[2]),
        .I1(out[1]),
        .I2(out[3]),
        .O(__0_n_0));
  (* SOFT_HLUTNM = "soft_lutpair24" *) 
  LUT4 #(
    .INIT(16'h6996)) 
    __1
       (.I0(p_8_out[1]),
        .I1(p_8_out[0]),
        .I2(p_8_out[3]),
        .I3(p_8_out[2]),
        .O(__1_n_0));
  (* SOFT_HLUTNM = "soft_lutpair24" *) 
  LUT3 #(
    .INIT(8'h96)) 
    __2
       (.I0(p_8_out[2]),
        .I1(p_8_out[1]),
        .I2(p_8_out[3]),
        .O(__2_n_0));
  axi_clock_converter_dramslim_synchronizer_ff__parameterized0 \gnxpm_cdc.gsync_stage[1].rd_stg_inst 
       (.D(p_3_out),
        .Q({\gnxpm_cdc.wr_pntr_gc_reg_n_0_[3] ,\gnxpm_cdc.wr_pntr_gc_reg_n_0_[2] ,\gnxpm_cdc.wr_pntr_gc_reg_n_0_[1] ,\gnxpm_cdc.wr_pntr_gc_reg_n_0_[0] }),
        .\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] (\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .s_aclk(s_aclk));
  axi_clock_converter_dramslim_synchronizer_ff__parameterized0_6 \gnxpm_cdc.gsync_stage[1].wr_stg_inst 
       (.AR(AR),
        .D(p_4_out),
        .Q({\gnxpm_cdc.rd_pntr_gc_reg_n_0_[3] ,\gnxpm_cdc.rd_pntr_gc_reg_n_0_[2] ,\gnxpm_cdc.rd_pntr_gc_reg_n_0_[1] ,\gnxpm_cdc.rd_pntr_gc_reg_n_0_[0] }),
        .m_aclk(m_aclk));
  axi_clock_converter_dramslim_synchronizer_ff__parameterized0_7 \gnxpm_cdc.gsync_stage[2].rd_stg_inst 
       (.D(p_5_out),
        .\Q_reg_reg[3]_0 (p_3_out),
        .\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] (\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .s_aclk(s_aclk));
  axi_clock_converter_dramslim_synchronizer_ff__parameterized0_8 \gnxpm_cdc.gsync_stage[2].wr_stg_inst 
       (.AR(AR),
        .D(p_6_out),
        .\Q_reg_reg[3]_0 (p_4_out),
        .m_aclk(m_aclk));
  axi_clock_converter_dramslim_synchronizer_ff__parameterized0_9 \gnxpm_cdc.gsync_stage[3].rd_stg_inst 
       (.D(\gnxpm_cdc.gsync_stage[3].rd_stg_inst_n_4 ),
        .\Q_reg_reg[3]_0 (p_5_out),
        .\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] (\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .out(out),
        .s_aclk(s_aclk));
  axi_clock_converter_dramslim_synchronizer_ff__parameterized0_10 \gnxpm_cdc.gsync_stage[3].wr_stg_inst 
       (.AR(AR),
        .D(\gnxpm_cdc.gsync_stage[3].wr_stg_inst_n_4 ),
        .\Q_reg_reg[3]_0 (p_6_out),
        .m_aclk(m_aclk),
        .out(p_8_out));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_bin_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(__1_n_0),
        .Q(p_23_out[0]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_bin_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(__2_n_0),
        .Q(p_23_out[1]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_bin_reg[2] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\gnxpm_cdc.gsync_stage[3].wr_stg_inst_n_4 ),
        .Q(p_23_out[2]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_bin_reg[3] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(p_8_out[3]),
        .Q(ram_full_fb_i_reg_0));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_gc_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(D[0]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg_n_0_[0] ));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_gc_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(D[1]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg_n_0_[1] ));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_gc_reg[2] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(D[2]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg_n_0_[2] ));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_gc_reg[3] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\gc0.count_d1_reg[3] ),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg_n_0_[3] ));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_bin_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[1] ),
        .Q(ram_empty_i_reg_0[0]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_bin_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(__0_n_0),
        .Q(ram_empty_i_reg_0[1]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_bin_reg[2] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\gnxpm_cdc.gsync_stage[3].rd_stg_inst_n_4 ),
        .Q(ram_empty_i_reg_0[2]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_bin_reg[3] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(out[3]),
        .Q(ram_empty_i_reg_0[3]));
  (* SOFT_HLUTNM = "soft_lutpair25" *) 
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.wr_pntr_gc[0]_i_1 
       (.I0(\gic0.gc0.count_d2_reg[3] [0]),
        .I1(\gic0.gc0.count_d2_reg[3] [1]),
        .O(bin2gray[0]));
  (* SOFT_HLUTNM = "soft_lutpair25" *) 
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.wr_pntr_gc[1]_i_1 
       (.I0(\gic0.gc0.count_d2_reg[3] [1]),
        .I1(\gic0.gc0.count_d2_reg[3] [2]),
        .O(bin2gray[1]));
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.wr_pntr_gc[2]_i_1 
       (.I0(\gic0.gc0.count_d2_reg[3] [2]),
        .I1(\gic0.gc0.count_d2_reg[3] [3]),
        .O(bin2gray[2]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_gc_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(bin2gray[0]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg_n_0_[0] ));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_gc_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(bin2gray[1]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg_n_0_[1] ));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_gc_reg[2] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(bin2gray[2]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg_n_0_[2] ));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_gc_reg[3] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\gic0.gc0.count_d2_reg[3] [3]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg_n_0_[3] ));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    ram_empty_i_i_4__2
       (.I0(ram_empty_i_reg_0[2]),
        .I1(\gc0.count_reg[2] [2]),
        .I2(ram_empty_i_reg_0[1]),
        .I3(\gc0.count_reg[2] [1]),
        .I4(\gc0.count_reg[2] [0]),
        .I5(ram_empty_i_reg_0[0]),
        .O(ram_empty_i_reg));
  LUT6 #(
    .INIT(64'h0000F88F00008888)) 
    ram_full_i_i_1
       (.I0(ram_full_i_i_2_n_0),
        .I1(ram_full_fb_i_reg_1),
        .I2(Q[3]),
        .I3(ram_full_fb_i_reg_0),
        .I4(\grstd1.grst_full.grst_f.rst_d3_reg ),
        .I5(ram_full_i_i_4_n_0),
        .O(ram_full_fb_i_reg));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    ram_full_i_i_2
       (.I0(p_23_out[2]),
        .I1(\gic0.gc0.count_reg[2] [2]),
        .I2(p_23_out[1]),
        .I3(\gic0.gc0.count_reg[2] [1]),
        .I4(\gic0.gc0.count_reg[2] [0]),
        .I5(p_23_out[0]),
        .O(ram_full_i_i_2_n_0));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    ram_full_i_i_4
       (.I0(p_23_out[2]),
        .I1(Q[2]),
        .I2(p_23_out[1]),
        .I3(Q[1]),
        .I4(Q[0]),
        .I5(p_23_out[0]),
        .O(ram_full_i_i_4_n_0));
endmodule

(* ORIG_REF_NAME = "clk_x_pntrs" *) 
module axi_clock_converter_dramslim_clk_x_pntrs_11
   (out,
    ram_empty_i_reg,
    Q,
    ram_full_fb_i_reg,
    ram_full_fb_i_reg_0,
    \gc0.count_reg[2] ,
    ram_full_fb_i_reg_1,
    \gic0.gc0.count_d1_reg[3] ,
    \grstd1.grst_full.grst_f.rst_d3_reg ,
    \gic0.gc0.count_reg[2] ,
    \gic0.gc0.count_d2_reg[3] ,
    s_aclk,
    AR,
    m_aclk,
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ,
    \gc0.count_d1_reg[3] ,
    D,
    \Q_reg_reg[1] );
  output [3:0]out;
  output ram_empty_i_reg;
  output [3:0]Q;
  output ram_full_fb_i_reg;
  output [0:0]ram_full_fb_i_reg_0;
  input [2:0]\gc0.count_reg[2] ;
  input ram_full_fb_i_reg_1;
  input [3:0]\gic0.gc0.count_d1_reg[3] ;
  input \grstd1.grst_full.grst_f.rst_d3_reg ;
  input [2:0]\gic0.gc0.count_reg[2] ;
  input [3:0]\gic0.gc0.count_d2_reg[3] ;
  input s_aclk;
  input [0:0]AR;
  input m_aclk;
  input [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;
  input [0:0]\gc0.count_d1_reg[3] ;
  input [2:0]D;
  input [0:0]\Q_reg_reg[1] ;

  wire [0:0]AR;
  wire [2:0]D;
  wire [3:0]Q;
  wire [0:0]\Q_reg_reg[1] ;
  wire __0_n_0;
  wire __1_n_0;
  wire __2_n_0;
  wire [2:0]bin2gray;
  wire [0:0]\gc0.count_d1_reg[3] ;
  wire [2:0]\gc0.count_reg[2] ;
  wire [3:0]\gic0.gc0.count_d1_reg[3] ;
  wire [3:0]\gic0.gc0.count_d2_reg[3] ;
  wire [2:0]\gic0.gc0.count_reg[2] ;
  wire \gnxpm_cdc.gsync_stage[3].rd_stg_inst_n_4 ;
  wire \gnxpm_cdc.gsync_stage[3].wr_stg_inst_n_4 ;
  wire \gnxpm_cdc.rd_pntr_gc_reg_n_0_[0] ;
  wire \gnxpm_cdc.rd_pntr_gc_reg_n_0_[1] ;
  wire \gnxpm_cdc.rd_pntr_gc_reg_n_0_[2] ;
  wire \gnxpm_cdc.rd_pntr_gc_reg_n_0_[3] ;
  wire \gnxpm_cdc.wr_pntr_gc_reg_n_0_[0] ;
  wire \gnxpm_cdc.wr_pntr_gc_reg_n_0_[1] ;
  wire \gnxpm_cdc.wr_pntr_gc_reg_n_0_[2] ;
  wire \gnxpm_cdc.wr_pntr_gc_reg_n_0_[3] ;
  wire \grstd1.grst_full.grst_f.rst_d3_reg ;
  wire m_aclk;
  wire [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;
  wire [3:0]out;
  wire [2:0]p_23_out;
  wire [3:0]p_3_out;
  wire [3:0]p_4_out;
  wire [3:0]p_5_out;
  wire [3:0]p_6_out;
  wire [3:0]p_8_out;
  wire ram_empty_i_reg;
  wire ram_full_fb_i_reg;
  wire [0:0]ram_full_fb_i_reg_0;
  wire ram_full_fb_i_reg_1;
  wire ram_full_i_i_2__2_n_0;
  wire ram_full_i_i_4__2_n_0;
  wire s_aclk;

  LUT3 #(
    .INIT(8'h96)) 
    __0
       (.I0(out[2]),
        .I1(out[1]),
        .I2(out[3]),
        .O(__0_n_0));
  (* SOFT_HLUTNM = "soft_lutpair18" *) 
  LUT4 #(
    .INIT(16'h6996)) 
    __1
       (.I0(p_8_out[1]),
        .I1(p_8_out[0]),
        .I2(p_8_out[3]),
        .I3(p_8_out[2]),
        .O(__1_n_0));
  (* SOFT_HLUTNM = "soft_lutpair18" *) 
  LUT3 #(
    .INIT(8'h96)) 
    __2
       (.I0(p_8_out[2]),
        .I1(p_8_out[1]),
        .I2(p_8_out[3]),
        .O(__2_n_0));
  axi_clock_converter_dramslim_synchronizer_ff__parameterized0_26 \gnxpm_cdc.gsync_stage[1].rd_stg_inst 
       (.D(p_3_out),
        .Q({\gnxpm_cdc.wr_pntr_gc_reg_n_0_[3] ,\gnxpm_cdc.wr_pntr_gc_reg_n_0_[2] ,\gnxpm_cdc.wr_pntr_gc_reg_n_0_[1] ,\gnxpm_cdc.wr_pntr_gc_reg_n_0_[0] }),
        .m_aclk(m_aclk),
        .\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] (\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ));
  axi_clock_converter_dramslim_synchronizer_ff__parameterized0_27 \gnxpm_cdc.gsync_stage[1].wr_stg_inst 
       (.AR(AR),
        .D(p_4_out),
        .Q({\gnxpm_cdc.rd_pntr_gc_reg_n_0_[3] ,\gnxpm_cdc.rd_pntr_gc_reg_n_0_[2] ,\gnxpm_cdc.rd_pntr_gc_reg_n_0_[1] ,\gnxpm_cdc.rd_pntr_gc_reg_n_0_[0] }),
        .s_aclk(s_aclk));
  axi_clock_converter_dramslim_synchronizer_ff__parameterized0_28 \gnxpm_cdc.gsync_stage[2].rd_stg_inst 
       (.D(p_5_out),
        .\Q_reg_reg[3]_0 (p_3_out),
        .m_aclk(m_aclk),
        .\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] (\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ));
  axi_clock_converter_dramslim_synchronizer_ff__parameterized0_29 \gnxpm_cdc.gsync_stage[2].wr_stg_inst 
       (.AR(AR),
        .D(p_6_out),
        .\Q_reg_reg[3]_0 (p_4_out),
        .s_aclk(s_aclk));
  axi_clock_converter_dramslim_synchronizer_ff__parameterized0_30 \gnxpm_cdc.gsync_stage[3].rd_stg_inst 
       (.D(\gnxpm_cdc.gsync_stage[3].rd_stg_inst_n_4 ),
        .\Q_reg_reg[3]_0 (p_5_out),
        .m_aclk(m_aclk),
        .\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] (\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .out(out));
  axi_clock_converter_dramslim_synchronizer_ff__parameterized0_31 \gnxpm_cdc.gsync_stage[3].wr_stg_inst 
       (.AR(AR),
        .D(\gnxpm_cdc.gsync_stage[3].wr_stg_inst_n_4 ),
        .\Q_reg_reg[3]_0 (p_6_out),
        .out(p_8_out),
        .s_aclk(s_aclk));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_bin_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(__1_n_0),
        .Q(p_23_out[0]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_bin_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(__2_n_0),
        .Q(p_23_out[1]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_bin_reg[2] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\gnxpm_cdc.gsync_stage[3].wr_stg_inst_n_4 ),
        .Q(p_23_out[2]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_bin_reg[3] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(p_8_out[3]),
        .Q(ram_full_fb_i_reg_0));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_gc_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(D[0]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg_n_0_[0] ));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_gc_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(D[1]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg_n_0_[1] ));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_gc_reg[2] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(D[2]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg_n_0_[2] ));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_gc_reg[3] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\gc0.count_d1_reg[3] ),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg_n_0_[3] ));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_bin_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[1] ),
        .Q(Q[0]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_bin_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(__0_n_0),
        .Q(Q[1]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_bin_reg[2] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\gnxpm_cdc.gsync_stage[3].rd_stg_inst_n_4 ),
        .Q(Q[2]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_bin_reg[3] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(out[3]),
        .Q(Q[3]));
  (* SOFT_HLUTNM = "soft_lutpair19" *) 
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.wr_pntr_gc[0]_i_1 
       (.I0(\gic0.gc0.count_d2_reg[3] [0]),
        .I1(\gic0.gc0.count_d2_reg[3] [1]),
        .O(bin2gray[0]));
  (* SOFT_HLUTNM = "soft_lutpair19" *) 
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.wr_pntr_gc[1]_i_1 
       (.I0(\gic0.gc0.count_d2_reg[3] [1]),
        .I1(\gic0.gc0.count_d2_reg[3] [2]),
        .O(bin2gray[1]));
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.wr_pntr_gc[2]_i_1 
       (.I0(\gic0.gc0.count_d2_reg[3] [2]),
        .I1(\gic0.gc0.count_d2_reg[3] [3]),
        .O(bin2gray[2]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_gc_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(bin2gray[0]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg_n_0_[0] ));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_gc_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(bin2gray[1]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg_n_0_[1] ));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_gc_reg[2] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(bin2gray[2]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg_n_0_[2] ));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_gc_reg[3] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\gic0.gc0.count_d2_reg[3] [3]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg_n_0_[3] ));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    ram_empty_i_i_4__0
       (.I0(Q[2]),
        .I1(\gc0.count_reg[2] [2]),
        .I2(Q[1]),
        .I3(\gc0.count_reg[2] [1]),
        .I4(\gc0.count_reg[2] [0]),
        .I5(Q[0]),
        .O(ram_empty_i_reg));
  LUT6 #(
    .INIT(64'h0000F88F00008888)) 
    ram_full_i_i_1__2
       (.I0(ram_full_i_i_2__2_n_0),
        .I1(ram_full_fb_i_reg_1),
        .I2(\gic0.gc0.count_d1_reg[3] [3]),
        .I3(ram_full_fb_i_reg_0),
        .I4(\grstd1.grst_full.grst_f.rst_d3_reg ),
        .I5(ram_full_i_i_4__2_n_0),
        .O(ram_full_fb_i_reg));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    ram_full_i_i_2__2
       (.I0(p_23_out[2]),
        .I1(\gic0.gc0.count_reg[2] [2]),
        .I2(p_23_out[1]),
        .I3(\gic0.gc0.count_reg[2] [1]),
        .I4(\gic0.gc0.count_reg[2] [0]),
        .I5(p_23_out[0]),
        .O(ram_full_i_i_2__2_n_0));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    ram_full_i_i_4__2
       (.I0(p_23_out[2]),
        .I1(\gic0.gc0.count_d1_reg[3] [2]),
        .I2(p_23_out[1]),
        .I3(\gic0.gc0.count_d1_reg[3] [1]),
        .I4(\gic0.gc0.count_d1_reg[3] [0]),
        .I5(p_23_out[0]),
        .O(ram_full_i_i_4__2_n_0));
endmodule

(* ORIG_REF_NAME = "clk_x_pntrs" *) 
module axi_clock_converter_dramslim_clk_x_pntrs_32
   (out,
    ram_empty_i_reg,
    Q,
    ram_full_fb_i_reg,
    ram_full_fb_i_reg_0,
    D,
    \gc0.count_reg[2] ,
    ram_full_fb_i_reg_1,
    \gic0.gc0.count_d1_reg[3] ,
    \grstd1.grst_full.grst_f.rst_d3_reg ,
    \gic0.gc0.count_reg[2] ,
    \gic0.gc0.count_d2_reg[3] ,
    s_aclk,
    AR,
    m_aclk,
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ,
    \gc0.count_d1_reg[3] ,
    \gc0.count_d1_reg[2] );
  output [3:0]out;
  output ram_empty_i_reg;
  output [3:0]Q;
  output ram_full_fb_i_reg;
  output [0:0]ram_full_fb_i_reg_0;
  input [0:0]D;
  input [2:0]\gc0.count_reg[2] ;
  input ram_full_fb_i_reg_1;
  input [3:0]\gic0.gc0.count_d1_reg[3] ;
  input \grstd1.grst_full.grst_f.rst_d3_reg ;
  input [2:0]\gic0.gc0.count_reg[2] ;
  input [3:0]\gic0.gc0.count_d2_reg[3] ;
  input s_aclk;
  input [0:0]AR;
  input m_aclk;
  input [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;
  input [0:0]\gc0.count_d1_reg[3] ;
  input [2:0]\gc0.count_d1_reg[2] ;

  wire [0:0]AR;
  wire [0:0]D;
  wire [3:0]Q;
  wire __1_n_0;
  wire __2_n_0;
  wire [2:0]bin2gray;
  wire [2:0]\gc0.count_d1_reg[2] ;
  wire [0:0]\gc0.count_d1_reg[3] ;
  wire [2:0]\gc0.count_reg[2] ;
  wire [3:0]\gic0.gc0.count_d1_reg[3] ;
  wire [3:0]\gic0.gc0.count_d2_reg[3] ;
  wire [2:0]\gic0.gc0.count_reg[2] ;
  wire \gnxpm_cdc.gsync_stage[3].wr_stg_inst_n_4 ;
  wire [1:1]gray2bin;
  wire \grstd1.grst_full.grst_f.rst_d3_reg ;
  wire m_aclk;
  wire [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;
  wire [3:0]out;
  wire p_0_out;
  wire [2:0]p_23_out_1;
  wire [3:0]p_3_out;
  wire [3:0]p_4_out;
  wire [3:0]p_5_out;
  wire [3:0]p_6_out;
  wire [3:0]p_8_out;
  wire ram_empty_i_reg;
  wire ram_full_fb_i_reg;
  wire [0:0]ram_full_fb_i_reg_0;
  wire ram_full_fb_i_reg_1;
  wire ram_full_i_i_2__1_n_0;
  wire ram_full_i_i_4__1_n_0;
  wire [3:0]rd_pntr_gc;
  wire s_aclk;
  wire [3:0]wr_pntr_gc;

  LUT3 #(
    .INIT(8'h96)) 
    __0
       (.I0(out[2]),
        .I1(out[1]),
        .I2(out[3]),
        .O(gray2bin));
  (* SOFT_HLUTNM = "soft_lutpair12" *) 
  LUT4 #(
    .INIT(16'h6996)) 
    __1
       (.I0(p_8_out[1]),
        .I1(p_8_out[0]),
        .I2(p_8_out[3]),
        .I3(p_8_out[2]),
        .O(__1_n_0));
  (* SOFT_HLUTNM = "soft_lutpair12" *) 
  LUT3 #(
    .INIT(8'h96)) 
    __2
       (.I0(p_8_out[2]),
        .I1(p_8_out[1]),
        .I2(p_8_out[3]),
        .O(__2_n_0));
  axi_clock_converter_dramslim_synchronizer_ff__parameterized0_47 \gnxpm_cdc.gsync_stage[1].rd_stg_inst 
       (.D(p_3_out),
        .Q(wr_pntr_gc),
        .m_aclk(m_aclk),
        .\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] (\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ));
  axi_clock_converter_dramslim_synchronizer_ff__parameterized0_48 \gnxpm_cdc.gsync_stage[1].wr_stg_inst 
       (.AR(AR),
        .D(p_4_out),
        .Q(rd_pntr_gc),
        .s_aclk(s_aclk));
  axi_clock_converter_dramslim_synchronizer_ff__parameterized0_49 \gnxpm_cdc.gsync_stage[2].rd_stg_inst 
       (.D(p_5_out),
        .\Q_reg_reg[3]_0 (p_3_out),
        .m_aclk(m_aclk),
        .\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] (\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ));
  axi_clock_converter_dramslim_synchronizer_ff__parameterized0_50 \gnxpm_cdc.gsync_stage[2].wr_stg_inst 
       (.AR(AR),
        .D(p_6_out),
        .\Q_reg_reg[3]_0 (p_4_out),
        .s_aclk(s_aclk));
  axi_clock_converter_dramslim_synchronizer_ff__parameterized0_51 \gnxpm_cdc.gsync_stage[3].rd_stg_inst 
       (.D(p_0_out),
        .\Q_reg_reg[3]_0 (p_5_out),
        .m_aclk(m_aclk),
        .\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] (\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .out(out));
  axi_clock_converter_dramslim_synchronizer_ff__parameterized0_52 \gnxpm_cdc.gsync_stage[3].wr_stg_inst 
       (.AR(AR),
        .D(\gnxpm_cdc.gsync_stage[3].wr_stg_inst_n_4 ),
        .\Q_reg_reg[3]_0 (p_6_out),
        .out(p_8_out),
        .s_aclk(s_aclk));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_bin_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(__1_n_0),
        .Q(p_23_out_1[0]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_bin_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(__2_n_0),
        .Q(p_23_out_1[1]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_bin_reg[2] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\gnxpm_cdc.gsync_stage[3].wr_stg_inst_n_4 ),
        .Q(p_23_out_1[2]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_bin_reg[3] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(p_8_out[3]),
        .Q(ram_full_fb_i_reg_0));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_gc_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\gc0.count_d1_reg[2] [0]),
        .Q(rd_pntr_gc[0]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_gc_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\gc0.count_d1_reg[2] [1]),
        .Q(rd_pntr_gc[1]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_gc_reg[2] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\gc0.count_d1_reg[2] [2]),
        .Q(rd_pntr_gc[2]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_gc_reg[3] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\gc0.count_d1_reg[3] ),
        .Q(rd_pntr_gc[3]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_bin_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(D),
        .Q(Q[0]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_bin_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(gray2bin),
        .Q(Q[1]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_bin_reg[2] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(p_0_out),
        .Q(Q[2]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_bin_reg[3] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(out[3]),
        .Q(Q[3]));
  (* SOFT_HLUTNM = "soft_lutpair13" *) 
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.wr_pntr_gc[0]_i_1 
       (.I0(\gic0.gc0.count_d2_reg[3] [0]),
        .I1(\gic0.gc0.count_d2_reg[3] [1]),
        .O(bin2gray[0]));
  (* SOFT_HLUTNM = "soft_lutpair13" *) 
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.wr_pntr_gc[1]_i_1 
       (.I0(\gic0.gc0.count_d2_reg[3] [1]),
        .I1(\gic0.gc0.count_d2_reg[3] [2]),
        .O(bin2gray[1]));
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.wr_pntr_gc[2]_i_1 
       (.I0(\gic0.gc0.count_d2_reg[3] [2]),
        .I1(\gic0.gc0.count_d2_reg[3] [3]),
        .O(bin2gray[2]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_gc_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(bin2gray[0]),
        .Q(wr_pntr_gc[0]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_gc_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(bin2gray[1]),
        .Q(wr_pntr_gc[1]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_gc_reg[2] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(bin2gray[2]),
        .Q(wr_pntr_gc[2]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_gc_reg[3] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\gic0.gc0.count_d2_reg[3] [3]),
        .Q(wr_pntr_gc[3]));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    ram_empty_i_i_4
       (.I0(Q[2]),
        .I1(\gc0.count_reg[2] [2]),
        .I2(Q[1]),
        .I3(\gc0.count_reg[2] [1]),
        .I4(\gc0.count_reg[2] [0]),
        .I5(Q[0]),
        .O(ram_empty_i_reg));
  LUT6 #(
    .INIT(64'h0000F88F00008888)) 
    ram_full_i_i_1__1
       (.I0(ram_full_i_i_2__1_n_0),
        .I1(ram_full_fb_i_reg_1),
        .I2(\gic0.gc0.count_d1_reg[3] [3]),
        .I3(ram_full_fb_i_reg_0),
        .I4(\grstd1.grst_full.grst_f.rst_d3_reg ),
        .I5(ram_full_i_i_4__1_n_0),
        .O(ram_full_fb_i_reg));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    ram_full_i_i_2__1
       (.I0(p_23_out_1[2]),
        .I1(\gic0.gc0.count_reg[2] [2]),
        .I2(p_23_out_1[1]),
        .I3(\gic0.gc0.count_reg[2] [1]),
        .I4(\gic0.gc0.count_reg[2] [0]),
        .I5(p_23_out_1[0]),
        .O(ram_full_i_i_2__1_n_0));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    ram_full_i_i_4__1
       (.I0(p_23_out_1[2]),
        .I1(\gic0.gc0.count_d1_reg[3] [2]),
        .I2(p_23_out_1[1]),
        .I3(\gic0.gc0.count_d1_reg[3] [1]),
        .I4(\gic0.gc0.count_d1_reg[3] [0]),
        .I5(p_23_out_1[0]),
        .O(ram_full_i_i_4__1_n_0));
endmodule

(* ORIG_REF_NAME = "clk_x_pntrs" *) 
module axi_clock_converter_dramslim_clk_x_pntrs_53
   (out,
    ram_full_fb_i_reg,
    ram_full_fb_i_reg_0,
    ram_empty_i_reg,
    ram_empty_i_reg_0,
    ram_full_fb_i_reg_1,
    Q,
    \grstd1.grst_full.grst_f.rst_d3_reg ,
    \gic0.gc0.count_reg[2] ,
    \gc0.count_reg[2] ,
    \gic0.gc0.count_d2_reg[3] ,
    m_aclk,
    AR,
    s_aclk,
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ,
    \gc0.count_d1_reg[3] ,
    D,
    \Q_reg_reg[1] );
  output [3:0]out;
  output ram_full_fb_i_reg;
  output [0:0]ram_full_fb_i_reg_0;
  output ram_empty_i_reg;
  output [3:0]ram_empty_i_reg_0;
  input ram_full_fb_i_reg_1;
  input [3:0]Q;
  input \grstd1.grst_full.grst_f.rst_d3_reg ;
  input [2:0]\gic0.gc0.count_reg[2] ;
  input [2:0]\gc0.count_reg[2] ;
  input [3:0]\gic0.gc0.count_d2_reg[3] ;
  input m_aclk;
  input [0:0]AR;
  input s_aclk;
  input [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;
  input [0:0]\gc0.count_d1_reg[3] ;
  input [2:0]D;
  input [0:0]\Q_reg_reg[1] ;

  wire [0:0]AR;
  wire [2:0]D;
  wire [3:0]Q;
  wire [0:0]\Q_reg_reg[1] ;
  wire __0_n_0;
  wire __1_n_0;
  wire __2_n_0;
  wire [2:0]bin2gray;
  wire [0:0]\gc0.count_d1_reg[3] ;
  wire [2:0]\gc0.count_reg[2] ;
  wire [3:0]\gic0.gc0.count_d2_reg[3] ;
  wire [2:0]\gic0.gc0.count_reg[2] ;
  wire \gnxpm_cdc.gsync_stage[3].rd_stg_inst_n_4 ;
  wire \gnxpm_cdc.gsync_stage[3].wr_stg_inst_n_4 ;
  wire \gnxpm_cdc.rd_pntr_gc_reg_n_0_[0] ;
  wire \gnxpm_cdc.rd_pntr_gc_reg_n_0_[1] ;
  wire \gnxpm_cdc.rd_pntr_gc_reg_n_0_[2] ;
  wire \gnxpm_cdc.rd_pntr_gc_reg_n_0_[3] ;
  wire \gnxpm_cdc.wr_pntr_gc_reg_n_0_[0] ;
  wire \gnxpm_cdc.wr_pntr_gc_reg_n_0_[1] ;
  wire \gnxpm_cdc.wr_pntr_gc_reg_n_0_[2] ;
  wire \gnxpm_cdc.wr_pntr_gc_reg_n_0_[3] ;
  wire \grstd1.grst_full.grst_f.rst_d3_reg ;
  wire m_aclk;
  wire [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;
  wire [3:0]out;
  wire [2:0]p_23_out;
  wire [3:0]p_3_out;
  wire [3:0]p_4_out;
  wire [3:0]p_5_out;
  wire [3:0]p_6_out;
  wire [3:0]p_8_out;
  wire ram_empty_i_reg;
  wire [3:0]ram_empty_i_reg_0;
  wire ram_full_fb_i_reg;
  wire [0:0]ram_full_fb_i_reg_0;
  wire ram_full_fb_i_reg_1;
  wire ram_full_i_i_2__0_n_0;
  wire ram_full_i_i_4__0_n_0;
  wire s_aclk;

  LUT3 #(
    .INIT(8'h96)) 
    __0
       (.I0(out[2]),
        .I1(out[1]),
        .I2(out[3]),
        .O(__0_n_0));
  (* SOFT_HLUTNM = "soft_lutpair6" *) 
  LUT4 #(
    .INIT(16'h6996)) 
    __1
       (.I0(p_8_out[1]),
        .I1(p_8_out[0]),
        .I2(p_8_out[3]),
        .I3(p_8_out[2]),
        .O(__1_n_0));
  (* SOFT_HLUTNM = "soft_lutpair6" *) 
  LUT3 #(
    .INIT(8'h96)) 
    __2
       (.I0(p_8_out[2]),
        .I1(p_8_out[1]),
        .I2(p_8_out[3]),
        .O(__2_n_0));
  axi_clock_converter_dramslim_synchronizer_ff__parameterized0_68 \gnxpm_cdc.gsync_stage[1].rd_stg_inst 
       (.D(p_3_out),
        .Q({\gnxpm_cdc.wr_pntr_gc_reg_n_0_[3] ,\gnxpm_cdc.wr_pntr_gc_reg_n_0_[2] ,\gnxpm_cdc.wr_pntr_gc_reg_n_0_[1] ,\gnxpm_cdc.wr_pntr_gc_reg_n_0_[0] }),
        .\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] (\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .s_aclk(s_aclk));
  axi_clock_converter_dramslim_synchronizer_ff__parameterized0_69 \gnxpm_cdc.gsync_stage[1].wr_stg_inst 
       (.AR(AR),
        .D(p_4_out),
        .Q({\gnxpm_cdc.rd_pntr_gc_reg_n_0_[3] ,\gnxpm_cdc.rd_pntr_gc_reg_n_0_[2] ,\gnxpm_cdc.rd_pntr_gc_reg_n_0_[1] ,\gnxpm_cdc.rd_pntr_gc_reg_n_0_[0] }),
        .m_aclk(m_aclk));
  axi_clock_converter_dramslim_synchronizer_ff__parameterized0_70 \gnxpm_cdc.gsync_stage[2].rd_stg_inst 
       (.D(p_5_out),
        .\Q_reg_reg[3]_0 (p_3_out),
        .\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] (\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .s_aclk(s_aclk));
  axi_clock_converter_dramslim_synchronizer_ff__parameterized0_71 \gnxpm_cdc.gsync_stage[2].wr_stg_inst 
       (.AR(AR),
        .D(p_6_out),
        .\Q_reg_reg[3]_0 (p_4_out),
        .m_aclk(m_aclk));
  axi_clock_converter_dramslim_synchronizer_ff__parameterized0_72 \gnxpm_cdc.gsync_stage[3].rd_stg_inst 
       (.D(\gnxpm_cdc.gsync_stage[3].rd_stg_inst_n_4 ),
        .\Q_reg_reg[3]_0 (p_5_out),
        .\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] (\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .out(out),
        .s_aclk(s_aclk));
  axi_clock_converter_dramslim_synchronizer_ff__parameterized0_73 \gnxpm_cdc.gsync_stage[3].wr_stg_inst 
       (.AR(AR),
        .D(\gnxpm_cdc.gsync_stage[3].wr_stg_inst_n_4 ),
        .\Q_reg_reg[3]_0 (p_6_out),
        .m_aclk(m_aclk),
        .out(p_8_out));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_bin_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(__1_n_0),
        .Q(p_23_out[0]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_bin_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(__2_n_0),
        .Q(p_23_out[1]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_bin_reg[2] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\gnxpm_cdc.gsync_stage[3].wr_stg_inst_n_4 ),
        .Q(p_23_out[2]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_bin_reg[3] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(p_8_out[3]),
        .Q(ram_full_fb_i_reg_0));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_gc_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(D[0]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg_n_0_[0] ));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_gc_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(D[1]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg_n_0_[1] ));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_gc_reg[2] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(D[2]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg_n_0_[2] ));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_gc_reg[3] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\gc0.count_d1_reg[3] ),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg_n_0_[3] ));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_bin_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[1] ),
        .Q(ram_empty_i_reg_0[0]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_bin_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(__0_n_0),
        .Q(ram_empty_i_reg_0[1]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_bin_reg[2] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\gnxpm_cdc.gsync_stage[3].rd_stg_inst_n_4 ),
        .Q(ram_empty_i_reg_0[2]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_bin_reg[3] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(out[3]),
        .Q(ram_empty_i_reg_0[3]));
  (* SOFT_HLUTNM = "soft_lutpair7" *) 
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.wr_pntr_gc[0]_i_1 
       (.I0(\gic0.gc0.count_d2_reg[3] [0]),
        .I1(\gic0.gc0.count_d2_reg[3] [1]),
        .O(bin2gray[0]));
  (* SOFT_HLUTNM = "soft_lutpair7" *) 
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.wr_pntr_gc[1]_i_1 
       (.I0(\gic0.gc0.count_d2_reg[3] [1]),
        .I1(\gic0.gc0.count_d2_reg[3] [2]),
        .O(bin2gray[1]));
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.wr_pntr_gc[2]_i_1 
       (.I0(\gic0.gc0.count_d2_reg[3] [2]),
        .I1(\gic0.gc0.count_d2_reg[3] [3]),
        .O(bin2gray[2]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_gc_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(bin2gray[0]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg_n_0_[0] ));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_gc_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(bin2gray[1]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg_n_0_[1] ));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_gc_reg[2] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(bin2gray[2]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg_n_0_[2] ));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_gc_reg[3] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\gic0.gc0.count_d2_reg[3] [3]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg_n_0_[3] ));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    ram_empty_i_i_4__3
       (.I0(ram_empty_i_reg_0[2]),
        .I1(\gc0.count_reg[2] [2]),
        .I2(ram_empty_i_reg_0[1]),
        .I3(\gc0.count_reg[2] [1]),
        .I4(\gc0.count_reg[2] [0]),
        .I5(ram_empty_i_reg_0[0]),
        .O(ram_empty_i_reg));
  LUT6 #(
    .INIT(64'h0000F88F00008888)) 
    ram_full_i_i_1__0
       (.I0(ram_full_i_i_2__0_n_0),
        .I1(ram_full_fb_i_reg_1),
        .I2(Q[3]),
        .I3(ram_full_fb_i_reg_0),
        .I4(\grstd1.grst_full.grst_f.rst_d3_reg ),
        .I5(ram_full_i_i_4__0_n_0),
        .O(ram_full_fb_i_reg));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    ram_full_i_i_2__0
       (.I0(p_23_out[2]),
        .I1(\gic0.gc0.count_reg[2] [2]),
        .I2(p_23_out[1]),
        .I3(\gic0.gc0.count_reg[2] [1]),
        .I4(\gic0.gc0.count_reg[2] [0]),
        .I5(p_23_out[0]),
        .O(ram_full_i_i_2__0_n_0));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    ram_full_i_i_4__0
       (.I0(p_23_out[2]),
        .I1(Q[2]),
        .I2(p_23_out[1]),
        .I3(Q[1]),
        .I4(Q[0]),
        .I5(p_23_out[0]),
        .O(ram_full_i_i_4__0_n_0));
endmodule

(* ORIG_REF_NAME = "clk_x_pntrs" *) 
module axi_clock_converter_dramslim_clk_x_pntrs_75
   (out,
    ram_empty_i_reg,
    Q,
    ram_full_fb_i_reg,
    ram_full_fb_i_reg_0,
    \gc0.count_reg[2] ,
    ram_full_fb_i_reg_1,
    \gic0.gc0.count_d1_reg[3] ,
    \grstd1.grst_full.grst_f.rst_d3_reg ,
    \gic0.gc0.count_reg[2] ,
    \gic0.gc0.count_d2_reg[3] ,
    s_aclk,
    AR,
    m_aclk,
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ,
    \gc0.count_d1_reg[3] ,
    D,
    \Q_reg_reg[1] );
  output [3:0]out;
  output ram_empty_i_reg;
  output [3:0]Q;
  output ram_full_fb_i_reg;
  output [0:0]ram_full_fb_i_reg_0;
  input [2:0]\gc0.count_reg[2] ;
  input ram_full_fb_i_reg_1;
  input [3:0]\gic0.gc0.count_d1_reg[3] ;
  input \grstd1.grst_full.grst_f.rst_d3_reg ;
  input [2:0]\gic0.gc0.count_reg[2] ;
  input [3:0]\gic0.gc0.count_d2_reg[3] ;
  input s_aclk;
  input [0:0]AR;
  input m_aclk;
  input [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;
  input [0:0]\gc0.count_d1_reg[3] ;
  input [2:0]D;
  input [0:0]\Q_reg_reg[1] ;

  wire [0:0]AR;
  wire [2:0]D;
  wire [3:0]Q;
  wire [0:0]\Q_reg_reg[1] ;
  wire __0_n_0;
  wire __1_n_0;
  wire __2_n_0;
  wire [2:0]bin2gray;
  wire [0:0]\gc0.count_d1_reg[3] ;
  wire [2:0]\gc0.count_reg[2] ;
  wire [3:0]\gic0.gc0.count_d1_reg[3] ;
  wire [3:0]\gic0.gc0.count_d2_reg[3] ;
  wire [2:0]\gic0.gc0.count_reg[2] ;
  wire \gnxpm_cdc.gsync_stage[3].rd_stg_inst_n_4 ;
  wire \gnxpm_cdc.gsync_stage[3].wr_stg_inst_n_4 ;
  wire \gnxpm_cdc.rd_pntr_gc_reg_n_0_[0] ;
  wire \gnxpm_cdc.rd_pntr_gc_reg_n_0_[1] ;
  wire \gnxpm_cdc.rd_pntr_gc_reg_n_0_[2] ;
  wire \gnxpm_cdc.rd_pntr_gc_reg_n_0_[3] ;
  wire \gnxpm_cdc.wr_pntr_gc_reg_n_0_[0] ;
  wire \gnxpm_cdc.wr_pntr_gc_reg_n_0_[1] ;
  wire \gnxpm_cdc.wr_pntr_gc_reg_n_0_[2] ;
  wire \gnxpm_cdc.wr_pntr_gc_reg_n_0_[3] ;
  wire \grstd1.grst_full.grst_f.rst_d3_reg ;
  wire m_aclk;
  wire [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;
  wire [3:0]out;
  wire [2:0]p_23_out;
  wire [3:0]p_3_out;
  wire [3:0]p_4_out;
  wire [3:0]p_5_out;
  wire [3:0]p_6_out;
  wire [3:0]p_8_out;
  wire ram_empty_i_reg;
  wire ram_full_fb_i_reg;
  wire [0:0]ram_full_fb_i_reg_0;
  wire ram_full_fb_i_reg_1;
  wire ram_full_i_i_2__3_n_0;
  wire ram_full_i_i_4__3_n_0;
  wire s_aclk;

  LUT3 #(
    .INIT(8'h96)) 
    __0
       (.I0(out[2]),
        .I1(out[1]),
        .I2(out[3]),
        .O(__0_n_0));
  (* SOFT_HLUTNM = "soft_lutpair0" *) 
  LUT4 #(
    .INIT(16'h6996)) 
    __1
       (.I0(p_8_out[1]),
        .I1(p_8_out[0]),
        .I2(p_8_out[3]),
        .I3(p_8_out[2]),
        .O(__1_n_0));
  (* SOFT_HLUTNM = "soft_lutpair0" *) 
  LUT3 #(
    .INIT(8'h96)) 
    __2
       (.I0(p_8_out[2]),
        .I1(p_8_out[1]),
        .I2(p_8_out[3]),
        .O(__2_n_0));
  axi_clock_converter_dramslim_synchronizer_ff__parameterized0_92 \gnxpm_cdc.gsync_stage[1].rd_stg_inst 
       (.D(p_3_out),
        .Q({\gnxpm_cdc.wr_pntr_gc_reg_n_0_[3] ,\gnxpm_cdc.wr_pntr_gc_reg_n_0_[2] ,\gnxpm_cdc.wr_pntr_gc_reg_n_0_[1] ,\gnxpm_cdc.wr_pntr_gc_reg_n_0_[0] }),
        .m_aclk(m_aclk),
        .\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] (\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ));
  axi_clock_converter_dramslim_synchronizer_ff__parameterized0_93 \gnxpm_cdc.gsync_stage[1].wr_stg_inst 
       (.AR(AR),
        .D(p_4_out),
        .Q({\gnxpm_cdc.rd_pntr_gc_reg_n_0_[3] ,\gnxpm_cdc.rd_pntr_gc_reg_n_0_[2] ,\gnxpm_cdc.rd_pntr_gc_reg_n_0_[1] ,\gnxpm_cdc.rd_pntr_gc_reg_n_0_[0] }),
        .s_aclk(s_aclk));
  axi_clock_converter_dramslim_synchronizer_ff__parameterized0_94 \gnxpm_cdc.gsync_stage[2].rd_stg_inst 
       (.D(p_5_out),
        .\Q_reg_reg[3]_0 (p_3_out),
        .m_aclk(m_aclk),
        .\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] (\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ));
  axi_clock_converter_dramslim_synchronizer_ff__parameterized0_95 \gnxpm_cdc.gsync_stage[2].wr_stg_inst 
       (.AR(AR),
        .D(p_6_out),
        .\Q_reg_reg[3]_0 (p_4_out),
        .s_aclk(s_aclk));
  axi_clock_converter_dramslim_synchronizer_ff__parameterized0_96 \gnxpm_cdc.gsync_stage[3].rd_stg_inst 
       (.D(\gnxpm_cdc.gsync_stage[3].rd_stg_inst_n_4 ),
        .\Q_reg_reg[3]_0 (p_5_out),
        .m_aclk(m_aclk),
        .\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] (\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .out(out));
  axi_clock_converter_dramslim_synchronizer_ff__parameterized0_97 \gnxpm_cdc.gsync_stage[3].wr_stg_inst 
       (.AR(AR),
        .D(\gnxpm_cdc.gsync_stage[3].wr_stg_inst_n_4 ),
        .\Q_reg_reg[3]_0 (p_6_out),
        .out(p_8_out),
        .s_aclk(s_aclk));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_bin_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(__1_n_0),
        .Q(p_23_out[0]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_bin_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(__2_n_0),
        .Q(p_23_out[1]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_bin_reg[2] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\gnxpm_cdc.gsync_stage[3].wr_stg_inst_n_4 ),
        .Q(p_23_out[2]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_bin_reg[3] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(p_8_out[3]),
        .Q(ram_full_fb_i_reg_0));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_gc_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(D[0]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg_n_0_[0] ));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_gc_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(D[1]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg_n_0_[1] ));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_gc_reg[2] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(D[2]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg_n_0_[2] ));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.rd_pntr_gc_reg[3] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\gc0.count_d1_reg[3] ),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg_n_0_[3] ));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_bin_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[1] ),
        .Q(Q[0]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_bin_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(__0_n_0),
        .Q(Q[1]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_bin_reg[2] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\gnxpm_cdc.gsync_stage[3].rd_stg_inst_n_4 ),
        .Q(Q[2]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_bin_reg[3] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(out[3]),
        .Q(Q[3]));
  (* SOFT_HLUTNM = "soft_lutpair1" *) 
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.wr_pntr_gc[0]_i_1 
       (.I0(\gic0.gc0.count_d2_reg[3] [0]),
        .I1(\gic0.gc0.count_d2_reg[3] [1]),
        .O(bin2gray[0]));
  (* SOFT_HLUTNM = "soft_lutpair1" *) 
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.wr_pntr_gc[1]_i_1 
       (.I0(\gic0.gc0.count_d2_reg[3] [1]),
        .I1(\gic0.gc0.count_d2_reg[3] [2]),
        .O(bin2gray[1]));
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.wr_pntr_gc[2]_i_1 
       (.I0(\gic0.gc0.count_d2_reg[3] [2]),
        .I1(\gic0.gc0.count_d2_reg[3] [3]),
        .O(bin2gray[2]));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_gc_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(bin2gray[0]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg_n_0_[0] ));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_gc_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(bin2gray[1]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg_n_0_[1] ));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_gc_reg[2] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(bin2gray[2]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg_n_0_[2] ));
  FDCE #(
    .INIT(1'b0)) 
    \gnxpm_cdc.wr_pntr_gc_reg[3] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\gic0.gc0.count_d2_reg[3] [3]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg_n_0_[3] ));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    ram_empty_i_i_4__1
       (.I0(Q[2]),
        .I1(\gc0.count_reg[2] [2]),
        .I2(Q[1]),
        .I3(\gc0.count_reg[2] [1]),
        .I4(\gc0.count_reg[2] [0]),
        .I5(Q[0]),
        .O(ram_empty_i_reg));
  LUT6 #(
    .INIT(64'h0000F88F00008888)) 
    ram_full_i_i_1__3
       (.I0(ram_full_i_i_2__3_n_0),
        .I1(ram_full_fb_i_reg_1),
        .I2(\gic0.gc0.count_d1_reg[3] [3]),
        .I3(ram_full_fb_i_reg_0),
        .I4(\grstd1.grst_full.grst_f.rst_d3_reg ),
        .I5(ram_full_i_i_4__3_n_0),
        .O(ram_full_fb_i_reg));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    ram_full_i_i_2__3
       (.I0(p_23_out[2]),
        .I1(\gic0.gc0.count_reg[2] [2]),
        .I2(p_23_out[1]),
        .I3(\gic0.gc0.count_reg[2] [1]),
        .I4(\gic0.gc0.count_reg[2] [0]),
        .I5(p_23_out[0]),
        .O(ram_full_i_i_2__3_n_0));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    ram_full_i_i_4__3
       (.I0(p_23_out[2]),
        .I1(\gic0.gc0.count_d1_reg[3] [2]),
        .I2(p_23_out[1]),
        .I3(\gic0.gc0.count_d1_reg[3] [1]),
        .I4(\gic0.gc0.count_d1_reg[3] [0]),
        .I5(p_23_out[0]),
        .O(ram_full_i_i_4__3_n_0));
endmodule

(* ORIG_REF_NAME = "dmem" *) 
module axi_clock_converter_dramslim_dmem
   (dout_i,
    s_aclk,
    ram_full_fb_i_reg,
    DI,
    \gc0.count_d1_reg[3] ,
    \gic0.gc0.count_d2_reg[3] ,
    \gpregsm1.curr_fwft_state_reg[1] ,
    m_aclk);
  output [108:0]dout_i;
  input s_aclk;
  input [0:0]ram_full_fb_i_reg;
  input [108:0]DI;
  input [3:0]\gc0.count_d1_reg[3] ;
  input [3:0]\gic0.gc0.count_d2_reg[3] ;
  input [0:0]\gpregsm1.curr_fwft_state_reg[1] ;
  input m_aclk;

  wire [108:0]DI;
  wire RAM_reg_0_15_0_5_n_0;
  wire RAM_reg_0_15_0_5_n_1;
  wire RAM_reg_0_15_0_5_n_10;
  wire RAM_reg_0_15_0_5_n_11;
  wire RAM_reg_0_15_0_5_n_12;
  wire RAM_reg_0_15_0_5_n_13;
  wire RAM_reg_0_15_0_5_n_2;
  wire RAM_reg_0_15_0_5_n_3;
  wire RAM_reg_0_15_0_5_n_4;
  wire RAM_reg_0_15_0_5_n_5;
  wire RAM_reg_0_15_0_5_n_6;
  wire RAM_reg_0_15_0_5_n_7;
  wire RAM_reg_0_15_0_5_n_8;
  wire RAM_reg_0_15_0_5_n_9;
  wire RAM_reg_0_15_12_17_n_0;
  wire RAM_reg_0_15_12_17_n_1;
  wire RAM_reg_0_15_12_17_n_10;
  wire RAM_reg_0_15_12_17_n_11;
  wire RAM_reg_0_15_12_17_n_12;
  wire RAM_reg_0_15_12_17_n_13;
  wire RAM_reg_0_15_12_17_n_2;
  wire RAM_reg_0_15_12_17_n_3;
  wire RAM_reg_0_15_12_17_n_4;
  wire RAM_reg_0_15_12_17_n_5;
  wire RAM_reg_0_15_12_17_n_6;
  wire RAM_reg_0_15_12_17_n_7;
  wire RAM_reg_0_15_12_17_n_8;
  wire RAM_reg_0_15_12_17_n_9;
  wire RAM_reg_0_15_18_23_n_0;
  wire RAM_reg_0_15_18_23_n_1;
  wire RAM_reg_0_15_18_23_n_10;
  wire RAM_reg_0_15_18_23_n_11;
  wire RAM_reg_0_15_18_23_n_12;
  wire RAM_reg_0_15_18_23_n_13;
  wire RAM_reg_0_15_18_23_n_2;
  wire RAM_reg_0_15_18_23_n_3;
  wire RAM_reg_0_15_18_23_n_4;
  wire RAM_reg_0_15_18_23_n_5;
  wire RAM_reg_0_15_18_23_n_6;
  wire RAM_reg_0_15_18_23_n_7;
  wire RAM_reg_0_15_18_23_n_8;
  wire RAM_reg_0_15_18_23_n_9;
  wire RAM_reg_0_15_24_29_n_0;
  wire RAM_reg_0_15_24_29_n_1;
  wire RAM_reg_0_15_24_29_n_10;
  wire RAM_reg_0_15_24_29_n_11;
  wire RAM_reg_0_15_24_29_n_12;
  wire RAM_reg_0_15_24_29_n_13;
  wire RAM_reg_0_15_24_29_n_2;
  wire RAM_reg_0_15_24_29_n_3;
  wire RAM_reg_0_15_24_29_n_4;
  wire RAM_reg_0_15_24_29_n_5;
  wire RAM_reg_0_15_24_29_n_6;
  wire RAM_reg_0_15_24_29_n_7;
  wire RAM_reg_0_15_24_29_n_8;
  wire RAM_reg_0_15_24_29_n_9;
  wire RAM_reg_0_15_30_35_n_0;
  wire RAM_reg_0_15_30_35_n_1;
  wire RAM_reg_0_15_30_35_n_10;
  wire RAM_reg_0_15_30_35_n_11;
  wire RAM_reg_0_15_30_35_n_12;
  wire RAM_reg_0_15_30_35_n_13;
  wire RAM_reg_0_15_30_35_n_2;
  wire RAM_reg_0_15_30_35_n_3;
  wire RAM_reg_0_15_30_35_n_4;
  wire RAM_reg_0_15_30_35_n_5;
  wire RAM_reg_0_15_30_35_n_6;
  wire RAM_reg_0_15_30_35_n_7;
  wire RAM_reg_0_15_30_35_n_8;
  wire RAM_reg_0_15_30_35_n_9;
  wire RAM_reg_0_15_36_41_n_0;
  wire RAM_reg_0_15_36_41_n_1;
  wire RAM_reg_0_15_36_41_n_10;
  wire RAM_reg_0_15_36_41_n_11;
  wire RAM_reg_0_15_36_41_n_12;
  wire RAM_reg_0_15_36_41_n_13;
  wire RAM_reg_0_15_36_41_n_2;
  wire RAM_reg_0_15_36_41_n_3;
  wire RAM_reg_0_15_36_41_n_4;
  wire RAM_reg_0_15_36_41_n_5;
  wire RAM_reg_0_15_36_41_n_6;
  wire RAM_reg_0_15_36_41_n_7;
  wire RAM_reg_0_15_36_41_n_8;
  wire RAM_reg_0_15_36_41_n_9;
  wire RAM_reg_0_15_42_47_n_0;
  wire RAM_reg_0_15_42_47_n_1;
  wire RAM_reg_0_15_42_47_n_11;
  wire RAM_reg_0_15_42_47_n_2;
  wire RAM_reg_0_15_42_47_n_3;
  wire RAM_reg_0_15_42_47_n_4;
  wire RAM_reg_0_15_42_47_n_5;
  wire RAM_reg_0_15_42_47_n_6;
  wire RAM_reg_0_15_42_47_n_7;
  wire RAM_reg_0_15_42_47_n_8;
  wire RAM_reg_0_15_42_47_n_9;
  wire RAM_reg_0_15_6_11_n_0;
  wire RAM_reg_0_15_6_11_n_1;
  wire RAM_reg_0_15_6_11_n_10;
  wire RAM_reg_0_15_6_11_n_11;
  wire RAM_reg_0_15_6_11_n_12;
  wire RAM_reg_0_15_6_11_n_13;
  wire RAM_reg_0_15_6_11_n_2;
  wire RAM_reg_0_15_6_11_n_3;
  wire RAM_reg_0_15_6_11_n_4;
  wire RAM_reg_0_15_6_11_n_5;
  wire RAM_reg_0_15_6_11_n_6;
  wire RAM_reg_0_15_6_11_n_7;
  wire RAM_reg_0_15_6_11_n_8;
  wire RAM_reg_0_15_6_11_n_9;
  wire [108:0]dout_i;
  wire [3:0]\gc0.count_d1_reg[3] ;
  wire [3:0]\gic0.gc0.count_d2_reg[3] ;
  wire [0:0]\gpregsm1.curr_fwft_state_reg[1] ;
  wire m_aclk;
  wire [0:0]ram_full_fb_i_reg;
  wire s_aclk;
  wire [1:0]NLW_RAM_reg_0_15_0_5_DOH_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_12_17_DOH_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_18_23_DOH_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_24_29_DOH_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_30_35_DOH_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_36_41_DOH_UNCONNECTED;
  wire [1:1]NLW_RAM_reg_0_15_42_47_DOF_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_42_47_DOG_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_42_47_DOH_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_6_11_DOH_UNCONNECTED;

  (* METHODOLOGY_DRC_VIOS = "" *) 
  RAM32M16 RAM_reg_0_15_0_5
       (.ADDRA({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRB({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRC({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRD({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRE({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRF({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRG({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRH({1'b0,\gic0.gc0.count_d2_reg[3] }),
        .DIA(DI[1:0]),
        .DIB(DI[3:2]),
        .DIC(DI[5:4]),
        .DID(DI[7:6]),
        .DIE(DI[9:8]),
        .DIF(DI[11:10]),
        .DIG(DI[13:12]),
        .DIH({1'b0,1'b0}),
        .DOA({RAM_reg_0_15_0_5_n_0,RAM_reg_0_15_0_5_n_1}),
        .DOB({RAM_reg_0_15_0_5_n_2,RAM_reg_0_15_0_5_n_3}),
        .DOC({RAM_reg_0_15_0_5_n_4,RAM_reg_0_15_0_5_n_5}),
        .DOD({RAM_reg_0_15_0_5_n_6,RAM_reg_0_15_0_5_n_7}),
        .DOE({RAM_reg_0_15_0_5_n_8,RAM_reg_0_15_0_5_n_9}),
        .DOF({RAM_reg_0_15_0_5_n_10,RAM_reg_0_15_0_5_n_11}),
        .DOG({RAM_reg_0_15_0_5_n_12,RAM_reg_0_15_0_5_n_13}),
        .DOH(NLW_RAM_reg_0_15_0_5_DOH_UNCONNECTED[1:0]),
        .WCLK(s_aclk),
        .WE(ram_full_fb_i_reg));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  RAM32M16 RAM_reg_0_15_12_17
       (.ADDRA({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRB({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRC({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRD({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRE({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRF({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRG({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRH({1'b0,\gic0.gc0.count_d2_reg[3] }),
        .DIA(DI[29:28]),
        .DIB(DI[31:30]),
        .DIC(DI[33:32]),
        .DID(DI[35:34]),
        .DIE(DI[37:36]),
        .DIF(DI[39:38]),
        .DIG(DI[41:40]),
        .DIH({1'b0,1'b0}),
        .DOA({RAM_reg_0_15_12_17_n_0,RAM_reg_0_15_12_17_n_1}),
        .DOB({RAM_reg_0_15_12_17_n_2,RAM_reg_0_15_12_17_n_3}),
        .DOC({RAM_reg_0_15_12_17_n_4,RAM_reg_0_15_12_17_n_5}),
        .DOD({RAM_reg_0_15_12_17_n_6,RAM_reg_0_15_12_17_n_7}),
        .DOE({RAM_reg_0_15_12_17_n_8,RAM_reg_0_15_12_17_n_9}),
        .DOF({RAM_reg_0_15_12_17_n_10,RAM_reg_0_15_12_17_n_11}),
        .DOG({RAM_reg_0_15_12_17_n_12,RAM_reg_0_15_12_17_n_13}),
        .DOH(NLW_RAM_reg_0_15_12_17_DOH_UNCONNECTED[1:0]),
        .WCLK(s_aclk),
        .WE(ram_full_fb_i_reg));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  RAM32M16 RAM_reg_0_15_18_23
       (.ADDRA({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRB({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRC({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRD({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRE({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRF({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRG({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRH({1'b0,\gic0.gc0.count_d2_reg[3] }),
        .DIA(DI[43:42]),
        .DIB(DI[45:44]),
        .DIC(DI[47:46]),
        .DID(DI[49:48]),
        .DIE(DI[51:50]),
        .DIF(DI[53:52]),
        .DIG(DI[55:54]),
        .DIH({1'b0,1'b0}),
        .DOA({RAM_reg_0_15_18_23_n_0,RAM_reg_0_15_18_23_n_1}),
        .DOB({RAM_reg_0_15_18_23_n_2,RAM_reg_0_15_18_23_n_3}),
        .DOC({RAM_reg_0_15_18_23_n_4,RAM_reg_0_15_18_23_n_5}),
        .DOD({RAM_reg_0_15_18_23_n_6,RAM_reg_0_15_18_23_n_7}),
        .DOE({RAM_reg_0_15_18_23_n_8,RAM_reg_0_15_18_23_n_9}),
        .DOF({RAM_reg_0_15_18_23_n_10,RAM_reg_0_15_18_23_n_11}),
        .DOG({RAM_reg_0_15_18_23_n_12,RAM_reg_0_15_18_23_n_13}),
        .DOH(NLW_RAM_reg_0_15_18_23_DOH_UNCONNECTED[1:0]),
        .WCLK(s_aclk),
        .WE(ram_full_fb_i_reg));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  RAM32M16 RAM_reg_0_15_24_29
       (.ADDRA({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRB({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRC({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRD({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRE({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRF({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRG({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRH({1'b0,\gic0.gc0.count_d2_reg[3] }),
        .DIA(DI[57:56]),
        .DIB(DI[59:58]),
        .DIC(DI[61:60]),
        .DID(DI[63:62]),
        .DIE(DI[65:64]),
        .DIF(DI[67:66]),
        .DIG(DI[69:68]),
        .DIH({1'b0,1'b0}),
        .DOA({RAM_reg_0_15_24_29_n_0,RAM_reg_0_15_24_29_n_1}),
        .DOB({RAM_reg_0_15_24_29_n_2,RAM_reg_0_15_24_29_n_3}),
        .DOC({RAM_reg_0_15_24_29_n_4,RAM_reg_0_15_24_29_n_5}),
        .DOD({RAM_reg_0_15_24_29_n_6,RAM_reg_0_15_24_29_n_7}),
        .DOE({RAM_reg_0_15_24_29_n_8,RAM_reg_0_15_24_29_n_9}),
        .DOF({RAM_reg_0_15_24_29_n_10,RAM_reg_0_15_24_29_n_11}),
        .DOG({RAM_reg_0_15_24_29_n_12,RAM_reg_0_15_24_29_n_13}),
        .DOH(NLW_RAM_reg_0_15_24_29_DOH_UNCONNECTED[1:0]),
        .WCLK(s_aclk),
        .WE(ram_full_fb_i_reg));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  RAM32M16 RAM_reg_0_15_30_35
       (.ADDRA({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRB({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRC({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRD({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRE({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRF({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRG({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRH({1'b0,\gic0.gc0.count_d2_reg[3] }),
        .DIA(DI[71:70]),
        .DIB(DI[73:72]),
        .DIC(DI[75:74]),
        .DID(DI[77:76]),
        .DIE(DI[79:78]),
        .DIF(DI[81:80]),
        .DIG(DI[83:82]),
        .DIH({1'b0,1'b0}),
        .DOA({RAM_reg_0_15_30_35_n_0,RAM_reg_0_15_30_35_n_1}),
        .DOB({RAM_reg_0_15_30_35_n_2,RAM_reg_0_15_30_35_n_3}),
        .DOC({RAM_reg_0_15_30_35_n_4,RAM_reg_0_15_30_35_n_5}),
        .DOD({RAM_reg_0_15_30_35_n_6,RAM_reg_0_15_30_35_n_7}),
        .DOE({RAM_reg_0_15_30_35_n_8,RAM_reg_0_15_30_35_n_9}),
        .DOF({RAM_reg_0_15_30_35_n_10,RAM_reg_0_15_30_35_n_11}),
        .DOG({RAM_reg_0_15_30_35_n_12,RAM_reg_0_15_30_35_n_13}),
        .DOH(NLW_RAM_reg_0_15_30_35_DOH_UNCONNECTED[1:0]),
        .WCLK(s_aclk),
        .WE(ram_full_fb_i_reg));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  RAM32M16 RAM_reg_0_15_36_41
       (.ADDRA({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRB({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRC({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRD({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRE({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRF({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRG({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRH({1'b0,\gic0.gc0.count_d2_reg[3] }),
        .DIA(DI[85:84]),
        .DIB(DI[87:86]),
        .DIC(DI[89:88]),
        .DID(DI[91:90]),
        .DIE(DI[93:92]),
        .DIF(DI[95:94]),
        .DIG(DI[97:96]),
        .DIH({1'b0,1'b0}),
        .DOA({RAM_reg_0_15_36_41_n_0,RAM_reg_0_15_36_41_n_1}),
        .DOB({RAM_reg_0_15_36_41_n_2,RAM_reg_0_15_36_41_n_3}),
        .DOC({RAM_reg_0_15_36_41_n_4,RAM_reg_0_15_36_41_n_5}),
        .DOD({RAM_reg_0_15_36_41_n_6,RAM_reg_0_15_36_41_n_7}),
        .DOE({RAM_reg_0_15_36_41_n_8,RAM_reg_0_15_36_41_n_9}),
        .DOF({RAM_reg_0_15_36_41_n_10,RAM_reg_0_15_36_41_n_11}),
        .DOG({RAM_reg_0_15_36_41_n_12,RAM_reg_0_15_36_41_n_13}),
        .DOH(NLW_RAM_reg_0_15_36_41_DOH_UNCONNECTED[1:0]),
        .WCLK(s_aclk),
        .WE(ram_full_fb_i_reg));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  RAM32M16 RAM_reg_0_15_42_47
       (.ADDRA({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRB({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRC({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRD({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRE({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRF({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRG({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRH({1'b0,\gic0.gc0.count_d2_reg[3] }),
        .DIA(DI[99:98]),
        .DIB(DI[101:100]),
        .DIC(DI[103:102]),
        .DID(DI[105:104]),
        .DIE(DI[107:106]),
        .DIF({1'b0,DI[108]}),
        .DIG({1'b0,1'b0}),
        .DIH({1'b0,1'b0}),
        .DOA({RAM_reg_0_15_42_47_n_0,RAM_reg_0_15_42_47_n_1}),
        .DOB({RAM_reg_0_15_42_47_n_2,RAM_reg_0_15_42_47_n_3}),
        .DOC({RAM_reg_0_15_42_47_n_4,RAM_reg_0_15_42_47_n_5}),
        .DOD({RAM_reg_0_15_42_47_n_6,RAM_reg_0_15_42_47_n_7}),
        .DOE({RAM_reg_0_15_42_47_n_8,RAM_reg_0_15_42_47_n_9}),
        .DOF({NLW_RAM_reg_0_15_42_47_DOF_UNCONNECTED[1],RAM_reg_0_15_42_47_n_11}),
        .DOG(NLW_RAM_reg_0_15_42_47_DOG_UNCONNECTED[1:0]),
        .DOH(NLW_RAM_reg_0_15_42_47_DOH_UNCONNECTED[1:0]),
        .WCLK(s_aclk),
        .WE(ram_full_fb_i_reg));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  RAM32M16 RAM_reg_0_15_6_11
       (.ADDRA({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRB({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRC({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRD({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRE({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRF({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRG({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRH({1'b0,\gic0.gc0.count_d2_reg[3] }),
        .DIA(DI[15:14]),
        .DIB(DI[17:16]),
        .DIC(DI[19:18]),
        .DID(DI[21:20]),
        .DIE(DI[23:22]),
        .DIF(DI[25:24]),
        .DIG(DI[27:26]),
        .DIH({1'b0,1'b0}),
        .DOA({RAM_reg_0_15_6_11_n_0,RAM_reg_0_15_6_11_n_1}),
        .DOB({RAM_reg_0_15_6_11_n_2,RAM_reg_0_15_6_11_n_3}),
        .DOC({RAM_reg_0_15_6_11_n_4,RAM_reg_0_15_6_11_n_5}),
        .DOD({RAM_reg_0_15_6_11_n_6,RAM_reg_0_15_6_11_n_7}),
        .DOE({RAM_reg_0_15_6_11_n_8,RAM_reg_0_15_6_11_n_9}),
        .DOF({RAM_reg_0_15_6_11_n_10,RAM_reg_0_15_6_11_n_11}),
        .DOG({RAM_reg_0_15_6_11_n_12,RAM_reg_0_15_6_11_n_13}),
        .DOH(NLW_RAM_reg_0_15_6_11_DOH_UNCONNECTED[1:0]),
        .WCLK(s_aclk),
        .WE(ram_full_fb_i_reg));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[0] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_1),
        .Q(dout_i[0]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[100] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_42_47_n_3),
        .Q(dout_i[100]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[101] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_42_47_n_2),
        .Q(dout_i[101]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[102] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_42_47_n_5),
        .Q(dout_i[102]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[103] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_42_47_n_4),
        .Q(dout_i[103]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[104] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_42_47_n_7),
        .Q(dout_i[104]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[105] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_42_47_n_6),
        .Q(dout_i[105]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[106] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_42_47_n_9),
        .Q(dout_i[106]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[107] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_42_47_n_8),
        .Q(dout_i[107]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[108] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_42_47_n_11),
        .Q(dout_i[108]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[10] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_11),
        .Q(dout_i[10]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[11] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_10),
        .Q(dout_i[11]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[12] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_13),
        .Q(dout_i[12]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[13] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_12),
        .Q(dout_i[13]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[14] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_1),
        .Q(dout_i[14]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[15] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_0),
        .Q(dout_i[15]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[16] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_3),
        .Q(dout_i[16]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[17] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_2),
        .Q(dout_i[17]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[18] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_5),
        .Q(dout_i[18]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[19] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_4),
        .Q(dout_i[19]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[1] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_0),
        .Q(dout_i[1]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[20] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_7),
        .Q(dout_i[20]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[21] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_6),
        .Q(dout_i[21]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[22] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_9),
        .Q(dout_i[22]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[23] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_8),
        .Q(dout_i[23]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[24] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_11),
        .Q(dout_i[24]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[25] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_10),
        .Q(dout_i[25]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[26] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_13),
        .Q(dout_i[26]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[27] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_12),
        .Q(dout_i[27]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[28] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_1),
        .Q(dout_i[28]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[29] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_0),
        .Q(dout_i[29]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[2] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_3),
        .Q(dout_i[2]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[30] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_3),
        .Q(dout_i[30]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[31] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_2),
        .Q(dout_i[31]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[32] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_5),
        .Q(dout_i[32]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[33] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_4),
        .Q(dout_i[33]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[34] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_7),
        .Q(dout_i[34]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[35] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_6),
        .Q(dout_i[35]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[36] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_9),
        .Q(dout_i[36]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[37] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_8),
        .Q(dout_i[37]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[38] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_11),
        .Q(dout_i[38]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[39] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_10),
        .Q(dout_i[39]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[3] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_2),
        .Q(dout_i[3]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[40] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_13),
        .Q(dout_i[40]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[41] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_12),
        .Q(dout_i[41]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[42] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_1),
        .Q(dout_i[42]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[43] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_0),
        .Q(dout_i[43]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[44] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_3),
        .Q(dout_i[44]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[45] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_2),
        .Q(dout_i[45]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[46] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_5),
        .Q(dout_i[46]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[47] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_4),
        .Q(dout_i[47]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[48] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_7),
        .Q(dout_i[48]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[49] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_6),
        .Q(dout_i[49]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[4] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_5),
        .Q(dout_i[4]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[50] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_9),
        .Q(dout_i[50]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[51] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_8),
        .Q(dout_i[51]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[52] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_11),
        .Q(dout_i[52]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[53] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_10),
        .Q(dout_i[53]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[54] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_13),
        .Q(dout_i[54]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[55] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_12),
        .Q(dout_i[55]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[56] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_1),
        .Q(dout_i[56]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[57] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_0),
        .Q(dout_i[57]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[58] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_3),
        .Q(dout_i[58]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[59] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_2),
        .Q(dout_i[59]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[5] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_4),
        .Q(dout_i[5]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[60] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_5),
        .Q(dout_i[60]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[61] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_4),
        .Q(dout_i[61]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[62] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_7),
        .Q(dout_i[62]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[63] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_6),
        .Q(dout_i[63]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[64] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_9),
        .Q(dout_i[64]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[65] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_8),
        .Q(dout_i[65]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[66] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_11),
        .Q(dout_i[66]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[67] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_10),
        .Q(dout_i[67]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[68] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_13),
        .Q(dout_i[68]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[69] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_12),
        .Q(dout_i[69]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[6] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_7),
        .Q(dout_i[6]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[70] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_1),
        .Q(dout_i[70]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[71] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_0),
        .Q(dout_i[71]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[72] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_3),
        .Q(dout_i[72]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[73] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_2),
        .Q(dout_i[73]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[74] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_5),
        .Q(dout_i[74]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[75] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_4),
        .Q(dout_i[75]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[76] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_7),
        .Q(dout_i[76]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[77] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_6),
        .Q(dout_i[77]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[78] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_9),
        .Q(dout_i[78]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[79] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_8),
        .Q(dout_i[79]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[7] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_6),
        .Q(dout_i[7]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[80] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_11),
        .Q(dout_i[80]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[81] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_10),
        .Q(dout_i[81]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[82] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_13),
        .Q(dout_i[82]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[83] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_12),
        .Q(dout_i[83]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[84] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_36_41_n_1),
        .Q(dout_i[84]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[85] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_36_41_n_0),
        .Q(dout_i[85]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[86] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_36_41_n_3),
        .Q(dout_i[86]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[87] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_36_41_n_2),
        .Q(dout_i[87]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[88] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_36_41_n_5),
        .Q(dout_i[88]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[89] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_36_41_n_4),
        .Q(dout_i[89]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[8] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_9),
        .Q(dout_i[8]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[90] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_36_41_n_7),
        .Q(dout_i[90]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[91] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_36_41_n_6),
        .Q(dout_i[91]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[92] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_36_41_n_9),
        .Q(dout_i[92]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[93] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_36_41_n_8),
        .Q(dout_i[93]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[94] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_36_41_n_11),
        .Q(dout_i[94]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[95] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_36_41_n_10),
        .Q(dout_i[95]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[96] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_36_41_n_13),
        .Q(dout_i[96]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[97] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_36_41_n_12),
        .Q(dout_i[97]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[98] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_42_47_n_1),
        .Q(dout_i[98]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[99] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_42_47_n_0),
        .Q(dout_i[99]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[9] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_8),
        .Q(dout_i[9]),
        .R(1'b0));
endmodule

(* ORIG_REF_NAME = "dmem" *) 
module axi_clock_converter_dramslim_dmem_86
   (dout_i,
    s_aclk,
    ram_full_fb_i_reg,
    I141,
    \gc0.count_d1_reg[3] ,
    \gic0.gc0.count_d2_reg[3] ,
    \gpregsm1.curr_fwft_state_reg[1] ,
    m_aclk);
  output [108:0]dout_i;
  input s_aclk;
  input [0:0]ram_full_fb_i_reg;
  input [108:0]I141;
  input [3:0]\gc0.count_d1_reg[3] ;
  input [3:0]\gic0.gc0.count_d2_reg[3] ;
  input [0:0]\gpregsm1.curr_fwft_state_reg[1] ;
  input m_aclk;

  wire [108:0]I141;
  wire RAM_reg_0_15_0_5_n_0;
  wire RAM_reg_0_15_0_5_n_1;
  wire RAM_reg_0_15_0_5_n_10;
  wire RAM_reg_0_15_0_5_n_11;
  wire RAM_reg_0_15_0_5_n_12;
  wire RAM_reg_0_15_0_5_n_13;
  wire RAM_reg_0_15_0_5_n_2;
  wire RAM_reg_0_15_0_5_n_3;
  wire RAM_reg_0_15_0_5_n_4;
  wire RAM_reg_0_15_0_5_n_5;
  wire RAM_reg_0_15_0_5_n_6;
  wire RAM_reg_0_15_0_5_n_7;
  wire RAM_reg_0_15_0_5_n_8;
  wire RAM_reg_0_15_0_5_n_9;
  wire RAM_reg_0_15_12_17_n_0;
  wire RAM_reg_0_15_12_17_n_1;
  wire RAM_reg_0_15_12_17_n_10;
  wire RAM_reg_0_15_12_17_n_11;
  wire RAM_reg_0_15_12_17_n_12;
  wire RAM_reg_0_15_12_17_n_13;
  wire RAM_reg_0_15_12_17_n_2;
  wire RAM_reg_0_15_12_17_n_3;
  wire RAM_reg_0_15_12_17_n_4;
  wire RAM_reg_0_15_12_17_n_5;
  wire RAM_reg_0_15_12_17_n_6;
  wire RAM_reg_0_15_12_17_n_7;
  wire RAM_reg_0_15_12_17_n_8;
  wire RAM_reg_0_15_12_17_n_9;
  wire RAM_reg_0_15_18_23_n_0;
  wire RAM_reg_0_15_18_23_n_1;
  wire RAM_reg_0_15_18_23_n_10;
  wire RAM_reg_0_15_18_23_n_11;
  wire RAM_reg_0_15_18_23_n_12;
  wire RAM_reg_0_15_18_23_n_13;
  wire RAM_reg_0_15_18_23_n_2;
  wire RAM_reg_0_15_18_23_n_3;
  wire RAM_reg_0_15_18_23_n_4;
  wire RAM_reg_0_15_18_23_n_5;
  wire RAM_reg_0_15_18_23_n_6;
  wire RAM_reg_0_15_18_23_n_7;
  wire RAM_reg_0_15_18_23_n_8;
  wire RAM_reg_0_15_18_23_n_9;
  wire RAM_reg_0_15_24_29_n_0;
  wire RAM_reg_0_15_24_29_n_1;
  wire RAM_reg_0_15_24_29_n_10;
  wire RAM_reg_0_15_24_29_n_11;
  wire RAM_reg_0_15_24_29_n_12;
  wire RAM_reg_0_15_24_29_n_13;
  wire RAM_reg_0_15_24_29_n_2;
  wire RAM_reg_0_15_24_29_n_3;
  wire RAM_reg_0_15_24_29_n_4;
  wire RAM_reg_0_15_24_29_n_5;
  wire RAM_reg_0_15_24_29_n_6;
  wire RAM_reg_0_15_24_29_n_7;
  wire RAM_reg_0_15_24_29_n_8;
  wire RAM_reg_0_15_24_29_n_9;
  wire RAM_reg_0_15_30_35_n_0;
  wire RAM_reg_0_15_30_35_n_1;
  wire RAM_reg_0_15_30_35_n_10;
  wire RAM_reg_0_15_30_35_n_11;
  wire RAM_reg_0_15_30_35_n_12;
  wire RAM_reg_0_15_30_35_n_13;
  wire RAM_reg_0_15_30_35_n_2;
  wire RAM_reg_0_15_30_35_n_3;
  wire RAM_reg_0_15_30_35_n_4;
  wire RAM_reg_0_15_30_35_n_5;
  wire RAM_reg_0_15_30_35_n_6;
  wire RAM_reg_0_15_30_35_n_7;
  wire RAM_reg_0_15_30_35_n_8;
  wire RAM_reg_0_15_30_35_n_9;
  wire RAM_reg_0_15_36_41_n_0;
  wire RAM_reg_0_15_36_41_n_1;
  wire RAM_reg_0_15_36_41_n_10;
  wire RAM_reg_0_15_36_41_n_11;
  wire RAM_reg_0_15_36_41_n_12;
  wire RAM_reg_0_15_36_41_n_13;
  wire RAM_reg_0_15_36_41_n_2;
  wire RAM_reg_0_15_36_41_n_3;
  wire RAM_reg_0_15_36_41_n_4;
  wire RAM_reg_0_15_36_41_n_5;
  wire RAM_reg_0_15_36_41_n_6;
  wire RAM_reg_0_15_36_41_n_7;
  wire RAM_reg_0_15_36_41_n_8;
  wire RAM_reg_0_15_36_41_n_9;
  wire RAM_reg_0_15_42_47_n_0;
  wire RAM_reg_0_15_42_47_n_1;
  wire RAM_reg_0_15_42_47_n_11;
  wire RAM_reg_0_15_42_47_n_2;
  wire RAM_reg_0_15_42_47_n_3;
  wire RAM_reg_0_15_42_47_n_4;
  wire RAM_reg_0_15_42_47_n_5;
  wire RAM_reg_0_15_42_47_n_6;
  wire RAM_reg_0_15_42_47_n_7;
  wire RAM_reg_0_15_42_47_n_8;
  wire RAM_reg_0_15_42_47_n_9;
  wire RAM_reg_0_15_6_11_n_0;
  wire RAM_reg_0_15_6_11_n_1;
  wire RAM_reg_0_15_6_11_n_10;
  wire RAM_reg_0_15_6_11_n_11;
  wire RAM_reg_0_15_6_11_n_12;
  wire RAM_reg_0_15_6_11_n_13;
  wire RAM_reg_0_15_6_11_n_2;
  wire RAM_reg_0_15_6_11_n_3;
  wire RAM_reg_0_15_6_11_n_4;
  wire RAM_reg_0_15_6_11_n_5;
  wire RAM_reg_0_15_6_11_n_6;
  wire RAM_reg_0_15_6_11_n_7;
  wire RAM_reg_0_15_6_11_n_8;
  wire RAM_reg_0_15_6_11_n_9;
  wire [108:0]dout_i;
  wire [3:0]\gc0.count_d1_reg[3] ;
  wire [3:0]\gic0.gc0.count_d2_reg[3] ;
  wire [0:0]\gpregsm1.curr_fwft_state_reg[1] ;
  wire m_aclk;
  wire [0:0]ram_full_fb_i_reg;
  wire s_aclk;
  wire [1:0]NLW_RAM_reg_0_15_0_5_DOH_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_12_17_DOH_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_18_23_DOH_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_24_29_DOH_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_30_35_DOH_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_36_41_DOH_UNCONNECTED;
  wire [1:1]NLW_RAM_reg_0_15_42_47_DOF_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_42_47_DOG_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_42_47_DOH_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_6_11_DOH_UNCONNECTED;

  (* METHODOLOGY_DRC_VIOS = "" *) 
  RAM32M16 RAM_reg_0_15_0_5
       (.ADDRA({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRB({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRC({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRD({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRE({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRF({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRG({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRH({1'b0,\gic0.gc0.count_d2_reg[3] }),
        .DIA(I141[1:0]),
        .DIB(I141[3:2]),
        .DIC(I141[5:4]),
        .DID(I141[7:6]),
        .DIE(I141[9:8]),
        .DIF(I141[11:10]),
        .DIG(I141[13:12]),
        .DIH({1'b0,1'b0}),
        .DOA({RAM_reg_0_15_0_5_n_0,RAM_reg_0_15_0_5_n_1}),
        .DOB({RAM_reg_0_15_0_5_n_2,RAM_reg_0_15_0_5_n_3}),
        .DOC({RAM_reg_0_15_0_5_n_4,RAM_reg_0_15_0_5_n_5}),
        .DOD({RAM_reg_0_15_0_5_n_6,RAM_reg_0_15_0_5_n_7}),
        .DOE({RAM_reg_0_15_0_5_n_8,RAM_reg_0_15_0_5_n_9}),
        .DOF({RAM_reg_0_15_0_5_n_10,RAM_reg_0_15_0_5_n_11}),
        .DOG({RAM_reg_0_15_0_5_n_12,RAM_reg_0_15_0_5_n_13}),
        .DOH(NLW_RAM_reg_0_15_0_5_DOH_UNCONNECTED[1:0]),
        .WCLK(s_aclk),
        .WE(ram_full_fb_i_reg));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  RAM32M16 RAM_reg_0_15_12_17
       (.ADDRA({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRB({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRC({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRD({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRE({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRF({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRG({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRH({1'b0,\gic0.gc0.count_d2_reg[3] }),
        .DIA(I141[29:28]),
        .DIB(I141[31:30]),
        .DIC(I141[33:32]),
        .DID(I141[35:34]),
        .DIE(I141[37:36]),
        .DIF(I141[39:38]),
        .DIG(I141[41:40]),
        .DIH({1'b0,1'b0}),
        .DOA({RAM_reg_0_15_12_17_n_0,RAM_reg_0_15_12_17_n_1}),
        .DOB({RAM_reg_0_15_12_17_n_2,RAM_reg_0_15_12_17_n_3}),
        .DOC({RAM_reg_0_15_12_17_n_4,RAM_reg_0_15_12_17_n_5}),
        .DOD({RAM_reg_0_15_12_17_n_6,RAM_reg_0_15_12_17_n_7}),
        .DOE({RAM_reg_0_15_12_17_n_8,RAM_reg_0_15_12_17_n_9}),
        .DOF({RAM_reg_0_15_12_17_n_10,RAM_reg_0_15_12_17_n_11}),
        .DOG({RAM_reg_0_15_12_17_n_12,RAM_reg_0_15_12_17_n_13}),
        .DOH(NLW_RAM_reg_0_15_12_17_DOH_UNCONNECTED[1:0]),
        .WCLK(s_aclk),
        .WE(ram_full_fb_i_reg));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  RAM32M16 RAM_reg_0_15_18_23
       (.ADDRA({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRB({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRC({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRD({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRE({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRF({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRG({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRH({1'b0,\gic0.gc0.count_d2_reg[3] }),
        .DIA(I141[43:42]),
        .DIB(I141[45:44]),
        .DIC(I141[47:46]),
        .DID(I141[49:48]),
        .DIE(I141[51:50]),
        .DIF(I141[53:52]),
        .DIG(I141[55:54]),
        .DIH({1'b0,1'b0}),
        .DOA({RAM_reg_0_15_18_23_n_0,RAM_reg_0_15_18_23_n_1}),
        .DOB({RAM_reg_0_15_18_23_n_2,RAM_reg_0_15_18_23_n_3}),
        .DOC({RAM_reg_0_15_18_23_n_4,RAM_reg_0_15_18_23_n_5}),
        .DOD({RAM_reg_0_15_18_23_n_6,RAM_reg_0_15_18_23_n_7}),
        .DOE({RAM_reg_0_15_18_23_n_8,RAM_reg_0_15_18_23_n_9}),
        .DOF({RAM_reg_0_15_18_23_n_10,RAM_reg_0_15_18_23_n_11}),
        .DOG({RAM_reg_0_15_18_23_n_12,RAM_reg_0_15_18_23_n_13}),
        .DOH(NLW_RAM_reg_0_15_18_23_DOH_UNCONNECTED[1:0]),
        .WCLK(s_aclk),
        .WE(ram_full_fb_i_reg));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  RAM32M16 RAM_reg_0_15_24_29
       (.ADDRA({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRB({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRC({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRD({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRE({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRF({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRG({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRH({1'b0,\gic0.gc0.count_d2_reg[3] }),
        .DIA(I141[57:56]),
        .DIB(I141[59:58]),
        .DIC(I141[61:60]),
        .DID(I141[63:62]),
        .DIE(I141[65:64]),
        .DIF(I141[67:66]),
        .DIG(I141[69:68]),
        .DIH({1'b0,1'b0}),
        .DOA({RAM_reg_0_15_24_29_n_0,RAM_reg_0_15_24_29_n_1}),
        .DOB({RAM_reg_0_15_24_29_n_2,RAM_reg_0_15_24_29_n_3}),
        .DOC({RAM_reg_0_15_24_29_n_4,RAM_reg_0_15_24_29_n_5}),
        .DOD({RAM_reg_0_15_24_29_n_6,RAM_reg_0_15_24_29_n_7}),
        .DOE({RAM_reg_0_15_24_29_n_8,RAM_reg_0_15_24_29_n_9}),
        .DOF({RAM_reg_0_15_24_29_n_10,RAM_reg_0_15_24_29_n_11}),
        .DOG({RAM_reg_0_15_24_29_n_12,RAM_reg_0_15_24_29_n_13}),
        .DOH(NLW_RAM_reg_0_15_24_29_DOH_UNCONNECTED[1:0]),
        .WCLK(s_aclk),
        .WE(ram_full_fb_i_reg));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  RAM32M16 RAM_reg_0_15_30_35
       (.ADDRA({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRB({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRC({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRD({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRE({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRF({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRG({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRH({1'b0,\gic0.gc0.count_d2_reg[3] }),
        .DIA(I141[71:70]),
        .DIB(I141[73:72]),
        .DIC(I141[75:74]),
        .DID(I141[77:76]),
        .DIE(I141[79:78]),
        .DIF(I141[81:80]),
        .DIG(I141[83:82]),
        .DIH({1'b0,1'b0}),
        .DOA({RAM_reg_0_15_30_35_n_0,RAM_reg_0_15_30_35_n_1}),
        .DOB({RAM_reg_0_15_30_35_n_2,RAM_reg_0_15_30_35_n_3}),
        .DOC({RAM_reg_0_15_30_35_n_4,RAM_reg_0_15_30_35_n_5}),
        .DOD({RAM_reg_0_15_30_35_n_6,RAM_reg_0_15_30_35_n_7}),
        .DOE({RAM_reg_0_15_30_35_n_8,RAM_reg_0_15_30_35_n_9}),
        .DOF({RAM_reg_0_15_30_35_n_10,RAM_reg_0_15_30_35_n_11}),
        .DOG({RAM_reg_0_15_30_35_n_12,RAM_reg_0_15_30_35_n_13}),
        .DOH(NLW_RAM_reg_0_15_30_35_DOH_UNCONNECTED[1:0]),
        .WCLK(s_aclk),
        .WE(ram_full_fb_i_reg));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  RAM32M16 RAM_reg_0_15_36_41
       (.ADDRA({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRB({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRC({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRD({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRE({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRF({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRG({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRH({1'b0,\gic0.gc0.count_d2_reg[3] }),
        .DIA(I141[85:84]),
        .DIB(I141[87:86]),
        .DIC(I141[89:88]),
        .DID(I141[91:90]),
        .DIE(I141[93:92]),
        .DIF(I141[95:94]),
        .DIG(I141[97:96]),
        .DIH({1'b0,1'b0}),
        .DOA({RAM_reg_0_15_36_41_n_0,RAM_reg_0_15_36_41_n_1}),
        .DOB({RAM_reg_0_15_36_41_n_2,RAM_reg_0_15_36_41_n_3}),
        .DOC({RAM_reg_0_15_36_41_n_4,RAM_reg_0_15_36_41_n_5}),
        .DOD({RAM_reg_0_15_36_41_n_6,RAM_reg_0_15_36_41_n_7}),
        .DOE({RAM_reg_0_15_36_41_n_8,RAM_reg_0_15_36_41_n_9}),
        .DOF({RAM_reg_0_15_36_41_n_10,RAM_reg_0_15_36_41_n_11}),
        .DOG({RAM_reg_0_15_36_41_n_12,RAM_reg_0_15_36_41_n_13}),
        .DOH(NLW_RAM_reg_0_15_36_41_DOH_UNCONNECTED[1:0]),
        .WCLK(s_aclk),
        .WE(ram_full_fb_i_reg));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  RAM32M16 RAM_reg_0_15_42_47
       (.ADDRA({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRB({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRC({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRD({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRE({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRF({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRG({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRH({1'b0,\gic0.gc0.count_d2_reg[3] }),
        .DIA(I141[99:98]),
        .DIB(I141[101:100]),
        .DIC(I141[103:102]),
        .DID(I141[105:104]),
        .DIE(I141[107:106]),
        .DIF({1'b0,I141[108]}),
        .DIG({1'b0,1'b0}),
        .DIH({1'b0,1'b0}),
        .DOA({RAM_reg_0_15_42_47_n_0,RAM_reg_0_15_42_47_n_1}),
        .DOB({RAM_reg_0_15_42_47_n_2,RAM_reg_0_15_42_47_n_3}),
        .DOC({RAM_reg_0_15_42_47_n_4,RAM_reg_0_15_42_47_n_5}),
        .DOD({RAM_reg_0_15_42_47_n_6,RAM_reg_0_15_42_47_n_7}),
        .DOE({RAM_reg_0_15_42_47_n_8,RAM_reg_0_15_42_47_n_9}),
        .DOF({NLW_RAM_reg_0_15_42_47_DOF_UNCONNECTED[1],RAM_reg_0_15_42_47_n_11}),
        .DOG(NLW_RAM_reg_0_15_42_47_DOG_UNCONNECTED[1:0]),
        .DOH(NLW_RAM_reg_0_15_42_47_DOH_UNCONNECTED[1:0]),
        .WCLK(s_aclk),
        .WE(ram_full_fb_i_reg));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  RAM32M16 RAM_reg_0_15_6_11
       (.ADDRA({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRB({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRC({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRD({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRE({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRF({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRG({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRH({1'b0,\gic0.gc0.count_d2_reg[3] }),
        .DIA(I141[15:14]),
        .DIB(I141[17:16]),
        .DIC(I141[19:18]),
        .DID(I141[21:20]),
        .DIE(I141[23:22]),
        .DIF(I141[25:24]),
        .DIG(I141[27:26]),
        .DIH({1'b0,1'b0}),
        .DOA({RAM_reg_0_15_6_11_n_0,RAM_reg_0_15_6_11_n_1}),
        .DOB({RAM_reg_0_15_6_11_n_2,RAM_reg_0_15_6_11_n_3}),
        .DOC({RAM_reg_0_15_6_11_n_4,RAM_reg_0_15_6_11_n_5}),
        .DOD({RAM_reg_0_15_6_11_n_6,RAM_reg_0_15_6_11_n_7}),
        .DOE({RAM_reg_0_15_6_11_n_8,RAM_reg_0_15_6_11_n_9}),
        .DOF({RAM_reg_0_15_6_11_n_10,RAM_reg_0_15_6_11_n_11}),
        .DOG({RAM_reg_0_15_6_11_n_12,RAM_reg_0_15_6_11_n_13}),
        .DOH(NLW_RAM_reg_0_15_6_11_DOH_UNCONNECTED[1:0]),
        .WCLK(s_aclk),
        .WE(ram_full_fb_i_reg));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[0] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_1),
        .Q(dout_i[0]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[100] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_42_47_n_3),
        .Q(dout_i[100]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[101] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_42_47_n_2),
        .Q(dout_i[101]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[102] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_42_47_n_5),
        .Q(dout_i[102]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[103] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_42_47_n_4),
        .Q(dout_i[103]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[104] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_42_47_n_7),
        .Q(dout_i[104]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[105] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_42_47_n_6),
        .Q(dout_i[105]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[106] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_42_47_n_9),
        .Q(dout_i[106]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[107] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_42_47_n_8),
        .Q(dout_i[107]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[108] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_42_47_n_11),
        .Q(dout_i[108]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[10] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_11),
        .Q(dout_i[10]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[11] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_10),
        .Q(dout_i[11]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[12] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_13),
        .Q(dout_i[12]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[13] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_12),
        .Q(dout_i[13]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[14] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_1),
        .Q(dout_i[14]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[15] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_0),
        .Q(dout_i[15]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[16] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_3),
        .Q(dout_i[16]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[17] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_2),
        .Q(dout_i[17]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[18] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_5),
        .Q(dout_i[18]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[19] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_4),
        .Q(dout_i[19]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[1] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_0),
        .Q(dout_i[1]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[20] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_7),
        .Q(dout_i[20]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[21] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_6),
        .Q(dout_i[21]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[22] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_9),
        .Q(dout_i[22]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[23] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_8),
        .Q(dout_i[23]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[24] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_11),
        .Q(dout_i[24]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[25] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_10),
        .Q(dout_i[25]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[26] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_13),
        .Q(dout_i[26]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[27] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_12),
        .Q(dout_i[27]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[28] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_1),
        .Q(dout_i[28]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[29] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_0),
        .Q(dout_i[29]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[2] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_3),
        .Q(dout_i[2]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[30] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_3),
        .Q(dout_i[30]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[31] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_2),
        .Q(dout_i[31]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[32] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_5),
        .Q(dout_i[32]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[33] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_4),
        .Q(dout_i[33]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[34] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_7),
        .Q(dout_i[34]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[35] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_6),
        .Q(dout_i[35]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[36] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_9),
        .Q(dout_i[36]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[37] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_8),
        .Q(dout_i[37]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[38] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_11),
        .Q(dout_i[38]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[39] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_10),
        .Q(dout_i[39]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[3] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_2),
        .Q(dout_i[3]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[40] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_13),
        .Q(dout_i[40]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[41] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_12),
        .Q(dout_i[41]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[42] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_1),
        .Q(dout_i[42]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[43] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_0),
        .Q(dout_i[43]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[44] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_3),
        .Q(dout_i[44]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[45] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_2),
        .Q(dout_i[45]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[46] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_5),
        .Q(dout_i[46]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[47] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_4),
        .Q(dout_i[47]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[48] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_7),
        .Q(dout_i[48]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[49] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_6),
        .Q(dout_i[49]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[4] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_5),
        .Q(dout_i[4]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[50] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_9),
        .Q(dout_i[50]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[51] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_8),
        .Q(dout_i[51]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[52] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_11),
        .Q(dout_i[52]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[53] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_10),
        .Q(dout_i[53]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[54] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_13),
        .Q(dout_i[54]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[55] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_12),
        .Q(dout_i[55]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[56] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_1),
        .Q(dout_i[56]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[57] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_0),
        .Q(dout_i[57]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[58] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_3),
        .Q(dout_i[58]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[59] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_2),
        .Q(dout_i[59]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[5] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_4),
        .Q(dout_i[5]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[60] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_5),
        .Q(dout_i[60]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[61] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_4),
        .Q(dout_i[61]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[62] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_7),
        .Q(dout_i[62]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[63] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_6),
        .Q(dout_i[63]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[64] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_9),
        .Q(dout_i[64]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[65] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_8),
        .Q(dout_i[65]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[66] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_11),
        .Q(dout_i[66]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[67] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_10),
        .Q(dout_i[67]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[68] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_13),
        .Q(dout_i[68]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[69] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_12),
        .Q(dout_i[69]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[6] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_7),
        .Q(dout_i[6]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[70] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_1),
        .Q(dout_i[70]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[71] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_0),
        .Q(dout_i[71]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[72] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_3),
        .Q(dout_i[72]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[73] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_2),
        .Q(dout_i[73]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[74] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_5),
        .Q(dout_i[74]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[75] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_4),
        .Q(dout_i[75]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[76] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_7),
        .Q(dout_i[76]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[77] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_6),
        .Q(dout_i[77]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[78] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_9),
        .Q(dout_i[78]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[79] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_8),
        .Q(dout_i[79]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[7] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_6),
        .Q(dout_i[7]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[80] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_11),
        .Q(dout_i[80]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[81] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_10),
        .Q(dout_i[81]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[82] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_13),
        .Q(dout_i[82]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[83] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_12),
        .Q(dout_i[83]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[84] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_36_41_n_1),
        .Q(dout_i[84]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[85] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_36_41_n_0),
        .Q(dout_i[85]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[86] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_36_41_n_3),
        .Q(dout_i[86]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[87] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_36_41_n_2),
        .Q(dout_i[87]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[88] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_36_41_n_5),
        .Q(dout_i[88]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[89] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_36_41_n_4),
        .Q(dout_i[89]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[8] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_9),
        .Q(dout_i[8]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[90] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_36_41_n_7),
        .Q(dout_i[90]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[91] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_36_41_n_6),
        .Q(dout_i[91]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[92] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_36_41_n_9),
        .Q(dout_i[92]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[93] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_36_41_n_8),
        .Q(dout_i[93]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[94] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_36_41_n_11),
        .Q(dout_i[94]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[95] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_36_41_n_10),
        .Q(dout_i[95]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[96] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_36_41_n_13),
        .Q(dout_i[96]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[97] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_36_41_n_12),
        .Q(dout_i[97]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[98] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_42_47_n_1),
        .Q(dout_i[98]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[99] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_42_47_n_0),
        .Q(dout_i[99]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[9] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_8),
        .Q(dout_i[9]),
        .R(1'b0));
endmodule

(* ORIG_REF_NAME = "dmem" *) 
module axi_clock_converter_dramslim_dmem__parameterized0
   (dout_i,
    s_aclk,
    ram_full_fb_i_reg,
    I133,
    \gc0.count_d1_reg[3] ,
    \gic0.gc0.count_d2_reg[3] ,
    \gpregsm1.curr_fwft_state_reg[1] ,
    m_aclk);
  output [72:0]dout_i;
  input s_aclk;
  input [0:0]ram_full_fb_i_reg;
  input [72:0]I133;
  input [3:0]\gc0.count_d1_reg[3] ;
  input [3:0]\gic0.gc0.count_d2_reg[3] ;
  input [0:0]\gpregsm1.curr_fwft_state_reg[1] ;
  input m_aclk;

  wire [72:0]I133;
  wire RAM_reg_0_15_0_5_n_0;
  wire RAM_reg_0_15_0_5_n_1;
  wire RAM_reg_0_15_0_5_n_10;
  wire RAM_reg_0_15_0_5_n_11;
  wire RAM_reg_0_15_0_5_n_12;
  wire RAM_reg_0_15_0_5_n_13;
  wire RAM_reg_0_15_0_5_n_2;
  wire RAM_reg_0_15_0_5_n_3;
  wire RAM_reg_0_15_0_5_n_4;
  wire RAM_reg_0_15_0_5_n_5;
  wire RAM_reg_0_15_0_5_n_6;
  wire RAM_reg_0_15_0_5_n_7;
  wire RAM_reg_0_15_0_5_n_8;
  wire RAM_reg_0_15_0_5_n_9;
  wire RAM_reg_0_15_12_17_n_0;
  wire RAM_reg_0_15_12_17_n_1;
  wire RAM_reg_0_15_12_17_n_10;
  wire RAM_reg_0_15_12_17_n_11;
  wire RAM_reg_0_15_12_17_n_12;
  wire RAM_reg_0_15_12_17_n_13;
  wire RAM_reg_0_15_12_17_n_2;
  wire RAM_reg_0_15_12_17_n_3;
  wire RAM_reg_0_15_12_17_n_4;
  wire RAM_reg_0_15_12_17_n_5;
  wire RAM_reg_0_15_12_17_n_6;
  wire RAM_reg_0_15_12_17_n_7;
  wire RAM_reg_0_15_12_17_n_8;
  wire RAM_reg_0_15_12_17_n_9;
  wire RAM_reg_0_15_18_23_n_0;
  wire RAM_reg_0_15_18_23_n_1;
  wire RAM_reg_0_15_18_23_n_10;
  wire RAM_reg_0_15_18_23_n_11;
  wire RAM_reg_0_15_18_23_n_12;
  wire RAM_reg_0_15_18_23_n_13;
  wire RAM_reg_0_15_18_23_n_2;
  wire RAM_reg_0_15_18_23_n_3;
  wire RAM_reg_0_15_18_23_n_4;
  wire RAM_reg_0_15_18_23_n_5;
  wire RAM_reg_0_15_18_23_n_6;
  wire RAM_reg_0_15_18_23_n_7;
  wire RAM_reg_0_15_18_23_n_8;
  wire RAM_reg_0_15_18_23_n_9;
  wire RAM_reg_0_15_24_29_n_0;
  wire RAM_reg_0_15_24_29_n_1;
  wire RAM_reg_0_15_24_29_n_10;
  wire RAM_reg_0_15_24_29_n_11;
  wire RAM_reg_0_15_24_29_n_12;
  wire RAM_reg_0_15_24_29_n_13;
  wire RAM_reg_0_15_24_29_n_2;
  wire RAM_reg_0_15_24_29_n_3;
  wire RAM_reg_0_15_24_29_n_4;
  wire RAM_reg_0_15_24_29_n_5;
  wire RAM_reg_0_15_24_29_n_6;
  wire RAM_reg_0_15_24_29_n_7;
  wire RAM_reg_0_15_24_29_n_8;
  wire RAM_reg_0_15_24_29_n_9;
  wire RAM_reg_0_15_30_35_n_0;
  wire RAM_reg_0_15_30_35_n_1;
  wire RAM_reg_0_15_30_35_n_3;
  wire RAM_reg_0_15_6_11_n_0;
  wire RAM_reg_0_15_6_11_n_1;
  wire RAM_reg_0_15_6_11_n_10;
  wire RAM_reg_0_15_6_11_n_11;
  wire RAM_reg_0_15_6_11_n_12;
  wire RAM_reg_0_15_6_11_n_13;
  wire RAM_reg_0_15_6_11_n_2;
  wire RAM_reg_0_15_6_11_n_3;
  wire RAM_reg_0_15_6_11_n_4;
  wire RAM_reg_0_15_6_11_n_5;
  wire RAM_reg_0_15_6_11_n_6;
  wire RAM_reg_0_15_6_11_n_7;
  wire RAM_reg_0_15_6_11_n_8;
  wire RAM_reg_0_15_6_11_n_9;
  wire [72:0]dout_i;
  wire [3:0]\gc0.count_d1_reg[3] ;
  wire [3:0]\gic0.gc0.count_d2_reg[3] ;
  wire [0:0]\gpregsm1.curr_fwft_state_reg[1] ;
  wire m_aclk;
  wire [0:0]ram_full_fb_i_reg;
  wire s_aclk;
  wire [1:0]NLW_RAM_reg_0_15_0_5_DOH_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_12_17_DOH_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_18_23_DOH_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_24_29_DOH_UNCONNECTED;
  wire [1:1]NLW_RAM_reg_0_15_30_35_DOB_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_30_35_DOC_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_30_35_DOD_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_30_35_DOE_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_30_35_DOF_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_30_35_DOG_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_30_35_DOH_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_6_11_DOH_UNCONNECTED;

  (* METHODOLOGY_DRC_VIOS = "" *) 
  RAM32M16 RAM_reg_0_15_0_5
       (.ADDRA({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRB({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRC({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRD({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRE({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRF({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRG({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRH({1'b0,\gic0.gc0.count_d2_reg[3] }),
        .DIA(I133[1:0]),
        .DIB(I133[3:2]),
        .DIC(I133[5:4]),
        .DID(I133[7:6]),
        .DIE(I133[9:8]),
        .DIF(I133[11:10]),
        .DIG(I133[13:12]),
        .DIH({1'b0,1'b0}),
        .DOA({RAM_reg_0_15_0_5_n_0,RAM_reg_0_15_0_5_n_1}),
        .DOB({RAM_reg_0_15_0_5_n_2,RAM_reg_0_15_0_5_n_3}),
        .DOC({RAM_reg_0_15_0_5_n_4,RAM_reg_0_15_0_5_n_5}),
        .DOD({RAM_reg_0_15_0_5_n_6,RAM_reg_0_15_0_5_n_7}),
        .DOE({RAM_reg_0_15_0_5_n_8,RAM_reg_0_15_0_5_n_9}),
        .DOF({RAM_reg_0_15_0_5_n_10,RAM_reg_0_15_0_5_n_11}),
        .DOG({RAM_reg_0_15_0_5_n_12,RAM_reg_0_15_0_5_n_13}),
        .DOH(NLW_RAM_reg_0_15_0_5_DOH_UNCONNECTED[1:0]),
        .WCLK(s_aclk),
        .WE(ram_full_fb_i_reg));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  RAM32M16 RAM_reg_0_15_12_17
       (.ADDRA({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRB({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRC({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRD({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRE({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRF({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRG({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRH({1'b0,\gic0.gc0.count_d2_reg[3] }),
        .DIA(I133[29:28]),
        .DIB(I133[31:30]),
        .DIC(I133[33:32]),
        .DID(I133[35:34]),
        .DIE(I133[37:36]),
        .DIF(I133[39:38]),
        .DIG(I133[41:40]),
        .DIH({1'b0,1'b0}),
        .DOA({RAM_reg_0_15_12_17_n_0,RAM_reg_0_15_12_17_n_1}),
        .DOB({RAM_reg_0_15_12_17_n_2,RAM_reg_0_15_12_17_n_3}),
        .DOC({RAM_reg_0_15_12_17_n_4,RAM_reg_0_15_12_17_n_5}),
        .DOD({RAM_reg_0_15_12_17_n_6,RAM_reg_0_15_12_17_n_7}),
        .DOE({RAM_reg_0_15_12_17_n_8,RAM_reg_0_15_12_17_n_9}),
        .DOF({RAM_reg_0_15_12_17_n_10,RAM_reg_0_15_12_17_n_11}),
        .DOG({RAM_reg_0_15_12_17_n_12,RAM_reg_0_15_12_17_n_13}),
        .DOH(NLW_RAM_reg_0_15_12_17_DOH_UNCONNECTED[1:0]),
        .WCLK(s_aclk),
        .WE(ram_full_fb_i_reg));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  RAM32M16 RAM_reg_0_15_18_23
       (.ADDRA({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRB({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRC({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRD({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRE({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRF({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRG({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRH({1'b0,\gic0.gc0.count_d2_reg[3] }),
        .DIA(I133[43:42]),
        .DIB(I133[45:44]),
        .DIC(I133[47:46]),
        .DID(I133[49:48]),
        .DIE(I133[51:50]),
        .DIF(I133[53:52]),
        .DIG(I133[55:54]),
        .DIH({1'b0,1'b0}),
        .DOA({RAM_reg_0_15_18_23_n_0,RAM_reg_0_15_18_23_n_1}),
        .DOB({RAM_reg_0_15_18_23_n_2,RAM_reg_0_15_18_23_n_3}),
        .DOC({RAM_reg_0_15_18_23_n_4,RAM_reg_0_15_18_23_n_5}),
        .DOD({RAM_reg_0_15_18_23_n_6,RAM_reg_0_15_18_23_n_7}),
        .DOE({RAM_reg_0_15_18_23_n_8,RAM_reg_0_15_18_23_n_9}),
        .DOF({RAM_reg_0_15_18_23_n_10,RAM_reg_0_15_18_23_n_11}),
        .DOG({RAM_reg_0_15_18_23_n_12,RAM_reg_0_15_18_23_n_13}),
        .DOH(NLW_RAM_reg_0_15_18_23_DOH_UNCONNECTED[1:0]),
        .WCLK(s_aclk),
        .WE(ram_full_fb_i_reg));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  RAM32M16 RAM_reg_0_15_24_29
       (.ADDRA({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRB({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRC({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRD({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRE({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRF({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRG({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRH({1'b0,\gic0.gc0.count_d2_reg[3] }),
        .DIA(I133[57:56]),
        .DIB(I133[59:58]),
        .DIC(I133[61:60]),
        .DID(I133[63:62]),
        .DIE(I133[65:64]),
        .DIF(I133[67:66]),
        .DIG(I133[69:68]),
        .DIH({1'b0,1'b0}),
        .DOA({RAM_reg_0_15_24_29_n_0,RAM_reg_0_15_24_29_n_1}),
        .DOB({RAM_reg_0_15_24_29_n_2,RAM_reg_0_15_24_29_n_3}),
        .DOC({RAM_reg_0_15_24_29_n_4,RAM_reg_0_15_24_29_n_5}),
        .DOD({RAM_reg_0_15_24_29_n_6,RAM_reg_0_15_24_29_n_7}),
        .DOE({RAM_reg_0_15_24_29_n_8,RAM_reg_0_15_24_29_n_9}),
        .DOF({RAM_reg_0_15_24_29_n_10,RAM_reg_0_15_24_29_n_11}),
        .DOG({RAM_reg_0_15_24_29_n_12,RAM_reg_0_15_24_29_n_13}),
        .DOH(NLW_RAM_reg_0_15_24_29_DOH_UNCONNECTED[1:0]),
        .WCLK(s_aclk),
        .WE(ram_full_fb_i_reg));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  RAM32M16 RAM_reg_0_15_30_35
       (.ADDRA({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRB({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRC({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRD({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRE({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRF({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRG({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRH({1'b0,\gic0.gc0.count_d2_reg[3] }),
        .DIA(I133[71:70]),
        .DIB({1'b0,I133[72]}),
        .DIC({1'b0,1'b0}),
        .DID({1'b0,1'b0}),
        .DIE({1'b0,1'b0}),
        .DIF({1'b0,1'b0}),
        .DIG({1'b0,1'b0}),
        .DIH({1'b0,1'b0}),
        .DOA({RAM_reg_0_15_30_35_n_0,RAM_reg_0_15_30_35_n_1}),
        .DOB({NLW_RAM_reg_0_15_30_35_DOB_UNCONNECTED[1],RAM_reg_0_15_30_35_n_3}),
        .DOC(NLW_RAM_reg_0_15_30_35_DOC_UNCONNECTED[1:0]),
        .DOD(NLW_RAM_reg_0_15_30_35_DOD_UNCONNECTED[1:0]),
        .DOE(NLW_RAM_reg_0_15_30_35_DOE_UNCONNECTED[1:0]),
        .DOF(NLW_RAM_reg_0_15_30_35_DOF_UNCONNECTED[1:0]),
        .DOG(NLW_RAM_reg_0_15_30_35_DOG_UNCONNECTED[1:0]),
        .DOH(NLW_RAM_reg_0_15_30_35_DOH_UNCONNECTED[1:0]),
        .WCLK(s_aclk),
        .WE(ram_full_fb_i_reg));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  RAM32M16 RAM_reg_0_15_6_11
       (.ADDRA({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRB({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRC({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRD({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRE({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRF({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRG({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRH({1'b0,\gic0.gc0.count_d2_reg[3] }),
        .DIA(I133[15:14]),
        .DIB(I133[17:16]),
        .DIC(I133[19:18]),
        .DID(I133[21:20]),
        .DIE(I133[23:22]),
        .DIF(I133[25:24]),
        .DIG(I133[27:26]),
        .DIH({1'b0,1'b0}),
        .DOA({RAM_reg_0_15_6_11_n_0,RAM_reg_0_15_6_11_n_1}),
        .DOB({RAM_reg_0_15_6_11_n_2,RAM_reg_0_15_6_11_n_3}),
        .DOC({RAM_reg_0_15_6_11_n_4,RAM_reg_0_15_6_11_n_5}),
        .DOD({RAM_reg_0_15_6_11_n_6,RAM_reg_0_15_6_11_n_7}),
        .DOE({RAM_reg_0_15_6_11_n_8,RAM_reg_0_15_6_11_n_9}),
        .DOF({RAM_reg_0_15_6_11_n_10,RAM_reg_0_15_6_11_n_11}),
        .DOG({RAM_reg_0_15_6_11_n_12,RAM_reg_0_15_6_11_n_13}),
        .DOH(NLW_RAM_reg_0_15_6_11_DOH_UNCONNECTED[1:0]),
        .WCLK(s_aclk),
        .WE(ram_full_fb_i_reg));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[0] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_1),
        .Q(dout_i[0]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[10] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_11),
        .Q(dout_i[10]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[11] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_10),
        .Q(dout_i[11]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[12] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_13),
        .Q(dout_i[12]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[13] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_12),
        .Q(dout_i[13]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[14] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_1),
        .Q(dout_i[14]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[15] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_0),
        .Q(dout_i[15]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[16] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_3),
        .Q(dout_i[16]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[17] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_2),
        .Q(dout_i[17]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[18] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_5),
        .Q(dout_i[18]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[19] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_4),
        .Q(dout_i[19]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[1] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_0),
        .Q(dout_i[1]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[20] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_7),
        .Q(dout_i[20]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[21] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_6),
        .Q(dout_i[21]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[22] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_9),
        .Q(dout_i[22]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[23] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_8),
        .Q(dout_i[23]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[24] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_11),
        .Q(dout_i[24]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[25] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_10),
        .Q(dout_i[25]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[26] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_13),
        .Q(dout_i[26]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[27] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_12),
        .Q(dout_i[27]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[28] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_1),
        .Q(dout_i[28]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[29] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_0),
        .Q(dout_i[29]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[2] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_3),
        .Q(dout_i[2]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[30] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_3),
        .Q(dout_i[30]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[31] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_2),
        .Q(dout_i[31]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[32] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_5),
        .Q(dout_i[32]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[33] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_4),
        .Q(dout_i[33]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[34] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_7),
        .Q(dout_i[34]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[35] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_6),
        .Q(dout_i[35]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[36] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_9),
        .Q(dout_i[36]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[37] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_8),
        .Q(dout_i[37]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[38] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_11),
        .Q(dout_i[38]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[39] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_10),
        .Q(dout_i[39]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[3] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_2),
        .Q(dout_i[3]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[40] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_13),
        .Q(dout_i[40]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[41] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_12),
        .Q(dout_i[41]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[42] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_1),
        .Q(dout_i[42]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[43] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_0),
        .Q(dout_i[43]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[44] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_3),
        .Q(dout_i[44]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[45] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_2),
        .Q(dout_i[45]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[46] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_5),
        .Q(dout_i[46]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[47] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_4),
        .Q(dout_i[47]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[48] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_7),
        .Q(dout_i[48]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[49] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_6),
        .Q(dout_i[49]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[4] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_5),
        .Q(dout_i[4]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[50] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_9),
        .Q(dout_i[50]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[51] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_8),
        .Q(dout_i[51]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[52] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_11),
        .Q(dout_i[52]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[53] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_10),
        .Q(dout_i[53]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[54] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_13),
        .Q(dout_i[54]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[55] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_12),
        .Q(dout_i[55]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[56] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_1),
        .Q(dout_i[56]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[57] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_0),
        .Q(dout_i[57]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[58] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_3),
        .Q(dout_i[58]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[59] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_2),
        .Q(dout_i[59]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[5] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_4),
        .Q(dout_i[5]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[60] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_5),
        .Q(dout_i[60]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[61] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_4),
        .Q(dout_i[61]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[62] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_7),
        .Q(dout_i[62]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[63] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_6),
        .Q(dout_i[63]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[64] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_9),
        .Q(dout_i[64]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[65] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_8),
        .Q(dout_i[65]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[66] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_11),
        .Q(dout_i[66]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[67] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_10),
        .Q(dout_i[67]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[68] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_13),
        .Q(dout_i[68]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[69] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_12),
        .Q(dout_i[69]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[6] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_7),
        .Q(dout_i[6]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[70] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_1),
        .Q(dout_i[70]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[71] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_0),
        .Q(dout_i[71]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[72] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_3),
        .Q(dout_i[72]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[7] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_6),
        .Q(dout_i[7]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[8] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_9),
        .Q(dout_i[8]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[9] 
       (.C(m_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_8),
        .Q(dout_i[9]),
        .R(1'b0));
endmodule

(* ORIG_REF_NAME = "dmem" *) 
module axi_clock_converter_dramslim_dmem__parameterized1
   (dout_i,
    m_aclk,
    I118,
    I137,
    \gc0.count_d1_reg[3] ,
    count_d2,
    \gpregsm1.curr_fwft_state_reg[1] ,
    s_aclk);
  output [17:0]dout_i;
  input m_aclk;
  input I118;
  input [17:0]I137;
  input [3:0]\gc0.count_d1_reg[3] ;
  input [3:0]count_d2;
  input [0:0]\gpregsm1.curr_fwft_state_reg[1] ;
  input s_aclk;

  wire I118;
  wire [17:0]I137;
  wire RAM_reg_0_15_0_5_n_0;
  wire RAM_reg_0_15_0_5_n_1;
  wire RAM_reg_0_15_0_5_n_10;
  wire RAM_reg_0_15_0_5_n_11;
  wire RAM_reg_0_15_0_5_n_12;
  wire RAM_reg_0_15_0_5_n_13;
  wire RAM_reg_0_15_0_5_n_2;
  wire RAM_reg_0_15_0_5_n_3;
  wire RAM_reg_0_15_0_5_n_4;
  wire RAM_reg_0_15_0_5_n_5;
  wire RAM_reg_0_15_0_5_n_6;
  wire RAM_reg_0_15_0_5_n_7;
  wire RAM_reg_0_15_0_5_n_8;
  wire RAM_reg_0_15_0_5_n_9;
  wire RAM_reg_0_15_6_11_n_0;
  wire RAM_reg_0_15_6_11_n_1;
  wire RAM_reg_0_15_6_11_n_2;
  wire RAM_reg_0_15_6_11_n_3;
  wire [3:0]count_d2;
  wire [17:0]dout_i;
  wire [3:0]\gc0.count_d1_reg[3] ;
  wire [0:0]\gpregsm1.curr_fwft_state_reg[1] ;
  wire m_aclk;
  wire s_aclk;
  wire [1:0]NLW_RAM_reg_0_15_0_5_DOH_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_6_11_DOC_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_6_11_DOD_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_6_11_DOE_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_6_11_DOF_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_6_11_DOG_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_6_11_DOH_UNCONNECTED;

  (* METHODOLOGY_DRC_VIOS = "" *) 
  RAM32M16 RAM_reg_0_15_0_5
       (.ADDRA({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRB({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRC({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRD({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRE({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRF({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRG({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRH({1'b0,count_d2}),
        .DIA(I137[1:0]),
        .DIB(I137[3:2]),
        .DIC(I137[5:4]),
        .DID(I137[7:6]),
        .DIE(I137[9:8]),
        .DIF(I137[11:10]),
        .DIG(I137[13:12]),
        .DIH({1'b0,1'b0}),
        .DOA({RAM_reg_0_15_0_5_n_0,RAM_reg_0_15_0_5_n_1}),
        .DOB({RAM_reg_0_15_0_5_n_2,RAM_reg_0_15_0_5_n_3}),
        .DOC({RAM_reg_0_15_0_5_n_4,RAM_reg_0_15_0_5_n_5}),
        .DOD({RAM_reg_0_15_0_5_n_6,RAM_reg_0_15_0_5_n_7}),
        .DOE({RAM_reg_0_15_0_5_n_8,RAM_reg_0_15_0_5_n_9}),
        .DOF({RAM_reg_0_15_0_5_n_10,RAM_reg_0_15_0_5_n_11}),
        .DOG({RAM_reg_0_15_0_5_n_12,RAM_reg_0_15_0_5_n_13}),
        .DOH(NLW_RAM_reg_0_15_0_5_DOH_UNCONNECTED[1:0]),
        .WCLK(m_aclk),
        .WE(I118));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  RAM32M16 RAM_reg_0_15_6_11
       (.ADDRA({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRB({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRC({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRD({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRE({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRF({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRG({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRH({1'b0,count_d2}),
        .DIA(I137[15:14]),
        .DIB(I137[17:16]),
        .DIC({1'b0,1'b0}),
        .DID({1'b0,1'b0}),
        .DIE({1'b0,1'b0}),
        .DIF({1'b0,1'b0}),
        .DIG({1'b0,1'b0}),
        .DIH({1'b0,1'b0}),
        .DOA({RAM_reg_0_15_6_11_n_0,RAM_reg_0_15_6_11_n_1}),
        .DOB({RAM_reg_0_15_6_11_n_2,RAM_reg_0_15_6_11_n_3}),
        .DOC(NLW_RAM_reg_0_15_6_11_DOC_UNCONNECTED[1:0]),
        .DOD(NLW_RAM_reg_0_15_6_11_DOD_UNCONNECTED[1:0]),
        .DOE(NLW_RAM_reg_0_15_6_11_DOE_UNCONNECTED[1:0]),
        .DOF(NLW_RAM_reg_0_15_6_11_DOF_UNCONNECTED[1:0]),
        .DOG(NLW_RAM_reg_0_15_6_11_DOG_UNCONNECTED[1:0]),
        .DOH(NLW_RAM_reg_0_15_6_11_DOH_UNCONNECTED[1:0]),
        .WCLK(m_aclk),
        .WE(I118));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[0] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_1),
        .Q(dout_i[0]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[10] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_11),
        .Q(dout_i[10]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[11] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_10),
        .Q(dout_i[11]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[12] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_13),
        .Q(dout_i[12]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[13] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_12),
        .Q(dout_i[13]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[14] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_1),
        .Q(dout_i[14]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[15] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_0),
        .Q(dout_i[15]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[16] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_3),
        .Q(dout_i[16]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[17] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_2),
        .Q(dout_i[17]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[1] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_0),
        .Q(dout_i[1]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[2] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_3),
        .Q(dout_i[2]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[3] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_2),
        .Q(dout_i[3]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[4] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_5),
        .Q(dout_i[4]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[5] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_4),
        .Q(dout_i[5]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[6] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_7),
        .Q(dout_i[6]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[7] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_6),
        .Q(dout_i[7]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[8] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_9),
        .Q(dout_i[8]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[9] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_8),
        .Q(dout_i[9]),
        .R(1'b0));
endmodule

(* ORIG_REF_NAME = "dmem" *) 
module axi_clock_converter_dramslim_dmem__parameterized2
   (dout_i,
    m_aclk,
    ram_full_fb_i_reg,
    I145,
    \gc0.count_d1_reg[3] ,
    \gic0.gc0.count_d2_reg[3] ,
    \gpregsm1.curr_fwft_state_reg[1] ,
    s_aclk);
  output [82:0]dout_i;
  input m_aclk;
  input [0:0]ram_full_fb_i_reg;
  input [82:0]I145;
  input [3:0]\gc0.count_d1_reg[3] ;
  input [3:0]\gic0.gc0.count_d2_reg[3] ;
  input [0:0]\gpregsm1.curr_fwft_state_reg[1] ;
  input s_aclk;

  wire [82:0]I145;
  wire RAM_reg_0_15_0_5_n_0;
  wire RAM_reg_0_15_0_5_n_1;
  wire RAM_reg_0_15_0_5_n_10;
  wire RAM_reg_0_15_0_5_n_11;
  wire RAM_reg_0_15_0_5_n_12;
  wire RAM_reg_0_15_0_5_n_13;
  wire RAM_reg_0_15_0_5_n_2;
  wire RAM_reg_0_15_0_5_n_3;
  wire RAM_reg_0_15_0_5_n_4;
  wire RAM_reg_0_15_0_5_n_5;
  wire RAM_reg_0_15_0_5_n_6;
  wire RAM_reg_0_15_0_5_n_7;
  wire RAM_reg_0_15_0_5_n_8;
  wire RAM_reg_0_15_0_5_n_9;
  wire RAM_reg_0_15_12_17_n_0;
  wire RAM_reg_0_15_12_17_n_1;
  wire RAM_reg_0_15_12_17_n_10;
  wire RAM_reg_0_15_12_17_n_11;
  wire RAM_reg_0_15_12_17_n_12;
  wire RAM_reg_0_15_12_17_n_13;
  wire RAM_reg_0_15_12_17_n_2;
  wire RAM_reg_0_15_12_17_n_3;
  wire RAM_reg_0_15_12_17_n_4;
  wire RAM_reg_0_15_12_17_n_5;
  wire RAM_reg_0_15_12_17_n_6;
  wire RAM_reg_0_15_12_17_n_7;
  wire RAM_reg_0_15_12_17_n_8;
  wire RAM_reg_0_15_12_17_n_9;
  wire RAM_reg_0_15_18_23_n_0;
  wire RAM_reg_0_15_18_23_n_1;
  wire RAM_reg_0_15_18_23_n_10;
  wire RAM_reg_0_15_18_23_n_11;
  wire RAM_reg_0_15_18_23_n_12;
  wire RAM_reg_0_15_18_23_n_13;
  wire RAM_reg_0_15_18_23_n_2;
  wire RAM_reg_0_15_18_23_n_3;
  wire RAM_reg_0_15_18_23_n_4;
  wire RAM_reg_0_15_18_23_n_5;
  wire RAM_reg_0_15_18_23_n_6;
  wire RAM_reg_0_15_18_23_n_7;
  wire RAM_reg_0_15_18_23_n_8;
  wire RAM_reg_0_15_18_23_n_9;
  wire RAM_reg_0_15_24_29_n_0;
  wire RAM_reg_0_15_24_29_n_1;
  wire RAM_reg_0_15_24_29_n_10;
  wire RAM_reg_0_15_24_29_n_11;
  wire RAM_reg_0_15_24_29_n_12;
  wire RAM_reg_0_15_24_29_n_13;
  wire RAM_reg_0_15_24_29_n_2;
  wire RAM_reg_0_15_24_29_n_3;
  wire RAM_reg_0_15_24_29_n_4;
  wire RAM_reg_0_15_24_29_n_5;
  wire RAM_reg_0_15_24_29_n_6;
  wire RAM_reg_0_15_24_29_n_7;
  wire RAM_reg_0_15_24_29_n_8;
  wire RAM_reg_0_15_24_29_n_9;
  wire RAM_reg_0_15_30_35_n_0;
  wire RAM_reg_0_15_30_35_n_1;
  wire RAM_reg_0_15_30_35_n_10;
  wire RAM_reg_0_15_30_35_n_11;
  wire RAM_reg_0_15_30_35_n_13;
  wire RAM_reg_0_15_30_35_n_2;
  wire RAM_reg_0_15_30_35_n_3;
  wire RAM_reg_0_15_30_35_n_4;
  wire RAM_reg_0_15_30_35_n_5;
  wire RAM_reg_0_15_30_35_n_6;
  wire RAM_reg_0_15_30_35_n_7;
  wire RAM_reg_0_15_30_35_n_8;
  wire RAM_reg_0_15_30_35_n_9;
  wire RAM_reg_0_15_6_11_n_0;
  wire RAM_reg_0_15_6_11_n_1;
  wire RAM_reg_0_15_6_11_n_10;
  wire RAM_reg_0_15_6_11_n_11;
  wire RAM_reg_0_15_6_11_n_12;
  wire RAM_reg_0_15_6_11_n_13;
  wire RAM_reg_0_15_6_11_n_2;
  wire RAM_reg_0_15_6_11_n_3;
  wire RAM_reg_0_15_6_11_n_4;
  wire RAM_reg_0_15_6_11_n_5;
  wire RAM_reg_0_15_6_11_n_6;
  wire RAM_reg_0_15_6_11_n_7;
  wire RAM_reg_0_15_6_11_n_8;
  wire RAM_reg_0_15_6_11_n_9;
  wire [82:0]dout_i;
  wire [3:0]\gc0.count_d1_reg[3] ;
  wire [3:0]\gic0.gc0.count_d2_reg[3] ;
  wire [0:0]\gpregsm1.curr_fwft_state_reg[1] ;
  wire m_aclk;
  wire [0:0]ram_full_fb_i_reg;
  wire s_aclk;
  wire [1:0]NLW_RAM_reg_0_15_0_5_DOH_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_12_17_DOH_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_18_23_DOH_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_24_29_DOH_UNCONNECTED;
  wire [1:1]NLW_RAM_reg_0_15_30_35_DOG_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_30_35_DOH_UNCONNECTED;
  wire [1:0]NLW_RAM_reg_0_15_6_11_DOH_UNCONNECTED;

  (* METHODOLOGY_DRC_VIOS = "" *) 
  RAM32M16 RAM_reg_0_15_0_5
       (.ADDRA({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRB({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRC({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRD({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRE({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRF({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRG({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRH({1'b0,\gic0.gc0.count_d2_reg[3] }),
        .DIA(I145[1:0]),
        .DIB(I145[3:2]),
        .DIC(I145[5:4]),
        .DID(I145[7:6]),
        .DIE(I145[9:8]),
        .DIF(I145[11:10]),
        .DIG(I145[13:12]),
        .DIH({1'b0,1'b0}),
        .DOA({RAM_reg_0_15_0_5_n_0,RAM_reg_0_15_0_5_n_1}),
        .DOB({RAM_reg_0_15_0_5_n_2,RAM_reg_0_15_0_5_n_3}),
        .DOC({RAM_reg_0_15_0_5_n_4,RAM_reg_0_15_0_5_n_5}),
        .DOD({RAM_reg_0_15_0_5_n_6,RAM_reg_0_15_0_5_n_7}),
        .DOE({RAM_reg_0_15_0_5_n_8,RAM_reg_0_15_0_5_n_9}),
        .DOF({RAM_reg_0_15_0_5_n_10,RAM_reg_0_15_0_5_n_11}),
        .DOG({RAM_reg_0_15_0_5_n_12,RAM_reg_0_15_0_5_n_13}),
        .DOH(NLW_RAM_reg_0_15_0_5_DOH_UNCONNECTED[1:0]),
        .WCLK(m_aclk),
        .WE(ram_full_fb_i_reg));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  RAM32M16 RAM_reg_0_15_12_17
       (.ADDRA({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRB({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRC({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRD({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRE({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRF({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRG({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRH({1'b0,\gic0.gc0.count_d2_reg[3] }),
        .DIA(I145[29:28]),
        .DIB(I145[31:30]),
        .DIC(I145[33:32]),
        .DID(I145[35:34]),
        .DIE(I145[37:36]),
        .DIF(I145[39:38]),
        .DIG(I145[41:40]),
        .DIH({1'b0,1'b0}),
        .DOA({RAM_reg_0_15_12_17_n_0,RAM_reg_0_15_12_17_n_1}),
        .DOB({RAM_reg_0_15_12_17_n_2,RAM_reg_0_15_12_17_n_3}),
        .DOC({RAM_reg_0_15_12_17_n_4,RAM_reg_0_15_12_17_n_5}),
        .DOD({RAM_reg_0_15_12_17_n_6,RAM_reg_0_15_12_17_n_7}),
        .DOE({RAM_reg_0_15_12_17_n_8,RAM_reg_0_15_12_17_n_9}),
        .DOF({RAM_reg_0_15_12_17_n_10,RAM_reg_0_15_12_17_n_11}),
        .DOG({RAM_reg_0_15_12_17_n_12,RAM_reg_0_15_12_17_n_13}),
        .DOH(NLW_RAM_reg_0_15_12_17_DOH_UNCONNECTED[1:0]),
        .WCLK(m_aclk),
        .WE(ram_full_fb_i_reg));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  RAM32M16 RAM_reg_0_15_18_23
       (.ADDRA({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRB({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRC({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRD({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRE({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRF({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRG({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRH({1'b0,\gic0.gc0.count_d2_reg[3] }),
        .DIA(I145[43:42]),
        .DIB(I145[45:44]),
        .DIC(I145[47:46]),
        .DID(I145[49:48]),
        .DIE(I145[51:50]),
        .DIF(I145[53:52]),
        .DIG(I145[55:54]),
        .DIH({1'b0,1'b0}),
        .DOA({RAM_reg_0_15_18_23_n_0,RAM_reg_0_15_18_23_n_1}),
        .DOB({RAM_reg_0_15_18_23_n_2,RAM_reg_0_15_18_23_n_3}),
        .DOC({RAM_reg_0_15_18_23_n_4,RAM_reg_0_15_18_23_n_5}),
        .DOD({RAM_reg_0_15_18_23_n_6,RAM_reg_0_15_18_23_n_7}),
        .DOE({RAM_reg_0_15_18_23_n_8,RAM_reg_0_15_18_23_n_9}),
        .DOF({RAM_reg_0_15_18_23_n_10,RAM_reg_0_15_18_23_n_11}),
        .DOG({RAM_reg_0_15_18_23_n_12,RAM_reg_0_15_18_23_n_13}),
        .DOH(NLW_RAM_reg_0_15_18_23_DOH_UNCONNECTED[1:0]),
        .WCLK(m_aclk),
        .WE(ram_full_fb_i_reg));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  RAM32M16 RAM_reg_0_15_24_29
       (.ADDRA({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRB({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRC({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRD({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRE({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRF({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRG({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRH({1'b0,\gic0.gc0.count_d2_reg[3] }),
        .DIA(I145[57:56]),
        .DIB(I145[59:58]),
        .DIC(I145[61:60]),
        .DID(I145[63:62]),
        .DIE(I145[65:64]),
        .DIF(I145[67:66]),
        .DIG(I145[69:68]),
        .DIH({1'b0,1'b0}),
        .DOA({RAM_reg_0_15_24_29_n_0,RAM_reg_0_15_24_29_n_1}),
        .DOB({RAM_reg_0_15_24_29_n_2,RAM_reg_0_15_24_29_n_3}),
        .DOC({RAM_reg_0_15_24_29_n_4,RAM_reg_0_15_24_29_n_5}),
        .DOD({RAM_reg_0_15_24_29_n_6,RAM_reg_0_15_24_29_n_7}),
        .DOE({RAM_reg_0_15_24_29_n_8,RAM_reg_0_15_24_29_n_9}),
        .DOF({RAM_reg_0_15_24_29_n_10,RAM_reg_0_15_24_29_n_11}),
        .DOG({RAM_reg_0_15_24_29_n_12,RAM_reg_0_15_24_29_n_13}),
        .DOH(NLW_RAM_reg_0_15_24_29_DOH_UNCONNECTED[1:0]),
        .WCLK(m_aclk),
        .WE(ram_full_fb_i_reg));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  RAM32M16 RAM_reg_0_15_30_35
       (.ADDRA({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRB({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRC({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRD({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRE({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRF({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRG({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRH({1'b0,\gic0.gc0.count_d2_reg[3] }),
        .DIA(I145[71:70]),
        .DIB(I145[73:72]),
        .DIC(I145[75:74]),
        .DID(I145[77:76]),
        .DIE(I145[79:78]),
        .DIF(I145[81:80]),
        .DIG({1'b0,I145[82]}),
        .DIH({1'b0,1'b0}),
        .DOA({RAM_reg_0_15_30_35_n_0,RAM_reg_0_15_30_35_n_1}),
        .DOB({RAM_reg_0_15_30_35_n_2,RAM_reg_0_15_30_35_n_3}),
        .DOC({RAM_reg_0_15_30_35_n_4,RAM_reg_0_15_30_35_n_5}),
        .DOD({RAM_reg_0_15_30_35_n_6,RAM_reg_0_15_30_35_n_7}),
        .DOE({RAM_reg_0_15_30_35_n_8,RAM_reg_0_15_30_35_n_9}),
        .DOF({RAM_reg_0_15_30_35_n_10,RAM_reg_0_15_30_35_n_11}),
        .DOG({NLW_RAM_reg_0_15_30_35_DOG_UNCONNECTED[1],RAM_reg_0_15_30_35_n_13}),
        .DOH(NLW_RAM_reg_0_15_30_35_DOH_UNCONNECTED[1:0]),
        .WCLK(m_aclk),
        .WE(ram_full_fb_i_reg));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  RAM32M16 RAM_reg_0_15_6_11
       (.ADDRA({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRB({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRC({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRD({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRE({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRF({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRG({1'b0,\gc0.count_d1_reg[3] }),
        .ADDRH({1'b0,\gic0.gc0.count_d2_reg[3] }),
        .DIA(I145[15:14]),
        .DIB(I145[17:16]),
        .DIC(I145[19:18]),
        .DID(I145[21:20]),
        .DIE(I145[23:22]),
        .DIF(I145[25:24]),
        .DIG(I145[27:26]),
        .DIH({1'b0,1'b0}),
        .DOA({RAM_reg_0_15_6_11_n_0,RAM_reg_0_15_6_11_n_1}),
        .DOB({RAM_reg_0_15_6_11_n_2,RAM_reg_0_15_6_11_n_3}),
        .DOC({RAM_reg_0_15_6_11_n_4,RAM_reg_0_15_6_11_n_5}),
        .DOD({RAM_reg_0_15_6_11_n_6,RAM_reg_0_15_6_11_n_7}),
        .DOE({RAM_reg_0_15_6_11_n_8,RAM_reg_0_15_6_11_n_9}),
        .DOF({RAM_reg_0_15_6_11_n_10,RAM_reg_0_15_6_11_n_11}),
        .DOG({RAM_reg_0_15_6_11_n_12,RAM_reg_0_15_6_11_n_13}),
        .DOH(NLW_RAM_reg_0_15_6_11_DOH_UNCONNECTED[1:0]),
        .WCLK(m_aclk),
        .WE(ram_full_fb_i_reg));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[0] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_1),
        .Q(dout_i[0]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[10] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_11),
        .Q(dout_i[10]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[11] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_10),
        .Q(dout_i[11]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[12] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_13),
        .Q(dout_i[12]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[13] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_12),
        .Q(dout_i[13]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[14] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_1),
        .Q(dout_i[14]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[15] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_0),
        .Q(dout_i[15]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[16] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_3),
        .Q(dout_i[16]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[17] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_2),
        .Q(dout_i[17]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[18] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_5),
        .Q(dout_i[18]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[19] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_4),
        .Q(dout_i[19]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[1] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_0),
        .Q(dout_i[1]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[20] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_7),
        .Q(dout_i[20]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[21] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_6),
        .Q(dout_i[21]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[22] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_9),
        .Q(dout_i[22]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[23] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_8),
        .Q(dout_i[23]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[24] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_11),
        .Q(dout_i[24]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[25] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_10),
        .Q(dout_i[25]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[26] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_13),
        .Q(dout_i[26]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[27] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_6_11_n_12),
        .Q(dout_i[27]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[28] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_1),
        .Q(dout_i[28]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[29] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_0),
        .Q(dout_i[29]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[2] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_3),
        .Q(dout_i[2]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[30] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_3),
        .Q(dout_i[30]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[31] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_2),
        .Q(dout_i[31]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[32] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_5),
        .Q(dout_i[32]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[33] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_4),
        .Q(dout_i[33]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[34] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_7),
        .Q(dout_i[34]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[35] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_6),
        .Q(dout_i[35]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[36] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_9),
        .Q(dout_i[36]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[37] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_8),
        .Q(dout_i[37]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[38] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_11),
        .Q(dout_i[38]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[39] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_10),
        .Q(dout_i[39]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[3] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_2),
        .Q(dout_i[3]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[40] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_13),
        .Q(dout_i[40]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[41] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_12_17_n_12),
        .Q(dout_i[41]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[42] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_1),
        .Q(dout_i[42]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[43] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_0),
        .Q(dout_i[43]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[44] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_3),
        .Q(dout_i[44]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[45] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_2),
        .Q(dout_i[45]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[46] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_5),
        .Q(dout_i[46]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[47] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_4),
        .Q(dout_i[47]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[48] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_7),
        .Q(dout_i[48]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[49] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_6),
        .Q(dout_i[49]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[4] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_5),
        .Q(dout_i[4]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[50] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_9),
        .Q(dout_i[50]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[51] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_8),
        .Q(dout_i[51]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[52] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_11),
        .Q(dout_i[52]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[53] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_10),
        .Q(dout_i[53]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[54] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_13),
        .Q(dout_i[54]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[55] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_18_23_n_12),
        .Q(dout_i[55]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[56] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_1),
        .Q(dout_i[56]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[57] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_0),
        .Q(dout_i[57]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[58] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_3),
        .Q(dout_i[58]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[59] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_2),
        .Q(dout_i[59]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[5] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_4),
        .Q(dout_i[5]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[60] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_5),
        .Q(dout_i[60]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[61] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_4),
        .Q(dout_i[61]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[62] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_7),
        .Q(dout_i[62]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[63] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_6),
        .Q(dout_i[63]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[64] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_9),
        .Q(dout_i[64]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[65] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_8),
        .Q(dout_i[65]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[66] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_11),
        .Q(dout_i[66]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[67] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_10),
        .Q(dout_i[67]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[68] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_13),
        .Q(dout_i[68]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[69] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_24_29_n_12),
        .Q(dout_i[69]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[6] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_7),
        .Q(dout_i[6]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[70] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_1),
        .Q(dout_i[70]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[71] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_0),
        .Q(dout_i[71]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[72] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_3),
        .Q(dout_i[72]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[73] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_2),
        .Q(dout_i[73]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[74] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_5),
        .Q(dout_i[74]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[75] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_4),
        .Q(dout_i[75]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[76] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_7),
        .Q(dout_i[76]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[77] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_6),
        .Q(dout_i[77]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[78] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_9),
        .Q(dout_i[78]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[79] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_8),
        .Q(dout_i[79]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[7] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_6),
        .Q(dout_i[7]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[80] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_11),
        .Q(dout_i[80]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[81] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_10),
        .Q(dout_i[81]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[82] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_30_35_n_13),
        .Q(dout_i[82]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[8] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_9),
        .Q(dout_i[8]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \gpr1.dout_i_reg[9] 
       (.C(s_aclk),
        .CE(\gpregsm1.curr_fwft_state_reg[1] ),
        .D(RAM_reg_0_15_0_5_n_8),
        .Q(dout_i[9]),
        .R(1'b0));
endmodule

(* ORIG_REF_NAME = "fifo_generator_ramfifo" *) 
module axi_clock_converter_dramslim_fifo_generator_ramfifo
   (s_axi_awready,
    m_axi_awvalid,
    Q,
    m_aclk,
    s_aclk,
    inverted_reset,
    m_axi_awready,
    s_axi_awvalid,
    DI);
  output s_axi_awready;
  output m_axi_awvalid;
  output [108:0]Q;
  input m_aclk;
  input s_aclk;
  input inverted_reset;
  input m_axi_awready;
  input s_axi_awvalid;
  input [108:0]DI;

  wire [108:0]DI;
  wire [108:0]Q;
  wire \gntv_or_sync_fifo.gcx.clkx_n_4 ;
  wire \gntv_or_sync_fifo.gcx.clkx_n_9 ;
  wire \gntv_or_sync_fifo.gl0.rd_n_4 ;
  wire \gntv_or_sync_fifo.gl0.rd_n_5 ;
  wire \gntv_or_sync_fifo.gl0.rd_n_6 ;
  wire \gntv_or_sync_fifo.gl0.rd_n_7 ;
  wire \gntv_or_sync_fifo.gl0.wr_n_3 ;
  wire [0:0]gray2bin;
  wire inverted_reset;
  wire m_aclk;
  wire m_axi_awready;
  wire m_axi_awvalid;
  wire [3:0]p_0_out_0;
  wire [3:0]p_12_out;
  wire [3:0]p_13_out;
  wire p_18_out;
  wire [3:0]p_22_out;
  wire p_23_out;
  wire [3:3]p_23_out_1;
  wire [3:0]p_7_out;
  wire ram_rd_en_i;
  wire [2:0]rd_pntr_plus1;
  wire [2:0]rd_rst_i;
  wire rst_full_ff_i;
  wire s_aclk;
  wire s_axi_awready;
  wire s_axi_awvalid;
  wire [2:0]wr_pntr_plus2;
  wire [1:0]wr_rst_i;

  axi_clock_converter_dramslim_clk_x_pntrs_32 \gntv_or_sync_fifo.gcx.clkx 
       (.AR(wr_rst_i[0]),
        .D(gray2bin),
        .Q(p_22_out),
        .\gc0.count_d1_reg[2] ({\gntv_or_sync_fifo.gl0.rd_n_5 ,\gntv_or_sync_fifo.gl0.rd_n_6 ,\gntv_or_sync_fifo.gl0.rd_n_7 }),
        .\gc0.count_d1_reg[3] (p_0_out_0[3]),
        .\gc0.count_reg[2] (rd_pntr_plus1),
        .\gic0.gc0.count_d1_reg[3] (p_13_out),
        .\gic0.gc0.count_d2_reg[3] (p_12_out),
        .\gic0.gc0.count_reg[2] (wr_pntr_plus2),
        .\grstd1.grst_full.grst_f.rst_d3_reg (p_23_out),
        .m_aclk(m_aclk),
        .\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] (rd_rst_i[1]),
        .out(p_7_out),
        .ram_empty_i_reg(\gntv_or_sync_fifo.gcx.clkx_n_4 ),
        .ram_full_fb_i_reg(\gntv_or_sync_fifo.gcx.clkx_n_9 ),
        .ram_full_fb_i_reg_0(p_23_out_1),
        .ram_full_fb_i_reg_1(\gntv_or_sync_fifo.gl0.wr_n_3 ),
        .s_aclk(s_aclk));
  LUT4 #(
    .INIT(16'h6996)) 
    \gntv_or_sync_fifo.gcx.clkx/ 
       (.I0(p_7_out[1]),
        .I1(p_7_out[0]),
        .I2(p_7_out[3]),
        .I3(p_7_out[2]),
        .O(gray2bin));
  axi_clock_converter_dramslim_rd_logic_33 \gntv_or_sync_fifo.gl0.rd 
       (.E(ram_rd_en_i),
        .Q(rd_pntr_plus1),
        .\gnxpm_cdc.rd_pntr_gc_reg[2] ({\gntv_or_sync_fifo.gl0.rd_n_5 ,\gntv_or_sync_fifo.gl0.rd_n_6 ,\gntv_or_sync_fifo.gl0.rd_n_7 }),
        .\gnxpm_cdc.rd_pntr_gc_reg[3] (p_0_out_0),
        .\gnxpm_cdc.wr_pntr_bin_reg[2] (\gntv_or_sync_fifo.gcx.clkx_n_4 ),
        .\gnxpm_cdc.wr_pntr_bin_reg[3] (p_22_out),
        .\goreg_dm.dout_i_reg[108] (\gntv_or_sync_fifo.gl0.rd_n_4 ),
        .m_aclk(m_aclk),
        .m_axi_awready(m_axi_awready),
        .m_axi_awvalid(m_axi_awvalid),
        .out({rd_rst_i[2],rd_rst_i[0]}));
  axi_clock_converter_dramslim_wr_logic_34 \gntv_or_sync_fifo.gl0.wr 
       (.AR(wr_rst_i[1]),
        .E(p_18_out),
        .Q(wr_pntr_plus2),
        .\gic0.gc0.count_d1_reg[3] (\gntv_or_sync_fifo.gcx.clkx_n_9 ),
        .\gic0.gc0.count_d2_reg[3] (p_13_out),
        .\gnxpm_cdc.rd_pntr_bin_reg[3] (p_23_out_1),
        .\gnxpm_cdc.wr_pntr_gc_reg[3] (p_12_out),
        .out(rst_full_ff_i),
        .ram_full_fb_i_reg(\gntv_or_sync_fifo.gl0.wr_n_3 ),
        .s_aclk(s_aclk),
        .s_axi_awready(s_axi_awready),
        .s_axi_awvalid(s_axi_awvalid));
  axi_clock_converter_dramslim_memory \gntv_or_sync_fifo.mem 
       (.DI(DI),
        .E(\gntv_or_sync_fifo.gl0.rd_n_4 ),
        .Q(Q),
        .\gc0.count_d1_reg[3] (p_0_out_0),
        .\gic0.gc0.count_d2_reg[3] (p_12_out),
        .\gpregsm1.curr_fwft_state_reg[1] (ram_rd_en_i),
        .m_aclk(m_aclk),
        .ram_full_fb_i_reg(p_18_out),
        .s_aclk(s_aclk));
  axi_clock_converter_dramslim_reset_blk_ramfifo_35 rstblk
       (.\gc0.count_reg[1] (rd_rst_i),
        .\grstd1.grst_full.grst_f.rst_d3_reg_0 (rst_full_ff_i),
        .inverted_reset(inverted_reset),
        .m_aclk(m_aclk),
        .out(wr_rst_i),
        .ram_full_fb_i_reg(p_23_out),
        .s_aclk(s_aclk));
endmodule

(* ORIG_REF_NAME = "fifo_generator_ramfifo" *) 
module axi_clock_converter_dramslim_fifo_generator_ramfifo_74
   (s_axi_arready,
    m_axi_arvalid,
    \m_axi_arid[15] ,
    m_aclk,
    s_aclk,
    inverted_reset,
    m_axi_arready,
    s_axi_arvalid,
    I141);
  output s_axi_arready;
  output m_axi_arvalid;
  output [108:0]\m_axi_arid[15] ;
  input m_aclk;
  input s_aclk;
  input inverted_reset;
  input m_axi_arready;
  input s_axi_arvalid;
  input [108:0]I141;

  wire [108:0]I141;
  wire \gntv_or_sync_fifo.gcx.clkx/_n_0 ;
  wire \gntv_or_sync_fifo.gcx.clkx_n_4 ;
  wire \gntv_or_sync_fifo.gcx.clkx_n_9 ;
  wire \gntv_or_sync_fifo.gl0.rd_n_4 ;
  wire \gntv_or_sync_fifo.gl0.rd_n_5 ;
  wire \gntv_or_sync_fifo.gl0.rd_n_6 ;
  wire \gntv_or_sync_fifo.gl0.rd_n_7 ;
  wire \gntv_or_sync_fifo.gl0.wr_n_3 ;
  wire inverted_reset;
  wire m_aclk;
  wire [108:0]\m_axi_arid[15] ;
  wire m_axi_arready;
  wire m_axi_arvalid;
  wire [3:0]p_0_out;
  wire [3:0]p_12_out;
  wire [3:0]p_13_out;
  wire p_18_out;
  wire [3:0]p_22_out;
  wire [3:3]p_23_out;
  wire [3:0]p_7_out;
  wire ram_rd_en_i;
  wire [2:0]rd_pntr_plus1;
  wire [2:0]rd_rst_i;
  wire rst_full_ff_i;
  wire s_aclk;
  wire s_axi_arready;
  wire s_axi_arvalid;
  wire [2:0]wr_pntr_plus2;
  wire wr_rst_busy_rach;
  wire [1:0]wr_rst_i;

  axi_clock_converter_dramslim_clk_x_pntrs_75 \gntv_or_sync_fifo.gcx.clkx 
       (.AR(wr_rst_i[0]),
        .D({\gntv_or_sync_fifo.gl0.rd_n_5 ,\gntv_or_sync_fifo.gl0.rd_n_6 ,\gntv_or_sync_fifo.gl0.rd_n_7 }),
        .Q(p_22_out),
        .\Q_reg_reg[1] (\gntv_or_sync_fifo.gcx.clkx/_n_0 ),
        .\gc0.count_d1_reg[3] (p_0_out[3]),
        .\gc0.count_reg[2] (rd_pntr_plus1),
        .\gic0.gc0.count_d1_reg[3] (p_13_out),
        .\gic0.gc0.count_d2_reg[3] (p_12_out),
        .\gic0.gc0.count_reg[2] (wr_pntr_plus2),
        .\grstd1.grst_full.grst_f.rst_d3_reg (wr_rst_busy_rach),
        .m_aclk(m_aclk),
        .\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] (rd_rst_i[1]),
        .out(p_7_out),
        .ram_empty_i_reg(\gntv_or_sync_fifo.gcx.clkx_n_4 ),
        .ram_full_fb_i_reg(\gntv_or_sync_fifo.gcx.clkx_n_9 ),
        .ram_full_fb_i_reg_0(p_23_out),
        .ram_full_fb_i_reg_1(\gntv_or_sync_fifo.gl0.wr_n_3 ),
        .s_aclk(s_aclk));
  LUT4 #(
    .INIT(16'h6996)) 
    \gntv_or_sync_fifo.gcx.clkx/ 
       (.I0(p_7_out[1]),
        .I1(p_7_out[0]),
        .I2(p_7_out[3]),
        .I3(p_7_out[2]),
        .O(\gntv_or_sync_fifo.gcx.clkx/_n_0 ));
  axi_clock_converter_dramslim_rd_logic_76 \gntv_or_sync_fifo.gl0.rd 
       (.D({\gntv_or_sync_fifo.gl0.rd_n_5 ,\gntv_or_sync_fifo.gl0.rd_n_6 ,\gntv_or_sync_fifo.gl0.rd_n_7 }),
        .E(ram_rd_en_i),
        .Q(rd_pntr_plus1),
        .\gnxpm_cdc.rd_pntr_gc_reg[3] (p_0_out),
        .\gnxpm_cdc.wr_pntr_bin_reg[2] (\gntv_or_sync_fifo.gcx.clkx_n_4 ),
        .\gnxpm_cdc.wr_pntr_bin_reg[3] (p_22_out),
        .\goreg_dm.dout_i_reg[108] (\gntv_or_sync_fifo.gl0.rd_n_4 ),
        .m_aclk(m_aclk),
        .m_axi_arready(m_axi_arready),
        .m_axi_arvalid(m_axi_arvalid),
        .out({rd_rst_i[2],rd_rst_i[0]}));
  axi_clock_converter_dramslim_wr_logic_77 \gntv_or_sync_fifo.gl0.wr 
       (.AR(wr_rst_i[1]),
        .E(p_18_out),
        .Q(wr_pntr_plus2),
        .\gic0.gc0.count_d1_reg[3] (\gntv_or_sync_fifo.gcx.clkx_n_9 ),
        .\gic0.gc0.count_d2_reg[3] (p_13_out),
        .\gnxpm_cdc.rd_pntr_bin_reg[3] (p_23_out),
        .\gnxpm_cdc.wr_pntr_gc_reg[3] (p_12_out),
        .out(rst_full_ff_i),
        .ram_full_fb_i_reg(\gntv_or_sync_fifo.gl0.wr_n_3 ),
        .s_aclk(s_aclk),
        .s_axi_arready(s_axi_arready),
        .s_axi_arvalid(s_axi_arvalid));
  axi_clock_converter_dramslim_memory_78 \gntv_or_sync_fifo.mem 
       (.E(\gntv_or_sync_fifo.gl0.rd_n_4 ),
        .I141(I141),
        .\gc0.count_d1_reg[3] (p_0_out),
        .\gic0.gc0.count_d2_reg[3] (p_12_out),
        .\gpregsm1.curr_fwft_state_reg[1] (ram_rd_en_i),
        .m_aclk(m_aclk),
        .\m_axi_arid[15] (\m_axi_arid[15] ),
        .ram_full_fb_i_reg(p_18_out),
        .s_aclk(s_aclk));
  axi_clock_converter_dramslim_reset_blk_ramfifo_79 rstblk
       (.\gc0.count_reg[1] (rd_rst_i),
        .\grstd1.grst_full.grst_f.rst_d3_reg_0 (rst_full_ff_i),
        .inverted_reset(inverted_reset),
        .m_aclk(m_aclk),
        .out(wr_rst_i),
        .ram_full_fb_i_reg(wr_rst_busy_rach),
        .s_aclk(s_aclk));
endmodule

(* ORIG_REF_NAME = "fifo_generator_ramfifo" *) 
module axi_clock_converter_dramslim_fifo_generator_ramfifo__parameterized0
   (s_axi_wready,
    m_axi_wvalid,
    \m_axi_wdata[63] ,
    m_aclk,
    s_aclk,
    inverted_reset,
    m_axi_wready,
    s_axi_wvalid,
    I133);
  output s_axi_wready;
  output m_axi_wvalid;
  output [72:0]\m_axi_wdata[63] ;
  input m_aclk;
  input s_aclk;
  input inverted_reset;
  input m_axi_wready;
  input s_axi_wvalid;
  input [72:0]I133;

  wire [72:0]I133;
  wire \gntv_or_sync_fifo.gcx.clkx/_n_0 ;
  wire \gntv_or_sync_fifo.gcx.clkx_n_4 ;
  wire \gntv_or_sync_fifo.gcx.clkx_n_9 ;
  wire \gntv_or_sync_fifo.gl0.rd_n_4 ;
  wire \gntv_or_sync_fifo.gl0.rd_n_5 ;
  wire \gntv_or_sync_fifo.gl0.rd_n_6 ;
  wire \gntv_or_sync_fifo.gl0.rd_n_7 ;
  wire \gntv_or_sync_fifo.gl0.wr_n_3 ;
  wire inverted_reset;
  wire m_aclk;
  wire [72:0]\m_axi_wdata[63] ;
  wire m_axi_wready;
  wire m_axi_wvalid;
  wire [3:0]p_0_out;
  wire [3:0]p_12_out;
  wire [3:0]p_13_out;
  wire p_15_out;
  wire p_18_out;
  wire [3:0]p_22_out;
  wire [3:3]p_23_out;
  wire [3:0]p_7_out;
  wire ram_rd_en_i;
  wire [2:0]rd_pntr_plus1;
  wire [2:0]rd_rst_i;
  wire rst_full_ff_i;
  wire s_aclk;
  wire s_axi_wready;
  wire s_axi_wvalid;
  wire [2:0]wr_pntr_plus2;
  wire [1:0]wr_rst_i;

  axi_clock_converter_dramslim_clk_x_pntrs_11 \gntv_or_sync_fifo.gcx.clkx 
       (.AR(wr_rst_i[0]),
        .D({\gntv_or_sync_fifo.gl0.rd_n_5 ,\gntv_or_sync_fifo.gl0.rd_n_6 ,\gntv_or_sync_fifo.gl0.rd_n_7 }),
        .Q(p_22_out),
        .\Q_reg_reg[1] (\gntv_or_sync_fifo.gcx.clkx/_n_0 ),
        .\gc0.count_d1_reg[3] (p_0_out[3]),
        .\gc0.count_reg[2] (rd_pntr_plus1),
        .\gic0.gc0.count_d1_reg[3] (p_13_out),
        .\gic0.gc0.count_d2_reg[3] (p_12_out),
        .\gic0.gc0.count_reg[2] (wr_pntr_plus2),
        .\grstd1.grst_full.grst_f.rst_d3_reg (p_15_out),
        .m_aclk(m_aclk),
        .\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] (rd_rst_i[1]),
        .out(p_7_out),
        .ram_empty_i_reg(\gntv_or_sync_fifo.gcx.clkx_n_4 ),
        .ram_full_fb_i_reg(\gntv_or_sync_fifo.gcx.clkx_n_9 ),
        .ram_full_fb_i_reg_0(p_23_out),
        .ram_full_fb_i_reg_1(\gntv_or_sync_fifo.gl0.wr_n_3 ),
        .s_aclk(s_aclk));
  LUT4 #(
    .INIT(16'h6996)) 
    \gntv_or_sync_fifo.gcx.clkx/ 
       (.I0(p_7_out[1]),
        .I1(p_7_out[0]),
        .I2(p_7_out[3]),
        .I3(p_7_out[2]),
        .O(\gntv_or_sync_fifo.gcx.clkx/_n_0 ));
  axi_clock_converter_dramslim_rd_logic_12 \gntv_or_sync_fifo.gl0.rd 
       (.D({\gntv_or_sync_fifo.gl0.rd_n_5 ,\gntv_or_sync_fifo.gl0.rd_n_6 ,\gntv_or_sync_fifo.gl0.rd_n_7 }),
        .E(ram_rd_en_i),
        .Q(rd_pntr_plus1),
        .\gnxpm_cdc.rd_pntr_gc_reg[3] (p_0_out),
        .\gnxpm_cdc.wr_pntr_bin_reg[2] (\gntv_or_sync_fifo.gcx.clkx_n_4 ),
        .\gnxpm_cdc.wr_pntr_bin_reg[3] (p_22_out),
        .\goreg_dm.dout_i_reg[72] (\gntv_or_sync_fifo.gl0.rd_n_4 ),
        .m_aclk(m_aclk),
        .m_axi_wready(m_axi_wready),
        .m_axi_wvalid(m_axi_wvalid),
        .out({rd_rst_i[2],rd_rst_i[0]}));
  axi_clock_converter_dramslim_wr_logic_13 \gntv_or_sync_fifo.gl0.wr 
       (.AR(wr_rst_i[1]),
        .E(p_18_out),
        .Q(wr_pntr_plus2),
        .\gic0.gc0.count_d1_reg[3] (\gntv_or_sync_fifo.gcx.clkx_n_9 ),
        .\gic0.gc0.count_d2_reg[3] (p_13_out),
        .\gnxpm_cdc.rd_pntr_bin_reg[3] (p_23_out),
        .\gnxpm_cdc.wr_pntr_gc_reg[3] (p_12_out),
        .out(rst_full_ff_i),
        .ram_full_fb_i_reg(\gntv_or_sync_fifo.gl0.wr_n_3 ),
        .s_aclk(s_aclk),
        .s_axi_wready(s_axi_wready),
        .s_axi_wvalid(s_axi_wvalid));
  axi_clock_converter_dramslim_memory__parameterized0 \gntv_or_sync_fifo.mem 
       (.E(\gntv_or_sync_fifo.gl0.rd_n_4 ),
        .I133(I133),
        .\gc0.count_d1_reg[3] (p_0_out),
        .\gic0.gc0.count_d2_reg[3] (p_12_out),
        .\gpregsm1.curr_fwft_state_reg[1] (ram_rd_en_i),
        .m_aclk(m_aclk),
        .\m_axi_wdata[63] (\m_axi_wdata[63] ),
        .ram_full_fb_i_reg(p_18_out),
        .s_aclk(s_aclk));
  axi_clock_converter_dramslim_reset_blk_ramfifo_14 rstblk
       (.\gc0.count_reg[1] (rd_rst_i),
        .\grstd1.grst_full.grst_f.rst_d3_reg_0 (rst_full_ff_i),
        .inverted_reset(inverted_reset),
        .m_aclk(m_aclk),
        .out(wr_rst_i),
        .ram_full_fb_i_reg(p_15_out),
        .s_aclk(s_aclk));
endmodule

(* ORIG_REF_NAME = "fifo_generator_ramfifo" *) 
module axi_clock_converter_dramslim_fifo_generator_ramfifo__parameterized1
   (s_axi_bvalid,
    m_axi_bready,
    \s_axi_bid[15] ,
    s_aclk,
    m_aclk,
    inverted_reset,
    m_axi_bvalid,
    s_axi_bready,
    I137);
  output s_axi_bvalid;
  output m_axi_bready;
  output [17:0]\s_axi_bid[15] ;
  input s_aclk;
  input m_aclk;
  input inverted_reset;
  input m_axi_bvalid;
  input s_axi_bready;
  input [17:0]I137;

  wire [17:0]I137;
  wire \gntv_or_sync_fifo.gcx.clkx/_n_0 ;
  wire \gntv_or_sync_fifo.gcx.clkx_n_4 ;
  wire \gntv_or_sync_fifo.gcx.clkx_n_6 ;
  wire \gntv_or_sync_fifo.gl0.rd_n_4 ;
  wire \gntv_or_sync_fifo.gl0.rd_n_5 ;
  wire \gntv_or_sync_fifo.gl0.rd_n_6 ;
  wire \gntv_or_sync_fifo.gl0.rd_n_7 ;
  wire \gntv_or_sync_fifo.gl0.wr_n_3 ;
  wire inverted_reset;
  wire m_aclk;
  wire m_axi_bready;
  wire m_axi_bvalid;
  wire [3:0]p_0_out;
  wire [3:0]p_12_out;
  wire [3:0]p_13_out;
  wire p_18_out;
  wire [3:0]p_22_out;
  wire [3:3]p_23_out;
  wire [3:0]p_7_out;
  wire ram_rd_en_i;
  wire [2:0]rd_pntr_plus1;
  wire [2:0]rd_rst_i;
  wire rst_full_ff_i;
  wire s_aclk;
  wire [17:0]\s_axi_bid[15] ;
  wire s_axi_bready;
  wire s_axi_bvalid;
  wire [2:0]wr_pntr_plus2;
  wire wr_rst_busy_wrch;
  wire [1:0]wr_rst_i;

  axi_clock_converter_dramslim_clk_x_pntrs \gntv_or_sync_fifo.gcx.clkx 
       (.AR(wr_rst_i[0]),
        .D({\gntv_or_sync_fifo.gl0.rd_n_5 ,\gntv_or_sync_fifo.gl0.rd_n_6 ,\gntv_or_sync_fifo.gl0.rd_n_7 }),
        .Q(p_13_out),
        .\Q_reg_reg[1] (\gntv_or_sync_fifo.gcx.clkx/_n_0 ),
        .\gc0.count_d1_reg[3] (p_0_out[3]),
        .\gc0.count_reg[2] (rd_pntr_plus1),
        .\gic0.gc0.count_d2_reg[3] (p_12_out),
        .\gic0.gc0.count_reg[2] (wr_pntr_plus2),
        .\grstd1.grst_full.grst_f.rst_d3_reg (wr_rst_busy_wrch),
        .m_aclk(m_aclk),
        .\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] (rd_rst_i[1]),
        .out(p_7_out),
        .ram_empty_i_reg(\gntv_or_sync_fifo.gcx.clkx_n_6 ),
        .ram_empty_i_reg_0(p_22_out),
        .ram_full_fb_i_reg(\gntv_or_sync_fifo.gcx.clkx_n_4 ),
        .ram_full_fb_i_reg_0(p_23_out),
        .ram_full_fb_i_reg_1(\gntv_or_sync_fifo.gl0.wr_n_3 ),
        .s_aclk(s_aclk));
  LUT4 #(
    .INIT(16'h6996)) 
    \gntv_or_sync_fifo.gcx.clkx/ 
       (.I0(p_7_out[1]),
        .I1(p_7_out[0]),
        .I2(p_7_out[3]),
        .I3(p_7_out[2]),
        .O(\gntv_or_sync_fifo.gcx.clkx/_n_0 ));
  axi_clock_converter_dramslim_rd_logic \gntv_or_sync_fifo.gl0.rd 
       (.D({\gntv_or_sync_fifo.gl0.rd_n_5 ,\gntv_or_sync_fifo.gl0.rd_n_6 ,\gntv_or_sync_fifo.gl0.rd_n_7 }),
        .E(ram_rd_en_i),
        .Q(rd_pntr_plus1),
        .\gnxpm_cdc.rd_pntr_gc_reg[3] (p_0_out),
        .\gnxpm_cdc.wr_pntr_bin_reg[2] (\gntv_or_sync_fifo.gcx.clkx_n_6 ),
        .\gnxpm_cdc.wr_pntr_bin_reg[3] (p_22_out),
        .\goreg_dm.dout_i_reg[17] (\gntv_or_sync_fifo.gl0.rd_n_4 ),
        .out({rd_rst_i[2],rd_rst_i[0]}),
        .s_aclk(s_aclk),
        .s_axi_bready(s_axi_bready),
        .s_axi_bvalid(s_axi_bvalid));
  axi_clock_converter_dramslim_wr_logic \gntv_or_sync_fifo.gl0.wr 
       (.AR(wr_rst_i[1]),
        .E(p_18_out),
        .Q(wr_pntr_plus2),
        .\gic0.gc0.count_d1_reg[3] (\gntv_or_sync_fifo.gcx.clkx_n_4 ),
        .\gic0.gc0.count_d2_reg[3] (p_13_out),
        .\gnxpm_cdc.rd_pntr_bin_reg[3] (p_23_out),
        .\gnxpm_cdc.wr_pntr_gc_reg[3] (p_12_out),
        .m_aclk(m_aclk),
        .m_axi_bready(m_axi_bready),
        .m_axi_bvalid(m_axi_bvalid),
        .out(rst_full_ff_i),
        .ram_full_fb_i_reg(\gntv_or_sync_fifo.gl0.wr_n_3 ));
  axi_clock_converter_dramslim_memory__parameterized1 \gntv_or_sync_fifo.mem 
       (.E(\gntv_or_sync_fifo.gl0.rd_n_4 ),
        .I118(p_18_out),
        .I137(I137),
        .count_d2(p_12_out),
        .\gc0.count_d1_reg[3] (p_0_out),
        .\gpregsm1.curr_fwft_state_reg[1] (ram_rd_en_i),
        .m_aclk(m_aclk),
        .s_aclk(s_aclk),
        .\s_axi_bid[15] (\s_axi_bid[15] ));
  axi_clock_converter_dramslim_reset_blk_ramfifo rstblk
       (.\gc0.count_reg[1] (rd_rst_i),
        .\grstd1.grst_full.grst_f.rst_d3_reg_0 (rst_full_ff_i),
        .inverted_reset(inverted_reset),
        .m_aclk(m_aclk),
        .out(wr_rst_i),
        .ram_full_fb_i_reg(wr_rst_busy_wrch),
        .s_aclk(s_aclk));
endmodule

(* ORIG_REF_NAME = "fifo_generator_ramfifo" *) 
module axi_clock_converter_dramslim_fifo_generator_ramfifo__parameterized2
   (\ngwrdrst.grst.g7serrst.rst_wr_reg1_reg ,
    s_axi_rvalid,
    m_axi_rready,
    \s_axi_rid[15] ,
    s_aclk,
    m_aclk,
    m_axi_rvalid,
    s_axi_rready,
    s_aresetn,
    I145);
  output \ngwrdrst.grst.g7serrst.rst_wr_reg1_reg ;
  output s_axi_rvalid;
  output m_axi_rready;
  output [82:0]\s_axi_rid[15] ;
  input s_aclk;
  input m_aclk;
  input m_axi_rvalid;
  input s_axi_rready;
  input s_aresetn;
  input [82:0]I145;

  wire [82:0]I145;
  wire \gntv_or_sync_fifo.gcx.clkx/_n_0 ;
  wire \gntv_or_sync_fifo.gcx.clkx_n_4 ;
  wire \gntv_or_sync_fifo.gcx.clkx_n_6 ;
  wire \gntv_or_sync_fifo.gl0.rd_n_4 ;
  wire \gntv_or_sync_fifo.gl0.rd_n_5 ;
  wire \gntv_or_sync_fifo.gl0.rd_n_6 ;
  wire \gntv_or_sync_fifo.gl0.rd_n_7 ;
  wire \gntv_or_sync_fifo.gl0.wr_n_3 ;
  wire m_aclk;
  wire m_axi_rready;
  wire m_axi_rvalid;
  wire \ngwrdrst.grst.g7serrst.rst_wr_reg1_reg ;
  wire [3:0]p_0_out;
  wire [3:0]p_12_out;
  wire [3:0]p_13_out;
  wire p_18_out;
  wire [3:0]p_22_out;
  wire [3:3]p_23_out;
  wire [3:0]p_7_out;
  wire ram_rd_en_i;
  wire [2:0]rd_pntr_plus1;
  wire [2:0]rd_rst_i;
  wire rst_full_ff_i;
  wire s_aclk;
  wire s_aresetn;
  wire [82:0]\s_axi_rid[15] ;
  wire s_axi_rready;
  wire s_axi_rvalid;
  wire [2:0]wr_pntr_plus2;
  wire wr_rst_busy_rdch;
  wire [1:0]wr_rst_i;

  axi_clock_converter_dramslim_clk_x_pntrs_53 \gntv_or_sync_fifo.gcx.clkx 
       (.AR(wr_rst_i[0]),
        .D({\gntv_or_sync_fifo.gl0.rd_n_5 ,\gntv_or_sync_fifo.gl0.rd_n_6 ,\gntv_or_sync_fifo.gl0.rd_n_7 }),
        .Q(p_13_out),
        .\Q_reg_reg[1] (\gntv_or_sync_fifo.gcx.clkx/_n_0 ),
        .\gc0.count_d1_reg[3] (p_0_out[3]),
        .\gc0.count_reg[2] (rd_pntr_plus1),
        .\gic0.gc0.count_d2_reg[3] (p_12_out),
        .\gic0.gc0.count_reg[2] (wr_pntr_plus2),
        .\grstd1.grst_full.grst_f.rst_d3_reg (wr_rst_busy_rdch),
        .m_aclk(m_aclk),
        .\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] (rd_rst_i[1]),
        .out(p_7_out),
        .ram_empty_i_reg(\gntv_or_sync_fifo.gcx.clkx_n_6 ),
        .ram_empty_i_reg_0(p_22_out),
        .ram_full_fb_i_reg(\gntv_or_sync_fifo.gcx.clkx_n_4 ),
        .ram_full_fb_i_reg_0(p_23_out),
        .ram_full_fb_i_reg_1(\gntv_or_sync_fifo.gl0.wr_n_3 ),
        .s_aclk(s_aclk));
  LUT4 #(
    .INIT(16'h6996)) 
    \gntv_or_sync_fifo.gcx.clkx/ 
       (.I0(p_7_out[1]),
        .I1(p_7_out[0]),
        .I2(p_7_out[3]),
        .I3(p_7_out[2]),
        .O(\gntv_or_sync_fifo.gcx.clkx/_n_0 ));
  axi_clock_converter_dramslim_rd_logic_54 \gntv_or_sync_fifo.gl0.rd 
       (.D({\gntv_or_sync_fifo.gl0.rd_n_5 ,\gntv_or_sync_fifo.gl0.rd_n_6 ,\gntv_or_sync_fifo.gl0.rd_n_7 }),
        .E(ram_rd_en_i),
        .Q(rd_pntr_plus1),
        .\gnxpm_cdc.rd_pntr_gc_reg[3] (p_0_out),
        .\gnxpm_cdc.wr_pntr_bin_reg[2] (\gntv_or_sync_fifo.gcx.clkx_n_6 ),
        .\gnxpm_cdc.wr_pntr_bin_reg[3] (p_22_out),
        .\goreg_dm.dout_i_reg[82] (\gntv_or_sync_fifo.gl0.rd_n_4 ),
        .out({rd_rst_i[2],rd_rst_i[0]}),
        .s_aclk(s_aclk),
        .s_axi_rready(s_axi_rready),
        .s_axi_rvalid(s_axi_rvalid));
  axi_clock_converter_dramslim_wr_logic_55 \gntv_or_sync_fifo.gl0.wr 
       (.AR(wr_rst_i[1]),
        .E(p_18_out),
        .Q(wr_pntr_plus2),
        .\gic0.gc0.count_d1_reg[3] (\gntv_or_sync_fifo.gcx.clkx_n_4 ),
        .\gic0.gc0.count_d2_reg[3] (p_13_out),
        .\gnxpm_cdc.rd_pntr_bin_reg[3] (p_23_out),
        .\gnxpm_cdc.wr_pntr_gc_reg[3] (p_12_out),
        .m_aclk(m_aclk),
        .m_axi_rready(m_axi_rready),
        .m_axi_rvalid(m_axi_rvalid),
        .out(rst_full_ff_i),
        .ram_full_fb_i_reg(\gntv_or_sync_fifo.gl0.wr_n_3 ));
  axi_clock_converter_dramslim_memory__parameterized2 \gntv_or_sync_fifo.mem 
       (.E(\gntv_or_sync_fifo.gl0.rd_n_4 ),
        .I145(I145),
        .\gc0.count_d1_reg[3] (p_0_out),
        .\gic0.gc0.count_d2_reg[3] (p_12_out),
        .\gpregsm1.curr_fwft_state_reg[1] (ram_rd_en_i),
        .m_aclk(m_aclk),
        .ram_full_fb_i_reg(p_18_out),
        .s_aclk(s_aclk),
        .\s_axi_rid[15] (\s_axi_rid[15] ));
  axi_clock_converter_dramslim_reset_blk_ramfifo_56 rstblk
       (.\gc0.count_reg[1] (rd_rst_i),
        .\grstd1.grst_full.grst_f.rst_d3_reg_0 (rst_full_ff_i),
        .m_aclk(m_aclk),
        .\ngwrdrst.grst.g7serrst.rst_wr_reg1_reg_0 (\ngwrdrst.grst.g7serrst.rst_wr_reg1_reg ),
        .out(wr_rst_i),
        .ram_full_fb_i_reg(wr_rst_busy_rdch),
        .s_aclk(s_aclk),
        .s_aresetn(s_aresetn));
endmodule

(* ORIG_REF_NAME = "fifo_generator_top" *) 
module axi_clock_converter_dramslim_fifo_generator_top
   (s_axi_arready,
    m_axi_arvalid,
    \m_axi_arid[15] ,
    m_aclk,
    s_aclk,
    inverted_reset,
    m_axi_arready,
    s_axi_arvalid,
    I141);
  output s_axi_arready;
  output m_axi_arvalid;
  output [108:0]\m_axi_arid[15] ;
  input m_aclk;
  input s_aclk;
  input inverted_reset;
  input m_axi_arready;
  input s_axi_arvalid;
  input [108:0]I141;

  wire [108:0]I141;
  wire inverted_reset;
  wire m_aclk;
  wire [108:0]\m_axi_arid[15] ;
  wire m_axi_arready;
  wire m_axi_arvalid;
  wire s_aclk;
  wire s_axi_arready;
  wire s_axi_arvalid;

  axi_clock_converter_dramslim_fifo_generator_ramfifo_74 \grf.rf 
       (.I141(I141),
        .inverted_reset(inverted_reset),
        .m_aclk(m_aclk),
        .\m_axi_arid[15] (\m_axi_arid[15] ),
        .m_axi_arready(m_axi_arready),
        .m_axi_arvalid(m_axi_arvalid),
        .s_aclk(s_aclk),
        .s_axi_arready(s_axi_arready),
        .s_axi_arvalid(s_axi_arvalid));
endmodule

(* ORIG_REF_NAME = "fifo_generator_top" *) 
module axi_clock_converter_dramslim_fifo_generator_top_0
   (s_axi_awready,
    m_axi_awvalid,
    Q,
    m_aclk,
    s_aclk,
    inverted_reset,
    m_axi_awready,
    s_axi_awvalid,
    DI);
  output s_axi_awready;
  output m_axi_awvalid;
  output [108:0]Q;
  input m_aclk;
  input s_aclk;
  input inverted_reset;
  input m_axi_awready;
  input s_axi_awvalid;
  input [108:0]DI;

  wire [108:0]DI;
  wire [108:0]Q;
  wire inverted_reset;
  wire m_aclk;
  wire m_axi_awready;
  wire m_axi_awvalid;
  wire s_aclk;
  wire s_axi_awready;
  wire s_axi_awvalid;

  axi_clock_converter_dramslim_fifo_generator_ramfifo \grf.rf 
       (.DI(DI),
        .Q(Q),
        .inverted_reset(inverted_reset),
        .m_aclk(m_aclk),
        .m_axi_awready(m_axi_awready),
        .m_axi_awvalid(m_axi_awvalid),
        .s_aclk(s_aclk),
        .s_axi_awready(s_axi_awready),
        .s_axi_awvalid(s_axi_awvalid));
endmodule

(* ORIG_REF_NAME = "fifo_generator_top" *) 
module axi_clock_converter_dramslim_fifo_generator_top__parameterized0
   (s_axi_wready,
    m_axi_wvalid,
    \m_axi_wdata[63] ,
    m_aclk,
    s_aclk,
    inverted_reset,
    m_axi_wready,
    s_axi_wvalid,
    I133);
  output s_axi_wready;
  output m_axi_wvalid;
  output [72:0]\m_axi_wdata[63] ;
  input m_aclk;
  input s_aclk;
  input inverted_reset;
  input m_axi_wready;
  input s_axi_wvalid;
  input [72:0]I133;

  wire [72:0]I133;
  wire inverted_reset;
  wire m_aclk;
  wire [72:0]\m_axi_wdata[63] ;
  wire m_axi_wready;
  wire m_axi_wvalid;
  wire s_aclk;
  wire s_axi_wready;
  wire s_axi_wvalid;

  axi_clock_converter_dramslim_fifo_generator_ramfifo__parameterized0 \grf.rf 
       (.I133(I133),
        .inverted_reset(inverted_reset),
        .m_aclk(m_aclk),
        .\m_axi_wdata[63] (\m_axi_wdata[63] ),
        .m_axi_wready(m_axi_wready),
        .m_axi_wvalid(m_axi_wvalid),
        .s_aclk(s_aclk),
        .s_axi_wready(s_axi_wready),
        .s_axi_wvalid(s_axi_wvalid));
endmodule

(* ORIG_REF_NAME = "fifo_generator_top" *) 
module axi_clock_converter_dramslim_fifo_generator_top__parameterized1
   (s_axi_bvalid,
    m_axi_bready,
    \s_axi_bid[15] ,
    s_aclk,
    m_aclk,
    inverted_reset,
    m_axi_bvalid,
    s_axi_bready,
    I137);
  output s_axi_bvalid;
  output m_axi_bready;
  output [17:0]\s_axi_bid[15] ;
  input s_aclk;
  input m_aclk;
  input inverted_reset;
  input m_axi_bvalid;
  input s_axi_bready;
  input [17:0]I137;

  wire [17:0]I137;
  wire inverted_reset;
  wire m_aclk;
  wire m_axi_bready;
  wire m_axi_bvalid;
  wire s_aclk;
  wire [17:0]\s_axi_bid[15] ;
  wire s_axi_bready;
  wire s_axi_bvalid;

  axi_clock_converter_dramslim_fifo_generator_ramfifo__parameterized1 \grf.rf 
       (.I137(I137),
        .inverted_reset(inverted_reset),
        .m_aclk(m_aclk),
        .m_axi_bready(m_axi_bready),
        .m_axi_bvalid(m_axi_bvalid),
        .s_aclk(s_aclk),
        .\s_axi_bid[15] (\s_axi_bid[15] ),
        .s_axi_bready(s_axi_bready),
        .s_axi_bvalid(s_axi_bvalid));
endmodule

(* ORIG_REF_NAME = "fifo_generator_top" *) 
module axi_clock_converter_dramslim_fifo_generator_top__parameterized2
   (inverted_reset,
    s_axi_rvalid,
    m_axi_rready,
    \s_axi_rid[15] ,
    s_aclk,
    m_aclk,
    m_axi_rvalid,
    s_axi_rready,
    s_aresetn,
    I145);
  output inverted_reset;
  output s_axi_rvalid;
  output m_axi_rready;
  output [82:0]\s_axi_rid[15] ;
  input s_aclk;
  input m_aclk;
  input m_axi_rvalid;
  input s_axi_rready;
  input s_aresetn;
  input [82:0]I145;

  wire [82:0]I145;
  wire inverted_reset;
  wire m_aclk;
  wire m_axi_rready;
  wire m_axi_rvalid;
  wire s_aclk;
  wire s_aresetn;
  wire [82:0]\s_axi_rid[15] ;
  wire s_axi_rready;
  wire s_axi_rvalid;

  axi_clock_converter_dramslim_fifo_generator_ramfifo__parameterized2 \grf.rf 
       (.I145(I145),
        .m_aclk(m_aclk),
        .m_axi_rready(m_axi_rready),
        .m_axi_rvalid(m_axi_rvalid),
        .\ngwrdrst.grst.g7serrst.rst_wr_reg1_reg (inverted_reset),
        .s_aclk(s_aclk),
        .s_aresetn(s_aresetn),
        .\s_axi_rid[15] (\s_axi_rid[15] ),
        .s_axi_rready(s_axi_rready),
        .s_axi_rvalid(s_axi_rvalid));
endmodule

(* C_ADD_NGC_CONSTRAINT = "0" *) (* C_APPLICATION_TYPE_AXIS = "0" *) (* C_APPLICATION_TYPE_RACH = "0" *) 
(* C_APPLICATION_TYPE_RDCH = "0" *) (* C_APPLICATION_TYPE_WACH = "0" *) (* C_APPLICATION_TYPE_WDCH = "0" *) 
(* C_APPLICATION_TYPE_WRCH = "0" *) (* C_AXIS_TDATA_WIDTH = "8" *) (* C_AXIS_TDEST_WIDTH = "1" *) 
(* C_AXIS_TID_WIDTH = "1" *) (* C_AXIS_TKEEP_WIDTH = "1" *) (* C_AXIS_TSTRB_WIDTH = "1" *) 
(* C_AXIS_TUSER_WIDTH = "4" *) (* C_AXIS_TYPE = "0" *) (* C_AXI_ADDR_WIDTH = "64" *) 
(* C_AXI_ARUSER_WIDTH = "1" *) (* C_AXI_AWUSER_WIDTH = "1" *) (* C_AXI_BUSER_WIDTH = "1" *) 
(* C_AXI_DATA_WIDTH = "64" *) (* C_AXI_ID_WIDTH = "16" *) (* C_AXI_LEN_WIDTH = "8" *) 
(* C_AXI_LOCK_WIDTH = "1" *) (* C_AXI_RUSER_WIDTH = "1" *) (* C_AXI_TYPE = "1" *) 
(* C_AXI_WUSER_WIDTH = "1" *) (* C_COMMON_CLOCK = "0" *) (* C_COUNT_TYPE = "0" *) 
(* C_DATA_COUNT_WIDTH = "10" *) (* C_DEFAULT_VALUE = "BlankString" *) (* C_DIN_WIDTH = "18" *) 
(* C_DIN_WIDTH_AXIS = "1" *) (* C_DIN_WIDTH_RACH = "109" *) (* C_DIN_WIDTH_RDCH = "83" *) 
(* C_DIN_WIDTH_WACH = "109" *) (* C_DIN_WIDTH_WDCH = "73" *) (* C_DIN_WIDTH_WRCH = "18" *) 
(* C_DOUT_RST_VAL = "0" *) (* C_DOUT_WIDTH = "18" *) (* C_ENABLE_RLOCS = "0" *) 
(* C_ENABLE_RST_SYNC = "1" *) (* C_EN_SAFETY_CKT = "0" *) (* C_ERROR_INJECTION_TYPE = "0" *) 
(* C_ERROR_INJECTION_TYPE_AXIS = "0" *) (* C_ERROR_INJECTION_TYPE_RACH = "0" *) (* C_ERROR_INJECTION_TYPE_RDCH = "0" *) 
(* C_ERROR_INJECTION_TYPE_WACH = "0" *) (* C_ERROR_INJECTION_TYPE_WDCH = "0" *) (* C_ERROR_INJECTION_TYPE_WRCH = "0" *) 
(* C_FAMILY = "virtexuplus" *) (* C_FULL_FLAGS_RST_VAL = "1" *) (* C_HAS_ALMOST_EMPTY = "0" *) 
(* C_HAS_ALMOST_FULL = "0" *) (* C_HAS_AXIS_TDATA = "1" *) (* C_HAS_AXIS_TDEST = "0" *) 
(* C_HAS_AXIS_TID = "0" *) (* C_HAS_AXIS_TKEEP = "0" *) (* C_HAS_AXIS_TLAST = "0" *) 
(* C_HAS_AXIS_TREADY = "1" *) (* C_HAS_AXIS_TSTRB = "0" *) (* C_HAS_AXIS_TUSER = "1" *) 
(* C_HAS_AXI_ARUSER = "0" *) (* C_HAS_AXI_AWUSER = "0" *) (* C_HAS_AXI_BUSER = "0" *) 
(* C_HAS_AXI_ID = "1" *) (* C_HAS_AXI_RD_CHANNEL = "1" *) (* C_HAS_AXI_RUSER = "0" *) 
(* C_HAS_AXI_WR_CHANNEL = "1" *) (* C_HAS_AXI_WUSER = "0" *) (* C_HAS_BACKUP = "0" *) 
(* C_HAS_DATA_COUNT = "0" *) (* C_HAS_DATA_COUNTS_AXIS = "0" *) (* C_HAS_DATA_COUNTS_RACH = "0" *) 
(* C_HAS_DATA_COUNTS_RDCH = "0" *) (* C_HAS_DATA_COUNTS_WACH = "0" *) (* C_HAS_DATA_COUNTS_WDCH = "0" *) 
(* C_HAS_DATA_COUNTS_WRCH = "0" *) (* C_HAS_INT_CLK = "0" *) (* C_HAS_MASTER_CE = "0" *) 
(* C_HAS_MEMINIT_FILE = "0" *) (* C_HAS_OVERFLOW = "0" *) (* C_HAS_PROG_FLAGS_AXIS = "0" *) 
(* C_HAS_PROG_FLAGS_RACH = "0" *) (* C_HAS_PROG_FLAGS_RDCH = "0" *) (* C_HAS_PROG_FLAGS_WACH = "0" *) 
(* C_HAS_PROG_FLAGS_WDCH = "0" *) (* C_HAS_PROG_FLAGS_WRCH = "0" *) (* C_HAS_RD_DATA_COUNT = "0" *) 
(* C_HAS_RD_RST = "0" *) (* C_HAS_RST = "1" *) (* C_HAS_SLAVE_CE = "0" *) 
(* C_HAS_SRST = "0" *) (* C_HAS_UNDERFLOW = "0" *) (* C_HAS_VALID = "0" *) 
(* C_HAS_WR_ACK = "0" *) (* C_HAS_WR_DATA_COUNT = "0" *) (* C_HAS_WR_RST = "0" *) 
(* C_IMPLEMENTATION_TYPE = "0" *) (* C_IMPLEMENTATION_TYPE_AXIS = "11" *) (* C_IMPLEMENTATION_TYPE_RACH = "12" *) 
(* C_IMPLEMENTATION_TYPE_RDCH = "12" *) (* C_IMPLEMENTATION_TYPE_WACH = "12" *) (* C_IMPLEMENTATION_TYPE_WDCH = "12" *) 
(* C_IMPLEMENTATION_TYPE_WRCH = "12" *) (* C_INIT_WR_PNTR_VAL = "0" *) (* C_INTERFACE_TYPE = "2" *) 
(* C_MEMORY_TYPE = "1" *) (* C_MIF_FILE_NAME = "BlankString" *) (* C_MSGON_VAL = "1" *) 
(* C_OPTIMIZATION_MODE = "0" *) (* C_OVERFLOW_LOW = "0" *) (* C_POWER_SAVING_MODE = "0" *) 
(* C_PRELOAD_LATENCY = "1" *) (* C_PRELOAD_REGS = "0" *) (* C_PRIM_FIFO_TYPE = "4kx4" *) 
(* C_PRIM_FIFO_TYPE_AXIS = "512x36" *) (* C_PRIM_FIFO_TYPE_RACH = "512x36" *) (* C_PRIM_FIFO_TYPE_RDCH = "512x36" *) 
(* C_PRIM_FIFO_TYPE_WACH = "512x36" *) (* C_PRIM_FIFO_TYPE_WDCH = "512x36" *) (* C_PRIM_FIFO_TYPE_WRCH = "512x36" *) 
(* C_PROG_EMPTY_THRESH_ASSERT_VAL = "2" *) (* C_PROG_EMPTY_THRESH_ASSERT_VAL_AXIS = "1021" *) (* C_PROG_EMPTY_THRESH_ASSERT_VAL_RACH = "13" *) 
(* C_PROG_EMPTY_THRESH_ASSERT_VAL_RDCH = "13" *) (* C_PROG_EMPTY_THRESH_ASSERT_VAL_WACH = "13" *) (* C_PROG_EMPTY_THRESH_ASSERT_VAL_WDCH = "13" *) 
(* C_PROG_EMPTY_THRESH_ASSERT_VAL_WRCH = "13" *) (* C_PROG_EMPTY_THRESH_NEGATE_VAL = "3" *) (* C_PROG_EMPTY_TYPE = "0" *) 
(* C_PROG_EMPTY_TYPE_AXIS = "0" *) (* C_PROG_EMPTY_TYPE_RACH = "0" *) (* C_PROG_EMPTY_TYPE_RDCH = "0" *) 
(* C_PROG_EMPTY_TYPE_WACH = "0" *) (* C_PROG_EMPTY_TYPE_WDCH = "0" *) (* C_PROG_EMPTY_TYPE_WRCH = "0" *) 
(* C_PROG_FULL_THRESH_ASSERT_VAL = "1022" *) (* C_PROG_FULL_THRESH_ASSERT_VAL_AXIS = "1023" *) (* C_PROG_FULL_THRESH_ASSERT_VAL_RACH = "15" *) 
(* C_PROG_FULL_THRESH_ASSERT_VAL_RDCH = "15" *) (* C_PROG_FULL_THRESH_ASSERT_VAL_WACH = "15" *) (* C_PROG_FULL_THRESH_ASSERT_VAL_WDCH = "15" *) 
(* C_PROG_FULL_THRESH_ASSERT_VAL_WRCH = "15" *) (* C_PROG_FULL_THRESH_NEGATE_VAL = "1021" *) (* C_PROG_FULL_TYPE = "0" *) 
(* C_PROG_FULL_TYPE_AXIS = "0" *) (* C_PROG_FULL_TYPE_RACH = "0" *) (* C_PROG_FULL_TYPE_RDCH = "0" *) 
(* C_PROG_FULL_TYPE_WACH = "0" *) (* C_PROG_FULL_TYPE_WDCH = "0" *) (* C_PROG_FULL_TYPE_WRCH = "0" *) 
(* C_RACH_TYPE = "0" *) (* C_RDCH_TYPE = "0" *) (* C_RD_DATA_COUNT_WIDTH = "10" *) 
(* C_RD_DEPTH = "1024" *) (* C_RD_FREQ = "1" *) (* C_RD_PNTR_WIDTH = "10" *) 
(* C_REG_SLICE_MODE_AXIS = "0" *) (* C_REG_SLICE_MODE_RACH = "0" *) (* C_REG_SLICE_MODE_RDCH = "0" *) 
(* C_REG_SLICE_MODE_WACH = "0" *) (* C_REG_SLICE_MODE_WDCH = "0" *) (* C_REG_SLICE_MODE_WRCH = "0" *) 
(* C_SELECT_XPM = "0" *) (* C_SYNCHRONIZER_STAGE = "3" *) (* C_UNDERFLOW_LOW = "0" *) 
(* C_USE_COMMON_OVERFLOW = "0" *) (* C_USE_COMMON_UNDERFLOW = "0" *) (* C_USE_DEFAULT_SETTINGS = "0" *) 
(* C_USE_DOUT_RST = "1" *) (* C_USE_ECC = "0" *) (* C_USE_ECC_AXIS = "0" *) 
(* C_USE_ECC_RACH = "0" *) (* C_USE_ECC_RDCH = "0" *) (* C_USE_ECC_WACH = "0" *) 
(* C_USE_ECC_WDCH = "0" *) (* C_USE_ECC_WRCH = "0" *) (* C_USE_EMBEDDED_REG = "0" *) 
(* C_USE_FIFO16_FLAGS = "0" *) (* C_USE_FWFT_DATA_COUNT = "0" *) (* C_USE_PIPELINE_REG = "0" *) 
(* C_VALID_LOW = "0" *) (* C_WACH_TYPE = "0" *) (* C_WDCH_TYPE = "0" *) 
(* C_WRCH_TYPE = "0" *) (* C_WR_ACK_LOW = "0" *) (* C_WR_DATA_COUNT_WIDTH = "10" *) 
(* C_WR_DEPTH = "1024" *) (* C_WR_DEPTH_AXIS = "1024" *) (* C_WR_DEPTH_RACH = "16" *) 
(* C_WR_DEPTH_RDCH = "16" *) (* C_WR_DEPTH_WACH = "16" *) (* C_WR_DEPTH_WDCH = "16" *) 
(* C_WR_DEPTH_WRCH = "16" *) (* C_WR_FREQ = "1" *) (* C_WR_PNTR_WIDTH = "10" *) 
(* C_WR_PNTR_WIDTH_AXIS = "10" *) (* C_WR_PNTR_WIDTH_RACH = "4" *) (* C_WR_PNTR_WIDTH_RDCH = "4" *) 
(* C_WR_PNTR_WIDTH_WACH = "4" *) (* C_WR_PNTR_WIDTH_WDCH = "4" *) (* C_WR_PNTR_WIDTH_WRCH = "4" *) 
(* C_WR_RESPONSE_LATENCY = "1" *) (* ORIG_REF_NAME = "fifo_generator_v13_1_4" *) 
module axi_clock_converter_dramslim_fifo_generator_v13_1_4
   (backup,
    backup_marker,
    clk,
    rst,
    srst,
    wr_clk,
    wr_rst,
    rd_clk,
    rd_rst,
    din,
    wr_en,
    rd_en,
    prog_empty_thresh,
    prog_empty_thresh_assert,
    prog_empty_thresh_negate,
    prog_full_thresh,
    prog_full_thresh_assert,
    prog_full_thresh_negate,
    int_clk,
    injectdbiterr,
    injectsbiterr,
    sleep,
    dout,
    full,
    almost_full,
    wr_ack,
    overflow,
    empty,
    almost_empty,
    valid,
    underflow,
    data_count,
    rd_data_count,
    wr_data_count,
    prog_full,
    prog_empty,
    sbiterr,
    dbiterr,
    wr_rst_busy,
    rd_rst_busy,
    m_aclk,
    s_aclk,
    s_aresetn,
    m_aclk_en,
    s_aclk_en,
    s_axi_awid,
    s_axi_awaddr,
    s_axi_awlen,
    s_axi_awsize,
    s_axi_awburst,
    s_axi_awlock,
    s_axi_awcache,
    s_axi_awprot,
    s_axi_awqos,
    s_axi_awregion,
    s_axi_awuser,
    s_axi_awvalid,
    s_axi_awready,
    s_axi_wid,
    s_axi_wdata,
    s_axi_wstrb,
    s_axi_wlast,
    s_axi_wuser,
    s_axi_wvalid,
    s_axi_wready,
    s_axi_bid,
    s_axi_bresp,
    s_axi_buser,
    s_axi_bvalid,
    s_axi_bready,
    m_axi_awid,
    m_axi_awaddr,
    m_axi_awlen,
    m_axi_awsize,
    m_axi_awburst,
    m_axi_awlock,
    m_axi_awcache,
    m_axi_awprot,
    m_axi_awqos,
    m_axi_awregion,
    m_axi_awuser,
    m_axi_awvalid,
    m_axi_awready,
    m_axi_wid,
    m_axi_wdata,
    m_axi_wstrb,
    m_axi_wlast,
    m_axi_wuser,
    m_axi_wvalid,
    m_axi_wready,
    m_axi_bid,
    m_axi_bresp,
    m_axi_buser,
    m_axi_bvalid,
    m_axi_bready,
    s_axi_arid,
    s_axi_araddr,
    s_axi_arlen,
    s_axi_arsize,
    s_axi_arburst,
    s_axi_arlock,
    s_axi_arcache,
    s_axi_arprot,
    s_axi_arqos,
    s_axi_arregion,
    s_axi_aruser,
    s_axi_arvalid,
    s_axi_arready,
    s_axi_rid,
    s_axi_rdata,
    s_axi_rresp,
    s_axi_rlast,
    s_axi_ruser,
    s_axi_rvalid,
    s_axi_rready,
    m_axi_arid,
    m_axi_araddr,
    m_axi_arlen,
    m_axi_arsize,
    m_axi_arburst,
    m_axi_arlock,
    m_axi_arcache,
    m_axi_arprot,
    m_axi_arqos,
    m_axi_arregion,
    m_axi_aruser,
    m_axi_arvalid,
    m_axi_arready,
    m_axi_rid,
    m_axi_rdata,
    m_axi_rresp,
    m_axi_rlast,
    m_axi_ruser,
    m_axi_rvalid,
    m_axi_rready,
    s_axis_tvalid,
    s_axis_tready,
    s_axis_tdata,
    s_axis_tstrb,
    s_axis_tkeep,
    s_axis_tlast,
    s_axis_tid,
    s_axis_tdest,
    s_axis_tuser,
    m_axis_tvalid,
    m_axis_tready,
    m_axis_tdata,
    m_axis_tstrb,
    m_axis_tkeep,
    m_axis_tlast,
    m_axis_tid,
    m_axis_tdest,
    m_axis_tuser,
    axi_aw_injectsbiterr,
    axi_aw_injectdbiterr,
    axi_aw_prog_full_thresh,
    axi_aw_prog_empty_thresh,
    axi_aw_data_count,
    axi_aw_wr_data_count,
    axi_aw_rd_data_count,
    axi_aw_sbiterr,
    axi_aw_dbiterr,
    axi_aw_overflow,
    axi_aw_underflow,
    axi_aw_prog_full,
    axi_aw_prog_empty,
    axi_w_injectsbiterr,
    axi_w_injectdbiterr,
    axi_w_prog_full_thresh,
    axi_w_prog_empty_thresh,
    axi_w_data_count,
    axi_w_wr_data_count,
    axi_w_rd_data_count,
    axi_w_sbiterr,
    axi_w_dbiterr,
    axi_w_overflow,
    axi_w_underflow,
    axi_w_prog_full,
    axi_w_prog_empty,
    axi_b_injectsbiterr,
    axi_b_injectdbiterr,
    axi_b_prog_full_thresh,
    axi_b_prog_empty_thresh,
    axi_b_data_count,
    axi_b_wr_data_count,
    axi_b_rd_data_count,
    axi_b_sbiterr,
    axi_b_dbiterr,
    axi_b_overflow,
    axi_b_underflow,
    axi_b_prog_full,
    axi_b_prog_empty,
    axi_ar_injectsbiterr,
    axi_ar_injectdbiterr,
    axi_ar_prog_full_thresh,
    axi_ar_prog_empty_thresh,
    axi_ar_data_count,
    axi_ar_wr_data_count,
    axi_ar_rd_data_count,
    axi_ar_sbiterr,
    axi_ar_dbiterr,
    axi_ar_overflow,
    axi_ar_underflow,
    axi_ar_prog_full,
    axi_ar_prog_empty,
    axi_r_injectsbiterr,
    axi_r_injectdbiterr,
    axi_r_prog_full_thresh,
    axi_r_prog_empty_thresh,
    axi_r_data_count,
    axi_r_wr_data_count,
    axi_r_rd_data_count,
    axi_r_sbiterr,
    axi_r_dbiterr,
    axi_r_overflow,
    axi_r_underflow,
    axi_r_prog_full,
    axi_r_prog_empty,
    axis_injectsbiterr,
    axis_injectdbiterr,
    axis_prog_full_thresh,
    axis_prog_empty_thresh,
    axis_data_count,
    axis_wr_data_count,
    axis_rd_data_count,
    axis_sbiterr,
    axis_dbiterr,
    axis_overflow,
    axis_underflow,
    axis_prog_full,
    axis_prog_empty);
  input backup;
  input backup_marker;
  input clk;
  input rst;
  input srst;
  input wr_clk;
  input wr_rst;
  input rd_clk;
  input rd_rst;
  input [17:0]din;
  input wr_en;
  input rd_en;
  input [9:0]prog_empty_thresh;
  input [9:0]prog_empty_thresh_assert;
  input [9:0]prog_empty_thresh_negate;
  input [9:0]prog_full_thresh;
  input [9:0]prog_full_thresh_assert;
  input [9:0]prog_full_thresh_negate;
  input int_clk;
  input injectdbiterr;
  input injectsbiterr;
  input sleep;
  output [17:0]dout;
  output full;
  output almost_full;
  output wr_ack;
  output overflow;
  output empty;
  output almost_empty;
  output valid;
  output underflow;
  output [9:0]data_count;
  output [9:0]rd_data_count;
  output [9:0]wr_data_count;
  output prog_full;
  output prog_empty;
  output sbiterr;
  output dbiterr;
  output wr_rst_busy;
  output rd_rst_busy;
  input m_aclk;
  input s_aclk;
  input s_aresetn;
  input m_aclk_en;
  input s_aclk_en;
  input [15:0]s_axi_awid;
  input [63:0]s_axi_awaddr;
  input [7:0]s_axi_awlen;
  input [2:0]s_axi_awsize;
  input [1:0]s_axi_awburst;
  input [0:0]s_axi_awlock;
  input [3:0]s_axi_awcache;
  input [2:0]s_axi_awprot;
  input [3:0]s_axi_awqos;
  input [3:0]s_axi_awregion;
  input [0:0]s_axi_awuser;
  input s_axi_awvalid;
  output s_axi_awready;
  input [15:0]s_axi_wid;
  input [63:0]s_axi_wdata;
  input [7:0]s_axi_wstrb;
  input s_axi_wlast;
  input [0:0]s_axi_wuser;
  input s_axi_wvalid;
  output s_axi_wready;
  output [15:0]s_axi_bid;
  output [1:0]s_axi_bresp;
  output [0:0]s_axi_buser;
  output s_axi_bvalid;
  input s_axi_bready;
  output [15:0]m_axi_awid;
  output [63:0]m_axi_awaddr;
  output [7:0]m_axi_awlen;
  output [2:0]m_axi_awsize;
  output [1:0]m_axi_awburst;
  output [0:0]m_axi_awlock;
  output [3:0]m_axi_awcache;
  output [2:0]m_axi_awprot;
  output [3:0]m_axi_awqos;
  output [3:0]m_axi_awregion;
  output [0:0]m_axi_awuser;
  output m_axi_awvalid;
  input m_axi_awready;
  output [15:0]m_axi_wid;
  output [63:0]m_axi_wdata;
  output [7:0]m_axi_wstrb;
  output m_axi_wlast;
  output [0:0]m_axi_wuser;
  output m_axi_wvalid;
  input m_axi_wready;
  input [15:0]m_axi_bid;
  input [1:0]m_axi_bresp;
  input [0:0]m_axi_buser;
  input m_axi_bvalid;
  output m_axi_bready;
  input [15:0]s_axi_arid;
  input [63:0]s_axi_araddr;
  input [7:0]s_axi_arlen;
  input [2:0]s_axi_arsize;
  input [1:0]s_axi_arburst;
  input [0:0]s_axi_arlock;
  input [3:0]s_axi_arcache;
  input [2:0]s_axi_arprot;
  input [3:0]s_axi_arqos;
  input [3:0]s_axi_arregion;
  input [0:0]s_axi_aruser;
  input s_axi_arvalid;
  output s_axi_arready;
  output [15:0]s_axi_rid;
  output [63:0]s_axi_rdata;
  output [1:0]s_axi_rresp;
  output s_axi_rlast;
  output [0:0]s_axi_ruser;
  output s_axi_rvalid;
  input s_axi_rready;
  output [15:0]m_axi_arid;
  output [63:0]m_axi_araddr;
  output [7:0]m_axi_arlen;
  output [2:0]m_axi_arsize;
  output [1:0]m_axi_arburst;
  output [0:0]m_axi_arlock;
  output [3:0]m_axi_arcache;
  output [2:0]m_axi_arprot;
  output [3:0]m_axi_arqos;
  output [3:0]m_axi_arregion;
  output [0:0]m_axi_aruser;
  output m_axi_arvalid;
  input m_axi_arready;
  input [15:0]m_axi_rid;
  input [63:0]m_axi_rdata;
  input [1:0]m_axi_rresp;
  input m_axi_rlast;
  input [0:0]m_axi_ruser;
  input m_axi_rvalid;
  output m_axi_rready;
  input s_axis_tvalid;
  output s_axis_tready;
  input [7:0]s_axis_tdata;
  input [0:0]s_axis_tstrb;
  input [0:0]s_axis_tkeep;
  input s_axis_tlast;
  input [0:0]s_axis_tid;
  input [0:0]s_axis_tdest;
  input [3:0]s_axis_tuser;
  output m_axis_tvalid;
  input m_axis_tready;
  output [7:0]m_axis_tdata;
  output [0:0]m_axis_tstrb;
  output [0:0]m_axis_tkeep;
  output m_axis_tlast;
  output [0:0]m_axis_tid;
  output [0:0]m_axis_tdest;
  output [3:0]m_axis_tuser;
  input axi_aw_injectsbiterr;
  input axi_aw_injectdbiterr;
  input [3:0]axi_aw_prog_full_thresh;
  input [3:0]axi_aw_prog_empty_thresh;
  output [4:0]axi_aw_data_count;
  output [4:0]axi_aw_wr_data_count;
  output [4:0]axi_aw_rd_data_count;
  output axi_aw_sbiterr;
  output axi_aw_dbiterr;
  output axi_aw_overflow;
  output axi_aw_underflow;
  output axi_aw_prog_full;
  output axi_aw_prog_empty;
  input axi_w_injectsbiterr;
  input axi_w_injectdbiterr;
  input [3:0]axi_w_prog_full_thresh;
  input [3:0]axi_w_prog_empty_thresh;
  output [4:0]axi_w_data_count;
  output [4:0]axi_w_wr_data_count;
  output [4:0]axi_w_rd_data_count;
  output axi_w_sbiterr;
  output axi_w_dbiterr;
  output axi_w_overflow;
  output axi_w_underflow;
  output axi_w_prog_full;
  output axi_w_prog_empty;
  input axi_b_injectsbiterr;
  input axi_b_injectdbiterr;
  input [3:0]axi_b_prog_full_thresh;
  input [3:0]axi_b_prog_empty_thresh;
  output [4:0]axi_b_data_count;
  output [4:0]axi_b_wr_data_count;
  output [4:0]axi_b_rd_data_count;
  output axi_b_sbiterr;
  output axi_b_dbiterr;
  output axi_b_overflow;
  output axi_b_underflow;
  output axi_b_prog_full;
  output axi_b_prog_empty;
  input axi_ar_injectsbiterr;
  input axi_ar_injectdbiterr;
  input [3:0]axi_ar_prog_full_thresh;
  input [3:0]axi_ar_prog_empty_thresh;
  output [4:0]axi_ar_data_count;
  output [4:0]axi_ar_wr_data_count;
  output [4:0]axi_ar_rd_data_count;
  output axi_ar_sbiterr;
  output axi_ar_dbiterr;
  output axi_ar_overflow;
  output axi_ar_underflow;
  output axi_ar_prog_full;
  output axi_ar_prog_empty;
  input axi_r_injectsbiterr;
  input axi_r_injectdbiterr;
  input [3:0]axi_r_prog_full_thresh;
  input [3:0]axi_r_prog_empty_thresh;
  output [4:0]axi_r_data_count;
  output [4:0]axi_r_wr_data_count;
  output [4:0]axi_r_rd_data_count;
  output axi_r_sbiterr;
  output axi_r_dbiterr;
  output axi_r_overflow;
  output axi_r_underflow;
  output axi_r_prog_full;
  output axi_r_prog_empty;
  input axis_injectsbiterr;
  input axis_injectdbiterr;
  input [9:0]axis_prog_full_thresh;
  input [9:0]axis_prog_empty_thresh;
  output [10:0]axis_data_count;
  output [10:0]axis_wr_data_count;
  output [10:0]axis_rd_data_count;
  output axis_sbiterr;
  output axis_dbiterr;
  output axis_overflow;
  output axis_underflow;
  output axis_prog_full;
  output axis_prog_empty;

  wire \<const0> ;
  wire m_aclk;
  wire [63:0]m_axi_araddr;
  wire [1:0]m_axi_arburst;
  wire [3:0]m_axi_arcache;
  wire [15:0]m_axi_arid;
  wire [7:0]m_axi_arlen;
  wire [0:0]m_axi_arlock;
  wire [2:0]m_axi_arprot;
  wire [3:0]m_axi_arqos;
  wire m_axi_arready;
  wire [3:0]m_axi_arregion;
  wire [2:0]m_axi_arsize;
  wire m_axi_arvalid;
  wire [63:0]m_axi_awaddr;
  wire [1:0]m_axi_awburst;
  wire [3:0]m_axi_awcache;
  wire [15:0]m_axi_awid;
  wire [7:0]m_axi_awlen;
  wire [0:0]m_axi_awlock;
  wire [2:0]m_axi_awprot;
  wire [3:0]m_axi_awqos;
  wire m_axi_awready;
  wire [3:0]m_axi_awregion;
  wire [2:0]m_axi_awsize;
  wire m_axi_awvalid;
  wire [15:0]m_axi_bid;
  wire m_axi_bready;
  wire [1:0]m_axi_bresp;
  wire m_axi_bvalid;
  wire [63:0]m_axi_rdata;
  wire [15:0]m_axi_rid;
  wire m_axi_rlast;
  wire m_axi_rready;
  wire [1:0]m_axi_rresp;
  wire m_axi_rvalid;
  wire [63:0]m_axi_wdata;
  wire m_axi_wlast;
  wire m_axi_wready;
  wire [7:0]m_axi_wstrb;
  wire m_axi_wvalid;
  wire s_aclk;
  wire s_aresetn;
  wire [63:0]s_axi_araddr;
  wire [1:0]s_axi_arburst;
  wire [3:0]s_axi_arcache;
  wire [15:0]s_axi_arid;
  wire [7:0]s_axi_arlen;
  wire [0:0]s_axi_arlock;
  wire [2:0]s_axi_arprot;
  wire [3:0]s_axi_arqos;
  wire s_axi_arready;
  wire [3:0]s_axi_arregion;
  wire [2:0]s_axi_arsize;
  wire s_axi_arvalid;
  wire [63:0]s_axi_awaddr;
  wire [1:0]s_axi_awburst;
  wire [3:0]s_axi_awcache;
  wire [15:0]s_axi_awid;
  wire [7:0]s_axi_awlen;
  wire [0:0]s_axi_awlock;
  wire [2:0]s_axi_awprot;
  wire [3:0]s_axi_awqos;
  wire s_axi_awready;
  wire [3:0]s_axi_awregion;
  wire [2:0]s_axi_awsize;
  wire s_axi_awvalid;
  wire [15:0]s_axi_bid;
  wire s_axi_bready;
  wire [1:0]s_axi_bresp;
  wire s_axi_bvalid;
  wire [63:0]s_axi_rdata;
  wire [15:0]s_axi_rid;
  wire s_axi_rlast;
  wire s_axi_rready;
  wire [1:0]s_axi_rresp;
  wire s_axi_rvalid;
  wire [63:0]s_axi_wdata;
  wire s_axi_wlast;
  wire s_axi_wready;
  wire [7:0]s_axi_wstrb;
  wire s_axi_wvalid;

  assign almost_empty = \<const0> ;
  assign almost_full = \<const0> ;
  assign axi_ar_data_count[4] = \<const0> ;
  assign axi_ar_data_count[3] = \<const0> ;
  assign axi_ar_data_count[2] = \<const0> ;
  assign axi_ar_data_count[1] = \<const0> ;
  assign axi_ar_data_count[0] = \<const0> ;
  assign axi_ar_dbiterr = \<const0> ;
  assign axi_ar_overflow = \<const0> ;
  assign axi_ar_prog_empty = \<const0> ;
  assign axi_ar_prog_full = \<const0> ;
  assign axi_ar_rd_data_count[4] = \<const0> ;
  assign axi_ar_rd_data_count[3] = \<const0> ;
  assign axi_ar_rd_data_count[2] = \<const0> ;
  assign axi_ar_rd_data_count[1] = \<const0> ;
  assign axi_ar_rd_data_count[0] = \<const0> ;
  assign axi_ar_sbiterr = \<const0> ;
  assign axi_ar_underflow = \<const0> ;
  assign axi_ar_wr_data_count[4] = \<const0> ;
  assign axi_ar_wr_data_count[3] = \<const0> ;
  assign axi_ar_wr_data_count[2] = \<const0> ;
  assign axi_ar_wr_data_count[1] = \<const0> ;
  assign axi_ar_wr_data_count[0] = \<const0> ;
  assign axi_aw_data_count[4] = \<const0> ;
  assign axi_aw_data_count[3] = \<const0> ;
  assign axi_aw_data_count[2] = \<const0> ;
  assign axi_aw_data_count[1] = \<const0> ;
  assign axi_aw_data_count[0] = \<const0> ;
  assign axi_aw_dbiterr = \<const0> ;
  assign axi_aw_overflow = \<const0> ;
  assign axi_aw_prog_empty = \<const0> ;
  assign axi_aw_prog_full = \<const0> ;
  assign axi_aw_rd_data_count[4] = \<const0> ;
  assign axi_aw_rd_data_count[3] = \<const0> ;
  assign axi_aw_rd_data_count[2] = \<const0> ;
  assign axi_aw_rd_data_count[1] = \<const0> ;
  assign axi_aw_rd_data_count[0] = \<const0> ;
  assign axi_aw_sbiterr = \<const0> ;
  assign axi_aw_underflow = \<const0> ;
  assign axi_aw_wr_data_count[4] = \<const0> ;
  assign axi_aw_wr_data_count[3] = \<const0> ;
  assign axi_aw_wr_data_count[2] = \<const0> ;
  assign axi_aw_wr_data_count[1] = \<const0> ;
  assign axi_aw_wr_data_count[0] = \<const0> ;
  assign axi_b_data_count[4] = \<const0> ;
  assign axi_b_data_count[3] = \<const0> ;
  assign axi_b_data_count[2] = \<const0> ;
  assign axi_b_data_count[1] = \<const0> ;
  assign axi_b_data_count[0] = \<const0> ;
  assign axi_b_dbiterr = \<const0> ;
  assign axi_b_overflow = \<const0> ;
  assign axi_b_prog_empty = \<const0> ;
  assign axi_b_prog_full = \<const0> ;
  assign axi_b_rd_data_count[4] = \<const0> ;
  assign axi_b_rd_data_count[3] = \<const0> ;
  assign axi_b_rd_data_count[2] = \<const0> ;
  assign axi_b_rd_data_count[1] = \<const0> ;
  assign axi_b_rd_data_count[0] = \<const0> ;
  assign axi_b_sbiterr = \<const0> ;
  assign axi_b_underflow = \<const0> ;
  assign axi_b_wr_data_count[4] = \<const0> ;
  assign axi_b_wr_data_count[3] = \<const0> ;
  assign axi_b_wr_data_count[2] = \<const0> ;
  assign axi_b_wr_data_count[1] = \<const0> ;
  assign axi_b_wr_data_count[0] = \<const0> ;
  assign axi_r_data_count[4] = \<const0> ;
  assign axi_r_data_count[3] = \<const0> ;
  assign axi_r_data_count[2] = \<const0> ;
  assign axi_r_data_count[1] = \<const0> ;
  assign axi_r_data_count[0] = \<const0> ;
  assign axi_r_dbiterr = \<const0> ;
  assign axi_r_overflow = \<const0> ;
  assign axi_r_prog_empty = \<const0> ;
  assign axi_r_prog_full = \<const0> ;
  assign axi_r_rd_data_count[4] = \<const0> ;
  assign axi_r_rd_data_count[3] = \<const0> ;
  assign axi_r_rd_data_count[2] = \<const0> ;
  assign axi_r_rd_data_count[1] = \<const0> ;
  assign axi_r_rd_data_count[0] = \<const0> ;
  assign axi_r_sbiterr = \<const0> ;
  assign axi_r_underflow = \<const0> ;
  assign axi_r_wr_data_count[4] = \<const0> ;
  assign axi_r_wr_data_count[3] = \<const0> ;
  assign axi_r_wr_data_count[2] = \<const0> ;
  assign axi_r_wr_data_count[1] = \<const0> ;
  assign axi_r_wr_data_count[0] = \<const0> ;
  assign axi_w_data_count[4] = \<const0> ;
  assign axi_w_data_count[3] = \<const0> ;
  assign axi_w_data_count[2] = \<const0> ;
  assign axi_w_data_count[1] = \<const0> ;
  assign axi_w_data_count[0] = \<const0> ;
  assign axi_w_dbiterr = \<const0> ;
  assign axi_w_overflow = \<const0> ;
  assign axi_w_prog_empty = \<const0> ;
  assign axi_w_prog_full = \<const0> ;
  assign axi_w_rd_data_count[4] = \<const0> ;
  assign axi_w_rd_data_count[3] = \<const0> ;
  assign axi_w_rd_data_count[2] = \<const0> ;
  assign axi_w_rd_data_count[1] = \<const0> ;
  assign axi_w_rd_data_count[0] = \<const0> ;
  assign axi_w_sbiterr = \<const0> ;
  assign axi_w_underflow = \<const0> ;
  assign axi_w_wr_data_count[4] = \<const0> ;
  assign axi_w_wr_data_count[3] = \<const0> ;
  assign axi_w_wr_data_count[2] = \<const0> ;
  assign axi_w_wr_data_count[1] = \<const0> ;
  assign axi_w_wr_data_count[0] = \<const0> ;
  assign axis_data_count[10] = \<const0> ;
  assign axis_data_count[9] = \<const0> ;
  assign axis_data_count[8] = \<const0> ;
  assign axis_data_count[7] = \<const0> ;
  assign axis_data_count[6] = \<const0> ;
  assign axis_data_count[5] = \<const0> ;
  assign axis_data_count[4] = \<const0> ;
  assign axis_data_count[3] = \<const0> ;
  assign axis_data_count[2] = \<const0> ;
  assign axis_data_count[1] = \<const0> ;
  assign axis_data_count[0] = \<const0> ;
  assign axis_dbiterr = \<const0> ;
  assign axis_overflow = \<const0> ;
  assign axis_prog_empty = \<const0> ;
  assign axis_prog_full = \<const0> ;
  assign axis_rd_data_count[10] = \<const0> ;
  assign axis_rd_data_count[9] = \<const0> ;
  assign axis_rd_data_count[8] = \<const0> ;
  assign axis_rd_data_count[7] = \<const0> ;
  assign axis_rd_data_count[6] = \<const0> ;
  assign axis_rd_data_count[5] = \<const0> ;
  assign axis_rd_data_count[4] = \<const0> ;
  assign axis_rd_data_count[3] = \<const0> ;
  assign axis_rd_data_count[2] = \<const0> ;
  assign axis_rd_data_count[1] = \<const0> ;
  assign axis_rd_data_count[0] = \<const0> ;
  assign axis_sbiterr = \<const0> ;
  assign axis_underflow = \<const0> ;
  assign axis_wr_data_count[10] = \<const0> ;
  assign axis_wr_data_count[9] = \<const0> ;
  assign axis_wr_data_count[8] = \<const0> ;
  assign axis_wr_data_count[7] = \<const0> ;
  assign axis_wr_data_count[6] = \<const0> ;
  assign axis_wr_data_count[5] = \<const0> ;
  assign axis_wr_data_count[4] = \<const0> ;
  assign axis_wr_data_count[3] = \<const0> ;
  assign axis_wr_data_count[2] = \<const0> ;
  assign axis_wr_data_count[1] = \<const0> ;
  assign axis_wr_data_count[0] = \<const0> ;
  assign data_count[9] = \<const0> ;
  assign data_count[8] = \<const0> ;
  assign data_count[7] = \<const0> ;
  assign data_count[6] = \<const0> ;
  assign data_count[5] = \<const0> ;
  assign data_count[4] = \<const0> ;
  assign data_count[3] = \<const0> ;
  assign data_count[2] = \<const0> ;
  assign data_count[1] = \<const0> ;
  assign data_count[0] = \<const0> ;
  assign dbiterr = \<const0> ;
  assign dout[17] = \<const0> ;
  assign dout[16] = \<const0> ;
  assign dout[15] = \<const0> ;
  assign dout[14] = \<const0> ;
  assign dout[13] = \<const0> ;
  assign dout[12] = \<const0> ;
  assign dout[11] = \<const0> ;
  assign dout[10] = \<const0> ;
  assign dout[9] = \<const0> ;
  assign dout[8] = \<const0> ;
  assign dout[7] = \<const0> ;
  assign dout[6] = \<const0> ;
  assign dout[5] = \<const0> ;
  assign dout[4] = \<const0> ;
  assign dout[3] = \<const0> ;
  assign dout[2] = \<const0> ;
  assign dout[1] = \<const0> ;
  assign dout[0] = \<const0> ;
  assign empty = \<const0> ;
  assign full = \<const0> ;
  assign m_axi_aruser[0] = \<const0> ;
  assign m_axi_awuser[0] = \<const0> ;
  assign m_axi_wid[15] = \<const0> ;
  assign m_axi_wid[14] = \<const0> ;
  assign m_axi_wid[13] = \<const0> ;
  assign m_axi_wid[12] = \<const0> ;
  assign m_axi_wid[11] = \<const0> ;
  assign m_axi_wid[10] = \<const0> ;
  assign m_axi_wid[9] = \<const0> ;
  assign m_axi_wid[8] = \<const0> ;
  assign m_axi_wid[7] = \<const0> ;
  assign m_axi_wid[6] = \<const0> ;
  assign m_axi_wid[5] = \<const0> ;
  assign m_axi_wid[4] = \<const0> ;
  assign m_axi_wid[3] = \<const0> ;
  assign m_axi_wid[2] = \<const0> ;
  assign m_axi_wid[1] = \<const0> ;
  assign m_axi_wid[0] = \<const0> ;
  assign m_axi_wuser[0] = \<const0> ;
  assign m_axis_tdata[7] = \<const0> ;
  assign m_axis_tdata[6] = \<const0> ;
  assign m_axis_tdata[5] = \<const0> ;
  assign m_axis_tdata[4] = \<const0> ;
  assign m_axis_tdata[3] = \<const0> ;
  assign m_axis_tdata[2] = \<const0> ;
  assign m_axis_tdata[1] = \<const0> ;
  assign m_axis_tdata[0] = \<const0> ;
  assign m_axis_tdest[0] = \<const0> ;
  assign m_axis_tid[0] = \<const0> ;
  assign m_axis_tkeep[0] = \<const0> ;
  assign m_axis_tlast = \<const0> ;
  assign m_axis_tstrb[0] = \<const0> ;
  assign m_axis_tuser[3] = \<const0> ;
  assign m_axis_tuser[2] = \<const0> ;
  assign m_axis_tuser[1] = \<const0> ;
  assign m_axis_tuser[0] = \<const0> ;
  assign m_axis_tvalid = \<const0> ;
  assign overflow = \<const0> ;
  assign prog_empty = \<const0> ;
  assign prog_full = \<const0> ;
  assign rd_data_count[9] = \<const0> ;
  assign rd_data_count[8] = \<const0> ;
  assign rd_data_count[7] = \<const0> ;
  assign rd_data_count[6] = \<const0> ;
  assign rd_data_count[5] = \<const0> ;
  assign rd_data_count[4] = \<const0> ;
  assign rd_data_count[3] = \<const0> ;
  assign rd_data_count[2] = \<const0> ;
  assign rd_data_count[1] = \<const0> ;
  assign rd_data_count[0] = \<const0> ;
  assign rd_rst_busy = \<const0> ;
  assign s_axi_buser[0] = \<const0> ;
  assign s_axi_ruser[0] = \<const0> ;
  assign s_axis_tready = \<const0> ;
  assign sbiterr = \<const0> ;
  assign underflow = \<const0> ;
  assign valid = \<const0> ;
  assign wr_ack = \<const0> ;
  assign wr_data_count[9] = \<const0> ;
  assign wr_data_count[8] = \<const0> ;
  assign wr_data_count[7] = \<const0> ;
  assign wr_data_count[6] = \<const0> ;
  assign wr_data_count[5] = \<const0> ;
  assign wr_data_count[4] = \<const0> ;
  assign wr_data_count[3] = \<const0> ;
  assign wr_data_count[2] = \<const0> ;
  assign wr_data_count[1] = \<const0> ;
  assign wr_data_count[0] = \<const0> ;
  assign wr_rst_busy = \<const0> ;
  GND GND
       (.G(\<const0> ));
  axi_clock_converter_dramslim_fifo_generator_v13_1_4_synth inst_fifo_gen
       (.DI({s_axi_awid,s_axi_awaddr,s_axi_awlen,s_axi_awsize,s_axi_awburst,s_axi_awlock,s_axi_awcache,s_axi_awprot,s_axi_awqos,s_axi_awregion}),
        .I133({s_axi_wdata,s_axi_wstrb,s_axi_wlast}),
        .I137({m_axi_bid,m_axi_bresp}),
        .I141({s_axi_arid,s_axi_araddr,s_axi_arlen,s_axi_arsize,s_axi_arburst,s_axi_arlock,s_axi_arcache,s_axi_arprot,s_axi_arqos,s_axi_arregion}),
        .I145({m_axi_rid,m_axi_rdata,m_axi_rresp,m_axi_rlast}),
        .Q({m_axi_awid,m_axi_awaddr,m_axi_awlen,m_axi_awsize,m_axi_awburst,m_axi_awlock,m_axi_awcache,m_axi_awprot,m_axi_awqos,m_axi_awregion}),
        .m_aclk(m_aclk),
        .\m_axi_arid[15] ({m_axi_arid,m_axi_araddr,m_axi_arlen,m_axi_arsize,m_axi_arburst,m_axi_arlock,m_axi_arcache,m_axi_arprot,m_axi_arqos,m_axi_arregion}),
        .m_axi_arready(m_axi_arready),
        .m_axi_arvalid(m_axi_arvalid),
        .m_axi_awready(m_axi_awready),
        .m_axi_awvalid(m_axi_awvalid),
        .m_axi_bready(m_axi_bready),
        .m_axi_bvalid(m_axi_bvalid),
        .m_axi_rready(m_axi_rready),
        .m_axi_rvalid(m_axi_rvalid),
        .\m_axi_wdata[63] ({m_axi_wdata,m_axi_wstrb,m_axi_wlast}),
        .m_axi_wready(m_axi_wready),
        .m_axi_wvalid(m_axi_wvalid),
        .s_aclk(s_aclk),
        .s_aresetn(s_aresetn),
        .s_axi_arready(s_axi_arready),
        .s_axi_arvalid(s_axi_arvalid),
        .s_axi_awready(s_axi_awready),
        .s_axi_awvalid(s_axi_awvalid),
        .\s_axi_bid[15] ({s_axi_bid,s_axi_bresp}),
        .s_axi_bready(s_axi_bready),
        .s_axi_bvalid(s_axi_bvalid),
        .\s_axi_rid[15] ({s_axi_rid,s_axi_rdata,s_axi_rresp,s_axi_rlast}),
        .s_axi_rready(s_axi_rready),
        .s_axi_rvalid(s_axi_rvalid),
        .s_axi_wready(s_axi_wready),
        .s_axi_wvalid(s_axi_wvalid));
endmodule

(* ORIG_REF_NAME = "fifo_generator_v13_1_4_synth" *) 
module axi_clock_converter_dramslim_fifo_generator_v13_1_4_synth
   (Q,
    \m_axi_wdata[63] ,
    \s_axi_bid[15] ,
    \m_axi_arid[15] ,
    \s_axi_rid[15] ,
    s_axi_awready,
    s_axi_wready,
    s_axi_bvalid,
    m_axi_awvalid,
    m_axi_wvalid,
    m_axi_bready,
    s_axi_arready,
    s_axi_rvalid,
    m_axi_arvalid,
    m_axi_rready,
    m_aclk,
    s_aclk,
    DI,
    I133,
    I137,
    I141,
    I145,
    m_axi_awready,
    m_axi_wready,
    m_axi_bvalid,
    m_axi_arready,
    m_axi_rvalid,
    s_axi_awvalid,
    s_axi_wvalid,
    s_axi_bready,
    s_axi_arvalid,
    s_axi_rready,
    s_aresetn);
  output [108:0]Q;
  output [72:0]\m_axi_wdata[63] ;
  output [17:0]\s_axi_bid[15] ;
  output [108:0]\m_axi_arid[15] ;
  output [82:0]\s_axi_rid[15] ;
  output s_axi_awready;
  output s_axi_wready;
  output s_axi_bvalid;
  output m_axi_awvalid;
  output m_axi_wvalid;
  output m_axi_bready;
  output s_axi_arready;
  output s_axi_rvalid;
  output m_axi_arvalid;
  output m_axi_rready;
  input m_aclk;
  input s_aclk;
  input [108:0]DI;
  input [72:0]I133;
  input [17:0]I137;
  input [108:0]I141;
  input [82:0]I145;
  input m_axi_awready;
  input m_axi_wready;
  input m_axi_bvalid;
  input m_axi_arready;
  input m_axi_rvalid;
  input s_axi_awvalid;
  input s_axi_wvalid;
  input s_axi_bready;
  input s_axi_arvalid;
  input s_axi_rready;
  input s_aresetn;

  wire [108:0]DI;
  wire [72:0]I133;
  wire [17:0]I137;
  wire [108:0]I141;
  wire [82:0]I145;
  wire [108:0]Q;
  wire inverted_reset;
  wire m_aclk;
  wire [108:0]\m_axi_arid[15] ;
  wire m_axi_arready;
  wire m_axi_arvalid;
  wire m_axi_awready;
  wire m_axi_awvalid;
  wire m_axi_bready;
  wire m_axi_bvalid;
  wire m_axi_rready;
  wire m_axi_rvalid;
  wire [72:0]\m_axi_wdata[63] ;
  wire m_axi_wready;
  wire m_axi_wvalid;
  wire s_aclk;
  wire s_aresetn;
  wire s_axi_arready;
  wire s_axi_arvalid;
  wire s_axi_awready;
  wire s_axi_awvalid;
  wire [17:0]\s_axi_bid[15] ;
  wire s_axi_bready;
  wire s_axi_bvalid;
  wire [82:0]\s_axi_rid[15] ;
  wire s_axi_rready;
  wire s_axi_rvalid;
  wire s_axi_wready;
  wire s_axi_wvalid;

  axi_clock_converter_dramslim_fifo_generator_top \gaxi_full_lite.gread_ch.grach2.axi_rach 
       (.I141(I141),
        .inverted_reset(inverted_reset),
        .m_aclk(m_aclk),
        .\m_axi_arid[15] (\m_axi_arid[15] ),
        .m_axi_arready(m_axi_arready),
        .m_axi_arvalid(m_axi_arvalid),
        .s_aclk(s_aclk),
        .s_axi_arready(s_axi_arready),
        .s_axi_arvalid(s_axi_arvalid));
  axi_clock_converter_dramslim_fifo_generator_top__parameterized2 \gaxi_full_lite.gread_ch.grdch2.axi_rdch 
       (.I145(I145),
        .inverted_reset(inverted_reset),
        .m_aclk(m_aclk),
        .m_axi_rready(m_axi_rready),
        .m_axi_rvalid(m_axi_rvalid),
        .s_aclk(s_aclk),
        .s_aresetn(s_aresetn),
        .\s_axi_rid[15] (\s_axi_rid[15] ),
        .s_axi_rready(s_axi_rready),
        .s_axi_rvalid(s_axi_rvalid));
  axi_clock_converter_dramslim_fifo_generator_top_0 \gaxi_full_lite.gwrite_ch.gwach2.axi_wach 
       (.DI(DI),
        .Q(Q),
        .inverted_reset(inverted_reset),
        .m_aclk(m_aclk),
        .m_axi_awready(m_axi_awready),
        .m_axi_awvalid(m_axi_awvalid),
        .s_aclk(s_aclk),
        .s_axi_awready(s_axi_awready),
        .s_axi_awvalid(s_axi_awvalid));
  axi_clock_converter_dramslim_fifo_generator_top__parameterized0 \gaxi_full_lite.gwrite_ch.gwdch2.axi_wdch 
       (.I133(I133),
        .inverted_reset(inverted_reset),
        .m_aclk(m_aclk),
        .\m_axi_wdata[63] (\m_axi_wdata[63] ),
        .m_axi_wready(m_axi_wready),
        .m_axi_wvalid(m_axi_wvalid),
        .s_aclk(s_aclk),
        .s_axi_wready(s_axi_wready),
        .s_axi_wvalid(s_axi_wvalid));
  axi_clock_converter_dramslim_fifo_generator_top__parameterized1 \gaxi_full_lite.gwrite_ch.gwrch2.axi_wrch 
       (.I137(I137),
        .inverted_reset(inverted_reset),
        .m_aclk(m_aclk),
        .m_axi_bready(m_axi_bready),
        .m_axi_bvalid(m_axi_bvalid),
        .s_aclk(s_aclk),
        .\s_axi_bid[15] (\s_axi_bid[15] ),
        .s_axi_bready(s_axi_bready),
        .s_axi_bvalid(s_axi_bvalid));
endmodule

(* ORIG_REF_NAME = "memory" *) 
module axi_clock_converter_dramslim_memory
   (Q,
    E,
    m_aclk,
    s_aclk,
    ram_full_fb_i_reg,
    DI,
    \gc0.count_d1_reg[3] ,
    \gic0.gc0.count_d2_reg[3] ,
    \gpregsm1.curr_fwft_state_reg[1] );
  output [108:0]Q;
  input [0:0]E;
  input m_aclk;
  input s_aclk;
  input [0:0]ram_full_fb_i_reg;
  input [108:0]DI;
  input [3:0]\gc0.count_d1_reg[3] ;
  input [3:0]\gic0.gc0.count_d2_reg[3] ;
  input [0:0]\gpregsm1.curr_fwft_state_reg[1] ;

  wire [108:0]DI;
  wire [0:0]E;
  wire [108:0]Q;
  wire [3:0]\gc0.count_d1_reg[3] ;
  wire \gdm.dm_gen.dm_n_0 ;
  wire \gdm.dm_gen.dm_n_1 ;
  wire \gdm.dm_gen.dm_n_10 ;
  wire \gdm.dm_gen.dm_n_100 ;
  wire \gdm.dm_gen.dm_n_101 ;
  wire \gdm.dm_gen.dm_n_102 ;
  wire \gdm.dm_gen.dm_n_103 ;
  wire \gdm.dm_gen.dm_n_104 ;
  wire \gdm.dm_gen.dm_n_105 ;
  wire \gdm.dm_gen.dm_n_106 ;
  wire \gdm.dm_gen.dm_n_107 ;
  wire \gdm.dm_gen.dm_n_108 ;
  wire \gdm.dm_gen.dm_n_11 ;
  wire \gdm.dm_gen.dm_n_12 ;
  wire \gdm.dm_gen.dm_n_13 ;
  wire \gdm.dm_gen.dm_n_14 ;
  wire \gdm.dm_gen.dm_n_15 ;
  wire \gdm.dm_gen.dm_n_16 ;
  wire \gdm.dm_gen.dm_n_17 ;
  wire \gdm.dm_gen.dm_n_18 ;
  wire \gdm.dm_gen.dm_n_19 ;
  wire \gdm.dm_gen.dm_n_2 ;
  wire \gdm.dm_gen.dm_n_20 ;
  wire \gdm.dm_gen.dm_n_21 ;
  wire \gdm.dm_gen.dm_n_22 ;
  wire \gdm.dm_gen.dm_n_23 ;
  wire \gdm.dm_gen.dm_n_24 ;
  wire \gdm.dm_gen.dm_n_25 ;
  wire \gdm.dm_gen.dm_n_26 ;
  wire \gdm.dm_gen.dm_n_27 ;
  wire \gdm.dm_gen.dm_n_28 ;
  wire \gdm.dm_gen.dm_n_29 ;
  wire \gdm.dm_gen.dm_n_3 ;
  wire \gdm.dm_gen.dm_n_30 ;
  wire \gdm.dm_gen.dm_n_31 ;
  wire \gdm.dm_gen.dm_n_32 ;
  wire \gdm.dm_gen.dm_n_33 ;
  wire \gdm.dm_gen.dm_n_34 ;
  wire \gdm.dm_gen.dm_n_35 ;
  wire \gdm.dm_gen.dm_n_36 ;
  wire \gdm.dm_gen.dm_n_37 ;
  wire \gdm.dm_gen.dm_n_38 ;
  wire \gdm.dm_gen.dm_n_39 ;
  wire \gdm.dm_gen.dm_n_4 ;
  wire \gdm.dm_gen.dm_n_40 ;
  wire \gdm.dm_gen.dm_n_41 ;
  wire \gdm.dm_gen.dm_n_42 ;
  wire \gdm.dm_gen.dm_n_43 ;
  wire \gdm.dm_gen.dm_n_44 ;
  wire \gdm.dm_gen.dm_n_45 ;
  wire \gdm.dm_gen.dm_n_46 ;
  wire \gdm.dm_gen.dm_n_47 ;
  wire \gdm.dm_gen.dm_n_48 ;
  wire \gdm.dm_gen.dm_n_49 ;
  wire \gdm.dm_gen.dm_n_5 ;
  wire \gdm.dm_gen.dm_n_50 ;
  wire \gdm.dm_gen.dm_n_51 ;
  wire \gdm.dm_gen.dm_n_52 ;
  wire \gdm.dm_gen.dm_n_53 ;
  wire \gdm.dm_gen.dm_n_54 ;
  wire \gdm.dm_gen.dm_n_55 ;
  wire \gdm.dm_gen.dm_n_56 ;
  wire \gdm.dm_gen.dm_n_57 ;
  wire \gdm.dm_gen.dm_n_58 ;
  wire \gdm.dm_gen.dm_n_59 ;
  wire \gdm.dm_gen.dm_n_6 ;
  wire \gdm.dm_gen.dm_n_60 ;
  wire \gdm.dm_gen.dm_n_61 ;
  wire \gdm.dm_gen.dm_n_62 ;
  wire \gdm.dm_gen.dm_n_63 ;
  wire \gdm.dm_gen.dm_n_64 ;
  wire \gdm.dm_gen.dm_n_65 ;
  wire \gdm.dm_gen.dm_n_66 ;
  wire \gdm.dm_gen.dm_n_67 ;
  wire \gdm.dm_gen.dm_n_68 ;
  wire \gdm.dm_gen.dm_n_69 ;
  wire \gdm.dm_gen.dm_n_7 ;
  wire \gdm.dm_gen.dm_n_70 ;
  wire \gdm.dm_gen.dm_n_71 ;
  wire \gdm.dm_gen.dm_n_72 ;
  wire \gdm.dm_gen.dm_n_73 ;
  wire \gdm.dm_gen.dm_n_74 ;
  wire \gdm.dm_gen.dm_n_75 ;
  wire \gdm.dm_gen.dm_n_76 ;
  wire \gdm.dm_gen.dm_n_77 ;
  wire \gdm.dm_gen.dm_n_78 ;
  wire \gdm.dm_gen.dm_n_79 ;
  wire \gdm.dm_gen.dm_n_8 ;
  wire \gdm.dm_gen.dm_n_80 ;
  wire \gdm.dm_gen.dm_n_81 ;
  wire \gdm.dm_gen.dm_n_82 ;
  wire \gdm.dm_gen.dm_n_83 ;
  wire \gdm.dm_gen.dm_n_84 ;
  wire \gdm.dm_gen.dm_n_85 ;
  wire \gdm.dm_gen.dm_n_86 ;
  wire \gdm.dm_gen.dm_n_87 ;
  wire \gdm.dm_gen.dm_n_88 ;
  wire \gdm.dm_gen.dm_n_89 ;
  wire \gdm.dm_gen.dm_n_9 ;
  wire \gdm.dm_gen.dm_n_90 ;
  wire \gdm.dm_gen.dm_n_91 ;
  wire \gdm.dm_gen.dm_n_92 ;
  wire \gdm.dm_gen.dm_n_93 ;
  wire \gdm.dm_gen.dm_n_94 ;
  wire \gdm.dm_gen.dm_n_95 ;
  wire \gdm.dm_gen.dm_n_96 ;
  wire \gdm.dm_gen.dm_n_97 ;
  wire \gdm.dm_gen.dm_n_98 ;
  wire \gdm.dm_gen.dm_n_99 ;
  wire [3:0]\gic0.gc0.count_d2_reg[3] ;
  wire [0:0]\gpregsm1.curr_fwft_state_reg[1] ;
  wire m_aclk;
  wire [0:0]ram_full_fb_i_reg;
  wire s_aclk;

  axi_clock_converter_dramslim_dmem \gdm.dm_gen.dm 
       (.DI(DI),
        .dout_i({\gdm.dm_gen.dm_n_0 ,\gdm.dm_gen.dm_n_1 ,\gdm.dm_gen.dm_n_2 ,\gdm.dm_gen.dm_n_3 ,\gdm.dm_gen.dm_n_4 ,\gdm.dm_gen.dm_n_5 ,\gdm.dm_gen.dm_n_6 ,\gdm.dm_gen.dm_n_7 ,\gdm.dm_gen.dm_n_8 ,\gdm.dm_gen.dm_n_9 ,\gdm.dm_gen.dm_n_10 ,\gdm.dm_gen.dm_n_11 ,\gdm.dm_gen.dm_n_12 ,\gdm.dm_gen.dm_n_13 ,\gdm.dm_gen.dm_n_14 ,\gdm.dm_gen.dm_n_15 ,\gdm.dm_gen.dm_n_16 ,\gdm.dm_gen.dm_n_17 ,\gdm.dm_gen.dm_n_18 ,\gdm.dm_gen.dm_n_19 ,\gdm.dm_gen.dm_n_20 ,\gdm.dm_gen.dm_n_21 ,\gdm.dm_gen.dm_n_22 ,\gdm.dm_gen.dm_n_23 ,\gdm.dm_gen.dm_n_24 ,\gdm.dm_gen.dm_n_25 ,\gdm.dm_gen.dm_n_26 ,\gdm.dm_gen.dm_n_27 ,\gdm.dm_gen.dm_n_28 ,\gdm.dm_gen.dm_n_29 ,\gdm.dm_gen.dm_n_30 ,\gdm.dm_gen.dm_n_31 ,\gdm.dm_gen.dm_n_32 ,\gdm.dm_gen.dm_n_33 ,\gdm.dm_gen.dm_n_34 ,\gdm.dm_gen.dm_n_35 ,\gdm.dm_gen.dm_n_36 ,\gdm.dm_gen.dm_n_37 ,\gdm.dm_gen.dm_n_38 ,\gdm.dm_gen.dm_n_39 ,\gdm.dm_gen.dm_n_40 ,\gdm.dm_gen.dm_n_41 ,\gdm.dm_gen.dm_n_42 ,\gdm.dm_gen.dm_n_43 ,\gdm.dm_gen.dm_n_44 ,\gdm.dm_gen.dm_n_45 ,\gdm.dm_gen.dm_n_46 ,\gdm.dm_gen.dm_n_47 ,\gdm.dm_gen.dm_n_48 ,\gdm.dm_gen.dm_n_49 ,\gdm.dm_gen.dm_n_50 ,\gdm.dm_gen.dm_n_51 ,\gdm.dm_gen.dm_n_52 ,\gdm.dm_gen.dm_n_53 ,\gdm.dm_gen.dm_n_54 ,\gdm.dm_gen.dm_n_55 ,\gdm.dm_gen.dm_n_56 ,\gdm.dm_gen.dm_n_57 ,\gdm.dm_gen.dm_n_58 ,\gdm.dm_gen.dm_n_59 ,\gdm.dm_gen.dm_n_60 ,\gdm.dm_gen.dm_n_61 ,\gdm.dm_gen.dm_n_62 ,\gdm.dm_gen.dm_n_63 ,\gdm.dm_gen.dm_n_64 ,\gdm.dm_gen.dm_n_65 ,\gdm.dm_gen.dm_n_66 ,\gdm.dm_gen.dm_n_67 ,\gdm.dm_gen.dm_n_68 ,\gdm.dm_gen.dm_n_69 ,\gdm.dm_gen.dm_n_70 ,\gdm.dm_gen.dm_n_71 ,\gdm.dm_gen.dm_n_72 ,\gdm.dm_gen.dm_n_73 ,\gdm.dm_gen.dm_n_74 ,\gdm.dm_gen.dm_n_75 ,\gdm.dm_gen.dm_n_76 ,\gdm.dm_gen.dm_n_77 ,\gdm.dm_gen.dm_n_78 ,\gdm.dm_gen.dm_n_79 ,\gdm.dm_gen.dm_n_80 ,\gdm.dm_gen.dm_n_81 ,\gdm.dm_gen.dm_n_82 ,\gdm.dm_gen.dm_n_83 ,\gdm.dm_gen.dm_n_84 ,\gdm.dm_gen.dm_n_85 ,\gdm.dm_gen.dm_n_86 ,\gdm.dm_gen.dm_n_87 ,\gdm.dm_gen.dm_n_88 ,\gdm.dm_gen.dm_n_89 ,\gdm.dm_gen.dm_n_90 ,\gdm.dm_gen.dm_n_91 ,\gdm.dm_gen.dm_n_92 ,\gdm.dm_gen.dm_n_93 ,\gdm.dm_gen.dm_n_94 ,\gdm.dm_gen.dm_n_95 ,\gdm.dm_gen.dm_n_96 ,\gdm.dm_gen.dm_n_97 ,\gdm.dm_gen.dm_n_98 ,\gdm.dm_gen.dm_n_99 ,\gdm.dm_gen.dm_n_100 ,\gdm.dm_gen.dm_n_101 ,\gdm.dm_gen.dm_n_102 ,\gdm.dm_gen.dm_n_103 ,\gdm.dm_gen.dm_n_104 ,\gdm.dm_gen.dm_n_105 ,\gdm.dm_gen.dm_n_106 ,\gdm.dm_gen.dm_n_107 ,\gdm.dm_gen.dm_n_108 }),
        .\gc0.count_d1_reg[3] (\gc0.count_d1_reg[3] ),
        .\gic0.gc0.count_d2_reg[3] (\gic0.gc0.count_d2_reg[3] ),
        .\gpregsm1.curr_fwft_state_reg[1] (\gpregsm1.curr_fwft_state_reg[1] ),
        .m_aclk(m_aclk),
        .ram_full_fb_i_reg(ram_full_fb_i_reg),
        .s_aclk(s_aclk));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[0] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_108 ),
        .Q(Q[0]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[100] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_8 ),
        .Q(Q[100]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[101] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_7 ),
        .Q(Q[101]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[102] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_6 ),
        .Q(Q[102]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[103] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_5 ),
        .Q(Q[103]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[104] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_4 ),
        .Q(Q[104]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[105] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_3 ),
        .Q(Q[105]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[106] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_2 ),
        .Q(Q[106]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[107] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_1 ),
        .Q(Q[107]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[108] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_0 ),
        .Q(Q[108]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[10] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_98 ),
        .Q(Q[10]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[11] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_97 ),
        .Q(Q[11]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[12] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_96 ),
        .Q(Q[12]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[13] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_95 ),
        .Q(Q[13]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[14] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_94 ),
        .Q(Q[14]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[15] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_93 ),
        .Q(Q[15]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[16] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_92 ),
        .Q(Q[16]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[17] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_91 ),
        .Q(Q[17]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[18] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_90 ),
        .Q(Q[18]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[19] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_89 ),
        .Q(Q[19]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[1] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_107 ),
        .Q(Q[1]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[20] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_88 ),
        .Q(Q[20]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[21] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_87 ),
        .Q(Q[21]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[22] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_86 ),
        .Q(Q[22]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[23] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_85 ),
        .Q(Q[23]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[24] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_84 ),
        .Q(Q[24]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[25] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_83 ),
        .Q(Q[25]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[26] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_82 ),
        .Q(Q[26]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[27] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_81 ),
        .Q(Q[27]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[28] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_80 ),
        .Q(Q[28]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[29] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_79 ),
        .Q(Q[29]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[2] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_106 ),
        .Q(Q[2]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[30] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_78 ),
        .Q(Q[30]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[31] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_77 ),
        .Q(Q[31]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[32] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_76 ),
        .Q(Q[32]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[33] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_75 ),
        .Q(Q[33]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[34] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_74 ),
        .Q(Q[34]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[35] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_73 ),
        .Q(Q[35]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[36] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_72 ),
        .Q(Q[36]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[37] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_71 ),
        .Q(Q[37]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[38] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_70 ),
        .Q(Q[38]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[39] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_69 ),
        .Q(Q[39]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[3] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_105 ),
        .Q(Q[3]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[40] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_68 ),
        .Q(Q[40]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[41] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_67 ),
        .Q(Q[41]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[42] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_66 ),
        .Q(Q[42]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[43] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_65 ),
        .Q(Q[43]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[44] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_64 ),
        .Q(Q[44]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[45] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_63 ),
        .Q(Q[45]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[46] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_62 ),
        .Q(Q[46]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[47] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_61 ),
        .Q(Q[47]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[48] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_60 ),
        .Q(Q[48]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[49] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_59 ),
        .Q(Q[49]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[4] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_104 ),
        .Q(Q[4]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[50] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_58 ),
        .Q(Q[50]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[51] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_57 ),
        .Q(Q[51]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[52] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_56 ),
        .Q(Q[52]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[53] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_55 ),
        .Q(Q[53]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[54] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_54 ),
        .Q(Q[54]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[55] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_53 ),
        .Q(Q[55]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[56] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_52 ),
        .Q(Q[56]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[57] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_51 ),
        .Q(Q[57]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[58] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_50 ),
        .Q(Q[58]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[59] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_49 ),
        .Q(Q[59]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[5] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_103 ),
        .Q(Q[5]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[60] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_48 ),
        .Q(Q[60]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[61] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_47 ),
        .Q(Q[61]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[62] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_46 ),
        .Q(Q[62]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[63] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_45 ),
        .Q(Q[63]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[64] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_44 ),
        .Q(Q[64]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[65] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_43 ),
        .Q(Q[65]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[66] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_42 ),
        .Q(Q[66]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[67] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_41 ),
        .Q(Q[67]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[68] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_40 ),
        .Q(Q[68]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[69] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_39 ),
        .Q(Q[69]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[6] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_102 ),
        .Q(Q[6]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[70] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_38 ),
        .Q(Q[70]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[71] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_37 ),
        .Q(Q[71]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[72] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_36 ),
        .Q(Q[72]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[73] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_35 ),
        .Q(Q[73]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[74] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_34 ),
        .Q(Q[74]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[75] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_33 ),
        .Q(Q[75]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[76] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_32 ),
        .Q(Q[76]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[77] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_31 ),
        .Q(Q[77]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[78] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_30 ),
        .Q(Q[78]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[79] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_29 ),
        .Q(Q[79]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[7] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_101 ),
        .Q(Q[7]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[80] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_28 ),
        .Q(Q[80]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[81] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_27 ),
        .Q(Q[81]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[82] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_26 ),
        .Q(Q[82]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[83] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_25 ),
        .Q(Q[83]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[84] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_24 ),
        .Q(Q[84]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[85] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_23 ),
        .Q(Q[85]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[86] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_22 ),
        .Q(Q[86]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[87] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_21 ),
        .Q(Q[87]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[88] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_20 ),
        .Q(Q[88]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[89] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_19 ),
        .Q(Q[89]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[8] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_100 ),
        .Q(Q[8]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[90] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_18 ),
        .Q(Q[90]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[91] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_17 ),
        .Q(Q[91]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[92] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_16 ),
        .Q(Q[92]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[93] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_15 ),
        .Q(Q[93]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[94] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_14 ),
        .Q(Q[94]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[95] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_13 ),
        .Q(Q[95]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[96] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_12 ),
        .Q(Q[96]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[97] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_11 ),
        .Q(Q[97]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[98] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_10 ),
        .Q(Q[98]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[99] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_9 ),
        .Q(Q[99]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[9] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_99 ),
        .Q(Q[9]),
        .R(1'b0));
endmodule

(* ORIG_REF_NAME = "memory" *) 
module axi_clock_converter_dramslim_memory_78
   (\m_axi_arid[15] ,
    E,
    m_aclk,
    s_aclk,
    ram_full_fb_i_reg,
    I141,
    \gc0.count_d1_reg[3] ,
    \gic0.gc0.count_d2_reg[3] ,
    \gpregsm1.curr_fwft_state_reg[1] );
  output [108:0]\m_axi_arid[15] ;
  input [0:0]E;
  input m_aclk;
  input s_aclk;
  input [0:0]ram_full_fb_i_reg;
  input [108:0]I141;
  input [3:0]\gc0.count_d1_reg[3] ;
  input [3:0]\gic0.gc0.count_d2_reg[3] ;
  input [0:0]\gpregsm1.curr_fwft_state_reg[1] ;

  wire [0:0]E;
  wire [108:0]I141;
  wire [3:0]\gc0.count_d1_reg[3] ;
  wire \gdm.dm_gen.dm_n_0 ;
  wire \gdm.dm_gen.dm_n_1 ;
  wire \gdm.dm_gen.dm_n_10 ;
  wire \gdm.dm_gen.dm_n_100 ;
  wire \gdm.dm_gen.dm_n_101 ;
  wire \gdm.dm_gen.dm_n_102 ;
  wire \gdm.dm_gen.dm_n_103 ;
  wire \gdm.dm_gen.dm_n_104 ;
  wire \gdm.dm_gen.dm_n_105 ;
  wire \gdm.dm_gen.dm_n_106 ;
  wire \gdm.dm_gen.dm_n_107 ;
  wire \gdm.dm_gen.dm_n_108 ;
  wire \gdm.dm_gen.dm_n_11 ;
  wire \gdm.dm_gen.dm_n_12 ;
  wire \gdm.dm_gen.dm_n_13 ;
  wire \gdm.dm_gen.dm_n_14 ;
  wire \gdm.dm_gen.dm_n_15 ;
  wire \gdm.dm_gen.dm_n_16 ;
  wire \gdm.dm_gen.dm_n_17 ;
  wire \gdm.dm_gen.dm_n_18 ;
  wire \gdm.dm_gen.dm_n_19 ;
  wire \gdm.dm_gen.dm_n_2 ;
  wire \gdm.dm_gen.dm_n_20 ;
  wire \gdm.dm_gen.dm_n_21 ;
  wire \gdm.dm_gen.dm_n_22 ;
  wire \gdm.dm_gen.dm_n_23 ;
  wire \gdm.dm_gen.dm_n_24 ;
  wire \gdm.dm_gen.dm_n_25 ;
  wire \gdm.dm_gen.dm_n_26 ;
  wire \gdm.dm_gen.dm_n_27 ;
  wire \gdm.dm_gen.dm_n_28 ;
  wire \gdm.dm_gen.dm_n_29 ;
  wire \gdm.dm_gen.dm_n_3 ;
  wire \gdm.dm_gen.dm_n_30 ;
  wire \gdm.dm_gen.dm_n_31 ;
  wire \gdm.dm_gen.dm_n_32 ;
  wire \gdm.dm_gen.dm_n_33 ;
  wire \gdm.dm_gen.dm_n_34 ;
  wire \gdm.dm_gen.dm_n_35 ;
  wire \gdm.dm_gen.dm_n_36 ;
  wire \gdm.dm_gen.dm_n_37 ;
  wire \gdm.dm_gen.dm_n_38 ;
  wire \gdm.dm_gen.dm_n_39 ;
  wire \gdm.dm_gen.dm_n_4 ;
  wire \gdm.dm_gen.dm_n_40 ;
  wire \gdm.dm_gen.dm_n_41 ;
  wire \gdm.dm_gen.dm_n_42 ;
  wire \gdm.dm_gen.dm_n_43 ;
  wire \gdm.dm_gen.dm_n_44 ;
  wire \gdm.dm_gen.dm_n_45 ;
  wire \gdm.dm_gen.dm_n_46 ;
  wire \gdm.dm_gen.dm_n_47 ;
  wire \gdm.dm_gen.dm_n_48 ;
  wire \gdm.dm_gen.dm_n_49 ;
  wire \gdm.dm_gen.dm_n_5 ;
  wire \gdm.dm_gen.dm_n_50 ;
  wire \gdm.dm_gen.dm_n_51 ;
  wire \gdm.dm_gen.dm_n_52 ;
  wire \gdm.dm_gen.dm_n_53 ;
  wire \gdm.dm_gen.dm_n_54 ;
  wire \gdm.dm_gen.dm_n_55 ;
  wire \gdm.dm_gen.dm_n_56 ;
  wire \gdm.dm_gen.dm_n_57 ;
  wire \gdm.dm_gen.dm_n_58 ;
  wire \gdm.dm_gen.dm_n_59 ;
  wire \gdm.dm_gen.dm_n_6 ;
  wire \gdm.dm_gen.dm_n_60 ;
  wire \gdm.dm_gen.dm_n_61 ;
  wire \gdm.dm_gen.dm_n_62 ;
  wire \gdm.dm_gen.dm_n_63 ;
  wire \gdm.dm_gen.dm_n_64 ;
  wire \gdm.dm_gen.dm_n_65 ;
  wire \gdm.dm_gen.dm_n_66 ;
  wire \gdm.dm_gen.dm_n_67 ;
  wire \gdm.dm_gen.dm_n_68 ;
  wire \gdm.dm_gen.dm_n_69 ;
  wire \gdm.dm_gen.dm_n_7 ;
  wire \gdm.dm_gen.dm_n_70 ;
  wire \gdm.dm_gen.dm_n_71 ;
  wire \gdm.dm_gen.dm_n_72 ;
  wire \gdm.dm_gen.dm_n_73 ;
  wire \gdm.dm_gen.dm_n_74 ;
  wire \gdm.dm_gen.dm_n_75 ;
  wire \gdm.dm_gen.dm_n_76 ;
  wire \gdm.dm_gen.dm_n_77 ;
  wire \gdm.dm_gen.dm_n_78 ;
  wire \gdm.dm_gen.dm_n_79 ;
  wire \gdm.dm_gen.dm_n_8 ;
  wire \gdm.dm_gen.dm_n_80 ;
  wire \gdm.dm_gen.dm_n_81 ;
  wire \gdm.dm_gen.dm_n_82 ;
  wire \gdm.dm_gen.dm_n_83 ;
  wire \gdm.dm_gen.dm_n_84 ;
  wire \gdm.dm_gen.dm_n_85 ;
  wire \gdm.dm_gen.dm_n_86 ;
  wire \gdm.dm_gen.dm_n_87 ;
  wire \gdm.dm_gen.dm_n_88 ;
  wire \gdm.dm_gen.dm_n_89 ;
  wire \gdm.dm_gen.dm_n_9 ;
  wire \gdm.dm_gen.dm_n_90 ;
  wire \gdm.dm_gen.dm_n_91 ;
  wire \gdm.dm_gen.dm_n_92 ;
  wire \gdm.dm_gen.dm_n_93 ;
  wire \gdm.dm_gen.dm_n_94 ;
  wire \gdm.dm_gen.dm_n_95 ;
  wire \gdm.dm_gen.dm_n_96 ;
  wire \gdm.dm_gen.dm_n_97 ;
  wire \gdm.dm_gen.dm_n_98 ;
  wire \gdm.dm_gen.dm_n_99 ;
  wire [3:0]\gic0.gc0.count_d2_reg[3] ;
  wire [0:0]\gpregsm1.curr_fwft_state_reg[1] ;
  wire m_aclk;
  wire [108:0]\m_axi_arid[15] ;
  wire [0:0]ram_full_fb_i_reg;
  wire s_aclk;

  axi_clock_converter_dramslim_dmem_86 \gdm.dm_gen.dm 
       (.I141(I141),
        .dout_i({\gdm.dm_gen.dm_n_0 ,\gdm.dm_gen.dm_n_1 ,\gdm.dm_gen.dm_n_2 ,\gdm.dm_gen.dm_n_3 ,\gdm.dm_gen.dm_n_4 ,\gdm.dm_gen.dm_n_5 ,\gdm.dm_gen.dm_n_6 ,\gdm.dm_gen.dm_n_7 ,\gdm.dm_gen.dm_n_8 ,\gdm.dm_gen.dm_n_9 ,\gdm.dm_gen.dm_n_10 ,\gdm.dm_gen.dm_n_11 ,\gdm.dm_gen.dm_n_12 ,\gdm.dm_gen.dm_n_13 ,\gdm.dm_gen.dm_n_14 ,\gdm.dm_gen.dm_n_15 ,\gdm.dm_gen.dm_n_16 ,\gdm.dm_gen.dm_n_17 ,\gdm.dm_gen.dm_n_18 ,\gdm.dm_gen.dm_n_19 ,\gdm.dm_gen.dm_n_20 ,\gdm.dm_gen.dm_n_21 ,\gdm.dm_gen.dm_n_22 ,\gdm.dm_gen.dm_n_23 ,\gdm.dm_gen.dm_n_24 ,\gdm.dm_gen.dm_n_25 ,\gdm.dm_gen.dm_n_26 ,\gdm.dm_gen.dm_n_27 ,\gdm.dm_gen.dm_n_28 ,\gdm.dm_gen.dm_n_29 ,\gdm.dm_gen.dm_n_30 ,\gdm.dm_gen.dm_n_31 ,\gdm.dm_gen.dm_n_32 ,\gdm.dm_gen.dm_n_33 ,\gdm.dm_gen.dm_n_34 ,\gdm.dm_gen.dm_n_35 ,\gdm.dm_gen.dm_n_36 ,\gdm.dm_gen.dm_n_37 ,\gdm.dm_gen.dm_n_38 ,\gdm.dm_gen.dm_n_39 ,\gdm.dm_gen.dm_n_40 ,\gdm.dm_gen.dm_n_41 ,\gdm.dm_gen.dm_n_42 ,\gdm.dm_gen.dm_n_43 ,\gdm.dm_gen.dm_n_44 ,\gdm.dm_gen.dm_n_45 ,\gdm.dm_gen.dm_n_46 ,\gdm.dm_gen.dm_n_47 ,\gdm.dm_gen.dm_n_48 ,\gdm.dm_gen.dm_n_49 ,\gdm.dm_gen.dm_n_50 ,\gdm.dm_gen.dm_n_51 ,\gdm.dm_gen.dm_n_52 ,\gdm.dm_gen.dm_n_53 ,\gdm.dm_gen.dm_n_54 ,\gdm.dm_gen.dm_n_55 ,\gdm.dm_gen.dm_n_56 ,\gdm.dm_gen.dm_n_57 ,\gdm.dm_gen.dm_n_58 ,\gdm.dm_gen.dm_n_59 ,\gdm.dm_gen.dm_n_60 ,\gdm.dm_gen.dm_n_61 ,\gdm.dm_gen.dm_n_62 ,\gdm.dm_gen.dm_n_63 ,\gdm.dm_gen.dm_n_64 ,\gdm.dm_gen.dm_n_65 ,\gdm.dm_gen.dm_n_66 ,\gdm.dm_gen.dm_n_67 ,\gdm.dm_gen.dm_n_68 ,\gdm.dm_gen.dm_n_69 ,\gdm.dm_gen.dm_n_70 ,\gdm.dm_gen.dm_n_71 ,\gdm.dm_gen.dm_n_72 ,\gdm.dm_gen.dm_n_73 ,\gdm.dm_gen.dm_n_74 ,\gdm.dm_gen.dm_n_75 ,\gdm.dm_gen.dm_n_76 ,\gdm.dm_gen.dm_n_77 ,\gdm.dm_gen.dm_n_78 ,\gdm.dm_gen.dm_n_79 ,\gdm.dm_gen.dm_n_80 ,\gdm.dm_gen.dm_n_81 ,\gdm.dm_gen.dm_n_82 ,\gdm.dm_gen.dm_n_83 ,\gdm.dm_gen.dm_n_84 ,\gdm.dm_gen.dm_n_85 ,\gdm.dm_gen.dm_n_86 ,\gdm.dm_gen.dm_n_87 ,\gdm.dm_gen.dm_n_88 ,\gdm.dm_gen.dm_n_89 ,\gdm.dm_gen.dm_n_90 ,\gdm.dm_gen.dm_n_91 ,\gdm.dm_gen.dm_n_92 ,\gdm.dm_gen.dm_n_93 ,\gdm.dm_gen.dm_n_94 ,\gdm.dm_gen.dm_n_95 ,\gdm.dm_gen.dm_n_96 ,\gdm.dm_gen.dm_n_97 ,\gdm.dm_gen.dm_n_98 ,\gdm.dm_gen.dm_n_99 ,\gdm.dm_gen.dm_n_100 ,\gdm.dm_gen.dm_n_101 ,\gdm.dm_gen.dm_n_102 ,\gdm.dm_gen.dm_n_103 ,\gdm.dm_gen.dm_n_104 ,\gdm.dm_gen.dm_n_105 ,\gdm.dm_gen.dm_n_106 ,\gdm.dm_gen.dm_n_107 ,\gdm.dm_gen.dm_n_108 }),
        .\gc0.count_d1_reg[3] (\gc0.count_d1_reg[3] ),
        .\gic0.gc0.count_d2_reg[3] (\gic0.gc0.count_d2_reg[3] ),
        .\gpregsm1.curr_fwft_state_reg[1] (\gpregsm1.curr_fwft_state_reg[1] ),
        .m_aclk(m_aclk),
        .ram_full_fb_i_reg(ram_full_fb_i_reg),
        .s_aclk(s_aclk));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[0] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_108 ),
        .Q(\m_axi_arid[15] [0]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[100] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_8 ),
        .Q(\m_axi_arid[15] [100]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[101] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_7 ),
        .Q(\m_axi_arid[15] [101]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[102] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_6 ),
        .Q(\m_axi_arid[15] [102]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[103] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_5 ),
        .Q(\m_axi_arid[15] [103]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[104] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_4 ),
        .Q(\m_axi_arid[15] [104]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[105] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_3 ),
        .Q(\m_axi_arid[15] [105]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[106] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_2 ),
        .Q(\m_axi_arid[15] [106]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[107] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_1 ),
        .Q(\m_axi_arid[15] [107]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[108] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_0 ),
        .Q(\m_axi_arid[15] [108]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[10] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_98 ),
        .Q(\m_axi_arid[15] [10]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[11] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_97 ),
        .Q(\m_axi_arid[15] [11]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[12] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_96 ),
        .Q(\m_axi_arid[15] [12]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[13] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_95 ),
        .Q(\m_axi_arid[15] [13]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[14] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_94 ),
        .Q(\m_axi_arid[15] [14]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[15] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_93 ),
        .Q(\m_axi_arid[15] [15]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[16] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_92 ),
        .Q(\m_axi_arid[15] [16]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[17] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_91 ),
        .Q(\m_axi_arid[15] [17]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[18] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_90 ),
        .Q(\m_axi_arid[15] [18]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[19] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_89 ),
        .Q(\m_axi_arid[15] [19]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[1] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_107 ),
        .Q(\m_axi_arid[15] [1]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[20] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_88 ),
        .Q(\m_axi_arid[15] [20]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[21] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_87 ),
        .Q(\m_axi_arid[15] [21]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[22] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_86 ),
        .Q(\m_axi_arid[15] [22]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[23] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_85 ),
        .Q(\m_axi_arid[15] [23]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[24] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_84 ),
        .Q(\m_axi_arid[15] [24]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[25] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_83 ),
        .Q(\m_axi_arid[15] [25]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[26] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_82 ),
        .Q(\m_axi_arid[15] [26]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[27] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_81 ),
        .Q(\m_axi_arid[15] [27]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[28] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_80 ),
        .Q(\m_axi_arid[15] [28]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[29] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_79 ),
        .Q(\m_axi_arid[15] [29]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[2] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_106 ),
        .Q(\m_axi_arid[15] [2]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[30] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_78 ),
        .Q(\m_axi_arid[15] [30]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[31] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_77 ),
        .Q(\m_axi_arid[15] [31]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[32] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_76 ),
        .Q(\m_axi_arid[15] [32]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[33] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_75 ),
        .Q(\m_axi_arid[15] [33]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[34] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_74 ),
        .Q(\m_axi_arid[15] [34]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[35] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_73 ),
        .Q(\m_axi_arid[15] [35]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[36] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_72 ),
        .Q(\m_axi_arid[15] [36]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[37] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_71 ),
        .Q(\m_axi_arid[15] [37]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[38] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_70 ),
        .Q(\m_axi_arid[15] [38]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[39] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_69 ),
        .Q(\m_axi_arid[15] [39]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[3] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_105 ),
        .Q(\m_axi_arid[15] [3]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[40] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_68 ),
        .Q(\m_axi_arid[15] [40]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[41] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_67 ),
        .Q(\m_axi_arid[15] [41]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[42] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_66 ),
        .Q(\m_axi_arid[15] [42]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[43] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_65 ),
        .Q(\m_axi_arid[15] [43]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[44] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_64 ),
        .Q(\m_axi_arid[15] [44]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[45] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_63 ),
        .Q(\m_axi_arid[15] [45]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[46] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_62 ),
        .Q(\m_axi_arid[15] [46]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[47] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_61 ),
        .Q(\m_axi_arid[15] [47]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[48] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_60 ),
        .Q(\m_axi_arid[15] [48]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[49] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_59 ),
        .Q(\m_axi_arid[15] [49]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[4] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_104 ),
        .Q(\m_axi_arid[15] [4]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[50] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_58 ),
        .Q(\m_axi_arid[15] [50]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[51] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_57 ),
        .Q(\m_axi_arid[15] [51]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[52] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_56 ),
        .Q(\m_axi_arid[15] [52]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[53] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_55 ),
        .Q(\m_axi_arid[15] [53]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[54] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_54 ),
        .Q(\m_axi_arid[15] [54]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[55] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_53 ),
        .Q(\m_axi_arid[15] [55]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[56] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_52 ),
        .Q(\m_axi_arid[15] [56]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[57] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_51 ),
        .Q(\m_axi_arid[15] [57]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[58] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_50 ),
        .Q(\m_axi_arid[15] [58]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[59] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_49 ),
        .Q(\m_axi_arid[15] [59]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[5] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_103 ),
        .Q(\m_axi_arid[15] [5]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[60] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_48 ),
        .Q(\m_axi_arid[15] [60]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[61] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_47 ),
        .Q(\m_axi_arid[15] [61]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[62] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_46 ),
        .Q(\m_axi_arid[15] [62]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[63] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_45 ),
        .Q(\m_axi_arid[15] [63]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[64] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_44 ),
        .Q(\m_axi_arid[15] [64]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[65] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_43 ),
        .Q(\m_axi_arid[15] [65]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[66] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_42 ),
        .Q(\m_axi_arid[15] [66]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[67] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_41 ),
        .Q(\m_axi_arid[15] [67]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[68] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_40 ),
        .Q(\m_axi_arid[15] [68]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[69] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_39 ),
        .Q(\m_axi_arid[15] [69]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[6] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_102 ),
        .Q(\m_axi_arid[15] [6]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[70] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_38 ),
        .Q(\m_axi_arid[15] [70]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[71] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_37 ),
        .Q(\m_axi_arid[15] [71]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[72] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_36 ),
        .Q(\m_axi_arid[15] [72]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[73] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_35 ),
        .Q(\m_axi_arid[15] [73]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[74] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_34 ),
        .Q(\m_axi_arid[15] [74]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[75] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_33 ),
        .Q(\m_axi_arid[15] [75]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[76] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_32 ),
        .Q(\m_axi_arid[15] [76]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[77] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_31 ),
        .Q(\m_axi_arid[15] [77]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[78] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_30 ),
        .Q(\m_axi_arid[15] [78]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[79] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_29 ),
        .Q(\m_axi_arid[15] [79]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[7] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_101 ),
        .Q(\m_axi_arid[15] [7]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[80] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_28 ),
        .Q(\m_axi_arid[15] [80]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[81] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_27 ),
        .Q(\m_axi_arid[15] [81]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[82] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_26 ),
        .Q(\m_axi_arid[15] [82]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[83] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_25 ),
        .Q(\m_axi_arid[15] [83]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[84] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_24 ),
        .Q(\m_axi_arid[15] [84]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[85] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_23 ),
        .Q(\m_axi_arid[15] [85]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[86] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_22 ),
        .Q(\m_axi_arid[15] [86]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[87] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_21 ),
        .Q(\m_axi_arid[15] [87]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[88] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_20 ),
        .Q(\m_axi_arid[15] [88]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[89] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_19 ),
        .Q(\m_axi_arid[15] [89]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[8] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_100 ),
        .Q(\m_axi_arid[15] [8]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[90] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_18 ),
        .Q(\m_axi_arid[15] [90]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[91] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_17 ),
        .Q(\m_axi_arid[15] [91]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[92] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_16 ),
        .Q(\m_axi_arid[15] [92]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[93] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_15 ),
        .Q(\m_axi_arid[15] [93]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[94] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_14 ),
        .Q(\m_axi_arid[15] [94]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[95] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_13 ),
        .Q(\m_axi_arid[15] [95]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[96] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_12 ),
        .Q(\m_axi_arid[15] [96]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[97] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_11 ),
        .Q(\m_axi_arid[15] [97]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[98] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_10 ),
        .Q(\m_axi_arid[15] [98]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[99] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_9 ),
        .Q(\m_axi_arid[15] [99]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[9] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_99 ),
        .Q(\m_axi_arid[15] [9]),
        .R(1'b0));
endmodule

(* ORIG_REF_NAME = "memory" *) 
module axi_clock_converter_dramslim_memory__parameterized0
   (\m_axi_wdata[63] ,
    E,
    m_aclk,
    s_aclk,
    ram_full_fb_i_reg,
    I133,
    \gc0.count_d1_reg[3] ,
    \gic0.gc0.count_d2_reg[3] ,
    \gpregsm1.curr_fwft_state_reg[1] );
  output [72:0]\m_axi_wdata[63] ;
  input [0:0]E;
  input m_aclk;
  input s_aclk;
  input [0:0]ram_full_fb_i_reg;
  input [72:0]I133;
  input [3:0]\gc0.count_d1_reg[3] ;
  input [3:0]\gic0.gc0.count_d2_reg[3] ;
  input [0:0]\gpregsm1.curr_fwft_state_reg[1] ;

  wire [0:0]E;
  wire [72:0]I133;
  wire [3:0]\gc0.count_d1_reg[3] ;
  wire \gdm.dm_gen.dm_n_0 ;
  wire \gdm.dm_gen.dm_n_1 ;
  wire \gdm.dm_gen.dm_n_10 ;
  wire \gdm.dm_gen.dm_n_11 ;
  wire \gdm.dm_gen.dm_n_12 ;
  wire \gdm.dm_gen.dm_n_13 ;
  wire \gdm.dm_gen.dm_n_14 ;
  wire \gdm.dm_gen.dm_n_15 ;
  wire \gdm.dm_gen.dm_n_16 ;
  wire \gdm.dm_gen.dm_n_17 ;
  wire \gdm.dm_gen.dm_n_18 ;
  wire \gdm.dm_gen.dm_n_19 ;
  wire \gdm.dm_gen.dm_n_2 ;
  wire \gdm.dm_gen.dm_n_20 ;
  wire \gdm.dm_gen.dm_n_21 ;
  wire \gdm.dm_gen.dm_n_22 ;
  wire \gdm.dm_gen.dm_n_23 ;
  wire \gdm.dm_gen.dm_n_24 ;
  wire \gdm.dm_gen.dm_n_25 ;
  wire \gdm.dm_gen.dm_n_26 ;
  wire \gdm.dm_gen.dm_n_27 ;
  wire \gdm.dm_gen.dm_n_28 ;
  wire \gdm.dm_gen.dm_n_29 ;
  wire \gdm.dm_gen.dm_n_3 ;
  wire \gdm.dm_gen.dm_n_30 ;
  wire \gdm.dm_gen.dm_n_31 ;
  wire \gdm.dm_gen.dm_n_32 ;
  wire \gdm.dm_gen.dm_n_33 ;
  wire \gdm.dm_gen.dm_n_34 ;
  wire \gdm.dm_gen.dm_n_35 ;
  wire \gdm.dm_gen.dm_n_36 ;
  wire \gdm.dm_gen.dm_n_37 ;
  wire \gdm.dm_gen.dm_n_38 ;
  wire \gdm.dm_gen.dm_n_39 ;
  wire \gdm.dm_gen.dm_n_4 ;
  wire \gdm.dm_gen.dm_n_40 ;
  wire \gdm.dm_gen.dm_n_41 ;
  wire \gdm.dm_gen.dm_n_42 ;
  wire \gdm.dm_gen.dm_n_43 ;
  wire \gdm.dm_gen.dm_n_44 ;
  wire \gdm.dm_gen.dm_n_45 ;
  wire \gdm.dm_gen.dm_n_46 ;
  wire \gdm.dm_gen.dm_n_47 ;
  wire \gdm.dm_gen.dm_n_48 ;
  wire \gdm.dm_gen.dm_n_49 ;
  wire \gdm.dm_gen.dm_n_5 ;
  wire \gdm.dm_gen.dm_n_50 ;
  wire \gdm.dm_gen.dm_n_51 ;
  wire \gdm.dm_gen.dm_n_52 ;
  wire \gdm.dm_gen.dm_n_53 ;
  wire \gdm.dm_gen.dm_n_54 ;
  wire \gdm.dm_gen.dm_n_55 ;
  wire \gdm.dm_gen.dm_n_56 ;
  wire \gdm.dm_gen.dm_n_57 ;
  wire \gdm.dm_gen.dm_n_58 ;
  wire \gdm.dm_gen.dm_n_59 ;
  wire \gdm.dm_gen.dm_n_6 ;
  wire \gdm.dm_gen.dm_n_60 ;
  wire \gdm.dm_gen.dm_n_61 ;
  wire \gdm.dm_gen.dm_n_62 ;
  wire \gdm.dm_gen.dm_n_63 ;
  wire \gdm.dm_gen.dm_n_64 ;
  wire \gdm.dm_gen.dm_n_65 ;
  wire \gdm.dm_gen.dm_n_66 ;
  wire \gdm.dm_gen.dm_n_67 ;
  wire \gdm.dm_gen.dm_n_68 ;
  wire \gdm.dm_gen.dm_n_69 ;
  wire \gdm.dm_gen.dm_n_7 ;
  wire \gdm.dm_gen.dm_n_70 ;
  wire \gdm.dm_gen.dm_n_71 ;
  wire \gdm.dm_gen.dm_n_72 ;
  wire \gdm.dm_gen.dm_n_8 ;
  wire \gdm.dm_gen.dm_n_9 ;
  wire [3:0]\gic0.gc0.count_d2_reg[3] ;
  wire [0:0]\gpregsm1.curr_fwft_state_reg[1] ;
  wire m_aclk;
  wire [72:0]\m_axi_wdata[63] ;
  wire [0:0]ram_full_fb_i_reg;
  wire s_aclk;

  axi_clock_converter_dramslim_dmem__parameterized0 \gdm.dm_gen.dm 
       (.I133(I133),
        .dout_i({\gdm.dm_gen.dm_n_0 ,\gdm.dm_gen.dm_n_1 ,\gdm.dm_gen.dm_n_2 ,\gdm.dm_gen.dm_n_3 ,\gdm.dm_gen.dm_n_4 ,\gdm.dm_gen.dm_n_5 ,\gdm.dm_gen.dm_n_6 ,\gdm.dm_gen.dm_n_7 ,\gdm.dm_gen.dm_n_8 ,\gdm.dm_gen.dm_n_9 ,\gdm.dm_gen.dm_n_10 ,\gdm.dm_gen.dm_n_11 ,\gdm.dm_gen.dm_n_12 ,\gdm.dm_gen.dm_n_13 ,\gdm.dm_gen.dm_n_14 ,\gdm.dm_gen.dm_n_15 ,\gdm.dm_gen.dm_n_16 ,\gdm.dm_gen.dm_n_17 ,\gdm.dm_gen.dm_n_18 ,\gdm.dm_gen.dm_n_19 ,\gdm.dm_gen.dm_n_20 ,\gdm.dm_gen.dm_n_21 ,\gdm.dm_gen.dm_n_22 ,\gdm.dm_gen.dm_n_23 ,\gdm.dm_gen.dm_n_24 ,\gdm.dm_gen.dm_n_25 ,\gdm.dm_gen.dm_n_26 ,\gdm.dm_gen.dm_n_27 ,\gdm.dm_gen.dm_n_28 ,\gdm.dm_gen.dm_n_29 ,\gdm.dm_gen.dm_n_30 ,\gdm.dm_gen.dm_n_31 ,\gdm.dm_gen.dm_n_32 ,\gdm.dm_gen.dm_n_33 ,\gdm.dm_gen.dm_n_34 ,\gdm.dm_gen.dm_n_35 ,\gdm.dm_gen.dm_n_36 ,\gdm.dm_gen.dm_n_37 ,\gdm.dm_gen.dm_n_38 ,\gdm.dm_gen.dm_n_39 ,\gdm.dm_gen.dm_n_40 ,\gdm.dm_gen.dm_n_41 ,\gdm.dm_gen.dm_n_42 ,\gdm.dm_gen.dm_n_43 ,\gdm.dm_gen.dm_n_44 ,\gdm.dm_gen.dm_n_45 ,\gdm.dm_gen.dm_n_46 ,\gdm.dm_gen.dm_n_47 ,\gdm.dm_gen.dm_n_48 ,\gdm.dm_gen.dm_n_49 ,\gdm.dm_gen.dm_n_50 ,\gdm.dm_gen.dm_n_51 ,\gdm.dm_gen.dm_n_52 ,\gdm.dm_gen.dm_n_53 ,\gdm.dm_gen.dm_n_54 ,\gdm.dm_gen.dm_n_55 ,\gdm.dm_gen.dm_n_56 ,\gdm.dm_gen.dm_n_57 ,\gdm.dm_gen.dm_n_58 ,\gdm.dm_gen.dm_n_59 ,\gdm.dm_gen.dm_n_60 ,\gdm.dm_gen.dm_n_61 ,\gdm.dm_gen.dm_n_62 ,\gdm.dm_gen.dm_n_63 ,\gdm.dm_gen.dm_n_64 ,\gdm.dm_gen.dm_n_65 ,\gdm.dm_gen.dm_n_66 ,\gdm.dm_gen.dm_n_67 ,\gdm.dm_gen.dm_n_68 ,\gdm.dm_gen.dm_n_69 ,\gdm.dm_gen.dm_n_70 ,\gdm.dm_gen.dm_n_71 ,\gdm.dm_gen.dm_n_72 }),
        .\gc0.count_d1_reg[3] (\gc0.count_d1_reg[3] ),
        .\gic0.gc0.count_d2_reg[3] (\gic0.gc0.count_d2_reg[3] ),
        .\gpregsm1.curr_fwft_state_reg[1] (\gpregsm1.curr_fwft_state_reg[1] ),
        .m_aclk(m_aclk),
        .ram_full_fb_i_reg(ram_full_fb_i_reg),
        .s_aclk(s_aclk));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[0] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_72 ),
        .Q(\m_axi_wdata[63] [0]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[10] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_62 ),
        .Q(\m_axi_wdata[63] [10]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[11] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_61 ),
        .Q(\m_axi_wdata[63] [11]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[12] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_60 ),
        .Q(\m_axi_wdata[63] [12]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[13] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_59 ),
        .Q(\m_axi_wdata[63] [13]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[14] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_58 ),
        .Q(\m_axi_wdata[63] [14]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[15] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_57 ),
        .Q(\m_axi_wdata[63] [15]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[16] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_56 ),
        .Q(\m_axi_wdata[63] [16]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[17] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_55 ),
        .Q(\m_axi_wdata[63] [17]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[18] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_54 ),
        .Q(\m_axi_wdata[63] [18]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[19] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_53 ),
        .Q(\m_axi_wdata[63] [19]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[1] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_71 ),
        .Q(\m_axi_wdata[63] [1]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[20] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_52 ),
        .Q(\m_axi_wdata[63] [20]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[21] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_51 ),
        .Q(\m_axi_wdata[63] [21]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[22] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_50 ),
        .Q(\m_axi_wdata[63] [22]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[23] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_49 ),
        .Q(\m_axi_wdata[63] [23]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[24] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_48 ),
        .Q(\m_axi_wdata[63] [24]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[25] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_47 ),
        .Q(\m_axi_wdata[63] [25]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[26] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_46 ),
        .Q(\m_axi_wdata[63] [26]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[27] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_45 ),
        .Q(\m_axi_wdata[63] [27]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[28] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_44 ),
        .Q(\m_axi_wdata[63] [28]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[29] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_43 ),
        .Q(\m_axi_wdata[63] [29]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[2] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_70 ),
        .Q(\m_axi_wdata[63] [2]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[30] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_42 ),
        .Q(\m_axi_wdata[63] [30]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[31] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_41 ),
        .Q(\m_axi_wdata[63] [31]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[32] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_40 ),
        .Q(\m_axi_wdata[63] [32]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[33] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_39 ),
        .Q(\m_axi_wdata[63] [33]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[34] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_38 ),
        .Q(\m_axi_wdata[63] [34]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[35] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_37 ),
        .Q(\m_axi_wdata[63] [35]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[36] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_36 ),
        .Q(\m_axi_wdata[63] [36]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[37] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_35 ),
        .Q(\m_axi_wdata[63] [37]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[38] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_34 ),
        .Q(\m_axi_wdata[63] [38]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[39] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_33 ),
        .Q(\m_axi_wdata[63] [39]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[3] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_69 ),
        .Q(\m_axi_wdata[63] [3]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[40] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_32 ),
        .Q(\m_axi_wdata[63] [40]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[41] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_31 ),
        .Q(\m_axi_wdata[63] [41]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[42] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_30 ),
        .Q(\m_axi_wdata[63] [42]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[43] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_29 ),
        .Q(\m_axi_wdata[63] [43]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[44] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_28 ),
        .Q(\m_axi_wdata[63] [44]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[45] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_27 ),
        .Q(\m_axi_wdata[63] [45]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[46] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_26 ),
        .Q(\m_axi_wdata[63] [46]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[47] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_25 ),
        .Q(\m_axi_wdata[63] [47]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[48] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_24 ),
        .Q(\m_axi_wdata[63] [48]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[49] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_23 ),
        .Q(\m_axi_wdata[63] [49]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[4] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_68 ),
        .Q(\m_axi_wdata[63] [4]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[50] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_22 ),
        .Q(\m_axi_wdata[63] [50]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[51] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_21 ),
        .Q(\m_axi_wdata[63] [51]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[52] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_20 ),
        .Q(\m_axi_wdata[63] [52]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[53] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_19 ),
        .Q(\m_axi_wdata[63] [53]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[54] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_18 ),
        .Q(\m_axi_wdata[63] [54]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[55] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_17 ),
        .Q(\m_axi_wdata[63] [55]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[56] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_16 ),
        .Q(\m_axi_wdata[63] [56]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[57] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_15 ),
        .Q(\m_axi_wdata[63] [57]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[58] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_14 ),
        .Q(\m_axi_wdata[63] [58]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[59] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_13 ),
        .Q(\m_axi_wdata[63] [59]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[5] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_67 ),
        .Q(\m_axi_wdata[63] [5]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[60] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_12 ),
        .Q(\m_axi_wdata[63] [60]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[61] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_11 ),
        .Q(\m_axi_wdata[63] [61]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[62] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_10 ),
        .Q(\m_axi_wdata[63] [62]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[63] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_9 ),
        .Q(\m_axi_wdata[63] [63]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[64] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_8 ),
        .Q(\m_axi_wdata[63] [64]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[65] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_7 ),
        .Q(\m_axi_wdata[63] [65]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[66] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_6 ),
        .Q(\m_axi_wdata[63] [66]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[67] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_5 ),
        .Q(\m_axi_wdata[63] [67]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[68] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_4 ),
        .Q(\m_axi_wdata[63] [68]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[69] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_3 ),
        .Q(\m_axi_wdata[63] [69]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[6] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_66 ),
        .Q(\m_axi_wdata[63] [6]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[70] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_2 ),
        .Q(\m_axi_wdata[63] [70]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[71] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_1 ),
        .Q(\m_axi_wdata[63] [71]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[72] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_0 ),
        .Q(\m_axi_wdata[63] [72]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[7] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_65 ),
        .Q(\m_axi_wdata[63] [7]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[8] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_64 ),
        .Q(\m_axi_wdata[63] [8]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[9] 
       (.C(m_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_63 ),
        .Q(\m_axi_wdata[63] [9]),
        .R(1'b0));
endmodule

(* ORIG_REF_NAME = "memory" *) 
module axi_clock_converter_dramslim_memory__parameterized1
   (\s_axi_bid[15] ,
    E,
    s_aclk,
    m_aclk,
    I118,
    I137,
    \gc0.count_d1_reg[3] ,
    count_d2,
    \gpregsm1.curr_fwft_state_reg[1] );
  output [17:0]\s_axi_bid[15] ;
  input [0:0]E;
  input s_aclk;
  input m_aclk;
  input I118;
  input [17:0]I137;
  input [3:0]\gc0.count_d1_reg[3] ;
  input [3:0]count_d2;
  input [0:0]\gpregsm1.curr_fwft_state_reg[1] ;

  wire [0:0]E;
  wire I118;
  wire [17:0]I137;
  wire [3:0]count_d2;
  wire [3:0]\gc0.count_d1_reg[3] ;
  wire \gdm.dm_gen.dm_n_0 ;
  wire \gdm.dm_gen.dm_n_1 ;
  wire \gdm.dm_gen.dm_n_10 ;
  wire \gdm.dm_gen.dm_n_11 ;
  wire \gdm.dm_gen.dm_n_12 ;
  wire \gdm.dm_gen.dm_n_13 ;
  wire \gdm.dm_gen.dm_n_14 ;
  wire \gdm.dm_gen.dm_n_15 ;
  wire \gdm.dm_gen.dm_n_16 ;
  wire \gdm.dm_gen.dm_n_17 ;
  wire \gdm.dm_gen.dm_n_2 ;
  wire \gdm.dm_gen.dm_n_3 ;
  wire \gdm.dm_gen.dm_n_4 ;
  wire \gdm.dm_gen.dm_n_5 ;
  wire \gdm.dm_gen.dm_n_6 ;
  wire \gdm.dm_gen.dm_n_7 ;
  wire \gdm.dm_gen.dm_n_8 ;
  wire \gdm.dm_gen.dm_n_9 ;
  wire [0:0]\gpregsm1.curr_fwft_state_reg[1] ;
  wire m_aclk;
  wire s_aclk;
  wire [17:0]\s_axi_bid[15] ;

  axi_clock_converter_dramslim_dmem__parameterized1 \gdm.dm_gen.dm 
       (.I118(I118),
        .I137(I137),
        .count_d2(count_d2),
        .dout_i({\gdm.dm_gen.dm_n_0 ,\gdm.dm_gen.dm_n_1 ,\gdm.dm_gen.dm_n_2 ,\gdm.dm_gen.dm_n_3 ,\gdm.dm_gen.dm_n_4 ,\gdm.dm_gen.dm_n_5 ,\gdm.dm_gen.dm_n_6 ,\gdm.dm_gen.dm_n_7 ,\gdm.dm_gen.dm_n_8 ,\gdm.dm_gen.dm_n_9 ,\gdm.dm_gen.dm_n_10 ,\gdm.dm_gen.dm_n_11 ,\gdm.dm_gen.dm_n_12 ,\gdm.dm_gen.dm_n_13 ,\gdm.dm_gen.dm_n_14 ,\gdm.dm_gen.dm_n_15 ,\gdm.dm_gen.dm_n_16 ,\gdm.dm_gen.dm_n_17 }),
        .\gc0.count_d1_reg[3] (\gc0.count_d1_reg[3] ),
        .\gpregsm1.curr_fwft_state_reg[1] (\gpregsm1.curr_fwft_state_reg[1] ),
        .m_aclk(m_aclk),
        .s_aclk(s_aclk));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[0] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_17 ),
        .Q(\s_axi_bid[15] [0]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[10] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_7 ),
        .Q(\s_axi_bid[15] [10]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[11] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_6 ),
        .Q(\s_axi_bid[15] [11]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[12] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_5 ),
        .Q(\s_axi_bid[15] [12]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[13] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_4 ),
        .Q(\s_axi_bid[15] [13]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[14] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_3 ),
        .Q(\s_axi_bid[15] [14]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[15] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_2 ),
        .Q(\s_axi_bid[15] [15]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[16] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_1 ),
        .Q(\s_axi_bid[15] [16]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[17] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_0 ),
        .Q(\s_axi_bid[15] [17]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[1] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_16 ),
        .Q(\s_axi_bid[15] [1]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[2] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_15 ),
        .Q(\s_axi_bid[15] [2]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[3] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_14 ),
        .Q(\s_axi_bid[15] [3]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[4] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_13 ),
        .Q(\s_axi_bid[15] [4]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[5] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_12 ),
        .Q(\s_axi_bid[15] [5]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[6] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_11 ),
        .Q(\s_axi_bid[15] [6]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[7] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_10 ),
        .Q(\s_axi_bid[15] [7]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[8] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_9 ),
        .Q(\s_axi_bid[15] [8]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[9] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_8 ),
        .Q(\s_axi_bid[15] [9]),
        .R(1'b0));
endmodule

(* ORIG_REF_NAME = "memory" *) 
module axi_clock_converter_dramslim_memory__parameterized2
   (\s_axi_rid[15] ,
    E,
    s_aclk,
    m_aclk,
    ram_full_fb_i_reg,
    I145,
    \gc0.count_d1_reg[3] ,
    \gic0.gc0.count_d2_reg[3] ,
    \gpregsm1.curr_fwft_state_reg[1] );
  output [82:0]\s_axi_rid[15] ;
  input [0:0]E;
  input s_aclk;
  input m_aclk;
  input [0:0]ram_full_fb_i_reg;
  input [82:0]I145;
  input [3:0]\gc0.count_d1_reg[3] ;
  input [3:0]\gic0.gc0.count_d2_reg[3] ;
  input [0:0]\gpregsm1.curr_fwft_state_reg[1] ;

  wire [0:0]E;
  wire [82:0]I145;
  wire [3:0]\gc0.count_d1_reg[3] ;
  wire \gdm.dm_gen.dm_n_0 ;
  wire \gdm.dm_gen.dm_n_1 ;
  wire \gdm.dm_gen.dm_n_10 ;
  wire \gdm.dm_gen.dm_n_11 ;
  wire \gdm.dm_gen.dm_n_12 ;
  wire \gdm.dm_gen.dm_n_13 ;
  wire \gdm.dm_gen.dm_n_14 ;
  wire \gdm.dm_gen.dm_n_15 ;
  wire \gdm.dm_gen.dm_n_16 ;
  wire \gdm.dm_gen.dm_n_17 ;
  wire \gdm.dm_gen.dm_n_18 ;
  wire \gdm.dm_gen.dm_n_19 ;
  wire \gdm.dm_gen.dm_n_2 ;
  wire \gdm.dm_gen.dm_n_20 ;
  wire \gdm.dm_gen.dm_n_21 ;
  wire \gdm.dm_gen.dm_n_22 ;
  wire \gdm.dm_gen.dm_n_23 ;
  wire \gdm.dm_gen.dm_n_24 ;
  wire \gdm.dm_gen.dm_n_25 ;
  wire \gdm.dm_gen.dm_n_26 ;
  wire \gdm.dm_gen.dm_n_27 ;
  wire \gdm.dm_gen.dm_n_28 ;
  wire \gdm.dm_gen.dm_n_29 ;
  wire \gdm.dm_gen.dm_n_3 ;
  wire \gdm.dm_gen.dm_n_30 ;
  wire \gdm.dm_gen.dm_n_31 ;
  wire \gdm.dm_gen.dm_n_32 ;
  wire \gdm.dm_gen.dm_n_33 ;
  wire \gdm.dm_gen.dm_n_34 ;
  wire \gdm.dm_gen.dm_n_35 ;
  wire \gdm.dm_gen.dm_n_36 ;
  wire \gdm.dm_gen.dm_n_37 ;
  wire \gdm.dm_gen.dm_n_38 ;
  wire \gdm.dm_gen.dm_n_39 ;
  wire \gdm.dm_gen.dm_n_4 ;
  wire \gdm.dm_gen.dm_n_40 ;
  wire \gdm.dm_gen.dm_n_41 ;
  wire \gdm.dm_gen.dm_n_42 ;
  wire \gdm.dm_gen.dm_n_43 ;
  wire \gdm.dm_gen.dm_n_44 ;
  wire \gdm.dm_gen.dm_n_45 ;
  wire \gdm.dm_gen.dm_n_46 ;
  wire \gdm.dm_gen.dm_n_47 ;
  wire \gdm.dm_gen.dm_n_48 ;
  wire \gdm.dm_gen.dm_n_49 ;
  wire \gdm.dm_gen.dm_n_5 ;
  wire \gdm.dm_gen.dm_n_50 ;
  wire \gdm.dm_gen.dm_n_51 ;
  wire \gdm.dm_gen.dm_n_52 ;
  wire \gdm.dm_gen.dm_n_53 ;
  wire \gdm.dm_gen.dm_n_54 ;
  wire \gdm.dm_gen.dm_n_55 ;
  wire \gdm.dm_gen.dm_n_56 ;
  wire \gdm.dm_gen.dm_n_57 ;
  wire \gdm.dm_gen.dm_n_58 ;
  wire \gdm.dm_gen.dm_n_59 ;
  wire \gdm.dm_gen.dm_n_6 ;
  wire \gdm.dm_gen.dm_n_60 ;
  wire \gdm.dm_gen.dm_n_61 ;
  wire \gdm.dm_gen.dm_n_62 ;
  wire \gdm.dm_gen.dm_n_63 ;
  wire \gdm.dm_gen.dm_n_64 ;
  wire \gdm.dm_gen.dm_n_65 ;
  wire \gdm.dm_gen.dm_n_66 ;
  wire \gdm.dm_gen.dm_n_67 ;
  wire \gdm.dm_gen.dm_n_68 ;
  wire \gdm.dm_gen.dm_n_69 ;
  wire \gdm.dm_gen.dm_n_7 ;
  wire \gdm.dm_gen.dm_n_70 ;
  wire \gdm.dm_gen.dm_n_71 ;
  wire \gdm.dm_gen.dm_n_72 ;
  wire \gdm.dm_gen.dm_n_73 ;
  wire \gdm.dm_gen.dm_n_74 ;
  wire \gdm.dm_gen.dm_n_75 ;
  wire \gdm.dm_gen.dm_n_76 ;
  wire \gdm.dm_gen.dm_n_77 ;
  wire \gdm.dm_gen.dm_n_78 ;
  wire \gdm.dm_gen.dm_n_79 ;
  wire \gdm.dm_gen.dm_n_8 ;
  wire \gdm.dm_gen.dm_n_80 ;
  wire \gdm.dm_gen.dm_n_81 ;
  wire \gdm.dm_gen.dm_n_82 ;
  wire \gdm.dm_gen.dm_n_9 ;
  wire [3:0]\gic0.gc0.count_d2_reg[3] ;
  wire [0:0]\gpregsm1.curr_fwft_state_reg[1] ;
  wire m_aclk;
  wire [0:0]ram_full_fb_i_reg;
  wire s_aclk;
  wire [82:0]\s_axi_rid[15] ;

  axi_clock_converter_dramslim_dmem__parameterized2 \gdm.dm_gen.dm 
       (.I145(I145),
        .dout_i({\gdm.dm_gen.dm_n_0 ,\gdm.dm_gen.dm_n_1 ,\gdm.dm_gen.dm_n_2 ,\gdm.dm_gen.dm_n_3 ,\gdm.dm_gen.dm_n_4 ,\gdm.dm_gen.dm_n_5 ,\gdm.dm_gen.dm_n_6 ,\gdm.dm_gen.dm_n_7 ,\gdm.dm_gen.dm_n_8 ,\gdm.dm_gen.dm_n_9 ,\gdm.dm_gen.dm_n_10 ,\gdm.dm_gen.dm_n_11 ,\gdm.dm_gen.dm_n_12 ,\gdm.dm_gen.dm_n_13 ,\gdm.dm_gen.dm_n_14 ,\gdm.dm_gen.dm_n_15 ,\gdm.dm_gen.dm_n_16 ,\gdm.dm_gen.dm_n_17 ,\gdm.dm_gen.dm_n_18 ,\gdm.dm_gen.dm_n_19 ,\gdm.dm_gen.dm_n_20 ,\gdm.dm_gen.dm_n_21 ,\gdm.dm_gen.dm_n_22 ,\gdm.dm_gen.dm_n_23 ,\gdm.dm_gen.dm_n_24 ,\gdm.dm_gen.dm_n_25 ,\gdm.dm_gen.dm_n_26 ,\gdm.dm_gen.dm_n_27 ,\gdm.dm_gen.dm_n_28 ,\gdm.dm_gen.dm_n_29 ,\gdm.dm_gen.dm_n_30 ,\gdm.dm_gen.dm_n_31 ,\gdm.dm_gen.dm_n_32 ,\gdm.dm_gen.dm_n_33 ,\gdm.dm_gen.dm_n_34 ,\gdm.dm_gen.dm_n_35 ,\gdm.dm_gen.dm_n_36 ,\gdm.dm_gen.dm_n_37 ,\gdm.dm_gen.dm_n_38 ,\gdm.dm_gen.dm_n_39 ,\gdm.dm_gen.dm_n_40 ,\gdm.dm_gen.dm_n_41 ,\gdm.dm_gen.dm_n_42 ,\gdm.dm_gen.dm_n_43 ,\gdm.dm_gen.dm_n_44 ,\gdm.dm_gen.dm_n_45 ,\gdm.dm_gen.dm_n_46 ,\gdm.dm_gen.dm_n_47 ,\gdm.dm_gen.dm_n_48 ,\gdm.dm_gen.dm_n_49 ,\gdm.dm_gen.dm_n_50 ,\gdm.dm_gen.dm_n_51 ,\gdm.dm_gen.dm_n_52 ,\gdm.dm_gen.dm_n_53 ,\gdm.dm_gen.dm_n_54 ,\gdm.dm_gen.dm_n_55 ,\gdm.dm_gen.dm_n_56 ,\gdm.dm_gen.dm_n_57 ,\gdm.dm_gen.dm_n_58 ,\gdm.dm_gen.dm_n_59 ,\gdm.dm_gen.dm_n_60 ,\gdm.dm_gen.dm_n_61 ,\gdm.dm_gen.dm_n_62 ,\gdm.dm_gen.dm_n_63 ,\gdm.dm_gen.dm_n_64 ,\gdm.dm_gen.dm_n_65 ,\gdm.dm_gen.dm_n_66 ,\gdm.dm_gen.dm_n_67 ,\gdm.dm_gen.dm_n_68 ,\gdm.dm_gen.dm_n_69 ,\gdm.dm_gen.dm_n_70 ,\gdm.dm_gen.dm_n_71 ,\gdm.dm_gen.dm_n_72 ,\gdm.dm_gen.dm_n_73 ,\gdm.dm_gen.dm_n_74 ,\gdm.dm_gen.dm_n_75 ,\gdm.dm_gen.dm_n_76 ,\gdm.dm_gen.dm_n_77 ,\gdm.dm_gen.dm_n_78 ,\gdm.dm_gen.dm_n_79 ,\gdm.dm_gen.dm_n_80 ,\gdm.dm_gen.dm_n_81 ,\gdm.dm_gen.dm_n_82 }),
        .\gc0.count_d1_reg[3] (\gc0.count_d1_reg[3] ),
        .\gic0.gc0.count_d2_reg[3] (\gic0.gc0.count_d2_reg[3] ),
        .\gpregsm1.curr_fwft_state_reg[1] (\gpregsm1.curr_fwft_state_reg[1] ),
        .m_aclk(m_aclk),
        .ram_full_fb_i_reg(ram_full_fb_i_reg),
        .s_aclk(s_aclk));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[0] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_82 ),
        .Q(\s_axi_rid[15] [0]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[10] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_72 ),
        .Q(\s_axi_rid[15] [10]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[11] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_71 ),
        .Q(\s_axi_rid[15] [11]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[12] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_70 ),
        .Q(\s_axi_rid[15] [12]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[13] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_69 ),
        .Q(\s_axi_rid[15] [13]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[14] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_68 ),
        .Q(\s_axi_rid[15] [14]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[15] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_67 ),
        .Q(\s_axi_rid[15] [15]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[16] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_66 ),
        .Q(\s_axi_rid[15] [16]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[17] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_65 ),
        .Q(\s_axi_rid[15] [17]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[18] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_64 ),
        .Q(\s_axi_rid[15] [18]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[19] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_63 ),
        .Q(\s_axi_rid[15] [19]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[1] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_81 ),
        .Q(\s_axi_rid[15] [1]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[20] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_62 ),
        .Q(\s_axi_rid[15] [20]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[21] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_61 ),
        .Q(\s_axi_rid[15] [21]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[22] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_60 ),
        .Q(\s_axi_rid[15] [22]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[23] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_59 ),
        .Q(\s_axi_rid[15] [23]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[24] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_58 ),
        .Q(\s_axi_rid[15] [24]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[25] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_57 ),
        .Q(\s_axi_rid[15] [25]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[26] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_56 ),
        .Q(\s_axi_rid[15] [26]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[27] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_55 ),
        .Q(\s_axi_rid[15] [27]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[28] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_54 ),
        .Q(\s_axi_rid[15] [28]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[29] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_53 ),
        .Q(\s_axi_rid[15] [29]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[2] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_80 ),
        .Q(\s_axi_rid[15] [2]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[30] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_52 ),
        .Q(\s_axi_rid[15] [30]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[31] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_51 ),
        .Q(\s_axi_rid[15] [31]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[32] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_50 ),
        .Q(\s_axi_rid[15] [32]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[33] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_49 ),
        .Q(\s_axi_rid[15] [33]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[34] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_48 ),
        .Q(\s_axi_rid[15] [34]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[35] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_47 ),
        .Q(\s_axi_rid[15] [35]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[36] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_46 ),
        .Q(\s_axi_rid[15] [36]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[37] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_45 ),
        .Q(\s_axi_rid[15] [37]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[38] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_44 ),
        .Q(\s_axi_rid[15] [38]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[39] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_43 ),
        .Q(\s_axi_rid[15] [39]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[3] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_79 ),
        .Q(\s_axi_rid[15] [3]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[40] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_42 ),
        .Q(\s_axi_rid[15] [40]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[41] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_41 ),
        .Q(\s_axi_rid[15] [41]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[42] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_40 ),
        .Q(\s_axi_rid[15] [42]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[43] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_39 ),
        .Q(\s_axi_rid[15] [43]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[44] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_38 ),
        .Q(\s_axi_rid[15] [44]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[45] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_37 ),
        .Q(\s_axi_rid[15] [45]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[46] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_36 ),
        .Q(\s_axi_rid[15] [46]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[47] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_35 ),
        .Q(\s_axi_rid[15] [47]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[48] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_34 ),
        .Q(\s_axi_rid[15] [48]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[49] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_33 ),
        .Q(\s_axi_rid[15] [49]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[4] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_78 ),
        .Q(\s_axi_rid[15] [4]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[50] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_32 ),
        .Q(\s_axi_rid[15] [50]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[51] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_31 ),
        .Q(\s_axi_rid[15] [51]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[52] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_30 ),
        .Q(\s_axi_rid[15] [52]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[53] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_29 ),
        .Q(\s_axi_rid[15] [53]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[54] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_28 ),
        .Q(\s_axi_rid[15] [54]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[55] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_27 ),
        .Q(\s_axi_rid[15] [55]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[56] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_26 ),
        .Q(\s_axi_rid[15] [56]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[57] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_25 ),
        .Q(\s_axi_rid[15] [57]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[58] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_24 ),
        .Q(\s_axi_rid[15] [58]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[59] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_23 ),
        .Q(\s_axi_rid[15] [59]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[5] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_77 ),
        .Q(\s_axi_rid[15] [5]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[60] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_22 ),
        .Q(\s_axi_rid[15] [60]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[61] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_21 ),
        .Q(\s_axi_rid[15] [61]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[62] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_20 ),
        .Q(\s_axi_rid[15] [62]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[63] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_19 ),
        .Q(\s_axi_rid[15] [63]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[64] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_18 ),
        .Q(\s_axi_rid[15] [64]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[65] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_17 ),
        .Q(\s_axi_rid[15] [65]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[66] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_16 ),
        .Q(\s_axi_rid[15] [66]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[67] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_15 ),
        .Q(\s_axi_rid[15] [67]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[68] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_14 ),
        .Q(\s_axi_rid[15] [68]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[69] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_13 ),
        .Q(\s_axi_rid[15] [69]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[6] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_76 ),
        .Q(\s_axi_rid[15] [6]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[70] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_12 ),
        .Q(\s_axi_rid[15] [70]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[71] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_11 ),
        .Q(\s_axi_rid[15] [71]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[72] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_10 ),
        .Q(\s_axi_rid[15] [72]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[73] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_9 ),
        .Q(\s_axi_rid[15] [73]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[74] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_8 ),
        .Q(\s_axi_rid[15] [74]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[75] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_7 ),
        .Q(\s_axi_rid[15] [75]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[76] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_6 ),
        .Q(\s_axi_rid[15] [76]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[77] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_5 ),
        .Q(\s_axi_rid[15] [77]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[78] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_4 ),
        .Q(\s_axi_rid[15] [78]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[79] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_3 ),
        .Q(\s_axi_rid[15] [79]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[7] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_75 ),
        .Q(\s_axi_rid[15] [7]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[80] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_2 ),
        .Q(\s_axi_rid[15] [80]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[81] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_1 ),
        .Q(\s_axi_rid[15] [81]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[82] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_0 ),
        .Q(\s_axi_rid[15] [82]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[8] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_74 ),
        .Q(\s_axi_rid[15] [8]),
        .R(1'b0));
  FDRE #(
    .INIT(1'b0)) 
    \goreg_dm.dout_i_reg[9] 
       (.C(s_aclk),
        .CE(E),
        .D(\gdm.dm_gen.dm_n_73 ),
        .Q(\s_axi_rid[15] [9]),
        .R(1'b0));
endmodule

(* ORIG_REF_NAME = "rd_bin_cntr" *) 
module axi_clock_converter_dramslim_rd_bin_cntr
   (Q,
    ram_empty_i_reg,
    D,
    \gnxpm_cdc.rd_pntr_gc_reg[3] ,
    \gnxpm_cdc.wr_pntr_bin_reg[2] ,
    \gpregsm1.curr_fwft_state_reg[1] ,
    \gnxpm_cdc.wr_pntr_bin_reg[3] ,
    E,
    s_aclk,
    out);
  output [3:0]Q;
  output ram_empty_i_reg;
  output [2:0]D;
  output [3:0]\gnxpm_cdc.rd_pntr_gc_reg[3] ;
  input \gnxpm_cdc.wr_pntr_bin_reg[2] ;
  input \gpregsm1.curr_fwft_state_reg[1] ;
  input [3:0]\gnxpm_cdc.wr_pntr_bin_reg[3] ;
  input [0:0]E;
  input s_aclk;
  input [0:0]out;

  wire [2:0]D;
  wire [0:0]E;
  wire [3:0]Q;
  wire [3:0]\gnxpm_cdc.rd_pntr_gc_reg[3] ;
  wire \gnxpm_cdc.wr_pntr_bin_reg[2] ;
  wire [3:0]\gnxpm_cdc.wr_pntr_bin_reg[3] ;
  wire \gpregsm1.curr_fwft_state_reg[1] ;
  wire [0:0]out;
  wire [3:0]plusOp__6;
  wire ram_empty_i_i_2__2_n_0;
  wire ram_empty_i_i_3__2_n_0;
  wire ram_empty_i_reg;
  wire s_aclk;

  LUT1 #(
    .INIT(2'h1)) 
    \gc0.count[0]_i_1__2 
       (.I0(Q[0]),
        .O(plusOp__6[0]));
  LUT2 #(
    .INIT(4'h6)) 
    \gc0.count[1]_i_1__2 
       (.I0(Q[0]),
        .I1(Q[1]),
        .O(plusOp__6[1]));
  (* SOFT_HLUTNM = "soft_lutpair28" *) 
  LUT3 #(
    .INIT(8'h78)) 
    \gc0.count[2]_i_1__2 
       (.I0(Q[1]),
        .I1(Q[0]),
        .I2(Q[2]),
        .O(plusOp__6[2]));
  (* SOFT_HLUTNM = "soft_lutpair28" *) 
  LUT4 #(
    .INIT(16'h7F80)) 
    \gc0.count[3]_i_1__2 
       (.I0(Q[2]),
        .I1(Q[0]),
        .I2(Q[1]),
        .I3(Q[3]),
        .O(plusOp__6[3]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_d1_reg[0] 
       (.C(s_aclk),
        .CE(E),
        .CLR(out),
        .D(Q[0]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg[3] [0]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_d1_reg[1] 
       (.C(s_aclk),
        .CE(E),
        .CLR(out),
        .D(Q[1]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg[3] [1]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_d1_reg[2] 
       (.C(s_aclk),
        .CE(E),
        .CLR(out),
        .D(Q[2]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg[3] [2]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_d1_reg[3] 
       (.C(s_aclk),
        .CE(E),
        .CLR(out),
        .D(Q[3]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg[3] [3]));
  FDPE #(
    .INIT(1'b1)) 
    \gc0.count_reg[0] 
       (.C(s_aclk),
        .CE(E),
        .D(plusOp__6[0]),
        .PRE(out),
        .Q(Q[0]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_reg[1] 
       (.C(s_aclk),
        .CE(E),
        .CLR(out),
        .D(plusOp__6[1]),
        .Q(Q[1]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_reg[2] 
       (.C(s_aclk),
        .CE(E),
        .CLR(out),
        .D(plusOp__6[2]),
        .Q(Q[2]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_reg[3] 
       (.C(s_aclk),
        .CE(E),
        .CLR(out),
        .D(plusOp__6[3]),
        .Q(Q[3]));
  (* SOFT_HLUTNM = "soft_lutpair27" *) 
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.rd_pntr_gc[0]_i_1__2 
       (.I0(\gnxpm_cdc.rd_pntr_gc_reg[3] [0]),
        .I1(\gnxpm_cdc.rd_pntr_gc_reg[3] [1]),
        .O(D[0]));
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.rd_pntr_gc[1]_i_1__2 
       (.I0(\gnxpm_cdc.rd_pntr_gc_reg[3] [1]),
        .I1(\gnxpm_cdc.rd_pntr_gc_reg[3] [2]),
        .O(D[1]));
  (* SOFT_HLUTNM = "soft_lutpair26" *) 
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.rd_pntr_gc[2]_i_1__2 
       (.I0(\gnxpm_cdc.rd_pntr_gc_reg[3] [2]),
        .I1(\gnxpm_cdc.rd_pntr_gc_reg[3] [3]),
        .O(D[2]));
  LUT4 #(
    .INIT(16'hF888)) 
    ram_empty_i_i_1__2
       (.I0(ram_empty_i_i_2__2_n_0),
        .I1(ram_empty_i_i_3__2_n_0),
        .I2(\gnxpm_cdc.wr_pntr_bin_reg[2] ),
        .I3(\gpregsm1.curr_fwft_state_reg[1] ),
        .O(ram_empty_i_reg));
  (* SOFT_HLUTNM = "soft_lutpair26" *) 
  LUT4 #(
    .INIT(16'h9009)) 
    ram_empty_i_i_2__2
       (.I0(\gnxpm_cdc.rd_pntr_gc_reg[3] [2]),
        .I1(\gnxpm_cdc.wr_pntr_bin_reg[3] [2]),
        .I2(\gnxpm_cdc.rd_pntr_gc_reg[3] [3]),
        .I3(\gnxpm_cdc.wr_pntr_bin_reg[3] [3]),
        .O(ram_empty_i_i_2__2_n_0));
  (* SOFT_HLUTNM = "soft_lutpair27" *) 
  LUT4 #(
    .INIT(16'h9009)) 
    ram_empty_i_i_3__2
       (.I0(\gnxpm_cdc.rd_pntr_gc_reg[3] [0]),
        .I1(\gnxpm_cdc.wr_pntr_bin_reg[3] [0]),
        .I2(\gnxpm_cdc.rd_pntr_gc_reg[3] [1]),
        .I3(\gnxpm_cdc.wr_pntr_bin_reg[3] [1]),
        .O(ram_empty_i_i_3__2_n_0));
endmodule

(* ORIG_REF_NAME = "rd_bin_cntr" *) 
module axi_clock_converter_dramslim_rd_bin_cntr_25
   (Q,
    ram_empty_i_reg,
    D,
    \gnxpm_cdc.rd_pntr_gc_reg[3] ,
    \gnxpm_cdc.wr_pntr_bin_reg[2] ,
    \gpregsm1.curr_fwft_state_reg[1] ,
    \gnxpm_cdc.wr_pntr_bin_reg[3] ,
    E,
    m_aclk,
    out);
  output [3:0]Q;
  output ram_empty_i_reg;
  output [2:0]D;
  output [3:0]\gnxpm_cdc.rd_pntr_gc_reg[3] ;
  input \gnxpm_cdc.wr_pntr_bin_reg[2] ;
  input \gpregsm1.curr_fwft_state_reg[1] ;
  input [3:0]\gnxpm_cdc.wr_pntr_bin_reg[3] ;
  input [0:0]E;
  input m_aclk;
  input [0:0]out;

  wire [2:0]D;
  wire [0:0]E;
  wire [3:0]Q;
  wire [3:0]\gnxpm_cdc.rd_pntr_gc_reg[3] ;
  wire \gnxpm_cdc.wr_pntr_bin_reg[2] ;
  wire [3:0]\gnxpm_cdc.wr_pntr_bin_reg[3] ;
  wire \gpregsm1.curr_fwft_state_reg[1] ;
  wire m_aclk;
  wire [0:0]out;
  wire [3:0]plusOp__0;
  wire ram_empty_i_i_2__0_n_0;
  wire ram_empty_i_i_3__0_n_0;
  wire ram_empty_i_reg;

  LUT1 #(
    .INIT(2'h1)) 
    \gc0.count[0]_i_1__0 
       (.I0(Q[0]),
        .O(plusOp__0[0]));
  LUT2 #(
    .INIT(4'h6)) 
    \gc0.count[1]_i_1__0 
       (.I0(Q[0]),
        .I1(Q[1]),
        .O(plusOp__0[1]));
  (* SOFT_HLUTNM = "soft_lutpair22" *) 
  LUT3 #(
    .INIT(8'h78)) 
    \gc0.count[2]_i_1__0 
       (.I0(Q[1]),
        .I1(Q[0]),
        .I2(Q[2]),
        .O(plusOp__0[2]));
  (* SOFT_HLUTNM = "soft_lutpair22" *) 
  LUT4 #(
    .INIT(16'h7F80)) 
    \gc0.count[3]_i_1__0 
       (.I0(Q[2]),
        .I1(Q[0]),
        .I2(Q[1]),
        .I3(Q[3]),
        .O(plusOp__0[3]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_d1_reg[0] 
       (.C(m_aclk),
        .CE(E),
        .CLR(out),
        .D(Q[0]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg[3] [0]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_d1_reg[1] 
       (.C(m_aclk),
        .CE(E),
        .CLR(out),
        .D(Q[1]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg[3] [1]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_d1_reg[2] 
       (.C(m_aclk),
        .CE(E),
        .CLR(out),
        .D(Q[2]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg[3] [2]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_d1_reg[3] 
       (.C(m_aclk),
        .CE(E),
        .CLR(out),
        .D(Q[3]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg[3] [3]));
  FDPE #(
    .INIT(1'b1)) 
    \gc0.count_reg[0] 
       (.C(m_aclk),
        .CE(E),
        .D(plusOp__0[0]),
        .PRE(out),
        .Q(Q[0]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_reg[1] 
       (.C(m_aclk),
        .CE(E),
        .CLR(out),
        .D(plusOp__0[1]),
        .Q(Q[1]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_reg[2] 
       (.C(m_aclk),
        .CE(E),
        .CLR(out),
        .D(plusOp__0[2]),
        .Q(Q[2]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_reg[3] 
       (.C(m_aclk),
        .CE(E),
        .CLR(out),
        .D(plusOp__0[3]),
        .Q(Q[3]));
  (* SOFT_HLUTNM = "soft_lutpair21" *) 
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.rd_pntr_gc[0]_i_1__0 
       (.I0(\gnxpm_cdc.rd_pntr_gc_reg[3] [0]),
        .I1(\gnxpm_cdc.rd_pntr_gc_reg[3] [1]),
        .O(D[0]));
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.rd_pntr_gc[1]_i_1__0 
       (.I0(\gnxpm_cdc.rd_pntr_gc_reg[3] [1]),
        .I1(\gnxpm_cdc.rd_pntr_gc_reg[3] [2]),
        .O(D[1]));
  (* SOFT_HLUTNM = "soft_lutpair20" *) 
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.rd_pntr_gc[2]_i_1__0 
       (.I0(\gnxpm_cdc.rd_pntr_gc_reg[3] [2]),
        .I1(\gnxpm_cdc.rd_pntr_gc_reg[3] [3]),
        .O(D[2]));
  LUT4 #(
    .INIT(16'hF888)) 
    ram_empty_i_i_1__0
       (.I0(ram_empty_i_i_2__0_n_0),
        .I1(ram_empty_i_i_3__0_n_0),
        .I2(\gnxpm_cdc.wr_pntr_bin_reg[2] ),
        .I3(\gpregsm1.curr_fwft_state_reg[1] ),
        .O(ram_empty_i_reg));
  (* SOFT_HLUTNM = "soft_lutpair20" *) 
  LUT4 #(
    .INIT(16'h9009)) 
    ram_empty_i_i_2__0
       (.I0(\gnxpm_cdc.rd_pntr_gc_reg[3] [2]),
        .I1(\gnxpm_cdc.wr_pntr_bin_reg[3] [2]),
        .I2(\gnxpm_cdc.rd_pntr_gc_reg[3] [3]),
        .I3(\gnxpm_cdc.wr_pntr_bin_reg[3] [3]),
        .O(ram_empty_i_i_2__0_n_0));
  (* SOFT_HLUTNM = "soft_lutpair21" *) 
  LUT4 #(
    .INIT(16'h9009)) 
    ram_empty_i_i_3__0
       (.I0(\gnxpm_cdc.rd_pntr_gc_reg[3] [0]),
        .I1(\gnxpm_cdc.wr_pntr_bin_reg[3] [0]),
        .I2(\gnxpm_cdc.rd_pntr_gc_reg[3] [1]),
        .I3(\gnxpm_cdc.wr_pntr_bin_reg[3] [1]),
        .O(ram_empty_i_i_3__0_n_0));
endmodule

(* ORIG_REF_NAME = "rd_bin_cntr" *) 
module axi_clock_converter_dramslim_rd_bin_cntr_46
   (Q,
    ram_empty_i_reg,
    \gnxpm_cdc.rd_pntr_gc_reg[2] ,
    \gnxpm_cdc.rd_pntr_gc_reg[3] ,
    \gnxpm_cdc.wr_pntr_bin_reg[2] ,
    \gpregsm1.curr_fwft_state_reg[1] ,
    \gnxpm_cdc.wr_pntr_bin_reg[3] ,
    E,
    m_aclk,
    out);
  output [3:0]Q;
  output ram_empty_i_reg;
  output [2:0]\gnxpm_cdc.rd_pntr_gc_reg[2] ;
  output [3:0]\gnxpm_cdc.rd_pntr_gc_reg[3] ;
  input \gnxpm_cdc.wr_pntr_bin_reg[2] ;
  input \gpregsm1.curr_fwft_state_reg[1] ;
  input [3:0]\gnxpm_cdc.wr_pntr_bin_reg[3] ;
  input [0:0]E;
  input m_aclk;
  input [0:0]out;

  wire [0:0]E;
  wire [3:0]Q;
  wire [2:0]\gnxpm_cdc.rd_pntr_gc_reg[2] ;
  wire [3:0]\gnxpm_cdc.rd_pntr_gc_reg[3] ;
  wire \gnxpm_cdc.wr_pntr_bin_reg[2] ;
  wire [3:0]\gnxpm_cdc.wr_pntr_bin_reg[3] ;
  wire \gpregsm1.curr_fwft_state_reg[1] ;
  wire m_aclk;
  wire [0:0]out;
  wire [3:0]plusOp;
  wire ram_empty_i_i_2_n_0;
  wire ram_empty_i_i_3_n_0;
  wire ram_empty_i_reg;

  LUT1 #(
    .INIT(2'h1)) 
    \gc0.count[0]_i_1 
       (.I0(Q[0]),
        .O(plusOp[0]));
  LUT2 #(
    .INIT(4'h6)) 
    \gc0.count[1]_i_1 
       (.I0(Q[0]),
        .I1(Q[1]),
        .O(plusOp[1]));
  (* SOFT_HLUTNM = "soft_lutpair16" *) 
  LUT3 #(
    .INIT(8'h78)) 
    \gc0.count[2]_i_1 
       (.I0(Q[1]),
        .I1(Q[0]),
        .I2(Q[2]),
        .O(plusOp[2]));
  (* SOFT_HLUTNM = "soft_lutpair16" *) 
  LUT4 #(
    .INIT(16'h7F80)) 
    \gc0.count[3]_i_1 
       (.I0(Q[2]),
        .I1(Q[0]),
        .I2(Q[1]),
        .I3(Q[3]),
        .O(plusOp[3]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_d1_reg[0] 
       (.C(m_aclk),
        .CE(E),
        .CLR(out),
        .D(Q[0]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg[3] [0]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_d1_reg[1] 
       (.C(m_aclk),
        .CE(E),
        .CLR(out),
        .D(Q[1]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg[3] [1]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_d1_reg[2] 
       (.C(m_aclk),
        .CE(E),
        .CLR(out),
        .D(Q[2]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg[3] [2]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_d1_reg[3] 
       (.C(m_aclk),
        .CE(E),
        .CLR(out),
        .D(Q[3]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg[3] [3]));
  FDPE #(
    .INIT(1'b1)) 
    \gc0.count_reg[0] 
       (.C(m_aclk),
        .CE(E),
        .D(plusOp[0]),
        .PRE(out),
        .Q(Q[0]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_reg[1] 
       (.C(m_aclk),
        .CE(E),
        .CLR(out),
        .D(plusOp[1]),
        .Q(Q[1]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_reg[2] 
       (.C(m_aclk),
        .CE(E),
        .CLR(out),
        .D(plusOp[2]),
        .Q(Q[2]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_reg[3] 
       (.C(m_aclk),
        .CE(E),
        .CLR(out),
        .D(plusOp[3]),
        .Q(Q[3]));
  (* SOFT_HLUTNM = "soft_lutpair15" *) 
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.rd_pntr_gc[0]_i_1 
       (.I0(\gnxpm_cdc.rd_pntr_gc_reg[3] [0]),
        .I1(\gnxpm_cdc.rd_pntr_gc_reg[3] [1]),
        .O(\gnxpm_cdc.rd_pntr_gc_reg[2] [0]));
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.rd_pntr_gc[1]_i_1 
       (.I0(\gnxpm_cdc.rd_pntr_gc_reg[3] [1]),
        .I1(\gnxpm_cdc.rd_pntr_gc_reg[3] [2]),
        .O(\gnxpm_cdc.rd_pntr_gc_reg[2] [1]));
  (* SOFT_HLUTNM = "soft_lutpair14" *) 
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.rd_pntr_gc[2]_i_1 
       (.I0(\gnxpm_cdc.rd_pntr_gc_reg[3] [2]),
        .I1(\gnxpm_cdc.rd_pntr_gc_reg[3] [3]),
        .O(\gnxpm_cdc.rd_pntr_gc_reg[2] [2]));
  LUT4 #(
    .INIT(16'hF888)) 
    ram_empty_i_i_1
       (.I0(ram_empty_i_i_2_n_0),
        .I1(ram_empty_i_i_3_n_0),
        .I2(\gnxpm_cdc.wr_pntr_bin_reg[2] ),
        .I3(\gpregsm1.curr_fwft_state_reg[1] ),
        .O(ram_empty_i_reg));
  (* SOFT_HLUTNM = "soft_lutpair14" *) 
  LUT4 #(
    .INIT(16'h9009)) 
    ram_empty_i_i_2
       (.I0(\gnxpm_cdc.rd_pntr_gc_reg[3] [2]),
        .I1(\gnxpm_cdc.wr_pntr_bin_reg[3] [2]),
        .I2(\gnxpm_cdc.rd_pntr_gc_reg[3] [3]),
        .I3(\gnxpm_cdc.wr_pntr_bin_reg[3] [3]),
        .O(ram_empty_i_i_2_n_0));
  (* SOFT_HLUTNM = "soft_lutpair15" *) 
  LUT4 #(
    .INIT(16'h9009)) 
    ram_empty_i_i_3
       (.I0(\gnxpm_cdc.rd_pntr_gc_reg[3] [0]),
        .I1(\gnxpm_cdc.wr_pntr_bin_reg[3] [0]),
        .I2(\gnxpm_cdc.rd_pntr_gc_reg[3] [1]),
        .I3(\gnxpm_cdc.wr_pntr_bin_reg[3] [1]),
        .O(ram_empty_i_i_3_n_0));
endmodule

(* ORIG_REF_NAME = "rd_bin_cntr" *) 
module axi_clock_converter_dramslim_rd_bin_cntr_67
   (Q,
    ram_empty_i_reg,
    D,
    \gnxpm_cdc.rd_pntr_gc_reg[3] ,
    \gnxpm_cdc.wr_pntr_bin_reg[2] ,
    \gpregsm1.curr_fwft_state_reg[1] ,
    \gnxpm_cdc.wr_pntr_bin_reg[3] ,
    E,
    s_aclk,
    out);
  output [3:0]Q;
  output ram_empty_i_reg;
  output [2:0]D;
  output [3:0]\gnxpm_cdc.rd_pntr_gc_reg[3] ;
  input \gnxpm_cdc.wr_pntr_bin_reg[2] ;
  input \gpregsm1.curr_fwft_state_reg[1] ;
  input [3:0]\gnxpm_cdc.wr_pntr_bin_reg[3] ;
  input [0:0]E;
  input s_aclk;
  input [0:0]out;

  wire [2:0]D;
  wire [0:0]E;
  wire [3:0]Q;
  wire [3:0]\gnxpm_cdc.rd_pntr_gc_reg[3] ;
  wire \gnxpm_cdc.wr_pntr_bin_reg[2] ;
  wire [3:0]\gnxpm_cdc.wr_pntr_bin_reg[3] ;
  wire \gpregsm1.curr_fwft_state_reg[1] ;
  wire [0:0]out;
  wire [3:0]plusOp__8;
  wire ram_empty_i_i_2__3_n_0;
  wire ram_empty_i_i_3__3_n_0;
  wire ram_empty_i_reg;
  wire s_aclk;

  LUT1 #(
    .INIT(2'h1)) 
    \gc0.count[0]_i_1__3 
       (.I0(Q[0]),
        .O(plusOp__8[0]));
  LUT2 #(
    .INIT(4'h6)) 
    \gc0.count[1]_i_1__3 
       (.I0(Q[0]),
        .I1(Q[1]),
        .O(plusOp__8[1]));
  (* SOFT_HLUTNM = "soft_lutpair10" *) 
  LUT3 #(
    .INIT(8'h78)) 
    \gc0.count[2]_i_1__3 
       (.I0(Q[1]),
        .I1(Q[0]),
        .I2(Q[2]),
        .O(plusOp__8[2]));
  (* SOFT_HLUTNM = "soft_lutpair10" *) 
  LUT4 #(
    .INIT(16'h7F80)) 
    \gc0.count[3]_i_1__3 
       (.I0(Q[2]),
        .I1(Q[0]),
        .I2(Q[1]),
        .I3(Q[3]),
        .O(plusOp__8[3]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_d1_reg[0] 
       (.C(s_aclk),
        .CE(E),
        .CLR(out),
        .D(Q[0]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg[3] [0]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_d1_reg[1] 
       (.C(s_aclk),
        .CE(E),
        .CLR(out),
        .D(Q[1]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg[3] [1]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_d1_reg[2] 
       (.C(s_aclk),
        .CE(E),
        .CLR(out),
        .D(Q[2]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg[3] [2]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_d1_reg[3] 
       (.C(s_aclk),
        .CE(E),
        .CLR(out),
        .D(Q[3]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg[3] [3]));
  FDPE #(
    .INIT(1'b1)) 
    \gc0.count_reg[0] 
       (.C(s_aclk),
        .CE(E),
        .D(plusOp__8[0]),
        .PRE(out),
        .Q(Q[0]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_reg[1] 
       (.C(s_aclk),
        .CE(E),
        .CLR(out),
        .D(plusOp__8[1]),
        .Q(Q[1]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_reg[2] 
       (.C(s_aclk),
        .CE(E),
        .CLR(out),
        .D(plusOp__8[2]),
        .Q(Q[2]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_reg[3] 
       (.C(s_aclk),
        .CE(E),
        .CLR(out),
        .D(plusOp__8[3]),
        .Q(Q[3]));
  (* SOFT_HLUTNM = "soft_lutpair9" *) 
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.rd_pntr_gc[0]_i_1__3 
       (.I0(\gnxpm_cdc.rd_pntr_gc_reg[3] [0]),
        .I1(\gnxpm_cdc.rd_pntr_gc_reg[3] [1]),
        .O(D[0]));
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.rd_pntr_gc[1]_i_1__3 
       (.I0(\gnxpm_cdc.rd_pntr_gc_reg[3] [1]),
        .I1(\gnxpm_cdc.rd_pntr_gc_reg[3] [2]),
        .O(D[1]));
  (* SOFT_HLUTNM = "soft_lutpair8" *) 
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.rd_pntr_gc[2]_i_1__3 
       (.I0(\gnxpm_cdc.rd_pntr_gc_reg[3] [2]),
        .I1(\gnxpm_cdc.rd_pntr_gc_reg[3] [3]),
        .O(D[2]));
  LUT4 #(
    .INIT(16'hF888)) 
    ram_empty_i_i_1__3
       (.I0(ram_empty_i_i_2__3_n_0),
        .I1(ram_empty_i_i_3__3_n_0),
        .I2(\gnxpm_cdc.wr_pntr_bin_reg[2] ),
        .I3(\gpregsm1.curr_fwft_state_reg[1] ),
        .O(ram_empty_i_reg));
  (* SOFT_HLUTNM = "soft_lutpair8" *) 
  LUT4 #(
    .INIT(16'h9009)) 
    ram_empty_i_i_2__3
       (.I0(\gnxpm_cdc.rd_pntr_gc_reg[3] [2]),
        .I1(\gnxpm_cdc.wr_pntr_bin_reg[3] [2]),
        .I2(\gnxpm_cdc.rd_pntr_gc_reg[3] [3]),
        .I3(\gnxpm_cdc.wr_pntr_bin_reg[3] [3]),
        .O(ram_empty_i_i_2__3_n_0));
  (* SOFT_HLUTNM = "soft_lutpair9" *) 
  LUT4 #(
    .INIT(16'h9009)) 
    ram_empty_i_i_3__3
       (.I0(\gnxpm_cdc.rd_pntr_gc_reg[3] [0]),
        .I1(\gnxpm_cdc.wr_pntr_bin_reg[3] [0]),
        .I2(\gnxpm_cdc.rd_pntr_gc_reg[3] [1]),
        .I3(\gnxpm_cdc.wr_pntr_bin_reg[3] [1]),
        .O(ram_empty_i_i_3__3_n_0));
endmodule

(* ORIG_REF_NAME = "rd_bin_cntr" *) 
module axi_clock_converter_dramslim_rd_bin_cntr_91
   (Q,
    ram_empty_i_reg,
    D,
    \gnxpm_cdc.rd_pntr_gc_reg[3] ,
    \gnxpm_cdc.wr_pntr_bin_reg[2] ,
    \gpregsm1.curr_fwft_state_reg[1] ,
    \gnxpm_cdc.wr_pntr_bin_reg[3] ,
    E,
    m_aclk,
    out);
  output [3:0]Q;
  output ram_empty_i_reg;
  output [2:0]D;
  output [3:0]\gnxpm_cdc.rd_pntr_gc_reg[3] ;
  input \gnxpm_cdc.wr_pntr_bin_reg[2] ;
  input \gpregsm1.curr_fwft_state_reg[1] ;
  input [3:0]\gnxpm_cdc.wr_pntr_bin_reg[3] ;
  input [0:0]E;
  input m_aclk;
  input [0:0]out;

  wire [2:0]D;
  wire [0:0]E;
  wire [3:0]Q;
  wire [3:0]\gnxpm_cdc.rd_pntr_gc_reg[3] ;
  wire \gnxpm_cdc.wr_pntr_bin_reg[2] ;
  wire [3:0]\gnxpm_cdc.wr_pntr_bin_reg[3] ;
  wire \gpregsm1.curr_fwft_state_reg[1] ;
  wire m_aclk;
  wire [0:0]out;
  wire [3:0]plusOp__2;
  wire ram_empty_i_i_2__1_n_0;
  wire ram_empty_i_i_3__1_n_0;
  wire ram_empty_i_reg;

  LUT1 #(
    .INIT(2'h1)) 
    \gc0.count[0]_i_1__1 
       (.I0(Q[0]),
        .O(plusOp__2[0]));
  LUT2 #(
    .INIT(4'h6)) 
    \gc0.count[1]_i_1__1 
       (.I0(Q[0]),
        .I1(Q[1]),
        .O(plusOp__2[1]));
  (* SOFT_HLUTNM = "soft_lutpair4" *) 
  LUT3 #(
    .INIT(8'h78)) 
    \gc0.count[2]_i_1__1 
       (.I0(Q[1]),
        .I1(Q[0]),
        .I2(Q[2]),
        .O(plusOp__2[2]));
  (* SOFT_HLUTNM = "soft_lutpair4" *) 
  LUT4 #(
    .INIT(16'h7F80)) 
    \gc0.count[3]_i_1__1 
       (.I0(Q[2]),
        .I1(Q[0]),
        .I2(Q[1]),
        .I3(Q[3]),
        .O(plusOp__2[3]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_d1_reg[0] 
       (.C(m_aclk),
        .CE(E),
        .CLR(out),
        .D(Q[0]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg[3] [0]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_d1_reg[1] 
       (.C(m_aclk),
        .CE(E),
        .CLR(out),
        .D(Q[1]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg[3] [1]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_d1_reg[2] 
       (.C(m_aclk),
        .CE(E),
        .CLR(out),
        .D(Q[2]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg[3] [2]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_d1_reg[3] 
       (.C(m_aclk),
        .CE(E),
        .CLR(out),
        .D(Q[3]),
        .Q(\gnxpm_cdc.rd_pntr_gc_reg[3] [3]));
  FDPE #(
    .INIT(1'b1)) 
    \gc0.count_reg[0] 
       (.C(m_aclk),
        .CE(E),
        .D(plusOp__2[0]),
        .PRE(out),
        .Q(Q[0]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_reg[1] 
       (.C(m_aclk),
        .CE(E),
        .CLR(out),
        .D(plusOp__2[1]),
        .Q(Q[1]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_reg[2] 
       (.C(m_aclk),
        .CE(E),
        .CLR(out),
        .D(plusOp__2[2]),
        .Q(Q[2]));
  FDCE #(
    .INIT(1'b0)) 
    \gc0.count_reg[3] 
       (.C(m_aclk),
        .CE(E),
        .CLR(out),
        .D(plusOp__2[3]),
        .Q(Q[3]));
  (* SOFT_HLUTNM = "soft_lutpair3" *) 
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.rd_pntr_gc[0]_i_1__1 
       (.I0(\gnxpm_cdc.rd_pntr_gc_reg[3] [0]),
        .I1(\gnxpm_cdc.rd_pntr_gc_reg[3] [1]),
        .O(D[0]));
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.rd_pntr_gc[1]_i_1__1 
       (.I0(\gnxpm_cdc.rd_pntr_gc_reg[3] [1]),
        .I1(\gnxpm_cdc.rd_pntr_gc_reg[3] [2]),
        .O(D[1]));
  (* SOFT_HLUTNM = "soft_lutpair2" *) 
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.rd_pntr_gc[2]_i_1__1 
       (.I0(\gnxpm_cdc.rd_pntr_gc_reg[3] [2]),
        .I1(\gnxpm_cdc.rd_pntr_gc_reg[3] [3]),
        .O(D[2]));
  LUT4 #(
    .INIT(16'hF888)) 
    ram_empty_i_i_1__1
       (.I0(ram_empty_i_i_2__1_n_0),
        .I1(ram_empty_i_i_3__1_n_0),
        .I2(\gnxpm_cdc.wr_pntr_bin_reg[2] ),
        .I3(\gpregsm1.curr_fwft_state_reg[1] ),
        .O(ram_empty_i_reg));
  (* SOFT_HLUTNM = "soft_lutpair2" *) 
  LUT4 #(
    .INIT(16'h9009)) 
    ram_empty_i_i_2__1
       (.I0(\gnxpm_cdc.rd_pntr_gc_reg[3] [2]),
        .I1(\gnxpm_cdc.wr_pntr_bin_reg[3] [2]),
        .I2(\gnxpm_cdc.rd_pntr_gc_reg[3] [3]),
        .I3(\gnxpm_cdc.wr_pntr_bin_reg[3] [3]),
        .O(ram_empty_i_i_2__1_n_0));
  (* SOFT_HLUTNM = "soft_lutpair3" *) 
  LUT4 #(
    .INIT(16'h9009)) 
    ram_empty_i_i_3__1
       (.I0(\gnxpm_cdc.rd_pntr_gc_reg[3] [0]),
        .I1(\gnxpm_cdc.wr_pntr_bin_reg[3] [0]),
        .I2(\gnxpm_cdc.rd_pntr_gc_reg[3] [1]),
        .I3(\gnxpm_cdc.wr_pntr_bin_reg[3] [1]),
        .O(ram_empty_i_i_3__1_n_0));
endmodule

(* ORIG_REF_NAME = "rd_fwft" *) 
module axi_clock_converter_dramslim_rd_fwft
   (ram_empty_i_reg,
    E,
    \goreg_dm.dout_i_reg[17] ,
    s_axi_bvalid,
    s_aclk,
    out,
    s_axi_bready,
    ram_empty_fb_i_reg,
    \gnxpm_cdc.wr_pntr_bin_reg[3] ,
    Q);
  output ram_empty_i_reg;
  output [0:0]E;
  output [0:0]\goreg_dm.dout_i_reg[17] ;
  output s_axi_bvalid;
  input s_aclk;
  input [1:0]out;
  input s_axi_bready;
  input ram_empty_fb_i_reg;
  input [0:0]\gnxpm_cdc.wr_pntr_bin_reg[3] ;
  input [0:0]Q;

  wire [0:0]E;
  wire [0:0]Q;
  (* DONT_TOUCH *) wire aempty_fwft_fb_i;
  (* DONT_TOUCH *) wire aempty_fwft_i;
  wire aempty_fwft_i0;
  (* DONT_TOUCH *) wire [1:0]curr_fwft_state;
  (* DONT_TOUCH *) wire empty_fwft_fb_i;
  (* DONT_TOUCH *) wire empty_fwft_fb_o_i;
  wire empty_fwft_fb_o_i0;
  (* DONT_TOUCH *) wire empty_fwft_i;
  wire empty_fwft_i0;
  wire [0:0]\gnxpm_cdc.wr_pntr_bin_reg[3] ;
  wire [0:0]\goreg_dm.dout_i_reg[17] ;
  wire [1:0]next_fwft_state;
  wire [1:0]out;
  wire ram_empty_fb_i_reg;
  wire ram_empty_i_reg;
  wire s_aclk;
  wire s_axi_bready;
  wire s_axi_bvalid;
  (* DONT_TOUCH *) wire user_valid;

  LUT5 #(
    .INIT(32'hF8E0C0F0)) 
    aempty_fwft_fb_i_i_1__2
       (.I0(s_axi_bready),
        .I1(ram_empty_fb_i_reg),
        .I2(aempty_fwft_fb_i),
        .I3(curr_fwft_state[1]),
        .I4(curr_fwft_state[0]),
        .O(aempty_fwft_i0));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    aempty_fwft_fb_i_reg
       (.C(s_aclk),
        .CE(1'b1),
        .D(aempty_fwft_i0),
        .PRE(out[1]),
        .Q(aempty_fwft_fb_i));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    aempty_fwft_i_reg
       (.C(s_aclk),
        .CE(1'b1),
        .D(aempty_fwft_i0),
        .PRE(out[1]),
        .Q(aempty_fwft_i));
  LUT4 #(
    .INIT(16'h88EA)) 
    empty_fwft_fb_i_i_1__2
       (.I0(empty_fwft_fb_i),
        .I1(curr_fwft_state[0]),
        .I2(s_axi_bready),
        .I3(curr_fwft_state[1]),
        .O(empty_fwft_i0));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    empty_fwft_fb_i_reg
       (.C(s_aclk),
        .CE(1'b1),
        .D(empty_fwft_i0),
        .PRE(out[1]),
        .Q(empty_fwft_fb_i));
  LUT4 #(
    .INIT(16'h88EA)) 
    empty_fwft_fb_o_i_i_1__2
       (.I0(empty_fwft_fb_o_i),
        .I1(curr_fwft_state[0]),
        .I2(s_axi_bready),
        .I3(curr_fwft_state[1]),
        .O(empty_fwft_fb_o_i0));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    empty_fwft_fb_o_i_reg
       (.C(s_aclk),
        .CE(1'b1),
        .D(empty_fwft_fb_o_i0),
        .PRE(out[1]),
        .Q(empty_fwft_fb_o_i));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    empty_fwft_i_reg
       (.C(s_aclk),
        .CE(1'b1),
        .D(empty_fwft_i0),
        .PRE(out[1]),
        .Q(empty_fwft_i));
  LUT4 #(
    .INIT(16'h00DF)) 
    \gc0.count_d1[3]_i_1__2 
       (.I0(curr_fwft_state[1]),
        .I1(s_axi_bready),
        .I2(curr_fwft_state[0]),
        .I3(ram_empty_fb_i_reg),
        .O(E));
  LUT4 #(
    .INIT(16'h4404)) 
    \goreg_dm.dout_i[17]_i_1 
       (.I0(out[0]),
        .I1(curr_fwft_state[1]),
        .I2(curr_fwft_state[0]),
        .I3(s_axi_bready),
        .O(\goreg_dm.dout_i_reg[17] ));
  LUT3 #(
    .INIT(8'hAE)) 
    \gpregsm1.curr_fwft_state[0]_i_1__2 
       (.I0(curr_fwft_state[1]),
        .I1(curr_fwft_state[0]),
        .I2(s_axi_bready),
        .O(next_fwft_state[0]));
  LUT4 #(
    .INIT(16'h20FF)) 
    \gpregsm1.curr_fwft_state[1]_i_1__2 
       (.I0(curr_fwft_state[1]),
        .I1(s_axi_bready),
        .I2(curr_fwft_state[0]),
        .I3(ram_empty_fb_i_reg),
        .O(next_fwft_state[1]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDCE #(
    .INIT(1'b0)) 
    \gpregsm1.curr_fwft_state_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(out[1]),
        .D(next_fwft_state[0]),
        .Q(curr_fwft_state[0]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDCE #(
    .INIT(1'b0)) 
    \gpregsm1.curr_fwft_state_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(out[1]),
        .D(next_fwft_state[1]),
        .Q(curr_fwft_state[1]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDCE #(
    .INIT(1'b0)) 
    \gpregsm1.user_valid_reg 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(out[1]),
        .D(next_fwft_state[0]),
        .Q(user_valid));
  LUT6 #(
    .INIT(64'h00DF0000000000DF)) 
    ram_empty_i_i_5__2
       (.I0(curr_fwft_state[1]),
        .I1(s_axi_bready),
        .I2(curr_fwft_state[0]),
        .I3(ram_empty_fb_i_reg),
        .I4(\gnxpm_cdc.wr_pntr_bin_reg[3] ),
        .I5(Q),
        .O(ram_empty_i_reg));
  LUT1 #(
    .INIT(2'h1)) 
    s_axi_bvalid_INST_0
       (.I0(empty_fwft_i),
        .O(s_axi_bvalid));
endmodule

(* ORIG_REF_NAME = "rd_fwft" *) 
module axi_clock_converter_dramslim_rd_fwft_23
   (ram_empty_i_reg,
    E,
    \goreg_dm.dout_i_reg[72] ,
    m_axi_wvalid,
    m_aclk,
    out,
    m_axi_wready,
    ram_empty_fb_i_reg,
    \gnxpm_cdc.wr_pntr_bin_reg[3] ,
    Q);
  output ram_empty_i_reg;
  output [0:0]E;
  output [0:0]\goreg_dm.dout_i_reg[72] ;
  output m_axi_wvalid;
  input m_aclk;
  input [1:0]out;
  input m_axi_wready;
  input ram_empty_fb_i_reg;
  input [0:0]\gnxpm_cdc.wr_pntr_bin_reg[3] ;
  input [0:0]Q;

  wire [0:0]E;
  wire [0:0]Q;
  (* DONT_TOUCH *) wire aempty_fwft_fb_i;
  (* DONT_TOUCH *) wire aempty_fwft_i;
  wire aempty_fwft_i0;
  (* DONT_TOUCH *) wire [1:0]curr_fwft_state;
  (* DONT_TOUCH *) wire empty_fwft_fb_i;
  (* DONT_TOUCH *) wire empty_fwft_fb_o_i;
  wire empty_fwft_fb_o_i0;
  (* DONT_TOUCH *) wire empty_fwft_i;
  wire empty_fwft_i0;
  wire [0:0]\gnxpm_cdc.wr_pntr_bin_reg[3] ;
  wire [0:0]\goreg_dm.dout_i_reg[72] ;
  wire m_aclk;
  wire m_axi_wready;
  wire m_axi_wvalid;
  wire [1:0]next_fwft_state;
  wire [1:0]out;
  wire ram_empty_fb_i_reg;
  wire ram_empty_i_reg;
  (* DONT_TOUCH *) wire user_valid;

  LUT5 #(
    .INIT(32'hFAEF8000)) 
    aempty_fwft_fb_i_i_1__0
       (.I0(ram_empty_fb_i_reg),
        .I1(m_axi_wready),
        .I2(curr_fwft_state[0]),
        .I3(curr_fwft_state[1]),
        .I4(aempty_fwft_fb_i),
        .O(aempty_fwft_i0));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    aempty_fwft_fb_i_reg
       (.C(m_aclk),
        .CE(1'b1),
        .D(aempty_fwft_i0),
        .PRE(out[1]),
        .Q(aempty_fwft_fb_i));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    aempty_fwft_i_reg
       (.C(m_aclk),
        .CE(1'b1),
        .D(aempty_fwft_i0),
        .PRE(out[1]),
        .Q(aempty_fwft_i));
  LUT4 #(
    .INIT(16'hB2A2)) 
    empty_fwft_fb_i_i_1__0
       (.I0(empty_fwft_fb_i),
        .I1(curr_fwft_state[1]),
        .I2(curr_fwft_state[0]),
        .I3(m_axi_wready),
        .O(empty_fwft_i0));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    empty_fwft_fb_i_reg
       (.C(m_aclk),
        .CE(1'b1),
        .D(empty_fwft_i0),
        .PRE(out[1]),
        .Q(empty_fwft_fb_i));
  LUT4 #(
    .INIT(16'hB2A2)) 
    empty_fwft_fb_o_i_i_1__0
       (.I0(empty_fwft_fb_o_i),
        .I1(curr_fwft_state[1]),
        .I2(curr_fwft_state[0]),
        .I3(m_axi_wready),
        .O(empty_fwft_fb_o_i0));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    empty_fwft_fb_o_i_reg
       (.C(m_aclk),
        .CE(1'b1),
        .D(empty_fwft_fb_o_i0),
        .PRE(out[1]),
        .Q(empty_fwft_fb_o_i));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    empty_fwft_i_reg
       (.C(m_aclk),
        .CE(1'b1),
        .D(empty_fwft_i0),
        .PRE(out[1]),
        .Q(empty_fwft_i));
  LUT4 #(
    .INIT(16'h00DF)) 
    \gc0.count_d1[3]_i_1__0 
       (.I0(curr_fwft_state[1]),
        .I1(m_axi_wready),
        .I2(curr_fwft_state[0]),
        .I3(ram_empty_fb_i_reg),
        .O(E));
  LUT4 #(
    .INIT(16'h4404)) 
    \goreg_dm.dout_i[72]_i_1 
       (.I0(out[0]),
        .I1(curr_fwft_state[1]),
        .I2(curr_fwft_state[0]),
        .I3(m_axi_wready),
        .O(\goreg_dm.dout_i_reg[72] ));
  LUT3 #(
    .INIT(8'hAE)) 
    \gpregsm1.curr_fwft_state[0]_i_1__0 
       (.I0(curr_fwft_state[1]),
        .I1(curr_fwft_state[0]),
        .I2(m_axi_wready),
        .O(next_fwft_state[0]));
  LUT4 #(
    .INIT(16'h20FF)) 
    \gpregsm1.curr_fwft_state[1]_i_1__0 
       (.I0(curr_fwft_state[1]),
        .I1(m_axi_wready),
        .I2(curr_fwft_state[0]),
        .I3(ram_empty_fb_i_reg),
        .O(next_fwft_state[1]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDCE #(
    .INIT(1'b0)) 
    \gpregsm1.curr_fwft_state_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(out[1]),
        .D(next_fwft_state[0]),
        .Q(curr_fwft_state[0]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDCE #(
    .INIT(1'b0)) 
    \gpregsm1.curr_fwft_state_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(out[1]),
        .D(next_fwft_state[1]),
        .Q(curr_fwft_state[1]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDCE #(
    .INIT(1'b0)) 
    \gpregsm1.user_valid_reg 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(out[1]),
        .D(next_fwft_state[0]),
        .Q(user_valid));
  LUT1 #(
    .INIT(2'h1)) 
    m_axi_wvalid_INST_0
       (.I0(empty_fwft_i),
        .O(m_axi_wvalid));
  LUT6 #(
    .INIT(64'h00DF0000000000DF)) 
    ram_empty_i_i_5__0
       (.I0(curr_fwft_state[1]),
        .I1(m_axi_wready),
        .I2(curr_fwft_state[0]),
        .I3(ram_empty_fb_i_reg),
        .I4(\gnxpm_cdc.wr_pntr_bin_reg[3] ),
        .I5(Q),
        .O(ram_empty_i_reg));
endmodule

(* ORIG_REF_NAME = "rd_fwft" *) 
module axi_clock_converter_dramslim_rd_fwft_44
   (ram_empty_i_reg,
    E,
    \goreg_dm.dout_i_reg[108] ,
    m_axi_awvalid,
    m_aclk,
    out,
    m_axi_awready,
    ram_empty_fb_i_reg,
    \gnxpm_cdc.wr_pntr_bin_reg[3] ,
    Q);
  output ram_empty_i_reg;
  output [0:0]E;
  output [0:0]\goreg_dm.dout_i_reg[108] ;
  output m_axi_awvalid;
  input m_aclk;
  input [1:0]out;
  input m_axi_awready;
  input ram_empty_fb_i_reg;
  input [0:0]\gnxpm_cdc.wr_pntr_bin_reg[3] ;
  input [0:0]Q;

  wire [0:0]E;
  wire [0:0]Q;
  (* DONT_TOUCH *) wire aempty_fwft_fb_i;
  (* DONT_TOUCH *) wire aempty_fwft_i;
  wire aempty_fwft_i0;
  (* DONT_TOUCH *) wire [1:0]curr_fwft_state;
  (* DONT_TOUCH *) wire empty_fwft_fb_i;
  (* DONT_TOUCH *) wire empty_fwft_fb_o_i;
  wire empty_fwft_fb_o_i0;
  (* DONT_TOUCH *) wire empty_fwft_i;
  wire empty_fwft_i0;
  wire [0:0]\gnxpm_cdc.wr_pntr_bin_reg[3] ;
  wire [0:0]\goreg_dm.dout_i_reg[108] ;
  wire m_aclk;
  wire m_axi_awready;
  wire m_axi_awvalid;
  wire [1:0]next_fwft_state;
  wire [1:0]out;
  wire ram_empty_fb_i_reg;
  wire ram_empty_i_reg;
  (* DONT_TOUCH *) wire user_valid;

  LUT5 #(
    .INIT(32'hF8E0C0F0)) 
    aempty_fwft_fb_i_i_1
       (.I0(m_axi_awready),
        .I1(ram_empty_fb_i_reg),
        .I2(aempty_fwft_fb_i),
        .I3(curr_fwft_state[1]),
        .I4(curr_fwft_state[0]),
        .O(aempty_fwft_i0));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    aempty_fwft_fb_i_reg
       (.C(m_aclk),
        .CE(1'b1),
        .D(aempty_fwft_i0),
        .PRE(out[1]),
        .Q(aempty_fwft_fb_i));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    aempty_fwft_i_reg
       (.C(m_aclk),
        .CE(1'b1),
        .D(aempty_fwft_i0),
        .PRE(out[1]),
        .Q(aempty_fwft_i));
  LUT4 #(
    .INIT(16'h88EA)) 
    empty_fwft_fb_i_i_1
       (.I0(empty_fwft_fb_i),
        .I1(curr_fwft_state[0]),
        .I2(m_axi_awready),
        .I3(curr_fwft_state[1]),
        .O(empty_fwft_i0));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    empty_fwft_fb_i_reg
       (.C(m_aclk),
        .CE(1'b1),
        .D(empty_fwft_i0),
        .PRE(out[1]),
        .Q(empty_fwft_fb_i));
  LUT4 #(
    .INIT(16'h88EA)) 
    empty_fwft_fb_o_i_i_1
       (.I0(empty_fwft_fb_o_i),
        .I1(curr_fwft_state[0]),
        .I2(m_axi_awready),
        .I3(curr_fwft_state[1]),
        .O(empty_fwft_fb_o_i0));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    empty_fwft_fb_o_i_reg
       (.C(m_aclk),
        .CE(1'b1),
        .D(empty_fwft_fb_o_i0),
        .PRE(out[1]),
        .Q(empty_fwft_fb_o_i));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    empty_fwft_i_reg
       (.C(m_aclk),
        .CE(1'b1),
        .D(empty_fwft_i0),
        .PRE(out[1]),
        .Q(empty_fwft_i));
  LUT4 #(
    .INIT(16'h00DF)) 
    \gc0.count_d1[3]_i_1 
       (.I0(curr_fwft_state[1]),
        .I1(m_axi_awready),
        .I2(curr_fwft_state[0]),
        .I3(ram_empty_fb_i_reg),
        .O(E));
  LUT4 #(
    .INIT(16'h4404)) 
    \goreg_dm.dout_i[108]_i_1 
       (.I0(out[0]),
        .I1(curr_fwft_state[1]),
        .I2(curr_fwft_state[0]),
        .I3(m_axi_awready),
        .O(\goreg_dm.dout_i_reg[108] ));
  LUT3 #(
    .INIT(8'hAE)) 
    \gpregsm1.curr_fwft_state[0]_i_1 
       (.I0(curr_fwft_state[1]),
        .I1(curr_fwft_state[0]),
        .I2(m_axi_awready),
        .O(next_fwft_state[0]));
  LUT4 #(
    .INIT(16'h20FF)) 
    \gpregsm1.curr_fwft_state[1]_i_1 
       (.I0(curr_fwft_state[1]),
        .I1(m_axi_awready),
        .I2(curr_fwft_state[0]),
        .I3(ram_empty_fb_i_reg),
        .O(next_fwft_state[1]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDCE #(
    .INIT(1'b0)) 
    \gpregsm1.curr_fwft_state_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(out[1]),
        .D(next_fwft_state[0]),
        .Q(curr_fwft_state[0]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDCE #(
    .INIT(1'b0)) 
    \gpregsm1.curr_fwft_state_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(out[1]),
        .D(next_fwft_state[1]),
        .Q(curr_fwft_state[1]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDCE #(
    .INIT(1'b0)) 
    \gpregsm1.user_valid_reg 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(out[1]),
        .D(next_fwft_state[0]),
        .Q(user_valid));
  LUT1 #(
    .INIT(2'h1)) 
    m_axi_awvalid_INST_0
       (.I0(empty_fwft_i),
        .O(m_axi_awvalid));
  LUT6 #(
    .INIT(64'h00DF0000000000DF)) 
    ram_empty_i_i_5
       (.I0(curr_fwft_state[1]),
        .I1(m_axi_awready),
        .I2(curr_fwft_state[0]),
        .I3(ram_empty_fb_i_reg),
        .I4(\gnxpm_cdc.wr_pntr_bin_reg[3] ),
        .I5(Q),
        .O(ram_empty_i_reg));
endmodule

(* ORIG_REF_NAME = "rd_fwft" *) 
module axi_clock_converter_dramslim_rd_fwft_65
   (ram_empty_i_reg,
    E,
    \goreg_dm.dout_i_reg[82] ,
    s_axi_rvalid,
    s_aclk,
    out,
    s_axi_rready,
    ram_empty_fb_i_reg,
    \gnxpm_cdc.wr_pntr_bin_reg[3] ,
    Q);
  output ram_empty_i_reg;
  output [0:0]E;
  output [0:0]\goreg_dm.dout_i_reg[82] ;
  output s_axi_rvalid;
  input s_aclk;
  input [1:0]out;
  input s_axi_rready;
  input ram_empty_fb_i_reg;
  input [0:0]\gnxpm_cdc.wr_pntr_bin_reg[3] ;
  input [0:0]Q;

  wire [0:0]E;
  wire [0:0]Q;
  (* DONT_TOUCH *) wire aempty_fwft_fb_i;
  (* DONT_TOUCH *) wire aempty_fwft_i;
  wire aempty_fwft_i0;
  (* DONT_TOUCH *) wire [1:0]curr_fwft_state;
  (* DONT_TOUCH *) wire empty_fwft_fb_i;
  (* DONT_TOUCH *) wire empty_fwft_fb_o_i;
  wire empty_fwft_fb_o_i0;
  (* DONT_TOUCH *) wire empty_fwft_i;
  wire empty_fwft_i0;
  wire [0:0]\gnxpm_cdc.wr_pntr_bin_reg[3] ;
  wire [0:0]\goreg_dm.dout_i_reg[82] ;
  wire [1:0]next_fwft_state;
  wire [1:0]out;
  wire ram_empty_fb_i_reg;
  wire ram_empty_i_reg;
  wire s_aclk;
  wire s_axi_rready;
  wire s_axi_rvalid;
  (* DONT_TOUCH *) wire user_valid;

  LUT5 #(
    .INIT(32'hFAEF8000)) 
    aempty_fwft_fb_i_i_1__3
       (.I0(ram_empty_fb_i_reg),
        .I1(s_axi_rready),
        .I2(curr_fwft_state[0]),
        .I3(curr_fwft_state[1]),
        .I4(aempty_fwft_fb_i),
        .O(aempty_fwft_i0));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    aempty_fwft_fb_i_reg
       (.C(s_aclk),
        .CE(1'b1),
        .D(aempty_fwft_i0),
        .PRE(out[1]),
        .Q(aempty_fwft_fb_i));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    aempty_fwft_i_reg
       (.C(s_aclk),
        .CE(1'b1),
        .D(aempty_fwft_i0),
        .PRE(out[1]),
        .Q(aempty_fwft_i));
  LUT4 #(
    .INIT(16'hB2A2)) 
    empty_fwft_fb_i_i_1__3
       (.I0(empty_fwft_fb_i),
        .I1(curr_fwft_state[1]),
        .I2(curr_fwft_state[0]),
        .I3(s_axi_rready),
        .O(empty_fwft_i0));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    empty_fwft_fb_i_reg
       (.C(s_aclk),
        .CE(1'b1),
        .D(empty_fwft_i0),
        .PRE(out[1]),
        .Q(empty_fwft_fb_i));
  LUT4 #(
    .INIT(16'hB2A2)) 
    empty_fwft_fb_o_i_i_1__3
       (.I0(empty_fwft_fb_o_i),
        .I1(curr_fwft_state[1]),
        .I2(curr_fwft_state[0]),
        .I3(s_axi_rready),
        .O(empty_fwft_fb_o_i0));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    empty_fwft_fb_o_i_reg
       (.C(s_aclk),
        .CE(1'b1),
        .D(empty_fwft_fb_o_i0),
        .PRE(out[1]),
        .Q(empty_fwft_fb_o_i));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    empty_fwft_i_reg
       (.C(s_aclk),
        .CE(1'b1),
        .D(empty_fwft_i0),
        .PRE(out[1]),
        .Q(empty_fwft_i));
  LUT4 #(
    .INIT(16'h00DF)) 
    \gc0.count_d1[3]_i_1__3 
       (.I0(curr_fwft_state[1]),
        .I1(s_axi_rready),
        .I2(curr_fwft_state[0]),
        .I3(ram_empty_fb_i_reg),
        .O(E));
  LUT4 #(
    .INIT(16'h4404)) 
    \goreg_dm.dout_i[82]_i_1 
       (.I0(out[0]),
        .I1(curr_fwft_state[1]),
        .I2(curr_fwft_state[0]),
        .I3(s_axi_rready),
        .O(\goreg_dm.dout_i_reg[82] ));
  LUT3 #(
    .INIT(8'hAE)) 
    \gpregsm1.curr_fwft_state[0]_i_1__3 
       (.I0(curr_fwft_state[1]),
        .I1(curr_fwft_state[0]),
        .I2(s_axi_rready),
        .O(next_fwft_state[0]));
  LUT4 #(
    .INIT(16'h20FF)) 
    \gpregsm1.curr_fwft_state[1]_i_1__3 
       (.I0(curr_fwft_state[1]),
        .I1(s_axi_rready),
        .I2(curr_fwft_state[0]),
        .I3(ram_empty_fb_i_reg),
        .O(next_fwft_state[1]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDCE #(
    .INIT(1'b0)) 
    \gpregsm1.curr_fwft_state_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(out[1]),
        .D(next_fwft_state[0]),
        .Q(curr_fwft_state[0]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDCE #(
    .INIT(1'b0)) 
    \gpregsm1.curr_fwft_state_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(out[1]),
        .D(next_fwft_state[1]),
        .Q(curr_fwft_state[1]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDCE #(
    .INIT(1'b0)) 
    \gpregsm1.user_valid_reg 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(out[1]),
        .D(next_fwft_state[0]),
        .Q(user_valid));
  LUT6 #(
    .INIT(64'h00DF0000000000DF)) 
    ram_empty_i_i_5__3
       (.I0(curr_fwft_state[1]),
        .I1(s_axi_rready),
        .I2(curr_fwft_state[0]),
        .I3(ram_empty_fb_i_reg),
        .I4(\gnxpm_cdc.wr_pntr_bin_reg[3] ),
        .I5(Q),
        .O(ram_empty_i_reg));
  LUT1 #(
    .INIT(2'h1)) 
    s_axi_rvalid_INST_0
       (.I0(empty_fwft_i),
        .O(s_axi_rvalid));
endmodule

(* ORIG_REF_NAME = "rd_fwft" *) 
module axi_clock_converter_dramslim_rd_fwft_89
   (ram_empty_i_reg,
    E,
    \goreg_dm.dout_i_reg[108] ,
    m_axi_arvalid,
    m_aclk,
    out,
    m_axi_arready,
    ram_empty_fb_i_reg,
    \gnxpm_cdc.wr_pntr_bin_reg[3] ,
    Q);
  output ram_empty_i_reg;
  output [0:0]E;
  output [0:0]\goreg_dm.dout_i_reg[108] ;
  output m_axi_arvalid;
  input m_aclk;
  input [1:0]out;
  input m_axi_arready;
  input ram_empty_fb_i_reg;
  input [0:0]\gnxpm_cdc.wr_pntr_bin_reg[3] ;
  input [0:0]Q;

  wire [0:0]E;
  wire [0:0]Q;
  (* DONT_TOUCH *) wire aempty_fwft_fb_i;
  (* DONT_TOUCH *) wire aempty_fwft_i;
  wire aempty_fwft_i0;
  (* DONT_TOUCH *) wire [1:0]curr_fwft_state;
  (* DONT_TOUCH *) wire empty_fwft_fb_i;
  (* DONT_TOUCH *) wire empty_fwft_fb_o_i;
  wire empty_fwft_fb_o_i0;
  (* DONT_TOUCH *) wire empty_fwft_i;
  wire empty_fwft_i0;
  wire [0:0]\gnxpm_cdc.wr_pntr_bin_reg[3] ;
  wire [0:0]\goreg_dm.dout_i_reg[108] ;
  wire m_aclk;
  wire m_axi_arready;
  wire m_axi_arvalid;
  wire [1:0]next_fwft_state;
  wire [1:0]out;
  wire ram_empty_fb_i_reg;
  wire ram_empty_i_reg;
  (* DONT_TOUCH *) wire user_valid;

  LUT5 #(
    .INIT(32'hFAEF8000)) 
    aempty_fwft_fb_i_i_1__1
       (.I0(ram_empty_fb_i_reg),
        .I1(m_axi_arready),
        .I2(curr_fwft_state[0]),
        .I3(curr_fwft_state[1]),
        .I4(aempty_fwft_fb_i),
        .O(aempty_fwft_i0));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    aempty_fwft_fb_i_reg
       (.C(m_aclk),
        .CE(1'b1),
        .D(aempty_fwft_i0),
        .PRE(out[1]),
        .Q(aempty_fwft_fb_i));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    aempty_fwft_i_reg
       (.C(m_aclk),
        .CE(1'b1),
        .D(aempty_fwft_i0),
        .PRE(out[1]),
        .Q(aempty_fwft_i));
  LUT4 #(
    .INIT(16'hB2A2)) 
    empty_fwft_fb_i_i_1__1
       (.I0(empty_fwft_fb_i),
        .I1(curr_fwft_state[1]),
        .I2(curr_fwft_state[0]),
        .I3(m_axi_arready),
        .O(empty_fwft_i0));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    empty_fwft_fb_i_reg
       (.C(m_aclk),
        .CE(1'b1),
        .D(empty_fwft_i0),
        .PRE(out[1]),
        .Q(empty_fwft_fb_i));
  LUT4 #(
    .INIT(16'hB2A2)) 
    empty_fwft_fb_o_i_i_1__1
       (.I0(empty_fwft_fb_o_i),
        .I1(curr_fwft_state[1]),
        .I2(curr_fwft_state[0]),
        .I3(m_axi_arready),
        .O(empty_fwft_fb_o_i0));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    empty_fwft_fb_o_i_reg
       (.C(m_aclk),
        .CE(1'b1),
        .D(empty_fwft_fb_o_i0),
        .PRE(out[1]),
        .Q(empty_fwft_fb_o_i));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    empty_fwft_i_reg
       (.C(m_aclk),
        .CE(1'b1),
        .D(empty_fwft_i0),
        .PRE(out[1]),
        .Q(empty_fwft_i));
  LUT4 #(
    .INIT(16'h00DF)) 
    \gc0.count_d1[3]_i_1__1 
       (.I0(curr_fwft_state[1]),
        .I1(m_axi_arready),
        .I2(curr_fwft_state[0]),
        .I3(ram_empty_fb_i_reg),
        .O(E));
  LUT4 #(
    .INIT(16'h4404)) 
    \goreg_dm.dout_i[108]_i_1__0 
       (.I0(out[0]),
        .I1(curr_fwft_state[1]),
        .I2(curr_fwft_state[0]),
        .I3(m_axi_arready),
        .O(\goreg_dm.dout_i_reg[108] ));
  LUT3 #(
    .INIT(8'hAE)) 
    \gpregsm1.curr_fwft_state[0]_i_1__1 
       (.I0(curr_fwft_state[1]),
        .I1(curr_fwft_state[0]),
        .I2(m_axi_arready),
        .O(next_fwft_state[0]));
  LUT4 #(
    .INIT(16'h20FF)) 
    \gpregsm1.curr_fwft_state[1]_i_1__1 
       (.I0(curr_fwft_state[1]),
        .I1(m_axi_arready),
        .I2(curr_fwft_state[0]),
        .I3(ram_empty_fb_i_reg),
        .O(next_fwft_state[1]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDCE #(
    .INIT(1'b0)) 
    \gpregsm1.curr_fwft_state_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(out[1]),
        .D(next_fwft_state[0]),
        .Q(curr_fwft_state[0]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDCE #(
    .INIT(1'b0)) 
    \gpregsm1.curr_fwft_state_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(out[1]),
        .D(next_fwft_state[1]),
        .Q(curr_fwft_state[1]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDCE #(
    .INIT(1'b0)) 
    \gpregsm1.user_valid_reg 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(out[1]),
        .D(next_fwft_state[0]),
        .Q(user_valid));
  LUT1 #(
    .INIT(2'h1)) 
    m_axi_arvalid_INST_0
       (.I0(empty_fwft_i),
        .O(m_axi_arvalid));
  LUT6 #(
    .INIT(64'h00DF0000000000DF)) 
    ram_empty_i_i_5__1
       (.I0(curr_fwft_state[1]),
        .I1(m_axi_arready),
        .I2(curr_fwft_state[0]),
        .I3(ram_empty_fb_i_reg),
        .I4(\gnxpm_cdc.wr_pntr_bin_reg[3] ),
        .I5(Q),
        .O(ram_empty_i_reg));
endmodule

(* ORIG_REF_NAME = "rd_logic" *) 
module axi_clock_converter_dramslim_rd_logic
   (Q,
    E,
    \goreg_dm.dout_i_reg[17] ,
    D,
    \gnxpm_cdc.rd_pntr_gc_reg[3] ,
    s_axi_bvalid,
    s_aclk,
    out,
    s_axi_bready,
    \gnxpm_cdc.wr_pntr_bin_reg[2] ,
    \gnxpm_cdc.wr_pntr_bin_reg[3] );
  output [2:0]Q;
  output [0:0]E;
  output [0:0]\goreg_dm.dout_i_reg[17] ;
  output [2:0]D;
  output [3:0]\gnxpm_cdc.rd_pntr_gc_reg[3] ;
  output s_axi_bvalid;
  input s_aclk;
  input [1:0]out;
  input s_axi_bready;
  input \gnxpm_cdc.wr_pntr_bin_reg[2] ;
  input [3:0]\gnxpm_cdc.wr_pntr_bin_reg[3] ;

  wire [2:0]D;
  wire [0:0]E;
  wire [2:0]Q;
  wire [3:0]\gnxpm_cdc.rd_pntr_gc_reg[3] ;
  wire \gnxpm_cdc.wr_pntr_bin_reg[2] ;
  wire [3:0]\gnxpm_cdc.wr_pntr_bin_reg[3] ;
  wire [0:0]\goreg_dm.dout_i_reg[17] ;
  wire \gr1.gr1_int.rfwft_n_0 ;
  wire [1:0]out;
  wire p_2_out;
  wire [3:3]rd_pntr_plus1;
  wire rpntr_n_4;
  wire s_aclk;
  wire s_axi_bready;
  wire s_axi_bvalid;

  axi_clock_converter_dramslim_rd_fwft \gr1.gr1_int.rfwft 
       (.E(E),
        .Q(rd_pntr_plus1),
        .\gnxpm_cdc.wr_pntr_bin_reg[3] (\gnxpm_cdc.wr_pntr_bin_reg[3] [3]),
        .\goreg_dm.dout_i_reg[17] (\goreg_dm.dout_i_reg[17] ),
        .out(out),
        .ram_empty_fb_i_reg(p_2_out),
        .ram_empty_i_reg(\gr1.gr1_int.rfwft_n_0 ),
        .s_aclk(s_aclk),
        .s_axi_bready(s_axi_bready),
        .s_axi_bvalid(s_axi_bvalid));
  axi_clock_converter_dramslim_rd_status_flags_as \gras.rsts 
       (.\gc0.count_d1_reg[2] (rpntr_n_4),
        .\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] (out[1]),
        .out(p_2_out),
        .s_aclk(s_aclk));
  axi_clock_converter_dramslim_rd_bin_cntr rpntr
       (.D(D),
        .E(E),
        .Q({rd_pntr_plus1,Q}),
        .\gnxpm_cdc.rd_pntr_gc_reg[3] (\gnxpm_cdc.rd_pntr_gc_reg[3] ),
        .\gnxpm_cdc.wr_pntr_bin_reg[2] (\gnxpm_cdc.wr_pntr_bin_reg[2] ),
        .\gnxpm_cdc.wr_pntr_bin_reg[3] (\gnxpm_cdc.wr_pntr_bin_reg[3] ),
        .\gpregsm1.curr_fwft_state_reg[1] (\gr1.gr1_int.rfwft_n_0 ),
        .out(out[1]),
        .ram_empty_i_reg(rpntr_n_4),
        .s_aclk(s_aclk));
endmodule

(* ORIG_REF_NAME = "rd_logic" *) 
module axi_clock_converter_dramslim_rd_logic_12
   (Q,
    E,
    \goreg_dm.dout_i_reg[72] ,
    D,
    \gnxpm_cdc.rd_pntr_gc_reg[3] ,
    m_axi_wvalid,
    m_aclk,
    out,
    m_axi_wready,
    \gnxpm_cdc.wr_pntr_bin_reg[2] ,
    \gnxpm_cdc.wr_pntr_bin_reg[3] );
  output [2:0]Q;
  output [0:0]E;
  output [0:0]\goreg_dm.dout_i_reg[72] ;
  output [2:0]D;
  output [3:0]\gnxpm_cdc.rd_pntr_gc_reg[3] ;
  output m_axi_wvalid;
  input m_aclk;
  input [1:0]out;
  input m_axi_wready;
  input \gnxpm_cdc.wr_pntr_bin_reg[2] ;
  input [3:0]\gnxpm_cdc.wr_pntr_bin_reg[3] ;

  wire [2:0]D;
  wire [0:0]E;
  wire [2:0]Q;
  wire [3:0]\gnxpm_cdc.rd_pntr_gc_reg[3] ;
  wire \gnxpm_cdc.wr_pntr_bin_reg[2] ;
  wire [3:0]\gnxpm_cdc.wr_pntr_bin_reg[3] ;
  wire [0:0]\goreg_dm.dout_i_reg[72] ;
  wire \gr1.gr1_int.rfwft_n_0 ;
  wire m_aclk;
  wire m_axi_wready;
  wire m_axi_wvalid;
  wire [1:0]out;
  wire p_2_out;
  wire [3:3]rd_pntr_plus1;
  wire rpntr_n_4;

  axi_clock_converter_dramslim_rd_fwft_23 \gr1.gr1_int.rfwft 
       (.E(E),
        .Q(rd_pntr_plus1),
        .\gnxpm_cdc.wr_pntr_bin_reg[3] (\gnxpm_cdc.wr_pntr_bin_reg[3] [3]),
        .\goreg_dm.dout_i_reg[72] (\goreg_dm.dout_i_reg[72] ),
        .m_aclk(m_aclk),
        .m_axi_wready(m_axi_wready),
        .m_axi_wvalid(m_axi_wvalid),
        .out(out),
        .ram_empty_fb_i_reg(p_2_out),
        .ram_empty_i_reg(\gr1.gr1_int.rfwft_n_0 ));
  axi_clock_converter_dramslim_rd_status_flags_as_24 \gras.rsts 
       (.\gc0.count_d1_reg[2] (rpntr_n_4),
        .m_aclk(m_aclk),
        .\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] (out[1]),
        .out(p_2_out));
  axi_clock_converter_dramslim_rd_bin_cntr_25 rpntr
       (.D(D),
        .E(E),
        .Q({rd_pntr_plus1,Q}),
        .\gnxpm_cdc.rd_pntr_gc_reg[3] (\gnxpm_cdc.rd_pntr_gc_reg[3] ),
        .\gnxpm_cdc.wr_pntr_bin_reg[2] (\gnxpm_cdc.wr_pntr_bin_reg[2] ),
        .\gnxpm_cdc.wr_pntr_bin_reg[3] (\gnxpm_cdc.wr_pntr_bin_reg[3] ),
        .\gpregsm1.curr_fwft_state_reg[1] (\gr1.gr1_int.rfwft_n_0 ),
        .m_aclk(m_aclk),
        .out(out[1]),
        .ram_empty_i_reg(rpntr_n_4));
endmodule

(* ORIG_REF_NAME = "rd_logic" *) 
module axi_clock_converter_dramslim_rd_logic_33
   (Q,
    E,
    \goreg_dm.dout_i_reg[108] ,
    \gnxpm_cdc.rd_pntr_gc_reg[2] ,
    \gnxpm_cdc.rd_pntr_gc_reg[3] ,
    m_axi_awvalid,
    m_aclk,
    out,
    m_axi_awready,
    \gnxpm_cdc.wr_pntr_bin_reg[2] ,
    \gnxpm_cdc.wr_pntr_bin_reg[3] );
  output [2:0]Q;
  output [0:0]E;
  output [0:0]\goreg_dm.dout_i_reg[108] ;
  output [2:0]\gnxpm_cdc.rd_pntr_gc_reg[2] ;
  output [3:0]\gnxpm_cdc.rd_pntr_gc_reg[3] ;
  output m_axi_awvalid;
  input m_aclk;
  input [1:0]out;
  input m_axi_awready;
  input \gnxpm_cdc.wr_pntr_bin_reg[2] ;
  input [3:0]\gnxpm_cdc.wr_pntr_bin_reg[3] ;

  wire [0:0]E;
  wire [2:0]Q;
  wire [2:0]\gnxpm_cdc.rd_pntr_gc_reg[2] ;
  wire [3:0]\gnxpm_cdc.rd_pntr_gc_reg[3] ;
  wire \gnxpm_cdc.wr_pntr_bin_reg[2] ;
  wire [3:0]\gnxpm_cdc.wr_pntr_bin_reg[3] ;
  wire [0:0]\goreg_dm.dout_i_reg[108] ;
  wire \gr1.gr1_int.rfwft_n_0 ;
  wire m_aclk;
  wire m_axi_awready;
  wire m_axi_awvalid;
  wire [1:0]out;
  wire p_2_out;
  wire [3:3]rd_pntr_plus1;
  wire rpntr_n_4;

  axi_clock_converter_dramslim_rd_fwft_44 \gr1.gr1_int.rfwft 
       (.E(E),
        .Q(rd_pntr_plus1),
        .\gnxpm_cdc.wr_pntr_bin_reg[3] (\gnxpm_cdc.wr_pntr_bin_reg[3] [3]),
        .\goreg_dm.dout_i_reg[108] (\goreg_dm.dout_i_reg[108] ),
        .m_aclk(m_aclk),
        .m_axi_awready(m_axi_awready),
        .m_axi_awvalid(m_axi_awvalid),
        .out(out),
        .ram_empty_fb_i_reg(p_2_out),
        .ram_empty_i_reg(\gr1.gr1_int.rfwft_n_0 ));
  axi_clock_converter_dramslim_rd_status_flags_as_45 \gras.rsts 
       (.\gc0.count_d1_reg[2] (rpntr_n_4),
        .m_aclk(m_aclk),
        .\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] (out[1]),
        .out(p_2_out));
  axi_clock_converter_dramslim_rd_bin_cntr_46 rpntr
       (.E(E),
        .Q({rd_pntr_plus1,Q}),
        .\gnxpm_cdc.rd_pntr_gc_reg[2] (\gnxpm_cdc.rd_pntr_gc_reg[2] ),
        .\gnxpm_cdc.rd_pntr_gc_reg[3] (\gnxpm_cdc.rd_pntr_gc_reg[3] ),
        .\gnxpm_cdc.wr_pntr_bin_reg[2] (\gnxpm_cdc.wr_pntr_bin_reg[2] ),
        .\gnxpm_cdc.wr_pntr_bin_reg[3] (\gnxpm_cdc.wr_pntr_bin_reg[3] ),
        .\gpregsm1.curr_fwft_state_reg[1] (\gr1.gr1_int.rfwft_n_0 ),
        .m_aclk(m_aclk),
        .out(out[1]),
        .ram_empty_i_reg(rpntr_n_4));
endmodule

(* ORIG_REF_NAME = "rd_logic" *) 
module axi_clock_converter_dramslim_rd_logic_54
   (Q,
    E,
    \goreg_dm.dout_i_reg[82] ,
    D,
    \gnxpm_cdc.rd_pntr_gc_reg[3] ,
    s_axi_rvalid,
    s_aclk,
    out,
    s_axi_rready,
    \gnxpm_cdc.wr_pntr_bin_reg[2] ,
    \gnxpm_cdc.wr_pntr_bin_reg[3] );
  output [2:0]Q;
  output [0:0]E;
  output [0:0]\goreg_dm.dout_i_reg[82] ;
  output [2:0]D;
  output [3:0]\gnxpm_cdc.rd_pntr_gc_reg[3] ;
  output s_axi_rvalid;
  input s_aclk;
  input [1:0]out;
  input s_axi_rready;
  input \gnxpm_cdc.wr_pntr_bin_reg[2] ;
  input [3:0]\gnxpm_cdc.wr_pntr_bin_reg[3] ;

  wire [2:0]D;
  wire [0:0]E;
  wire [2:0]Q;
  wire [3:0]\gnxpm_cdc.rd_pntr_gc_reg[3] ;
  wire \gnxpm_cdc.wr_pntr_bin_reg[2] ;
  wire [3:0]\gnxpm_cdc.wr_pntr_bin_reg[3] ;
  wire [0:0]\goreg_dm.dout_i_reg[82] ;
  wire \gr1.gr1_int.rfwft_n_0 ;
  wire [1:0]out;
  wire p_2_out;
  wire [3:3]rd_pntr_plus1;
  wire rpntr_n_4;
  wire s_aclk;
  wire s_axi_rready;
  wire s_axi_rvalid;

  axi_clock_converter_dramslim_rd_fwft_65 \gr1.gr1_int.rfwft 
       (.E(E),
        .Q(rd_pntr_plus1),
        .\gnxpm_cdc.wr_pntr_bin_reg[3] (\gnxpm_cdc.wr_pntr_bin_reg[3] [3]),
        .\goreg_dm.dout_i_reg[82] (\goreg_dm.dout_i_reg[82] ),
        .out(out),
        .ram_empty_fb_i_reg(p_2_out),
        .ram_empty_i_reg(\gr1.gr1_int.rfwft_n_0 ),
        .s_aclk(s_aclk),
        .s_axi_rready(s_axi_rready),
        .s_axi_rvalid(s_axi_rvalid));
  axi_clock_converter_dramslim_rd_status_flags_as_66 \gras.rsts 
       (.\gc0.count_d1_reg[2] (rpntr_n_4),
        .\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] (out[1]),
        .out(p_2_out),
        .s_aclk(s_aclk));
  axi_clock_converter_dramslim_rd_bin_cntr_67 rpntr
       (.D(D),
        .E(E),
        .Q({rd_pntr_plus1,Q}),
        .\gnxpm_cdc.rd_pntr_gc_reg[3] (\gnxpm_cdc.rd_pntr_gc_reg[3] ),
        .\gnxpm_cdc.wr_pntr_bin_reg[2] (\gnxpm_cdc.wr_pntr_bin_reg[2] ),
        .\gnxpm_cdc.wr_pntr_bin_reg[3] (\gnxpm_cdc.wr_pntr_bin_reg[3] ),
        .\gpregsm1.curr_fwft_state_reg[1] (\gr1.gr1_int.rfwft_n_0 ),
        .out(out[1]),
        .ram_empty_i_reg(rpntr_n_4),
        .s_aclk(s_aclk));
endmodule

(* ORIG_REF_NAME = "rd_logic" *) 
module axi_clock_converter_dramslim_rd_logic_76
   (Q,
    E,
    \goreg_dm.dout_i_reg[108] ,
    D,
    \gnxpm_cdc.rd_pntr_gc_reg[3] ,
    m_axi_arvalid,
    m_aclk,
    out,
    m_axi_arready,
    \gnxpm_cdc.wr_pntr_bin_reg[2] ,
    \gnxpm_cdc.wr_pntr_bin_reg[3] );
  output [2:0]Q;
  output [0:0]E;
  output [0:0]\goreg_dm.dout_i_reg[108] ;
  output [2:0]D;
  output [3:0]\gnxpm_cdc.rd_pntr_gc_reg[3] ;
  output m_axi_arvalid;
  input m_aclk;
  input [1:0]out;
  input m_axi_arready;
  input \gnxpm_cdc.wr_pntr_bin_reg[2] ;
  input [3:0]\gnxpm_cdc.wr_pntr_bin_reg[3] ;

  wire [2:0]D;
  wire [0:0]E;
  wire [2:0]Q;
  wire [3:0]\gnxpm_cdc.rd_pntr_gc_reg[3] ;
  wire \gnxpm_cdc.wr_pntr_bin_reg[2] ;
  wire [3:0]\gnxpm_cdc.wr_pntr_bin_reg[3] ;
  wire [0:0]\goreg_dm.dout_i_reg[108] ;
  wire \gr1.gr1_int.rfwft_n_0 ;
  wire m_aclk;
  wire m_axi_arready;
  wire m_axi_arvalid;
  wire [1:0]out;
  wire p_2_out;
  wire [3:3]rd_pntr_plus1;
  wire rpntr_n_4;

  axi_clock_converter_dramslim_rd_fwft_89 \gr1.gr1_int.rfwft 
       (.E(E),
        .Q(rd_pntr_plus1),
        .\gnxpm_cdc.wr_pntr_bin_reg[3] (\gnxpm_cdc.wr_pntr_bin_reg[3] [3]),
        .\goreg_dm.dout_i_reg[108] (\goreg_dm.dout_i_reg[108] ),
        .m_aclk(m_aclk),
        .m_axi_arready(m_axi_arready),
        .m_axi_arvalid(m_axi_arvalid),
        .out(out),
        .ram_empty_fb_i_reg(p_2_out),
        .ram_empty_i_reg(\gr1.gr1_int.rfwft_n_0 ));
  axi_clock_converter_dramslim_rd_status_flags_as_90 \gras.rsts 
       (.\gc0.count_d1_reg[2] (rpntr_n_4),
        .m_aclk(m_aclk),
        .\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] (out[1]),
        .out(p_2_out));
  axi_clock_converter_dramslim_rd_bin_cntr_91 rpntr
       (.D(D),
        .E(E),
        .Q({rd_pntr_plus1,Q}),
        .\gnxpm_cdc.rd_pntr_gc_reg[3] (\gnxpm_cdc.rd_pntr_gc_reg[3] ),
        .\gnxpm_cdc.wr_pntr_bin_reg[2] (\gnxpm_cdc.wr_pntr_bin_reg[2] ),
        .\gnxpm_cdc.wr_pntr_bin_reg[3] (\gnxpm_cdc.wr_pntr_bin_reg[3] ),
        .\gpregsm1.curr_fwft_state_reg[1] (\gr1.gr1_int.rfwft_n_0 ),
        .m_aclk(m_aclk),
        .out(out[1]),
        .ram_empty_i_reg(rpntr_n_4));
endmodule

(* ORIG_REF_NAME = "rd_status_flags_as" *) 
module axi_clock_converter_dramslim_rd_status_flags_as
   (out,
    \gc0.count_d1_reg[2] ,
    s_aclk,
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] );
  output out;
  input \gc0.count_d1_reg[2] ;
  input s_aclk;
  input [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] ;

  wire \gc0.count_d1_reg[2] ;
  wire [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] ;
  (* DONT_TOUCH *) wire ram_empty_fb_i;
  (* DONT_TOUCH *) wire ram_empty_i;
  wire s_aclk;

  assign out = ram_empty_fb_i;
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    ram_empty_fb_i_reg
       (.C(s_aclk),
        .CE(1'b1),
        .D(\gc0.count_d1_reg[2] ),
        .PRE(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] ),
        .Q(ram_empty_fb_i));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    ram_empty_i_reg
       (.C(s_aclk),
        .CE(1'b1),
        .D(\gc0.count_d1_reg[2] ),
        .PRE(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] ),
        .Q(ram_empty_i));
endmodule

(* ORIG_REF_NAME = "rd_status_flags_as" *) 
module axi_clock_converter_dramslim_rd_status_flags_as_24
   (out,
    \gc0.count_d1_reg[2] ,
    m_aclk,
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] );
  output out;
  input \gc0.count_d1_reg[2] ;
  input m_aclk;
  input [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] ;

  wire \gc0.count_d1_reg[2] ;
  wire m_aclk;
  wire [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] ;
  (* DONT_TOUCH *) wire ram_empty_fb_i;
  (* DONT_TOUCH *) wire ram_empty_i;

  assign out = ram_empty_fb_i;
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    ram_empty_fb_i_reg
       (.C(m_aclk),
        .CE(1'b1),
        .D(\gc0.count_d1_reg[2] ),
        .PRE(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] ),
        .Q(ram_empty_fb_i));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    ram_empty_i_reg
       (.C(m_aclk),
        .CE(1'b1),
        .D(\gc0.count_d1_reg[2] ),
        .PRE(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] ),
        .Q(ram_empty_i));
endmodule

(* ORIG_REF_NAME = "rd_status_flags_as" *) 
module axi_clock_converter_dramslim_rd_status_flags_as_45
   (out,
    \gc0.count_d1_reg[2] ,
    m_aclk,
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] );
  output out;
  input \gc0.count_d1_reg[2] ;
  input m_aclk;
  input [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] ;

  wire \gc0.count_d1_reg[2] ;
  wire m_aclk;
  wire [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] ;
  (* DONT_TOUCH *) wire ram_empty_fb_i;
  (* DONT_TOUCH *) wire ram_empty_i;

  assign out = ram_empty_fb_i;
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    ram_empty_fb_i_reg
       (.C(m_aclk),
        .CE(1'b1),
        .D(\gc0.count_d1_reg[2] ),
        .PRE(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] ),
        .Q(ram_empty_fb_i));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    ram_empty_i_reg
       (.C(m_aclk),
        .CE(1'b1),
        .D(\gc0.count_d1_reg[2] ),
        .PRE(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] ),
        .Q(ram_empty_i));
endmodule

(* ORIG_REF_NAME = "rd_status_flags_as" *) 
module axi_clock_converter_dramslim_rd_status_flags_as_66
   (out,
    \gc0.count_d1_reg[2] ,
    s_aclk,
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] );
  output out;
  input \gc0.count_d1_reg[2] ;
  input s_aclk;
  input [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] ;

  wire \gc0.count_d1_reg[2] ;
  wire [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] ;
  (* DONT_TOUCH *) wire ram_empty_fb_i;
  (* DONT_TOUCH *) wire ram_empty_i;
  wire s_aclk;

  assign out = ram_empty_fb_i;
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    ram_empty_fb_i_reg
       (.C(s_aclk),
        .CE(1'b1),
        .D(\gc0.count_d1_reg[2] ),
        .PRE(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] ),
        .Q(ram_empty_fb_i));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    ram_empty_i_reg
       (.C(s_aclk),
        .CE(1'b1),
        .D(\gc0.count_d1_reg[2] ),
        .PRE(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] ),
        .Q(ram_empty_i));
endmodule

(* ORIG_REF_NAME = "rd_status_flags_as" *) 
module axi_clock_converter_dramslim_rd_status_flags_as_90
   (out,
    \gc0.count_d1_reg[2] ,
    m_aclk,
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] );
  output out;
  input \gc0.count_d1_reg[2] ;
  input m_aclk;
  input [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] ;

  wire \gc0.count_d1_reg[2] ;
  wire m_aclk;
  wire [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] ;
  (* DONT_TOUCH *) wire ram_empty_fb_i;
  (* DONT_TOUCH *) wire ram_empty_i;

  assign out = ram_empty_fb_i;
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    ram_empty_fb_i_reg
       (.C(m_aclk),
        .CE(1'b1),
        .D(\gc0.count_d1_reg[2] ),
        .PRE(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] ),
        .Q(ram_empty_fb_i));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    ram_empty_i_reg
       (.C(m_aclk),
        .CE(1'b1),
        .D(\gc0.count_d1_reg[2] ),
        .PRE(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] ),
        .Q(ram_empty_i));
endmodule

(* ORIG_REF_NAME = "reset_blk_ramfifo" *) 
module axi_clock_converter_dramslim_reset_blk_ramfifo
   (out,
    \gc0.count_reg[1] ,
    \grstd1.grst_full.grst_f.rst_d3_reg_0 ,
    ram_full_fb_i_reg,
    s_aclk,
    m_aclk,
    inverted_reset);
  output [1:0]out;
  output [2:0]\gc0.count_reg[1] ;
  output \grstd1.grst_full.grst_f.rst_d3_reg_0 ;
  output ram_full_fb_i_reg;
  input s_aclk;
  input m_aclk;
  input inverted_reset;

  wire inverted_reset;
  wire m_aclk;
  wire \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst_n_1 ;
  wire \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst_n_1 ;
  wire p_5_out;
  wire p_6_out;
  wire p_7_out;
  wire p_8_out;
  wire rd_rst_asreg;
  (* DONT_TOUCH *) wire [2:0]rd_rst_reg;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_d1;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_d2;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_d3;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_rd_reg1;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_rd_reg2;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_wr_reg1;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_wr_reg2;
  wire s_aclk;
  wire wr_rst_asreg;
  (* DONT_TOUCH *) wire [2:0]wr_rst_reg;

  assign \gc0.count_reg[1] [2:0] = rd_rst_reg;
  assign \grstd1.grst_full.grst_f.rst_d3_reg_0  = rst_d2;
  assign out[1:0] = wr_rst_reg[1:0];
  assign ram_full_fb_i_reg = rst_d3;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b1)) 
    \grstd1.grst_full.grst_f.rst_d1_reg 
       (.C(m_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(rst_wr_reg2),
        .Q(rst_d1));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b1)) 
    \grstd1.grst_full.grst_f.rst_d2_reg 
       (.C(m_aclk),
        .CE(1'b1),
        .D(rst_d1),
        .PRE(rst_wr_reg2),
        .Q(rst_d2));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b1)) 
    \grstd1.grst_full.grst_f.rst_d3_reg 
       (.C(m_aclk),
        .CE(1'b1),
        .D(rst_d2),
        .PRE(rst_wr_reg2),
        .Q(rst_d3));
  axi_clock_converter_dramslim_synchronizer_ff \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[1].rrst_inst 
       (.in0(rd_rst_asreg),
        .out(p_5_out),
        .s_aclk(s_aclk));
  axi_clock_converter_dramslim_synchronizer_ff_1 \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[1].wrst_inst 
       (.in0(wr_rst_asreg),
        .m_aclk(m_aclk),
        .out(p_6_out));
  axi_clock_converter_dramslim_synchronizer_ff_2 \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst 
       (.AS(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst_n_1 ),
        .\Q_reg_reg[0]_0 (p_7_out),
        .in0(rd_rst_asreg),
        .out(p_5_out),
        .s_aclk(s_aclk));
  axi_clock_converter_dramslim_synchronizer_ff_3 \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst 
       (.AS(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst_n_1 ),
        .\Q_reg_reg[0]_0 (p_8_out),
        .in0(wr_rst_asreg),
        .m_aclk(m_aclk),
        .out(p_6_out));
  axi_clock_converter_dramslim_synchronizer_ff_4 \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[3].rrst_inst 
       (.\Q_reg_reg[0]_0 (p_7_out),
        .s_aclk(s_aclk));
  axi_clock_converter_dramslim_synchronizer_ff_5 \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[3].wrst_inst 
       (.\Q_reg_reg[0]_0 (p_8_out),
        .m_aclk(m_aclk));
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.rd_rst_asreg_reg 
       (.C(s_aclk),
        .CE(1'b1),
        .D(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst_n_1 ),
        .PRE(rst_rd_reg2),
        .Q(rd_rst_asreg));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst_n_1 ),
        .Q(rd_rst_reg[0]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst_n_1 ),
        .Q(rd_rst_reg[1]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] 
       (.C(s_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst_n_1 ),
        .Q(rd_rst_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b0)) 
    \ngwrdrst.grst.g7serrst.rst_rd_reg1_reg 
       (.C(s_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(inverted_reset),
        .Q(rst_rd_reg1));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b0)) 
    \ngwrdrst.grst.g7serrst.rst_rd_reg2_reg 
       (.C(s_aclk),
        .CE(1'b1),
        .D(rst_rd_reg1),
        .PRE(inverted_reset),
        .Q(rst_rd_reg2));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b0)) 
    \ngwrdrst.grst.g7serrst.rst_wr_reg1_reg 
       (.C(m_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(inverted_reset),
        .Q(rst_wr_reg1));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b0)) 
    \ngwrdrst.grst.g7serrst.rst_wr_reg2_reg 
       (.C(m_aclk),
        .CE(1'b1),
        .D(rst_wr_reg1),
        .PRE(inverted_reset),
        .Q(rst_wr_reg2));
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.wr_rst_asreg_reg 
       (.C(m_aclk),
        .CE(1'b1),
        .D(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst_n_1 ),
        .PRE(rst_wr_reg2),
        .Q(wr_rst_asreg));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.wr_rst_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst_n_1 ),
        .Q(wr_rst_reg[0]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.wr_rst_reg_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst_n_1 ),
        .Q(wr_rst_reg[1]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.wr_rst_reg_reg[2] 
       (.C(m_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst_n_1 ),
        .Q(wr_rst_reg[2]));
endmodule

(* ORIG_REF_NAME = "reset_blk_ramfifo" *) 
module axi_clock_converter_dramslim_reset_blk_ramfifo_14
   (out,
    \gc0.count_reg[1] ,
    \grstd1.grst_full.grst_f.rst_d3_reg_0 ,
    ram_full_fb_i_reg,
    m_aclk,
    s_aclk,
    inverted_reset);
  output [1:0]out;
  output [2:0]\gc0.count_reg[1] ;
  output \grstd1.grst_full.grst_f.rst_d3_reg_0 ;
  output ram_full_fb_i_reg;
  input m_aclk;
  input s_aclk;
  input inverted_reset;

  wire inverted_reset;
  wire m_aclk;
  wire \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst_n_1 ;
  wire \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst_n_1 ;
  wire p_5_out;
  wire p_6_out;
  wire p_7_out;
  wire p_8_out;
  wire rd_rst_asreg;
  (* DONT_TOUCH *) wire [2:0]rd_rst_reg;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_d1;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_d2;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_d3;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_rd_reg1;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_rd_reg2;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_wr_reg1;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_wr_reg2;
  wire s_aclk;
  wire wr_rst_asreg;
  (* DONT_TOUCH *) wire [2:0]wr_rst_reg;

  assign \gc0.count_reg[1] [2:0] = rd_rst_reg;
  assign \grstd1.grst_full.grst_f.rst_d3_reg_0  = rst_d2;
  assign out[1:0] = wr_rst_reg[1:0];
  assign ram_full_fb_i_reg = rst_d3;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b1)) 
    \grstd1.grst_full.grst_f.rst_d1_reg 
       (.C(s_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(rst_wr_reg2),
        .Q(rst_d1));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b1)) 
    \grstd1.grst_full.grst_f.rst_d2_reg 
       (.C(s_aclk),
        .CE(1'b1),
        .D(rst_d1),
        .PRE(rst_wr_reg2),
        .Q(rst_d2));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b1)) 
    \grstd1.grst_full.grst_f.rst_d3_reg 
       (.C(s_aclk),
        .CE(1'b1),
        .D(rst_d2),
        .PRE(rst_wr_reg2),
        .Q(rst_d3));
  axi_clock_converter_dramslim_synchronizer_ff_15 \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[1].rrst_inst 
       (.in0(rd_rst_asreg),
        .m_aclk(m_aclk),
        .out(p_5_out));
  axi_clock_converter_dramslim_synchronizer_ff_16 \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[1].wrst_inst 
       (.in0(wr_rst_asreg),
        .out(p_6_out),
        .s_aclk(s_aclk));
  axi_clock_converter_dramslim_synchronizer_ff_17 \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst 
       (.AS(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst_n_1 ),
        .\Q_reg_reg[0]_0 (p_7_out),
        .in0(rd_rst_asreg),
        .m_aclk(m_aclk),
        .out(p_5_out));
  axi_clock_converter_dramslim_synchronizer_ff_18 \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst 
       (.AS(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst_n_1 ),
        .\Q_reg_reg[0]_0 (p_8_out),
        .in0(wr_rst_asreg),
        .out(p_6_out),
        .s_aclk(s_aclk));
  axi_clock_converter_dramslim_synchronizer_ff_19 \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[3].rrst_inst 
       (.\Q_reg_reg[0]_0 (p_7_out),
        .m_aclk(m_aclk));
  axi_clock_converter_dramslim_synchronizer_ff_20 \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[3].wrst_inst 
       (.\Q_reg_reg[0]_0 (p_8_out),
        .s_aclk(s_aclk));
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.rd_rst_asreg_reg 
       (.C(m_aclk),
        .CE(1'b1),
        .D(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst_n_1 ),
        .PRE(rst_rd_reg2),
        .Q(rd_rst_asreg));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst_n_1 ),
        .Q(rd_rst_reg[0]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst_n_1 ),
        .Q(rd_rst_reg[1]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] 
       (.C(m_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst_n_1 ),
        .Q(rd_rst_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b0)) 
    \ngwrdrst.grst.g7serrst.rst_rd_reg1_reg 
       (.C(m_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(inverted_reset),
        .Q(rst_rd_reg1));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b0)) 
    \ngwrdrst.grst.g7serrst.rst_rd_reg2_reg 
       (.C(m_aclk),
        .CE(1'b1),
        .D(rst_rd_reg1),
        .PRE(inverted_reset),
        .Q(rst_rd_reg2));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b0)) 
    \ngwrdrst.grst.g7serrst.rst_wr_reg1_reg 
       (.C(s_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(inverted_reset),
        .Q(rst_wr_reg1));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b0)) 
    \ngwrdrst.grst.g7serrst.rst_wr_reg2_reg 
       (.C(s_aclk),
        .CE(1'b1),
        .D(rst_wr_reg1),
        .PRE(inverted_reset),
        .Q(rst_wr_reg2));
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.wr_rst_asreg_reg 
       (.C(s_aclk),
        .CE(1'b1),
        .D(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst_n_1 ),
        .PRE(rst_wr_reg2),
        .Q(wr_rst_asreg));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.wr_rst_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst_n_1 ),
        .Q(wr_rst_reg[0]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.wr_rst_reg_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst_n_1 ),
        .Q(wr_rst_reg[1]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.wr_rst_reg_reg[2] 
       (.C(s_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst_n_1 ),
        .Q(wr_rst_reg[2]));
endmodule

(* ORIG_REF_NAME = "reset_blk_ramfifo" *) 
module axi_clock_converter_dramslim_reset_blk_ramfifo_35
   (out,
    \gc0.count_reg[1] ,
    \grstd1.grst_full.grst_f.rst_d3_reg_0 ,
    ram_full_fb_i_reg,
    m_aclk,
    s_aclk,
    inverted_reset);
  output [1:0]out;
  output [2:0]\gc0.count_reg[1] ;
  output \grstd1.grst_full.grst_f.rst_d3_reg_0 ;
  output ram_full_fb_i_reg;
  input m_aclk;
  input s_aclk;
  input inverted_reset;

  wire inverted_reset;
  wire m_aclk;
  wire \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst_n_1 ;
  wire \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst_n_1 ;
  wire p_5_out;
  wire p_6_out;
  wire p_7_out;
  wire p_8_out;
  wire rd_rst_asreg;
  (* DONT_TOUCH *) wire [2:0]rd_rst_reg;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_d1;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_d2;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_d3;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_rd_reg1;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_rd_reg2;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_wr_reg1;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_wr_reg2;
  wire s_aclk;
  wire wr_rst_asreg;
  (* DONT_TOUCH *) wire [2:0]wr_rst_reg;

  assign \gc0.count_reg[1] [2:0] = rd_rst_reg;
  assign \grstd1.grst_full.grst_f.rst_d3_reg_0  = rst_d2;
  assign out[1:0] = wr_rst_reg[1:0];
  assign ram_full_fb_i_reg = rst_d3;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b1)) 
    \grstd1.grst_full.grst_f.rst_d1_reg 
       (.C(s_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(rst_wr_reg2),
        .Q(rst_d1));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b1)) 
    \grstd1.grst_full.grst_f.rst_d2_reg 
       (.C(s_aclk),
        .CE(1'b1),
        .D(rst_d1),
        .PRE(rst_wr_reg2),
        .Q(rst_d2));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b1)) 
    \grstd1.grst_full.grst_f.rst_d3_reg 
       (.C(s_aclk),
        .CE(1'b1),
        .D(rst_d2),
        .PRE(rst_wr_reg2),
        .Q(rst_d3));
  axi_clock_converter_dramslim_synchronizer_ff_36 \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[1].rrst_inst 
       (.in0(rd_rst_asreg),
        .m_aclk(m_aclk),
        .out(p_5_out));
  axi_clock_converter_dramslim_synchronizer_ff_37 \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[1].wrst_inst 
       (.in0(wr_rst_asreg),
        .out(p_6_out),
        .s_aclk(s_aclk));
  axi_clock_converter_dramslim_synchronizer_ff_38 \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst 
       (.AS(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst_n_1 ),
        .\Q_reg_reg[0]_0 (p_7_out),
        .in0(rd_rst_asreg),
        .m_aclk(m_aclk),
        .out(p_5_out));
  axi_clock_converter_dramslim_synchronizer_ff_39 \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst 
       (.AS(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst_n_1 ),
        .\Q_reg_reg[0]_0 (p_8_out),
        .in0(wr_rst_asreg),
        .out(p_6_out),
        .s_aclk(s_aclk));
  axi_clock_converter_dramslim_synchronizer_ff_40 \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[3].rrst_inst 
       (.\Q_reg_reg[0]_0 (p_7_out),
        .m_aclk(m_aclk));
  axi_clock_converter_dramslim_synchronizer_ff_41 \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[3].wrst_inst 
       (.\Q_reg_reg[0]_0 (p_8_out),
        .s_aclk(s_aclk));
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.rd_rst_asreg_reg 
       (.C(m_aclk),
        .CE(1'b1),
        .D(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst_n_1 ),
        .PRE(rst_rd_reg2),
        .Q(rd_rst_asreg));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst_n_1 ),
        .Q(rd_rst_reg[0]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst_n_1 ),
        .Q(rd_rst_reg[1]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] 
       (.C(m_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst_n_1 ),
        .Q(rd_rst_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b0)) 
    \ngwrdrst.grst.g7serrst.rst_rd_reg1_reg 
       (.C(m_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(inverted_reset),
        .Q(rst_rd_reg1));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b0)) 
    \ngwrdrst.grst.g7serrst.rst_rd_reg2_reg 
       (.C(m_aclk),
        .CE(1'b1),
        .D(rst_rd_reg1),
        .PRE(inverted_reset),
        .Q(rst_rd_reg2));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b0)) 
    \ngwrdrst.grst.g7serrst.rst_wr_reg1_reg 
       (.C(s_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(inverted_reset),
        .Q(rst_wr_reg1));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b0)) 
    \ngwrdrst.grst.g7serrst.rst_wr_reg2_reg 
       (.C(s_aclk),
        .CE(1'b1),
        .D(rst_wr_reg1),
        .PRE(inverted_reset),
        .Q(rst_wr_reg2));
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.wr_rst_asreg_reg 
       (.C(s_aclk),
        .CE(1'b1),
        .D(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst_n_1 ),
        .PRE(rst_wr_reg2),
        .Q(wr_rst_asreg));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.wr_rst_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst_n_1 ),
        .Q(wr_rst_reg[0]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.wr_rst_reg_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst_n_1 ),
        .Q(wr_rst_reg[1]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.wr_rst_reg_reg[2] 
       (.C(s_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst_n_1 ),
        .Q(wr_rst_reg[2]));
endmodule

(* ORIG_REF_NAME = "reset_blk_ramfifo" *) 
module axi_clock_converter_dramslim_reset_blk_ramfifo_56
   (out,
    \gc0.count_reg[1] ,
    \grstd1.grst_full.grst_f.rst_d3_reg_0 ,
    ram_full_fb_i_reg,
    \ngwrdrst.grst.g7serrst.rst_wr_reg1_reg_0 ,
    s_aclk,
    m_aclk,
    s_aresetn);
  output [1:0]out;
  output [2:0]\gc0.count_reg[1] ;
  output \grstd1.grst_full.grst_f.rst_d3_reg_0 ;
  output ram_full_fb_i_reg;
  output \ngwrdrst.grst.g7serrst.rst_wr_reg1_reg_0 ;
  input s_aclk;
  input m_aclk;
  input s_aresetn;

  wire m_aclk;
  wire \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst_n_1 ;
  wire \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst_n_1 ;
  wire \ngwrdrst.grst.g7serrst.rst_wr_reg1_reg_0 ;
  wire p_5_out;
  wire p_6_out;
  wire p_7_out;
  wire p_8_out;
  wire rd_rst_asreg;
  (* DONT_TOUCH *) wire [2:0]rd_rst_reg;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_d1;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_d2;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_d3;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_rd_reg1;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_rd_reg2;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_wr_reg1;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_wr_reg2;
  wire s_aclk;
  wire s_aresetn;
  wire wr_rst_asreg;
  (* DONT_TOUCH *) wire [2:0]wr_rst_reg;

  assign \gc0.count_reg[1] [2:0] = rd_rst_reg;
  assign \grstd1.grst_full.grst_f.rst_d3_reg_0  = rst_d2;
  assign out[1:0] = wr_rst_reg[1:0];
  assign ram_full_fb_i_reg = rst_d3;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b1)) 
    \grstd1.grst_full.grst_f.rst_d1_reg 
       (.C(m_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(rst_wr_reg2),
        .Q(rst_d1));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b1)) 
    \grstd1.grst_full.grst_f.rst_d2_reg 
       (.C(m_aclk),
        .CE(1'b1),
        .D(rst_d1),
        .PRE(rst_wr_reg2),
        .Q(rst_d2));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b1)) 
    \grstd1.grst_full.grst_f.rst_d3_reg 
       (.C(m_aclk),
        .CE(1'b1),
        .D(rst_d2),
        .PRE(rst_wr_reg2),
        .Q(rst_d3));
  axi_clock_converter_dramslim_synchronizer_ff_57 \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[1].rrst_inst 
       (.in0(rd_rst_asreg),
        .out(p_5_out),
        .s_aclk(s_aclk));
  axi_clock_converter_dramslim_synchronizer_ff_58 \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[1].wrst_inst 
       (.in0(wr_rst_asreg),
        .m_aclk(m_aclk),
        .out(p_6_out));
  axi_clock_converter_dramslim_synchronizer_ff_59 \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst 
       (.AS(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst_n_1 ),
        .\Q_reg_reg[0]_0 (p_7_out),
        .in0(rd_rst_asreg),
        .out(p_5_out),
        .s_aclk(s_aclk));
  axi_clock_converter_dramslim_synchronizer_ff_60 \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst 
       (.AS(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst_n_1 ),
        .\Q_reg_reg[0]_0 (p_8_out),
        .in0(wr_rst_asreg),
        .m_aclk(m_aclk),
        .out(p_6_out));
  axi_clock_converter_dramslim_synchronizer_ff_61 \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[3].rrst_inst 
       (.\Q_reg_reg[0]_0 (p_7_out),
        .s_aclk(s_aclk));
  axi_clock_converter_dramslim_synchronizer_ff_62 \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[3].wrst_inst 
       (.\Q_reg_reg[0]_0 (p_8_out),
        .m_aclk(m_aclk));
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.rd_rst_asreg_reg 
       (.C(s_aclk),
        .CE(1'b1),
        .D(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst_n_1 ),
        .PRE(rst_rd_reg2),
        .Q(rd_rst_asreg));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst_n_1 ),
        .Q(rd_rst_reg[0]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst_n_1 ),
        .Q(rd_rst_reg[1]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] 
       (.C(s_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst_n_1 ),
        .Q(rd_rst_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b0)) 
    \ngwrdrst.grst.g7serrst.rst_rd_reg1_reg 
       (.C(s_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.rst_wr_reg1_reg_0 ),
        .Q(rst_rd_reg1));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b0)) 
    \ngwrdrst.grst.g7serrst.rst_rd_reg2_reg 
       (.C(s_aclk),
        .CE(1'b1),
        .D(rst_rd_reg1),
        .PRE(\ngwrdrst.grst.g7serrst.rst_wr_reg1_reg_0 ),
        .Q(rst_rd_reg2));
  LUT1 #(
    .INIT(2'h1)) 
    \ngwrdrst.grst.g7serrst.rst_wr_reg1_i_1 
       (.I0(s_aresetn),
        .O(\ngwrdrst.grst.g7serrst.rst_wr_reg1_reg_0 ));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b0)) 
    \ngwrdrst.grst.g7serrst.rst_wr_reg1_reg 
       (.C(m_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.rst_wr_reg1_reg_0 ),
        .Q(rst_wr_reg1));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b0)) 
    \ngwrdrst.grst.g7serrst.rst_wr_reg2_reg 
       (.C(m_aclk),
        .CE(1'b1),
        .D(rst_wr_reg1),
        .PRE(\ngwrdrst.grst.g7serrst.rst_wr_reg1_reg_0 ),
        .Q(rst_wr_reg2));
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.wr_rst_asreg_reg 
       (.C(m_aclk),
        .CE(1'b1),
        .D(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst_n_1 ),
        .PRE(rst_wr_reg2),
        .Q(wr_rst_asreg));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.wr_rst_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst_n_1 ),
        .Q(wr_rst_reg[0]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.wr_rst_reg_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst_n_1 ),
        .Q(wr_rst_reg[1]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.wr_rst_reg_reg[2] 
       (.C(m_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst_n_1 ),
        .Q(wr_rst_reg[2]));
endmodule

(* ORIG_REF_NAME = "reset_blk_ramfifo" *) 
module axi_clock_converter_dramslim_reset_blk_ramfifo_79
   (out,
    \gc0.count_reg[1] ,
    \grstd1.grst_full.grst_f.rst_d3_reg_0 ,
    ram_full_fb_i_reg,
    m_aclk,
    s_aclk,
    inverted_reset);
  output [1:0]out;
  output [2:0]\gc0.count_reg[1] ;
  output \grstd1.grst_full.grst_f.rst_d3_reg_0 ;
  output ram_full_fb_i_reg;
  input m_aclk;
  input s_aclk;
  input inverted_reset;

  wire inverted_reset;
  wire m_aclk;
  wire \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst_n_1 ;
  wire \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst_n_1 ;
  wire p_5_out;
  wire p_6_out;
  wire p_7_out;
  wire p_8_out;
  wire rd_rst_asreg;
  (* DONT_TOUCH *) wire [2:0]rd_rst_reg;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_d1;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_d2;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_d3;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_rd_reg1;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_rd_reg2;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_wr_reg1;
  (* async_reg = "true" *) (* msgon = "true" *) wire rst_wr_reg2;
  wire s_aclk;
  wire wr_rst_asreg;
  (* DONT_TOUCH *) wire [2:0]wr_rst_reg;

  assign \gc0.count_reg[1] [2:0] = rd_rst_reg;
  assign \grstd1.grst_full.grst_f.rst_d3_reg_0  = rst_d2;
  assign out[1:0] = wr_rst_reg[1:0];
  assign ram_full_fb_i_reg = rst_d3;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b1)) 
    \grstd1.grst_full.grst_f.rst_d1_reg 
       (.C(s_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(rst_wr_reg2),
        .Q(rst_d1));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b1)) 
    \grstd1.grst_full.grst_f.rst_d2_reg 
       (.C(s_aclk),
        .CE(1'b1),
        .D(rst_d1),
        .PRE(rst_wr_reg2),
        .Q(rst_d2));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b1)) 
    \grstd1.grst_full.grst_f.rst_d3_reg 
       (.C(s_aclk),
        .CE(1'b1),
        .D(rst_d2),
        .PRE(rst_wr_reg2),
        .Q(rst_d3));
  axi_clock_converter_dramslim_synchronizer_ff_80 \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[1].rrst_inst 
       (.in0(rd_rst_asreg),
        .m_aclk(m_aclk),
        .out(p_5_out));
  axi_clock_converter_dramslim_synchronizer_ff_81 \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[1].wrst_inst 
       (.in0(wr_rst_asreg),
        .out(p_6_out),
        .s_aclk(s_aclk));
  axi_clock_converter_dramslim_synchronizer_ff_82 \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst 
       (.AS(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst_n_1 ),
        .\Q_reg_reg[0]_0 (p_7_out),
        .in0(rd_rst_asreg),
        .m_aclk(m_aclk),
        .out(p_5_out));
  axi_clock_converter_dramslim_synchronizer_ff_83 \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst 
       (.AS(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst_n_1 ),
        .\Q_reg_reg[0]_0 (p_8_out),
        .in0(wr_rst_asreg),
        .out(p_6_out),
        .s_aclk(s_aclk));
  axi_clock_converter_dramslim_synchronizer_ff_84 \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[3].rrst_inst 
       (.\Q_reg_reg[0]_0 (p_7_out),
        .m_aclk(m_aclk));
  axi_clock_converter_dramslim_synchronizer_ff_85 \ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[3].wrst_inst 
       (.\Q_reg_reg[0]_0 (p_8_out),
        .s_aclk(s_aclk));
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.rd_rst_asreg_reg 
       (.C(m_aclk),
        .CE(1'b1),
        .D(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst_n_1 ),
        .PRE(rst_rd_reg2),
        .Q(rd_rst_asreg));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst_n_1 ),
        .Q(rd_rst_reg[0]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst_n_1 ),
        .Q(rd_rst_reg[1]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[2] 
       (.C(m_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].rrst_inst_n_1 ),
        .Q(rd_rst_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b0)) 
    \ngwrdrst.grst.g7serrst.rst_rd_reg1_reg 
       (.C(m_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(inverted_reset),
        .Q(rst_rd_reg1));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b0)) 
    \ngwrdrst.grst.g7serrst.rst_rd_reg2_reg 
       (.C(m_aclk),
        .CE(1'b1),
        .D(rst_rd_reg1),
        .PRE(inverted_reset),
        .Q(rst_rd_reg2));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b0)) 
    \ngwrdrst.grst.g7serrst.rst_wr_reg1_reg 
       (.C(s_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(inverted_reset),
        .Q(rst_wr_reg1));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDPE #(
    .INIT(1'b0)) 
    \ngwrdrst.grst.g7serrst.rst_wr_reg2_reg 
       (.C(s_aclk),
        .CE(1'b1),
        .D(rst_wr_reg1),
        .PRE(inverted_reset),
        .Q(rst_wr_reg2));
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.wr_rst_asreg_reg 
       (.C(s_aclk),
        .CE(1'b1),
        .D(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst_n_1 ),
        .PRE(rst_wr_reg2),
        .Q(wr_rst_asreg));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.wr_rst_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst_n_1 ),
        .Q(wr_rst_reg[0]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.wr_rst_reg_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst_n_1 ),
        .Q(wr_rst_reg[1]));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    \ngwrdrst.grst.g7serrst.wr_rst_reg_reg[2] 
       (.C(s_aclk),
        .CE(1'b1),
        .D(1'b0),
        .PRE(\ngwrdrst.grst.g7serrst.gwrrd_rst_sync_stage[2].wrst_inst_n_1 ),
        .Q(wr_rst_reg[2]));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff
   (out,
    in0,
    s_aclk);
  output out;
  input [0:0]in0;
  input s_aclk;

  (* async_reg = "true" *) (* msgon = "true" *) wire Q_reg;
  wire [0:0]in0;
  wire s_aclk;

  assign out = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDRE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .D(in0),
        .Q(Q_reg),
        .R(1'b0));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff_1
   (out,
    in0,
    m_aclk);
  output out;
  input [0:0]in0;
  input m_aclk;

  (* async_reg = "true" *) (* msgon = "true" *) wire Q_reg;
  wire [0:0]in0;
  wire m_aclk;

  assign out = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDRE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .D(in0),
        .Q(Q_reg),
        .R(1'b0));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff_15
   (out,
    in0,
    m_aclk);
  output out;
  input [0:0]in0;
  input m_aclk;

  (* async_reg = "true" *) (* msgon = "true" *) wire Q_reg;
  wire [0:0]in0;
  wire m_aclk;

  assign out = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDRE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .D(in0),
        .Q(Q_reg),
        .R(1'b0));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff_16
   (out,
    in0,
    s_aclk);
  output out;
  input [0:0]in0;
  input s_aclk;

  (* async_reg = "true" *) (* msgon = "true" *) wire Q_reg;
  wire [0:0]in0;
  wire s_aclk;

  assign out = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDRE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .D(in0),
        .Q(Q_reg),
        .R(1'b0));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff_17
   (\Q_reg_reg[0]_0 ,
    AS,
    out,
    m_aclk,
    in0);
  output \Q_reg_reg[0]_0 ;
  output [0:0]AS;
  input out;
  input m_aclk;
  input [0:0]in0;

  wire [0:0]AS;
  (* async_reg = "true" *) (* msgon = "true" *) wire Q_reg;
  wire [0:0]in0;
  wire m_aclk;
  wire out;

  assign \Q_reg_reg[0]_0  = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDRE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .D(out),
        .Q(Q_reg),
        .R(1'b0));
  LUT2 #(
    .INIT(4'h2)) 
    \ngwrdrst.grst.g7serrst.rd_rst_reg[2]_i_1__0 
       (.I0(in0),
        .I1(Q_reg),
        .O(AS));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff_18
   (\Q_reg_reg[0]_0 ,
    AS,
    out,
    s_aclk,
    in0);
  output \Q_reg_reg[0]_0 ;
  output [0:0]AS;
  input out;
  input s_aclk;
  input [0:0]in0;

  wire [0:0]AS;
  (* async_reg = "true" *) (* msgon = "true" *) wire Q_reg;
  wire [0:0]in0;
  wire out;
  wire s_aclk;

  assign \Q_reg_reg[0]_0  = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDRE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .D(out),
        .Q(Q_reg),
        .R(1'b0));
  LUT2 #(
    .INIT(4'h2)) 
    \ngwrdrst.grst.g7serrst.wr_rst_reg[2]_i_1__0 
       (.I0(in0),
        .I1(Q_reg),
        .O(AS));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff_19
   (\Q_reg_reg[0]_0 ,
    m_aclk);
  input \Q_reg_reg[0]_0 ;
  input m_aclk;

  (* async_reg = "true" *) (* msgon = "true" *) wire Q_reg;
  wire \Q_reg_reg[0]_0 ;
  wire m_aclk;

  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDRE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .D(\Q_reg_reg[0]_0 ),
        .Q(Q_reg),
        .R(1'b0));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff_2
   (\Q_reg_reg[0]_0 ,
    AS,
    out,
    s_aclk,
    in0);
  output \Q_reg_reg[0]_0 ;
  output [0:0]AS;
  input out;
  input s_aclk;
  input [0:0]in0;

  wire [0:0]AS;
  (* async_reg = "true" *) (* msgon = "true" *) wire Q_reg;
  wire [0:0]in0;
  wire out;
  wire s_aclk;

  assign \Q_reg_reg[0]_0  = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDRE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .D(out),
        .Q(Q_reg),
        .R(1'b0));
  LUT2 #(
    .INIT(4'h2)) 
    \ngwrdrst.grst.g7serrst.rd_rst_reg[2]_i_1__1 
       (.I0(in0),
        .I1(Q_reg),
        .O(AS));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff_20
   (\Q_reg_reg[0]_0 ,
    s_aclk);
  input \Q_reg_reg[0]_0 ;
  input s_aclk;

  (* async_reg = "true" *) (* msgon = "true" *) wire Q_reg;
  wire \Q_reg_reg[0]_0 ;
  wire s_aclk;

  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDRE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .D(\Q_reg_reg[0]_0 ),
        .Q(Q_reg),
        .R(1'b0));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff_3
   (\Q_reg_reg[0]_0 ,
    AS,
    out,
    m_aclk,
    in0);
  output \Q_reg_reg[0]_0 ;
  output [0:0]AS;
  input out;
  input m_aclk;
  input [0:0]in0;

  wire [0:0]AS;
  (* async_reg = "true" *) (* msgon = "true" *) wire Q_reg;
  wire [0:0]in0;
  wire m_aclk;
  wire out;

  assign \Q_reg_reg[0]_0  = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDRE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .D(out),
        .Q(Q_reg),
        .R(1'b0));
  LUT2 #(
    .INIT(4'h2)) 
    \ngwrdrst.grst.g7serrst.wr_rst_reg[2]_i_1__1 
       (.I0(in0),
        .I1(Q_reg),
        .O(AS));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff_36
   (out,
    in0,
    m_aclk);
  output out;
  input [0:0]in0;
  input m_aclk;

  (* async_reg = "true" *) (* msgon = "true" *) wire Q_reg;
  wire [0:0]in0;
  wire m_aclk;

  assign out = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDRE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .D(in0),
        .Q(Q_reg),
        .R(1'b0));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff_37
   (out,
    in0,
    s_aclk);
  output out;
  input [0:0]in0;
  input s_aclk;

  (* async_reg = "true" *) (* msgon = "true" *) wire Q_reg;
  wire [0:0]in0;
  wire s_aclk;

  assign out = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDRE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .D(in0),
        .Q(Q_reg),
        .R(1'b0));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff_38
   (\Q_reg_reg[0]_0 ,
    AS,
    out,
    m_aclk,
    in0);
  output \Q_reg_reg[0]_0 ;
  output [0:0]AS;
  input out;
  input m_aclk;
  input [0:0]in0;

  wire [0:0]AS;
  (* async_reg = "true" *) (* msgon = "true" *) wire Q_reg;
  wire [0:0]in0;
  wire m_aclk;
  wire out;

  assign \Q_reg_reg[0]_0  = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDRE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .D(out),
        .Q(Q_reg),
        .R(1'b0));
  LUT2 #(
    .INIT(4'h2)) 
    \ngwrdrst.grst.g7serrst.rd_rst_reg[2]_i_1 
       (.I0(in0),
        .I1(Q_reg),
        .O(AS));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff_39
   (\Q_reg_reg[0]_0 ,
    AS,
    out,
    s_aclk,
    in0);
  output \Q_reg_reg[0]_0 ;
  output [0:0]AS;
  input out;
  input s_aclk;
  input [0:0]in0;

  wire [0:0]AS;
  (* async_reg = "true" *) (* msgon = "true" *) wire Q_reg;
  wire [0:0]in0;
  wire out;
  wire s_aclk;

  assign \Q_reg_reg[0]_0  = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDRE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .D(out),
        .Q(Q_reg),
        .R(1'b0));
  LUT2 #(
    .INIT(4'h2)) 
    \ngwrdrst.grst.g7serrst.wr_rst_reg[2]_i_1 
       (.I0(in0),
        .I1(Q_reg),
        .O(AS));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff_4
   (\Q_reg_reg[0]_0 ,
    s_aclk);
  input \Q_reg_reg[0]_0 ;
  input s_aclk;

  (* async_reg = "true" *) (* msgon = "true" *) wire Q_reg;
  wire \Q_reg_reg[0]_0 ;
  wire s_aclk;

  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDRE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .D(\Q_reg_reg[0]_0 ),
        .Q(Q_reg),
        .R(1'b0));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff_40
   (\Q_reg_reg[0]_0 ,
    m_aclk);
  input \Q_reg_reg[0]_0 ;
  input m_aclk;

  (* async_reg = "true" *) (* msgon = "true" *) wire Q_reg;
  wire \Q_reg_reg[0]_0 ;
  wire m_aclk;

  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDRE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .D(\Q_reg_reg[0]_0 ),
        .Q(Q_reg),
        .R(1'b0));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff_41
   (\Q_reg_reg[0]_0 ,
    s_aclk);
  input \Q_reg_reg[0]_0 ;
  input s_aclk;

  (* async_reg = "true" *) (* msgon = "true" *) wire Q_reg;
  wire \Q_reg_reg[0]_0 ;
  wire s_aclk;

  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDRE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .D(\Q_reg_reg[0]_0 ),
        .Q(Q_reg),
        .R(1'b0));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff_5
   (\Q_reg_reg[0]_0 ,
    m_aclk);
  input \Q_reg_reg[0]_0 ;
  input m_aclk;

  (* async_reg = "true" *) (* msgon = "true" *) wire Q_reg;
  wire \Q_reg_reg[0]_0 ;
  wire m_aclk;

  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDRE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .D(\Q_reg_reg[0]_0 ),
        .Q(Q_reg),
        .R(1'b0));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff_57
   (out,
    in0,
    s_aclk);
  output out;
  input [0:0]in0;
  input s_aclk;

  (* async_reg = "true" *) (* msgon = "true" *) wire Q_reg;
  wire [0:0]in0;
  wire s_aclk;

  assign out = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDRE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .D(in0),
        .Q(Q_reg),
        .R(1'b0));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff_58
   (out,
    in0,
    m_aclk);
  output out;
  input [0:0]in0;
  input m_aclk;

  (* async_reg = "true" *) (* msgon = "true" *) wire Q_reg;
  wire [0:0]in0;
  wire m_aclk;

  assign out = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDRE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .D(in0),
        .Q(Q_reg),
        .R(1'b0));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff_59
   (\Q_reg_reg[0]_0 ,
    AS,
    out,
    s_aclk,
    in0);
  output \Q_reg_reg[0]_0 ;
  output [0:0]AS;
  input out;
  input s_aclk;
  input [0:0]in0;

  wire [0:0]AS;
  (* async_reg = "true" *) (* msgon = "true" *) wire Q_reg;
  wire [0:0]in0;
  wire out;
  wire s_aclk;

  assign \Q_reg_reg[0]_0  = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDRE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .D(out),
        .Q(Q_reg),
        .R(1'b0));
  LUT2 #(
    .INIT(4'h2)) 
    \ngwrdrst.grst.g7serrst.rd_rst_reg[2]_i_1__3 
       (.I0(in0),
        .I1(Q_reg),
        .O(AS));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff_60
   (\Q_reg_reg[0]_0 ,
    AS,
    out,
    m_aclk,
    in0);
  output \Q_reg_reg[0]_0 ;
  output [0:0]AS;
  input out;
  input m_aclk;
  input [0:0]in0;

  wire [0:0]AS;
  (* async_reg = "true" *) (* msgon = "true" *) wire Q_reg;
  wire [0:0]in0;
  wire m_aclk;
  wire out;

  assign \Q_reg_reg[0]_0  = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDRE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .D(out),
        .Q(Q_reg),
        .R(1'b0));
  LUT2 #(
    .INIT(4'h2)) 
    \ngwrdrst.grst.g7serrst.wr_rst_reg[2]_i_1__3 
       (.I0(in0),
        .I1(Q_reg),
        .O(AS));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff_61
   (\Q_reg_reg[0]_0 ,
    s_aclk);
  input \Q_reg_reg[0]_0 ;
  input s_aclk;

  (* async_reg = "true" *) (* msgon = "true" *) wire Q_reg;
  wire \Q_reg_reg[0]_0 ;
  wire s_aclk;

  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDRE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .D(\Q_reg_reg[0]_0 ),
        .Q(Q_reg),
        .R(1'b0));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff_62
   (\Q_reg_reg[0]_0 ,
    m_aclk);
  input \Q_reg_reg[0]_0 ;
  input m_aclk;

  (* async_reg = "true" *) (* msgon = "true" *) wire Q_reg;
  wire \Q_reg_reg[0]_0 ;
  wire m_aclk;

  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDRE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .D(\Q_reg_reg[0]_0 ),
        .Q(Q_reg),
        .R(1'b0));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff_80
   (out,
    in0,
    m_aclk);
  output out;
  input [0:0]in0;
  input m_aclk;

  (* async_reg = "true" *) (* msgon = "true" *) wire Q_reg;
  wire [0:0]in0;
  wire m_aclk;

  assign out = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDRE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .D(in0),
        .Q(Q_reg),
        .R(1'b0));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff_81
   (out,
    in0,
    s_aclk);
  output out;
  input [0:0]in0;
  input s_aclk;

  (* async_reg = "true" *) (* msgon = "true" *) wire Q_reg;
  wire [0:0]in0;
  wire s_aclk;

  assign out = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDRE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .D(in0),
        .Q(Q_reg),
        .R(1'b0));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff_82
   (\Q_reg_reg[0]_0 ,
    AS,
    out,
    m_aclk,
    in0);
  output \Q_reg_reg[0]_0 ;
  output [0:0]AS;
  input out;
  input m_aclk;
  input [0:0]in0;

  wire [0:0]AS;
  (* async_reg = "true" *) (* msgon = "true" *) wire Q_reg;
  wire [0:0]in0;
  wire m_aclk;
  wire out;

  assign \Q_reg_reg[0]_0  = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDRE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .D(out),
        .Q(Q_reg),
        .R(1'b0));
  LUT2 #(
    .INIT(4'h2)) 
    \ngwrdrst.grst.g7serrst.rd_rst_reg[2]_i_1__2 
       (.I0(in0),
        .I1(Q_reg),
        .O(AS));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff_83
   (\Q_reg_reg[0]_0 ,
    AS,
    out,
    s_aclk,
    in0);
  output \Q_reg_reg[0]_0 ;
  output [0:0]AS;
  input out;
  input s_aclk;
  input [0:0]in0;

  wire [0:0]AS;
  (* async_reg = "true" *) (* msgon = "true" *) wire Q_reg;
  wire [0:0]in0;
  wire out;
  wire s_aclk;

  assign \Q_reg_reg[0]_0  = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDRE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .D(out),
        .Q(Q_reg),
        .R(1'b0));
  LUT2 #(
    .INIT(4'h2)) 
    \ngwrdrst.grst.g7serrst.wr_rst_reg[2]_i_1__2 
       (.I0(in0),
        .I1(Q_reg),
        .O(AS));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff_84
   (\Q_reg_reg[0]_0 ,
    m_aclk);
  input \Q_reg_reg[0]_0 ;
  input m_aclk;

  (* async_reg = "true" *) (* msgon = "true" *) wire Q_reg;
  wire \Q_reg_reg[0]_0 ;
  wire m_aclk;

  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDRE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .D(\Q_reg_reg[0]_0 ),
        .Q(Q_reg),
        .R(1'b0));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff_85
   (\Q_reg_reg[0]_0 ,
    s_aclk);
  input \Q_reg_reg[0]_0 ;
  input s_aclk;

  (* async_reg = "true" *) (* msgon = "true" *) wire Q_reg;
  wire \Q_reg_reg[0]_0 ;
  wire s_aclk;

  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDRE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .D(\Q_reg_reg[0]_0 ),
        .Q(Q_reg),
        .R(1'b0));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff__parameterized0
   (D,
    Q,
    s_aclk,
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] );
  output [3:0]D;
  input [3:0]Q;
  input s_aclk;
  input [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;

  wire [3:0]Q;
  (* async_reg = "true" *) (* msgon = "true" *) wire [3:0]Q_reg;
  wire [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;
  wire s_aclk;

  assign D[3:0] = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(Q[0]),
        .Q(Q_reg[0]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(Q[1]),
        .Q(Q_reg[1]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[2] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(Q[2]),
        .Q(Q_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[3] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(Q[3]),
        .Q(Q_reg[3]));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff__parameterized0_10
   (out,
    D,
    \Q_reg_reg[3]_0 ,
    m_aclk,
    AR);
  output [3:0]out;
  output [0:0]D;
  input [3:0]\Q_reg_reg[3]_0 ;
  input m_aclk;
  input [0:0]AR;

  wire [0:0]AR;
  wire [0:0]D;
  (* async_reg = "true" *) (* msgon = "true" *) wire [3:0]Q_reg;
  wire [3:0]\Q_reg_reg[3]_0 ;
  wire m_aclk;

  assign out[3:0] = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [0]),
        .Q(Q_reg[0]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [1]),
        .Q(Q_reg[1]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[2] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [2]),
        .Q(Q_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[3] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [3]),
        .Q(Q_reg[3]));
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.rd_pntr_bin[2]_i_1__1 
       (.I0(Q_reg[2]),
        .I1(Q_reg[3]),
        .O(D));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff__parameterized0_26
   (D,
    Q,
    m_aclk,
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] );
  output [3:0]D;
  input [3:0]Q;
  input m_aclk;
  input [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;

  wire [3:0]Q;
  (* async_reg = "true" *) (* msgon = "true" *) wire [3:0]Q_reg;
  wire m_aclk;
  wire [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;

  assign D[3:0] = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(Q[0]),
        .Q(Q_reg[0]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(Q[1]),
        .Q(Q_reg[1]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[2] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(Q[2]),
        .Q(Q_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[3] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(Q[3]),
        .Q(Q_reg[3]));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff__parameterized0_27
   (D,
    Q,
    s_aclk,
    AR);
  output [3:0]D;
  input [3:0]Q;
  input s_aclk;
  input [0:0]AR;

  wire [0:0]AR;
  wire [3:0]Q;
  (* async_reg = "true" *) (* msgon = "true" *) wire [3:0]Q_reg;
  wire s_aclk;

  assign D[3:0] = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(Q[0]),
        .Q(Q_reg[0]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(Q[1]),
        .Q(Q_reg[1]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[2] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(Q[2]),
        .Q(Q_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[3] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(Q[3]),
        .Q(Q_reg[3]));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff__parameterized0_28
   (D,
    \Q_reg_reg[3]_0 ,
    m_aclk,
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] );
  output [3:0]D;
  input [3:0]\Q_reg_reg[3]_0 ;
  input m_aclk;
  input [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;

  (* async_reg = "true" *) (* msgon = "true" *) wire [3:0]Q_reg;
  wire [3:0]\Q_reg_reg[3]_0 ;
  wire m_aclk;
  wire [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;

  assign D[3:0] = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [0]),
        .Q(Q_reg[0]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [1]),
        .Q(Q_reg[1]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[2] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [2]),
        .Q(Q_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[3] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [3]),
        .Q(Q_reg[3]));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff__parameterized0_29
   (D,
    \Q_reg_reg[3]_0 ,
    s_aclk,
    AR);
  output [3:0]D;
  input [3:0]\Q_reg_reg[3]_0 ;
  input s_aclk;
  input [0:0]AR;

  wire [0:0]AR;
  (* async_reg = "true" *) (* msgon = "true" *) wire [3:0]Q_reg;
  wire [3:0]\Q_reg_reg[3]_0 ;
  wire s_aclk;

  assign D[3:0] = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [0]),
        .Q(Q_reg[0]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [1]),
        .Q(Q_reg[1]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[2] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [2]),
        .Q(Q_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[3] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [3]),
        .Q(Q_reg[3]));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff__parameterized0_30
   (out,
    D,
    \Q_reg_reg[3]_0 ,
    m_aclk,
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] );
  output [3:0]out;
  output [0:0]D;
  input [3:0]\Q_reg_reg[3]_0 ;
  input m_aclk;
  input [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;

  wire [0:0]D;
  (* async_reg = "true" *) (* msgon = "true" *) wire [3:0]Q_reg;
  wire [3:0]\Q_reg_reg[3]_0 ;
  wire m_aclk;
  wire [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;

  assign out[3:0] = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [0]),
        .Q(Q_reg[0]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [1]),
        .Q(Q_reg[1]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[2] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [2]),
        .Q(Q_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[3] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [3]),
        .Q(Q_reg[3]));
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.wr_pntr_bin[2]_i_1__0 
       (.I0(Q_reg[2]),
        .I1(Q_reg[3]),
        .O(D));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff__parameterized0_31
   (out,
    D,
    \Q_reg_reg[3]_0 ,
    s_aclk,
    AR);
  output [3:0]out;
  output [0:0]D;
  input [3:0]\Q_reg_reg[3]_0 ;
  input s_aclk;
  input [0:0]AR;

  wire [0:0]AR;
  wire [0:0]D;
  (* async_reg = "true" *) (* msgon = "true" *) wire [3:0]Q_reg;
  wire [3:0]\Q_reg_reg[3]_0 ;
  wire s_aclk;

  assign out[3:0] = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [0]),
        .Q(Q_reg[0]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [1]),
        .Q(Q_reg[1]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[2] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [2]),
        .Q(Q_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[3] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [3]),
        .Q(Q_reg[3]));
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.rd_pntr_bin[2]_i_1__0 
       (.I0(Q_reg[2]),
        .I1(Q_reg[3]),
        .O(D));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff__parameterized0_47
   (D,
    Q,
    m_aclk,
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] );
  output [3:0]D;
  input [3:0]Q;
  input m_aclk;
  input [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;

  wire [3:0]Q;
  (* async_reg = "true" *) (* msgon = "true" *) wire [3:0]Q_reg;
  wire m_aclk;
  wire [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;

  assign D[3:0] = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(Q[0]),
        .Q(Q_reg[0]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(Q[1]),
        .Q(Q_reg[1]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[2] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(Q[2]),
        .Q(Q_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[3] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(Q[3]),
        .Q(Q_reg[3]));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff__parameterized0_48
   (D,
    Q,
    s_aclk,
    AR);
  output [3:0]D;
  input [3:0]Q;
  input s_aclk;
  input [0:0]AR;

  wire [0:0]AR;
  wire [3:0]Q;
  (* async_reg = "true" *) (* msgon = "true" *) wire [3:0]Q_reg;
  wire s_aclk;

  assign D[3:0] = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(Q[0]),
        .Q(Q_reg[0]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(Q[1]),
        .Q(Q_reg[1]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[2] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(Q[2]),
        .Q(Q_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[3] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(Q[3]),
        .Q(Q_reg[3]));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff__parameterized0_49
   (D,
    \Q_reg_reg[3]_0 ,
    m_aclk,
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] );
  output [3:0]D;
  input [3:0]\Q_reg_reg[3]_0 ;
  input m_aclk;
  input [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;

  (* async_reg = "true" *) (* msgon = "true" *) wire [3:0]Q_reg;
  wire [3:0]\Q_reg_reg[3]_0 ;
  wire m_aclk;
  wire [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;

  assign D[3:0] = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [0]),
        .Q(Q_reg[0]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [1]),
        .Q(Q_reg[1]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[2] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [2]),
        .Q(Q_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[3] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [3]),
        .Q(Q_reg[3]));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff__parameterized0_50
   (D,
    \Q_reg_reg[3]_0 ,
    s_aclk,
    AR);
  output [3:0]D;
  input [3:0]\Q_reg_reg[3]_0 ;
  input s_aclk;
  input [0:0]AR;

  wire [0:0]AR;
  (* async_reg = "true" *) (* msgon = "true" *) wire [3:0]Q_reg;
  wire [3:0]\Q_reg_reg[3]_0 ;
  wire s_aclk;

  assign D[3:0] = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [0]),
        .Q(Q_reg[0]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [1]),
        .Q(Q_reg[1]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[2] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [2]),
        .Q(Q_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[3] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [3]),
        .Q(Q_reg[3]));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff__parameterized0_51
   (out,
    D,
    \Q_reg_reg[3]_0 ,
    m_aclk,
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] );
  output [3:0]out;
  output [0:0]D;
  input [3:0]\Q_reg_reg[3]_0 ;
  input m_aclk;
  input [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;

  wire [0:0]D;
  (* async_reg = "true" *) (* msgon = "true" *) wire [3:0]Q_reg;
  wire [3:0]\Q_reg_reg[3]_0 ;
  wire m_aclk;
  wire [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;

  assign out[3:0] = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [0]),
        .Q(Q_reg[0]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [1]),
        .Q(Q_reg[1]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[2] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [2]),
        .Q(Q_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[3] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [3]),
        .Q(Q_reg[3]));
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.wr_pntr_bin[2]_i_1 
       (.I0(Q_reg[2]),
        .I1(Q_reg[3]),
        .O(D));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff__parameterized0_52
   (out,
    D,
    \Q_reg_reg[3]_0 ,
    s_aclk,
    AR);
  output [3:0]out;
  output [0:0]D;
  input [3:0]\Q_reg_reg[3]_0 ;
  input s_aclk;
  input [0:0]AR;

  wire [0:0]AR;
  wire [0:0]D;
  (* async_reg = "true" *) (* msgon = "true" *) wire [3:0]Q_reg;
  wire [3:0]\Q_reg_reg[3]_0 ;
  wire s_aclk;

  assign out[3:0] = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [0]),
        .Q(Q_reg[0]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [1]),
        .Q(Q_reg[1]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[2] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [2]),
        .Q(Q_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[3] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [3]),
        .Q(Q_reg[3]));
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.rd_pntr_bin[2]_i_1 
       (.I0(Q_reg[2]),
        .I1(Q_reg[3]),
        .O(D));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff__parameterized0_6
   (D,
    Q,
    m_aclk,
    AR);
  output [3:0]D;
  input [3:0]Q;
  input m_aclk;
  input [0:0]AR;

  wire [0:0]AR;
  wire [3:0]Q;
  (* async_reg = "true" *) (* msgon = "true" *) wire [3:0]Q_reg;
  wire m_aclk;

  assign D[3:0] = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(Q[0]),
        .Q(Q_reg[0]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(Q[1]),
        .Q(Q_reg[1]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[2] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(Q[2]),
        .Q(Q_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[3] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(Q[3]),
        .Q(Q_reg[3]));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff__parameterized0_68
   (D,
    Q,
    s_aclk,
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] );
  output [3:0]D;
  input [3:0]Q;
  input s_aclk;
  input [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;

  wire [3:0]Q;
  (* async_reg = "true" *) (* msgon = "true" *) wire [3:0]Q_reg;
  wire [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;
  wire s_aclk;

  assign D[3:0] = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(Q[0]),
        .Q(Q_reg[0]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(Q[1]),
        .Q(Q_reg[1]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[2] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(Q[2]),
        .Q(Q_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[3] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(Q[3]),
        .Q(Q_reg[3]));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff__parameterized0_69
   (D,
    Q,
    m_aclk,
    AR);
  output [3:0]D;
  input [3:0]Q;
  input m_aclk;
  input [0:0]AR;

  wire [0:0]AR;
  wire [3:0]Q;
  (* async_reg = "true" *) (* msgon = "true" *) wire [3:0]Q_reg;
  wire m_aclk;

  assign D[3:0] = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(Q[0]),
        .Q(Q_reg[0]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(Q[1]),
        .Q(Q_reg[1]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[2] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(Q[2]),
        .Q(Q_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[3] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(Q[3]),
        .Q(Q_reg[3]));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff__parameterized0_7
   (D,
    \Q_reg_reg[3]_0 ,
    s_aclk,
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] );
  output [3:0]D;
  input [3:0]\Q_reg_reg[3]_0 ;
  input s_aclk;
  input [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;

  (* async_reg = "true" *) (* msgon = "true" *) wire [3:0]Q_reg;
  wire [3:0]\Q_reg_reg[3]_0 ;
  wire [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;
  wire s_aclk;

  assign D[3:0] = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [0]),
        .Q(Q_reg[0]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [1]),
        .Q(Q_reg[1]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[2] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [2]),
        .Q(Q_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[3] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [3]),
        .Q(Q_reg[3]));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff__parameterized0_70
   (D,
    \Q_reg_reg[3]_0 ,
    s_aclk,
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] );
  output [3:0]D;
  input [3:0]\Q_reg_reg[3]_0 ;
  input s_aclk;
  input [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;

  (* async_reg = "true" *) (* msgon = "true" *) wire [3:0]Q_reg;
  wire [3:0]\Q_reg_reg[3]_0 ;
  wire [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;
  wire s_aclk;

  assign D[3:0] = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [0]),
        .Q(Q_reg[0]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [1]),
        .Q(Q_reg[1]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[2] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [2]),
        .Q(Q_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[3] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [3]),
        .Q(Q_reg[3]));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff__parameterized0_71
   (D,
    \Q_reg_reg[3]_0 ,
    m_aclk,
    AR);
  output [3:0]D;
  input [3:0]\Q_reg_reg[3]_0 ;
  input m_aclk;
  input [0:0]AR;

  wire [0:0]AR;
  (* async_reg = "true" *) (* msgon = "true" *) wire [3:0]Q_reg;
  wire [3:0]\Q_reg_reg[3]_0 ;
  wire m_aclk;

  assign D[3:0] = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [0]),
        .Q(Q_reg[0]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [1]),
        .Q(Q_reg[1]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[2] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [2]),
        .Q(Q_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[3] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [3]),
        .Q(Q_reg[3]));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff__parameterized0_72
   (out,
    D,
    \Q_reg_reg[3]_0 ,
    s_aclk,
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] );
  output [3:0]out;
  output [0:0]D;
  input [3:0]\Q_reg_reg[3]_0 ;
  input s_aclk;
  input [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;

  wire [0:0]D;
  (* async_reg = "true" *) (* msgon = "true" *) wire [3:0]Q_reg;
  wire [3:0]\Q_reg_reg[3]_0 ;
  wire [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;
  wire s_aclk;

  assign out[3:0] = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [0]),
        .Q(Q_reg[0]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [1]),
        .Q(Q_reg[1]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[2] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [2]),
        .Q(Q_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[3] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [3]),
        .Q(Q_reg[3]));
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.wr_pntr_bin[2]_i_1__3 
       (.I0(Q_reg[2]),
        .I1(Q_reg[3]),
        .O(D));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff__parameterized0_73
   (out,
    D,
    \Q_reg_reg[3]_0 ,
    m_aclk,
    AR);
  output [3:0]out;
  output [0:0]D;
  input [3:0]\Q_reg_reg[3]_0 ;
  input m_aclk;
  input [0:0]AR;

  wire [0:0]AR;
  wire [0:0]D;
  (* async_reg = "true" *) (* msgon = "true" *) wire [3:0]Q_reg;
  wire [3:0]\Q_reg_reg[3]_0 ;
  wire m_aclk;

  assign out[3:0] = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [0]),
        .Q(Q_reg[0]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [1]),
        .Q(Q_reg[1]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[2] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [2]),
        .Q(Q_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[3] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [3]),
        .Q(Q_reg[3]));
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.rd_pntr_bin[2]_i_1__3 
       (.I0(Q_reg[2]),
        .I1(Q_reg[3]),
        .O(D));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff__parameterized0_8
   (D,
    \Q_reg_reg[3]_0 ,
    m_aclk,
    AR);
  output [3:0]D;
  input [3:0]\Q_reg_reg[3]_0 ;
  input m_aclk;
  input [0:0]AR;

  wire [0:0]AR;
  (* async_reg = "true" *) (* msgon = "true" *) wire [3:0]Q_reg;
  wire [3:0]\Q_reg_reg[3]_0 ;
  wire m_aclk;

  assign D[3:0] = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [0]),
        .Q(Q_reg[0]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [1]),
        .Q(Q_reg[1]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[2] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [2]),
        .Q(Q_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[3] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [3]),
        .Q(Q_reg[3]));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff__parameterized0_9
   (out,
    D,
    \Q_reg_reg[3]_0 ,
    s_aclk,
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] );
  output [3:0]out;
  output [0:0]D;
  input [3:0]\Q_reg_reg[3]_0 ;
  input s_aclk;
  input [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;

  wire [0:0]D;
  (* async_reg = "true" *) (* msgon = "true" *) wire [3:0]Q_reg;
  wire [3:0]\Q_reg_reg[3]_0 ;
  wire [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;
  wire s_aclk;

  assign out[3:0] = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [0]),
        .Q(Q_reg[0]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [1]),
        .Q(Q_reg[1]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[2] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [2]),
        .Q(Q_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[3] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [3]),
        .Q(Q_reg[3]));
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.wr_pntr_bin[2]_i_1__1 
       (.I0(Q_reg[2]),
        .I1(Q_reg[3]),
        .O(D));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff__parameterized0_92
   (D,
    Q,
    m_aclk,
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] );
  output [3:0]D;
  input [3:0]Q;
  input m_aclk;
  input [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;

  wire [3:0]Q;
  (* async_reg = "true" *) (* msgon = "true" *) wire [3:0]Q_reg;
  wire m_aclk;
  wire [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;

  assign D[3:0] = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(Q[0]),
        .Q(Q_reg[0]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(Q[1]),
        .Q(Q_reg[1]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[2] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(Q[2]),
        .Q(Q_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[3] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(Q[3]),
        .Q(Q_reg[3]));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff__parameterized0_93
   (D,
    Q,
    s_aclk,
    AR);
  output [3:0]D;
  input [3:0]Q;
  input s_aclk;
  input [0:0]AR;

  wire [0:0]AR;
  wire [3:0]Q;
  (* async_reg = "true" *) (* msgon = "true" *) wire [3:0]Q_reg;
  wire s_aclk;

  assign D[3:0] = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(Q[0]),
        .Q(Q_reg[0]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(Q[1]),
        .Q(Q_reg[1]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[2] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(Q[2]),
        .Q(Q_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[3] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(Q[3]),
        .Q(Q_reg[3]));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff__parameterized0_94
   (D,
    \Q_reg_reg[3]_0 ,
    m_aclk,
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] );
  output [3:0]D;
  input [3:0]\Q_reg_reg[3]_0 ;
  input m_aclk;
  input [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;

  (* async_reg = "true" *) (* msgon = "true" *) wire [3:0]Q_reg;
  wire [3:0]\Q_reg_reg[3]_0 ;
  wire m_aclk;
  wire [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;

  assign D[3:0] = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [0]),
        .Q(Q_reg[0]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [1]),
        .Q(Q_reg[1]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[2] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [2]),
        .Q(Q_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[3] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [3]),
        .Q(Q_reg[3]));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff__parameterized0_95
   (D,
    \Q_reg_reg[3]_0 ,
    s_aclk,
    AR);
  output [3:0]D;
  input [3:0]\Q_reg_reg[3]_0 ;
  input s_aclk;
  input [0:0]AR;

  wire [0:0]AR;
  (* async_reg = "true" *) (* msgon = "true" *) wire [3:0]Q_reg;
  wire [3:0]\Q_reg_reg[3]_0 ;
  wire s_aclk;

  assign D[3:0] = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [0]),
        .Q(Q_reg[0]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [1]),
        .Q(Q_reg[1]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[2] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [2]),
        .Q(Q_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[3] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [3]),
        .Q(Q_reg[3]));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff__parameterized0_96
   (out,
    D,
    \Q_reg_reg[3]_0 ,
    m_aclk,
    \ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] );
  output [3:0]out;
  output [0:0]D;
  input [3:0]\Q_reg_reg[3]_0 ;
  input m_aclk;
  input [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;

  wire [0:0]D;
  (* async_reg = "true" *) (* msgon = "true" *) wire [3:0]Q_reg;
  wire [3:0]\Q_reg_reg[3]_0 ;
  wire m_aclk;
  wire [0:0]\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ;

  assign out[3:0] = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [0]),
        .Q(Q_reg[0]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[1] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [1]),
        .Q(Q_reg[1]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[2] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [2]),
        .Q(Q_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[3] 
       (.C(m_aclk),
        .CE(1'b1),
        .CLR(\ngwrdrst.grst.g7serrst.rd_rst_reg_reg[1] ),
        .D(\Q_reg_reg[3]_0 [3]),
        .Q(Q_reg[3]));
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.wr_pntr_bin[2]_i_1__2 
       (.I0(Q_reg[2]),
        .I1(Q_reg[3]),
        .O(D));
endmodule

(* ORIG_REF_NAME = "synchronizer_ff" *) 
module axi_clock_converter_dramslim_synchronizer_ff__parameterized0_97
   (out,
    D,
    \Q_reg_reg[3]_0 ,
    s_aclk,
    AR);
  output [3:0]out;
  output [0:0]D;
  input [3:0]\Q_reg_reg[3]_0 ;
  input s_aclk;
  input [0:0]AR;

  wire [0:0]AR;
  wire [0:0]D;
  (* async_reg = "true" *) (* msgon = "true" *) wire [3:0]Q_reg;
  wire [3:0]\Q_reg_reg[3]_0 ;
  wire s_aclk;

  assign out[3:0] = Q_reg;
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[0] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [0]),
        .Q(Q_reg[0]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[1] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [1]),
        .Q(Q_reg[1]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[2] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [2]),
        .Q(Q_reg[2]));
  (* ASYNC_REG *) 
  (* KEEP = "yes" *) 
  (* msgon = "true" *) 
  FDCE #(
    .INIT(1'b0)) 
    \Q_reg_reg[3] 
       (.C(s_aclk),
        .CE(1'b1),
        .CLR(AR),
        .D(\Q_reg_reg[3]_0 [3]),
        .Q(Q_reg[3]));
  LUT2 #(
    .INIT(4'h6)) 
    \gnxpm_cdc.rd_pntr_bin[2]_i_1__2 
       (.I0(Q_reg[2]),
        .I1(Q_reg[3]),
        .O(D));
endmodule

(* ORIG_REF_NAME = "wr_bin_cntr" *) 
module axi_clock_converter_dramslim_wr_bin_cntr
   (Q,
    \gic0.gc0.count_d2_reg[3]_0 ,
    \gnxpm_cdc.wr_pntr_gc_reg[3] ,
    E,
    m_aclk,
    AR);
  output [3:0]Q;
  output [3:0]\gic0.gc0.count_d2_reg[3]_0 ;
  output [3:0]\gnxpm_cdc.wr_pntr_gc_reg[3] ;
  input [0:0]E;
  input m_aclk;
  input [0:0]AR;

  wire [0:0]AR;
  wire [0:0]E;
  wire [3:0]Q;
  wire [3:0]\gic0.gc0.count_d2_reg[3]_0 ;
  wire [3:0]\gnxpm_cdc.wr_pntr_gc_reg[3] ;
  wire m_aclk;
  wire [3:0]plusOp__1;

  LUT1 #(
    .INIT(2'h1)) 
    \gic0.gc0.count[0]_i_1 
       (.I0(Q[0]),
        .O(plusOp__1[0]));
  LUT2 #(
    .INIT(4'h6)) 
    \gic0.gc0.count[1]_i_1 
       (.I0(Q[0]),
        .I1(Q[1]),
        .O(plusOp__1[1]));
  (* SOFT_HLUTNM = "soft_lutpair29" *) 
  LUT3 #(
    .INIT(8'h78)) 
    \gic0.gc0.count[2]_i_1 
       (.I0(Q[1]),
        .I1(Q[0]),
        .I2(Q[2]),
        .O(plusOp__1[2]));
  (* SOFT_HLUTNM = "soft_lutpair29" *) 
  LUT4 #(
    .INIT(16'h7F80)) 
    \gic0.gc0.count[3]_i_1 
       (.I0(Q[2]),
        .I1(Q[0]),
        .I2(Q[1]),
        .I3(Q[3]),
        .O(plusOp__1[3]));
  FDPE #(
    .INIT(1'b1)) 
    \gic0.gc0.count_d1_reg[0] 
       (.C(m_aclk),
        .CE(E),
        .D(Q[0]),
        .PRE(AR),
        .Q(\gic0.gc0.count_d2_reg[3]_0 [0]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d1_reg[1] 
       (.C(m_aclk),
        .CE(E),
        .CLR(AR),
        .D(Q[1]),
        .Q(\gic0.gc0.count_d2_reg[3]_0 [1]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d1_reg[2] 
       (.C(m_aclk),
        .CE(E),
        .CLR(AR),
        .D(Q[2]),
        .Q(\gic0.gc0.count_d2_reg[3]_0 [2]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d1_reg[3] 
       (.C(m_aclk),
        .CE(E),
        .CLR(AR),
        .D(Q[3]),
        .Q(\gic0.gc0.count_d2_reg[3]_0 [3]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d2_reg[0] 
       (.C(m_aclk),
        .CE(E),
        .CLR(AR),
        .D(\gic0.gc0.count_d2_reg[3]_0 [0]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg[3] [0]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d2_reg[1] 
       (.C(m_aclk),
        .CE(E),
        .CLR(AR),
        .D(\gic0.gc0.count_d2_reg[3]_0 [1]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg[3] [1]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d2_reg[2] 
       (.C(m_aclk),
        .CE(E),
        .CLR(AR),
        .D(\gic0.gc0.count_d2_reg[3]_0 [2]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg[3] [2]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d2_reg[3] 
       (.C(m_aclk),
        .CE(E),
        .CLR(AR),
        .D(\gic0.gc0.count_d2_reg[3]_0 [3]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg[3] [3]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_reg[0] 
       (.C(m_aclk),
        .CE(E),
        .CLR(AR),
        .D(plusOp__1[0]),
        .Q(Q[0]));
  FDPE #(
    .INIT(1'b1)) 
    \gic0.gc0.count_reg[1] 
       (.C(m_aclk),
        .CE(E),
        .D(plusOp__1[1]),
        .PRE(AR),
        .Q(Q[1]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_reg[2] 
       (.C(m_aclk),
        .CE(E),
        .CLR(AR),
        .D(plusOp__1[2]),
        .Q(Q[2]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_reg[3] 
       (.C(m_aclk),
        .CE(E),
        .CLR(AR),
        .D(plusOp__1[3]),
        .Q(Q[3]));
endmodule

(* ORIG_REF_NAME = "wr_bin_cntr" *) 
module axi_clock_converter_dramslim_wr_bin_cntr_22
   (Q,
    \gic0.gc0.count_d2_reg[3]_0 ,
    \gnxpm_cdc.wr_pntr_gc_reg[3] ,
    E,
    s_aclk,
    AR);
  output [3:0]Q;
  output [3:0]\gic0.gc0.count_d2_reg[3]_0 ;
  output [3:0]\gnxpm_cdc.wr_pntr_gc_reg[3] ;
  input [0:0]E;
  input s_aclk;
  input [0:0]AR;

  wire [0:0]AR;
  wire [0:0]E;
  wire [3:0]Q;
  wire [3:0]\gic0.gc0.count_d2_reg[3]_0 ;
  wire [3:0]\gnxpm_cdc.wr_pntr_gc_reg[3] ;
  wire [3:0]plusOp__5;
  wire s_aclk;

  LUT1 #(
    .INIT(2'h1)) 
    \gic0.gc0.count[0]_i_1__2 
       (.I0(Q[0]),
        .O(plusOp__5[0]));
  LUT2 #(
    .INIT(4'h6)) 
    \gic0.gc0.count[1]_i_1__2 
       (.I0(Q[0]),
        .I1(Q[1]),
        .O(plusOp__5[1]));
  (* SOFT_HLUTNM = "soft_lutpair23" *) 
  LUT3 #(
    .INIT(8'h78)) 
    \gic0.gc0.count[2]_i_1__2 
       (.I0(Q[1]),
        .I1(Q[0]),
        .I2(Q[2]),
        .O(plusOp__5[2]));
  (* SOFT_HLUTNM = "soft_lutpair23" *) 
  LUT4 #(
    .INIT(16'h7F80)) 
    \gic0.gc0.count[3]_i_1__2 
       (.I0(Q[2]),
        .I1(Q[0]),
        .I2(Q[1]),
        .I3(Q[3]),
        .O(plusOp__5[3]));
  FDPE #(
    .INIT(1'b1)) 
    \gic0.gc0.count_d1_reg[0] 
       (.C(s_aclk),
        .CE(E),
        .D(Q[0]),
        .PRE(AR),
        .Q(\gic0.gc0.count_d2_reg[3]_0 [0]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d1_reg[1] 
       (.C(s_aclk),
        .CE(E),
        .CLR(AR),
        .D(Q[1]),
        .Q(\gic0.gc0.count_d2_reg[3]_0 [1]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d1_reg[2] 
       (.C(s_aclk),
        .CE(E),
        .CLR(AR),
        .D(Q[2]),
        .Q(\gic0.gc0.count_d2_reg[3]_0 [2]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d1_reg[3] 
       (.C(s_aclk),
        .CE(E),
        .CLR(AR),
        .D(Q[3]),
        .Q(\gic0.gc0.count_d2_reg[3]_0 [3]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d2_reg[0] 
       (.C(s_aclk),
        .CE(E),
        .CLR(AR),
        .D(\gic0.gc0.count_d2_reg[3]_0 [0]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg[3] [0]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d2_reg[1] 
       (.C(s_aclk),
        .CE(E),
        .CLR(AR),
        .D(\gic0.gc0.count_d2_reg[3]_0 [1]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg[3] [1]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d2_reg[2] 
       (.C(s_aclk),
        .CE(E),
        .CLR(AR),
        .D(\gic0.gc0.count_d2_reg[3]_0 [2]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg[3] [2]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d2_reg[3] 
       (.C(s_aclk),
        .CE(E),
        .CLR(AR),
        .D(\gic0.gc0.count_d2_reg[3]_0 [3]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg[3] [3]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_reg[0] 
       (.C(s_aclk),
        .CE(E),
        .CLR(AR),
        .D(plusOp__5[0]),
        .Q(Q[0]));
  FDPE #(
    .INIT(1'b1)) 
    \gic0.gc0.count_reg[1] 
       (.C(s_aclk),
        .CE(E),
        .D(plusOp__5[1]),
        .PRE(AR),
        .Q(Q[1]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_reg[2] 
       (.C(s_aclk),
        .CE(E),
        .CLR(AR),
        .D(plusOp__5[2]),
        .Q(Q[2]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_reg[3] 
       (.C(s_aclk),
        .CE(E),
        .CLR(AR),
        .D(plusOp__5[3]),
        .Q(Q[3]));
endmodule

(* ORIG_REF_NAME = "wr_bin_cntr" *) 
module axi_clock_converter_dramslim_wr_bin_cntr_43
   (Q,
    \gic0.gc0.count_d2_reg[3]_0 ,
    \gnxpm_cdc.wr_pntr_gc_reg[3] ,
    E,
    s_aclk,
    AR);
  output [3:0]Q;
  output [3:0]\gic0.gc0.count_d2_reg[3]_0 ;
  output [3:0]\gnxpm_cdc.wr_pntr_gc_reg[3] ;
  input [0:0]E;
  input s_aclk;
  input [0:0]AR;

  wire [0:0]AR;
  wire [0:0]E;
  wire [3:0]Q;
  wire [3:0]\gic0.gc0.count_d2_reg[3]_0 ;
  wire [3:0]\gnxpm_cdc.wr_pntr_gc_reg[3] ;
  wire [3:0]plusOp__4;
  wire s_aclk;

  LUT1 #(
    .INIT(2'h1)) 
    \gic0.gc0.count[0]_i_1__1 
       (.I0(Q[0]),
        .O(plusOp__4[0]));
  LUT2 #(
    .INIT(4'h6)) 
    \gic0.gc0.count[1]_i_1__1 
       (.I0(Q[0]),
        .I1(Q[1]),
        .O(plusOp__4[1]));
  (* SOFT_HLUTNM = "soft_lutpair17" *) 
  LUT3 #(
    .INIT(8'h78)) 
    \gic0.gc0.count[2]_i_1__1 
       (.I0(Q[1]),
        .I1(Q[0]),
        .I2(Q[2]),
        .O(plusOp__4[2]));
  (* SOFT_HLUTNM = "soft_lutpair17" *) 
  LUT4 #(
    .INIT(16'h7F80)) 
    \gic0.gc0.count[3]_i_1__1 
       (.I0(Q[2]),
        .I1(Q[0]),
        .I2(Q[1]),
        .I3(Q[3]),
        .O(plusOp__4[3]));
  FDPE #(
    .INIT(1'b1)) 
    \gic0.gc0.count_d1_reg[0] 
       (.C(s_aclk),
        .CE(E),
        .D(Q[0]),
        .PRE(AR),
        .Q(\gic0.gc0.count_d2_reg[3]_0 [0]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d1_reg[1] 
       (.C(s_aclk),
        .CE(E),
        .CLR(AR),
        .D(Q[1]),
        .Q(\gic0.gc0.count_d2_reg[3]_0 [1]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d1_reg[2] 
       (.C(s_aclk),
        .CE(E),
        .CLR(AR),
        .D(Q[2]),
        .Q(\gic0.gc0.count_d2_reg[3]_0 [2]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d1_reg[3] 
       (.C(s_aclk),
        .CE(E),
        .CLR(AR),
        .D(Q[3]),
        .Q(\gic0.gc0.count_d2_reg[3]_0 [3]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d2_reg[0] 
       (.C(s_aclk),
        .CE(E),
        .CLR(AR),
        .D(\gic0.gc0.count_d2_reg[3]_0 [0]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg[3] [0]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d2_reg[1] 
       (.C(s_aclk),
        .CE(E),
        .CLR(AR),
        .D(\gic0.gc0.count_d2_reg[3]_0 [1]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg[3] [1]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d2_reg[2] 
       (.C(s_aclk),
        .CE(E),
        .CLR(AR),
        .D(\gic0.gc0.count_d2_reg[3]_0 [2]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg[3] [2]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d2_reg[3] 
       (.C(s_aclk),
        .CE(E),
        .CLR(AR),
        .D(\gic0.gc0.count_d2_reg[3]_0 [3]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg[3] [3]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_reg[0] 
       (.C(s_aclk),
        .CE(E),
        .CLR(AR),
        .D(plusOp__4[0]),
        .Q(Q[0]));
  FDPE #(
    .INIT(1'b1)) 
    \gic0.gc0.count_reg[1] 
       (.C(s_aclk),
        .CE(E),
        .D(plusOp__4[1]),
        .PRE(AR),
        .Q(Q[1]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_reg[2] 
       (.C(s_aclk),
        .CE(E),
        .CLR(AR),
        .D(plusOp__4[2]),
        .Q(Q[2]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_reg[3] 
       (.C(s_aclk),
        .CE(E),
        .CLR(AR),
        .D(plusOp__4[3]),
        .Q(Q[3]));
endmodule

(* ORIG_REF_NAME = "wr_bin_cntr" *) 
module axi_clock_converter_dramslim_wr_bin_cntr_64
   (Q,
    \gic0.gc0.count_d2_reg[3]_0 ,
    \gnxpm_cdc.wr_pntr_gc_reg[3] ,
    E,
    m_aclk,
    AR);
  output [3:0]Q;
  output [3:0]\gic0.gc0.count_d2_reg[3]_0 ;
  output [3:0]\gnxpm_cdc.wr_pntr_gc_reg[3] ;
  input [0:0]E;
  input m_aclk;
  input [0:0]AR;

  wire [0:0]AR;
  wire [0:0]E;
  wire [3:0]Q;
  wire [3:0]\gic0.gc0.count_d2_reg[3]_0 ;
  wire [3:0]\gnxpm_cdc.wr_pntr_gc_reg[3] ;
  wire m_aclk;
  wire [3:0]plusOp__3;

  LUT1 #(
    .INIT(2'h1)) 
    \gic0.gc0.count[0]_i_1__0 
       (.I0(Q[0]),
        .O(plusOp__3[0]));
  LUT2 #(
    .INIT(4'h6)) 
    \gic0.gc0.count[1]_i_1__0 
       (.I0(Q[0]),
        .I1(Q[1]),
        .O(plusOp__3[1]));
  (* SOFT_HLUTNM = "soft_lutpair11" *) 
  LUT3 #(
    .INIT(8'h78)) 
    \gic0.gc0.count[2]_i_1__0 
       (.I0(Q[1]),
        .I1(Q[0]),
        .I2(Q[2]),
        .O(plusOp__3[2]));
  (* SOFT_HLUTNM = "soft_lutpair11" *) 
  LUT4 #(
    .INIT(16'h7F80)) 
    \gic0.gc0.count[3]_i_1__0 
       (.I0(Q[2]),
        .I1(Q[0]),
        .I2(Q[1]),
        .I3(Q[3]),
        .O(plusOp__3[3]));
  FDPE #(
    .INIT(1'b1)) 
    \gic0.gc0.count_d1_reg[0] 
       (.C(m_aclk),
        .CE(E),
        .D(Q[0]),
        .PRE(AR),
        .Q(\gic0.gc0.count_d2_reg[3]_0 [0]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d1_reg[1] 
       (.C(m_aclk),
        .CE(E),
        .CLR(AR),
        .D(Q[1]),
        .Q(\gic0.gc0.count_d2_reg[3]_0 [1]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d1_reg[2] 
       (.C(m_aclk),
        .CE(E),
        .CLR(AR),
        .D(Q[2]),
        .Q(\gic0.gc0.count_d2_reg[3]_0 [2]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d1_reg[3] 
       (.C(m_aclk),
        .CE(E),
        .CLR(AR),
        .D(Q[3]),
        .Q(\gic0.gc0.count_d2_reg[3]_0 [3]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d2_reg[0] 
       (.C(m_aclk),
        .CE(E),
        .CLR(AR),
        .D(\gic0.gc0.count_d2_reg[3]_0 [0]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg[3] [0]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d2_reg[1] 
       (.C(m_aclk),
        .CE(E),
        .CLR(AR),
        .D(\gic0.gc0.count_d2_reg[3]_0 [1]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg[3] [1]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d2_reg[2] 
       (.C(m_aclk),
        .CE(E),
        .CLR(AR),
        .D(\gic0.gc0.count_d2_reg[3]_0 [2]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg[3] [2]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d2_reg[3] 
       (.C(m_aclk),
        .CE(E),
        .CLR(AR),
        .D(\gic0.gc0.count_d2_reg[3]_0 [3]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg[3] [3]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_reg[0] 
       (.C(m_aclk),
        .CE(E),
        .CLR(AR),
        .D(plusOp__3[0]),
        .Q(Q[0]));
  FDPE #(
    .INIT(1'b1)) 
    \gic0.gc0.count_reg[1] 
       (.C(m_aclk),
        .CE(E),
        .D(plusOp__3[1]),
        .PRE(AR),
        .Q(Q[1]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_reg[2] 
       (.C(m_aclk),
        .CE(E),
        .CLR(AR),
        .D(plusOp__3[2]),
        .Q(Q[2]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_reg[3] 
       (.C(m_aclk),
        .CE(E),
        .CLR(AR),
        .D(plusOp__3[3]),
        .Q(Q[3]));
endmodule

(* ORIG_REF_NAME = "wr_bin_cntr" *) 
module axi_clock_converter_dramslim_wr_bin_cntr_88
   (Q,
    \gic0.gc0.count_d2_reg[3]_0 ,
    \gnxpm_cdc.wr_pntr_gc_reg[3] ,
    E,
    s_aclk,
    AR);
  output [3:0]Q;
  output [3:0]\gic0.gc0.count_d2_reg[3]_0 ;
  output [3:0]\gnxpm_cdc.wr_pntr_gc_reg[3] ;
  input [0:0]E;
  input s_aclk;
  input [0:0]AR;

  wire [0:0]AR;
  wire [0:0]E;
  wire [3:0]Q;
  wire [3:0]\gic0.gc0.count_d2_reg[3]_0 ;
  wire [3:0]\gnxpm_cdc.wr_pntr_gc_reg[3] ;
  wire [3:0]plusOp__7;
  wire s_aclk;

  LUT1 #(
    .INIT(2'h1)) 
    \gic0.gc0.count[0]_i_1__3 
       (.I0(Q[0]),
        .O(plusOp__7[0]));
  LUT2 #(
    .INIT(4'h6)) 
    \gic0.gc0.count[1]_i_1__3 
       (.I0(Q[0]),
        .I1(Q[1]),
        .O(plusOp__7[1]));
  (* SOFT_HLUTNM = "soft_lutpair5" *) 
  LUT3 #(
    .INIT(8'h78)) 
    \gic0.gc0.count[2]_i_1__3 
       (.I0(Q[1]),
        .I1(Q[0]),
        .I2(Q[2]),
        .O(plusOp__7[2]));
  (* SOFT_HLUTNM = "soft_lutpair5" *) 
  LUT4 #(
    .INIT(16'h7F80)) 
    \gic0.gc0.count[3]_i_1__3 
       (.I0(Q[2]),
        .I1(Q[0]),
        .I2(Q[1]),
        .I3(Q[3]),
        .O(plusOp__7[3]));
  FDPE #(
    .INIT(1'b1)) 
    \gic0.gc0.count_d1_reg[0] 
       (.C(s_aclk),
        .CE(E),
        .D(Q[0]),
        .PRE(AR),
        .Q(\gic0.gc0.count_d2_reg[3]_0 [0]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d1_reg[1] 
       (.C(s_aclk),
        .CE(E),
        .CLR(AR),
        .D(Q[1]),
        .Q(\gic0.gc0.count_d2_reg[3]_0 [1]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d1_reg[2] 
       (.C(s_aclk),
        .CE(E),
        .CLR(AR),
        .D(Q[2]),
        .Q(\gic0.gc0.count_d2_reg[3]_0 [2]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d1_reg[3] 
       (.C(s_aclk),
        .CE(E),
        .CLR(AR),
        .D(Q[3]),
        .Q(\gic0.gc0.count_d2_reg[3]_0 [3]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d2_reg[0] 
       (.C(s_aclk),
        .CE(E),
        .CLR(AR),
        .D(\gic0.gc0.count_d2_reg[3]_0 [0]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg[3] [0]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d2_reg[1] 
       (.C(s_aclk),
        .CE(E),
        .CLR(AR),
        .D(\gic0.gc0.count_d2_reg[3]_0 [1]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg[3] [1]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d2_reg[2] 
       (.C(s_aclk),
        .CE(E),
        .CLR(AR),
        .D(\gic0.gc0.count_d2_reg[3]_0 [2]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg[3] [2]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_d2_reg[3] 
       (.C(s_aclk),
        .CE(E),
        .CLR(AR),
        .D(\gic0.gc0.count_d2_reg[3]_0 [3]),
        .Q(\gnxpm_cdc.wr_pntr_gc_reg[3] [3]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_reg[0] 
       (.C(s_aclk),
        .CE(E),
        .CLR(AR),
        .D(plusOp__7[0]),
        .Q(Q[0]));
  FDPE #(
    .INIT(1'b1)) 
    \gic0.gc0.count_reg[1] 
       (.C(s_aclk),
        .CE(E),
        .D(plusOp__7[1]),
        .PRE(AR),
        .Q(Q[1]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_reg[2] 
       (.C(s_aclk),
        .CE(E),
        .CLR(AR),
        .D(plusOp__7[2]),
        .Q(Q[2]));
  FDCE #(
    .INIT(1'b0)) 
    \gic0.gc0.count_reg[3] 
       (.C(s_aclk),
        .CE(E),
        .CLR(AR),
        .D(plusOp__7[3]),
        .Q(Q[3]));
endmodule

(* ORIG_REF_NAME = "wr_logic" *) 
module axi_clock_converter_dramslim_wr_logic
   (Q,
    ram_full_fb_i_reg,
    E,
    m_axi_bready,
    \gic0.gc0.count_d2_reg[3] ,
    \gnxpm_cdc.wr_pntr_gc_reg[3] ,
    \gic0.gc0.count_d1_reg[3] ,
    m_aclk,
    out,
    m_axi_bvalid,
    \gnxpm_cdc.rd_pntr_bin_reg[3] ,
    AR);
  output [2:0]Q;
  output ram_full_fb_i_reg;
  output [0:0]E;
  output m_axi_bready;
  output [3:0]\gic0.gc0.count_d2_reg[3] ;
  output [3:0]\gnxpm_cdc.wr_pntr_gc_reg[3] ;
  input \gic0.gc0.count_d1_reg[3] ;
  input m_aclk;
  input out;
  input m_axi_bvalid;
  input [0:0]\gnxpm_cdc.rd_pntr_bin_reg[3] ;
  input [0:0]AR;

  wire [0:0]AR;
  wire [0:0]E;
  wire [2:0]Q;
  wire \gic0.gc0.count_d1_reg[3] ;
  wire [3:0]\gic0.gc0.count_d2_reg[3] ;
  wire [0:0]\gnxpm_cdc.rd_pntr_bin_reg[3] ;
  wire [3:0]\gnxpm_cdc.wr_pntr_gc_reg[3] ;
  wire m_aclk;
  wire m_axi_bready;
  wire m_axi_bvalid;
  wire out;
  wire ram_full_fb_i_reg;
  wire [3:3]wr_pntr_plus2;

  axi_clock_converter_dramslim_wr_status_flags_as \gwas.wsts 
       (.E(E),
        .Q(wr_pntr_plus2),
        .\gic0.gc0.count_d1_reg[3] (\gic0.gc0.count_d1_reg[3] ),
        .\gnxpm_cdc.rd_pntr_bin_reg[3] (\gnxpm_cdc.rd_pntr_bin_reg[3] ),
        .m_aclk(m_aclk),
        .m_axi_bready(m_axi_bready),
        .m_axi_bvalid(m_axi_bvalid),
        .out(out),
        .ram_full_fb_i_reg_0(ram_full_fb_i_reg));
  axi_clock_converter_dramslim_wr_bin_cntr wpntr
       (.AR(AR),
        .E(E),
        .Q({wr_pntr_plus2,Q}),
        .\gic0.gc0.count_d2_reg[3]_0 (\gic0.gc0.count_d2_reg[3] ),
        .\gnxpm_cdc.wr_pntr_gc_reg[3] (\gnxpm_cdc.wr_pntr_gc_reg[3] ),
        .m_aclk(m_aclk));
endmodule

(* ORIG_REF_NAME = "wr_logic" *) 
module axi_clock_converter_dramslim_wr_logic_13
   (Q,
    ram_full_fb_i_reg,
    E,
    s_axi_wready,
    \gic0.gc0.count_d2_reg[3] ,
    \gnxpm_cdc.wr_pntr_gc_reg[3] ,
    \gic0.gc0.count_d1_reg[3] ,
    s_aclk,
    out,
    s_axi_wvalid,
    \gnxpm_cdc.rd_pntr_bin_reg[3] ,
    AR);
  output [2:0]Q;
  output ram_full_fb_i_reg;
  output [0:0]E;
  output s_axi_wready;
  output [3:0]\gic0.gc0.count_d2_reg[3] ;
  output [3:0]\gnxpm_cdc.wr_pntr_gc_reg[3] ;
  input \gic0.gc0.count_d1_reg[3] ;
  input s_aclk;
  input out;
  input s_axi_wvalid;
  input [0:0]\gnxpm_cdc.rd_pntr_bin_reg[3] ;
  input [0:0]AR;

  wire [0:0]AR;
  wire [0:0]E;
  wire [2:0]Q;
  wire \gic0.gc0.count_d1_reg[3] ;
  wire [3:0]\gic0.gc0.count_d2_reg[3] ;
  wire [0:0]\gnxpm_cdc.rd_pntr_bin_reg[3] ;
  wire [3:0]\gnxpm_cdc.wr_pntr_gc_reg[3] ;
  wire out;
  wire ram_full_fb_i_reg;
  wire s_aclk;
  wire s_axi_wready;
  wire s_axi_wvalid;
  wire [3:3]wr_pntr_plus2;

  axi_clock_converter_dramslim_wr_status_flags_as_21 \gwas.wsts 
       (.E(E),
        .Q(wr_pntr_plus2),
        .\gic0.gc0.count_d1_reg[3] (\gic0.gc0.count_d1_reg[3] ),
        .\gnxpm_cdc.rd_pntr_bin_reg[3] (\gnxpm_cdc.rd_pntr_bin_reg[3] ),
        .out(out),
        .ram_full_fb_i_reg_0(ram_full_fb_i_reg),
        .s_aclk(s_aclk),
        .s_axi_wready(s_axi_wready),
        .s_axi_wvalid(s_axi_wvalid));
  axi_clock_converter_dramslim_wr_bin_cntr_22 wpntr
       (.AR(AR),
        .E(E),
        .Q({wr_pntr_plus2,Q}),
        .\gic0.gc0.count_d2_reg[3]_0 (\gic0.gc0.count_d2_reg[3] ),
        .\gnxpm_cdc.wr_pntr_gc_reg[3] (\gnxpm_cdc.wr_pntr_gc_reg[3] ),
        .s_aclk(s_aclk));
endmodule

(* ORIG_REF_NAME = "wr_logic" *) 
module axi_clock_converter_dramslim_wr_logic_34
   (Q,
    ram_full_fb_i_reg,
    E,
    s_axi_awready,
    \gic0.gc0.count_d2_reg[3] ,
    \gnxpm_cdc.wr_pntr_gc_reg[3] ,
    \gic0.gc0.count_d1_reg[3] ,
    s_aclk,
    out,
    s_axi_awvalid,
    \gnxpm_cdc.rd_pntr_bin_reg[3] ,
    AR);
  output [2:0]Q;
  output ram_full_fb_i_reg;
  output [0:0]E;
  output s_axi_awready;
  output [3:0]\gic0.gc0.count_d2_reg[3] ;
  output [3:0]\gnxpm_cdc.wr_pntr_gc_reg[3] ;
  input \gic0.gc0.count_d1_reg[3] ;
  input s_aclk;
  input out;
  input s_axi_awvalid;
  input [0:0]\gnxpm_cdc.rd_pntr_bin_reg[3] ;
  input [0:0]AR;

  wire [0:0]AR;
  wire [0:0]E;
  wire [2:0]Q;
  wire \gic0.gc0.count_d1_reg[3] ;
  wire [3:0]\gic0.gc0.count_d2_reg[3] ;
  wire [0:0]\gnxpm_cdc.rd_pntr_bin_reg[3] ;
  wire [3:0]\gnxpm_cdc.wr_pntr_gc_reg[3] ;
  wire out;
  wire ram_full_fb_i_reg;
  wire s_aclk;
  wire s_axi_awready;
  wire s_axi_awvalid;
  wire [3:3]wr_pntr_plus2;

  axi_clock_converter_dramslim_wr_status_flags_as_42 \gwas.wsts 
       (.E(E),
        .Q(wr_pntr_plus2),
        .\gic0.gc0.count_d1_reg[3] (\gic0.gc0.count_d1_reg[3] ),
        .\gnxpm_cdc.rd_pntr_bin_reg[3] (\gnxpm_cdc.rd_pntr_bin_reg[3] ),
        .out(out),
        .ram_full_fb_i_reg_0(ram_full_fb_i_reg),
        .s_aclk(s_aclk),
        .s_axi_awready(s_axi_awready),
        .s_axi_awvalid(s_axi_awvalid));
  axi_clock_converter_dramslim_wr_bin_cntr_43 wpntr
       (.AR(AR),
        .E(E),
        .Q({wr_pntr_plus2,Q}),
        .\gic0.gc0.count_d2_reg[3]_0 (\gic0.gc0.count_d2_reg[3] ),
        .\gnxpm_cdc.wr_pntr_gc_reg[3] (\gnxpm_cdc.wr_pntr_gc_reg[3] ),
        .s_aclk(s_aclk));
endmodule

(* ORIG_REF_NAME = "wr_logic" *) 
module axi_clock_converter_dramslim_wr_logic_55
   (Q,
    ram_full_fb_i_reg,
    E,
    m_axi_rready,
    \gic0.gc0.count_d2_reg[3] ,
    \gnxpm_cdc.wr_pntr_gc_reg[3] ,
    \gic0.gc0.count_d1_reg[3] ,
    m_aclk,
    out,
    m_axi_rvalid,
    \gnxpm_cdc.rd_pntr_bin_reg[3] ,
    AR);
  output [2:0]Q;
  output ram_full_fb_i_reg;
  output [0:0]E;
  output m_axi_rready;
  output [3:0]\gic0.gc0.count_d2_reg[3] ;
  output [3:0]\gnxpm_cdc.wr_pntr_gc_reg[3] ;
  input \gic0.gc0.count_d1_reg[3] ;
  input m_aclk;
  input out;
  input m_axi_rvalid;
  input [0:0]\gnxpm_cdc.rd_pntr_bin_reg[3] ;
  input [0:0]AR;

  wire [0:0]AR;
  wire [0:0]E;
  wire [2:0]Q;
  wire \gic0.gc0.count_d1_reg[3] ;
  wire [3:0]\gic0.gc0.count_d2_reg[3] ;
  wire [0:0]\gnxpm_cdc.rd_pntr_bin_reg[3] ;
  wire [3:0]\gnxpm_cdc.wr_pntr_gc_reg[3] ;
  wire m_aclk;
  wire m_axi_rready;
  wire m_axi_rvalid;
  wire out;
  wire ram_full_fb_i_reg;
  wire [3:3]wr_pntr_plus2;

  axi_clock_converter_dramslim_wr_status_flags_as_63 \gwas.wsts 
       (.E(E),
        .Q(wr_pntr_plus2),
        .\gic0.gc0.count_d1_reg[3] (\gic0.gc0.count_d1_reg[3] ),
        .\gnxpm_cdc.rd_pntr_bin_reg[3] (\gnxpm_cdc.rd_pntr_bin_reg[3] ),
        .m_aclk(m_aclk),
        .m_axi_rready(m_axi_rready),
        .m_axi_rvalid(m_axi_rvalid),
        .out(out),
        .ram_full_fb_i_reg_0(ram_full_fb_i_reg));
  axi_clock_converter_dramslim_wr_bin_cntr_64 wpntr
       (.AR(AR),
        .E(E),
        .Q({wr_pntr_plus2,Q}),
        .\gic0.gc0.count_d2_reg[3]_0 (\gic0.gc0.count_d2_reg[3] ),
        .\gnxpm_cdc.wr_pntr_gc_reg[3] (\gnxpm_cdc.wr_pntr_gc_reg[3] ),
        .m_aclk(m_aclk));
endmodule

(* ORIG_REF_NAME = "wr_logic" *) 
module axi_clock_converter_dramslim_wr_logic_77
   (Q,
    ram_full_fb_i_reg,
    E,
    s_axi_arready,
    \gic0.gc0.count_d2_reg[3] ,
    \gnxpm_cdc.wr_pntr_gc_reg[3] ,
    \gic0.gc0.count_d1_reg[3] ,
    s_aclk,
    out,
    s_axi_arvalid,
    \gnxpm_cdc.rd_pntr_bin_reg[3] ,
    AR);
  output [2:0]Q;
  output ram_full_fb_i_reg;
  output [0:0]E;
  output s_axi_arready;
  output [3:0]\gic0.gc0.count_d2_reg[3] ;
  output [3:0]\gnxpm_cdc.wr_pntr_gc_reg[3] ;
  input \gic0.gc0.count_d1_reg[3] ;
  input s_aclk;
  input out;
  input s_axi_arvalid;
  input [0:0]\gnxpm_cdc.rd_pntr_bin_reg[3] ;
  input [0:0]AR;

  wire [0:0]AR;
  wire [0:0]E;
  wire [2:0]Q;
  wire \gic0.gc0.count_d1_reg[3] ;
  wire [3:0]\gic0.gc0.count_d2_reg[3] ;
  wire [0:0]\gnxpm_cdc.rd_pntr_bin_reg[3] ;
  wire [3:0]\gnxpm_cdc.wr_pntr_gc_reg[3] ;
  wire out;
  wire ram_full_fb_i_reg;
  wire s_aclk;
  wire s_axi_arready;
  wire s_axi_arvalid;
  wire [3:3]wr_pntr_plus2;

  axi_clock_converter_dramslim_wr_status_flags_as_87 \gwas.wsts 
       (.E(E),
        .Q(wr_pntr_plus2),
        .\gic0.gc0.count_d1_reg[3] (\gic0.gc0.count_d1_reg[3] ),
        .\gnxpm_cdc.rd_pntr_bin_reg[3] (\gnxpm_cdc.rd_pntr_bin_reg[3] ),
        .out(out),
        .ram_full_fb_i_reg_0(ram_full_fb_i_reg),
        .s_aclk(s_aclk),
        .s_axi_arready(s_axi_arready),
        .s_axi_arvalid(s_axi_arvalid));
  axi_clock_converter_dramslim_wr_bin_cntr_88 wpntr
       (.AR(AR),
        .E(E),
        .Q({wr_pntr_plus2,Q}),
        .\gic0.gc0.count_d2_reg[3]_0 (\gic0.gc0.count_d2_reg[3] ),
        .\gnxpm_cdc.wr_pntr_gc_reg[3] (\gnxpm_cdc.wr_pntr_gc_reg[3] ),
        .s_aclk(s_aclk));
endmodule

(* ORIG_REF_NAME = "wr_status_flags_as" *) 
module axi_clock_converter_dramslim_wr_status_flags_as
   (ram_full_fb_i_reg_0,
    E,
    m_axi_bready,
    \gic0.gc0.count_d1_reg[3] ,
    m_aclk,
    out,
    m_axi_bvalid,
    Q,
    \gnxpm_cdc.rd_pntr_bin_reg[3] );
  output ram_full_fb_i_reg_0;
  output [0:0]E;
  output m_axi_bready;
  input \gic0.gc0.count_d1_reg[3] ;
  input m_aclk;
  input out;
  input m_axi_bvalid;
  input [0:0]Q;
  input [0:0]\gnxpm_cdc.rd_pntr_bin_reg[3] ;

  wire [0:0]E;
  wire [0:0]Q;
  wire \gic0.gc0.count_d1_reg[3] ;
  wire [0:0]\gnxpm_cdc.rd_pntr_bin_reg[3] ;
  wire m_aclk;
  wire m_axi_bready;
  wire m_axi_bvalid;
  wire out;
  (* DONT_TOUCH *) wire ram_full_fb_i;
  wire ram_full_fb_i_reg_0;
  (* DONT_TOUCH *) wire ram_full_i;

  LUT2 #(
    .INIT(4'h2)) 
    \gic0.gc0.count_d1[3]_i_1 
       (.I0(m_axi_bvalid),
        .I1(ram_full_fb_i),
        .O(E));
  LUT1 #(
    .INIT(2'h1)) 
    m_axi_bready_INST_0
       (.I0(ram_full_i),
        .O(m_axi_bready));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    ram_full_fb_i_reg
       (.C(m_aclk),
        .CE(1'b1),
        .D(\gic0.gc0.count_d1_reg[3] ),
        .PRE(out),
        .Q(ram_full_fb_i));
  LUT4 #(
    .INIT(16'h4004)) 
    ram_full_i_i_3
       (.I0(ram_full_fb_i),
        .I1(m_axi_bvalid),
        .I2(Q),
        .I3(\gnxpm_cdc.rd_pntr_bin_reg[3] ),
        .O(ram_full_fb_i_reg_0));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    ram_full_i_reg
       (.C(m_aclk),
        .CE(1'b1),
        .D(\gic0.gc0.count_d1_reg[3] ),
        .PRE(out),
        .Q(ram_full_i));
endmodule

(* ORIG_REF_NAME = "wr_status_flags_as" *) 
module axi_clock_converter_dramslim_wr_status_flags_as_21
   (ram_full_fb_i_reg_0,
    E,
    s_axi_wready,
    \gic0.gc0.count_d1_reg[3] ,
    s_aclk,
    out,
    s_axi_wvalid,
    Q,
    \gnxpm_cdc.rd_pntr_bin_reg[3] );
  output ram_full_fb_i_reg_0;
  output [0:0]E;
  output s_axi_wready;
  input \gic0.gc0.count_d1_reg[3] ;
  input s_aclk;
  input out;
  input s_axi_wvalid;
  input [0:0]Q;
  input [0:0]\gnxpm_cdc.rd_pntr_bin_reg[3] ;

  wire [0:0]E;
  wire [0:0]Q;
  wire \gic0.gc0.count_d1_reg[3] ;
  wire [0:0]\gnxpm_cdc.rd_pntr_bin_reg[3] ;
  wire out;
  (* DONT_TOUCH *) wire ram_full_fb_i;
  wire ram_full_fb_i_reg_0;
  (* DONT_TOUCH *) wire ram_full_i;
  wire s_aclk;
  wire s_axi_wready;
  wire s_axi_wvalid;

  LUT2 #(
    .INIT(4'h2)) 
    \gic0.gc0.count_d1[3]_i_1__2 
       (.I0(s_axi_wvalid),
        .I1(ram_full_fb_i),
        .O(E));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    ram_full_fb_i_reg
       (.C(s_aclk),
        .CE(1'b1),
        .D(\gic0.gc0.count_d1_reg[3] ),
        .PRE(out),
        .Q(ram_full_fb_i));
  LUT4 #(
    .INIT(16'h4004)) 
    ram_full_i_i_3__2
       (.I0(ram_full_fb_i),
        .I1(s_axi_wvalid),
        .I2(Q),
        .I3(\gnxpm_cdc.rd_pntr_bin_reg[3] ),
        .O(ram_full_fb_i_reg_0));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    ram_full_i_reg
       (.C(s_aclk),
        .CE(1'b1),
        .D(\gic0.gc0.count_d1_reg[3] ),
        .PRE(out),
        .Q(ram_full_i));
  LUT1 #(
    .INIT(2'h1)) 
    s_axi_wready_INST_0
       (.I0(ram_full_i),
        .O(s_axi_wready));
endmodule

(* ORIG_REF_NAME = "wr_status_flags_as" *) 
module axi_clock_converter_dramslim_wr_status_flags_as_42
   (ram_full_fb_i_reg_0,
    E,
    s_axi_awready,
    \gic0.gc0.count_d1_reg[3] ,
    s_aclk,
    out,
    s_axi_awvalid,
    Q,
    \gnxpm_cdc.rd_pntr_bin_reg[3] );
  output ram_full_fb_i_reg_0;
  output [0:0]E;
  output s_axi_awready;
  input \gic0.gc0.count_d1_reg[3] ;
  input s_aclk;
  input out;
  input s_axi_awvalid;
  input [0:0]Q;
  input [0:0]\gnxpm_cdc.rd_pntr_bin_reg[3] ;

  wire [0:0]E;
  wire [0:0]Q;
  wire \gic0.gc0.count_d1_reg[3] ;
  wire [0:0]\gnxpm_cdc.rd_pntr_bin_reg[3] ;
  wire out;
  (* DONT_TOUCH *) wire ram_full_fb_i;
  wire ram_full_fb_i_reg_0;
  (* DONT_TOUCH *) wire ram_full_i;
  wire s_aclk;
  wire s_axi_awready;
  wire s_axi_awvalid;

  LUT2 #(
    .INIT(4'h2)) 
    \gic0.gc0.count_d1[3]_i_1__1 
       (.I0(s_axi_awvalid),
        .I1(ram_full_fb_i),
        .O(E));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    ram_full_fb_i_reg
       (.C(s_aclk),
        .CE(1'b1),
        .D(\gic0.gc0.count_d1_reg[3] ),
        .PRE(out),
        .Q(ram_full_fb_i));
  LUT4 #(
    .INIT(16'h4004)) 
    ram_full_i_i_3__1
       (.I0(ram_full_fb_i),
        .I1(s_axi_awvalid),
        .I2(Q),
        .I3(\gnxpm_cdc.rd_pntr_bin_reg[3] ),
        .O(ram_full_fb_i_reg_0));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    ram_full_i_reg
       (.C(s_aclk),
        .CE(1'b1),
        .D(\gic0.gc0.count_d1_reg[3] ),
        .PRE(out),
        .Q(ram_full_i));
  LUT1 #(
    .INIT(2'h1)) 
    s_axi_awready_INST_0
       (.I0(ram_full_i),
        .O(s_axi_awready));
endmodule

(* ORIG_REF_NAME = "wr_status_flags_as" *) 
module axi_clock_converter_dramslim_wr_status_flags_as_63
   (ram_full_fb_i_reg_0,
    E,
    m_axi_rready,
    \gic0.gc0.count_d1_reg[3] ,
    m_aclk,
    out,
    m_axi_rvalid,
    Q,
    \gnxpm_cdc.rd_pntr_bin_reg[3] );
  output ram_full_fb_i_reg_0;
  output [0:0]E;
  output m_axi_rready;
  input \gic0.gc0.count_d1_reg[3] ;
  input m_aclk;
  input out;
  input m_axi_rvalid;
  input [0:0]Q;
  input [0:0]\gnxpm_cdc.rd_pntr_bin_reg[3] ;

  wire [0:0]E;
  wire [0:0]Q;
  wire \gic0.gc0.count_d1_reg[3] ;
  wire [0:0]\gnxpm_cdc.rd_pntr_bin_reg[3] ;
  wire m_aclk;
  wire m_axi_rready;
  wire m_axi_rvalid;
  wire out;
  (* DONT_TOUCH *) wire ram_full_fb_i;
  wire ram_full_fb_i_reg_0;
  (* DONT_TOUCH *) wire ram_full_i;

  LUT2 #(
    .INIT(4'h2)) 
    \gic0.gc0.count_d1[3]_i_1__0 
       (.I0(m_axi_rvalid),
        .I1(ram_full_fb_i),
        .O(E));
  LUT1 #(
    .INIT(2'h1)) 
    m_axi_rready_INST_0
       (.I0(ram_full_i),
        .O(m_axi_rready));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    ram_full_fb_i_reg
       (.C(m_aclk),
        .CE(1'b1),
        .D(\gic0.gc0.count_d1_reg[3] ),
        .PRE(out),
        .Q(ram_full_fb_i));
  LUT4 #(
    .INIT(16'h4004)) 
    ram_full_i_i_3__0
       (.I0(ram_full_fb_i),
        .I1(m_axi_rvalid),
        .I2(Q),
        .I3(\gnxpm_cdc.rd_pntr_bin_reg[3] ),
        .O(ram_full_fb_i_reg_0));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    ram_full_i_reg
       (.C(m_aclk),
        .CE(1'b1),
        .D(\gic0.gc0.count_d1_reg[3] ),
        .PRE(out),
        .Q(ram_full_i));
endmodule

(* ORIG_REF_NAME = "wr_status_flags_as" *) 
module axi_clock_converter_dramslim_wr_status_flags_as_87
   (ram_full_fb_i_reg_0,
    E,
    s_axi_arready,
    \gic0.gc0.count_d1_reg[3] ,
    s_aclk,
    out,
    s_axi_arvalid,
    Q,
    \gnxpm_cdc.rd_pntr_bin_reg[3] );
  output ram_full_fb_i_reg_0;
  output [0:0]E;
  output s_axi_arready;
  input \gic0.gc0.count_d1_reg[3] ;
  input s_aclk;
  input out;
  input s_axi_arvalid;
  input [0:0]Q;
  input [0:0]\gnxpm_cdc.rd_pntr_bin_reg[3] ;

  wire [0:0]E;
  wire [0:0]Q;
  wire \gic0.gc0.count_d1_reg[3] ;
  wire [0:0]\gnxpm_cdc.rd_pntr_bin_reg[3] ;
  wire out;
  (* DONT_TOUCH *) wire ram_full_fb_i;
  wire ram_full_fb_i_reg_0;
  (* DONT_TOUCH *) wire ram_full_i;
  wire s_aclk;
  wire s_axi_arready;
  wire s_axi_arvalid;

  LUT2 #(
    .INIT(4'h2)) 
    \gic0.gc0.count_d1[3]_i_1__3 
       (.I0(s_axi_arvalid),
        .I1(ram_full_fb_i),
        .O(E));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    ram_full_fb_i_reg
       (.C(s_aclk),
        .CE(1'b1),
        .D(\gic0.gc0.count_d1_reg[3] ),
        .PRE(out),
        .Q(ram_full_fb_i));
  LUT4 #(
    .INIT(16'h4004)) 
    ram_full_i_i_3__3
       (.I0(ram_full_fb_i),
        .I1(s_axi_arvalid),
        .I2(Q),
        .I3(\gnxpm_cdc.rd_pntr_bin_reg[3] ),
        .O(ram_full_fb_i_reg_0));
  (* DONT_TOUCH *) 
  (* KEEP = "yes" *) 
  (* equivalent_register_removal = "no" *) 
  FDPE #(
    .INIT(1'b1)) 
    ram_full_i_reg
       (.C(s_aclk),
        .CE(1'b1),
        .D(\gic0.gc0.count_d1_reg[3] ),
        .PRE(out),
        .Q(ram_full_i));
  LUT1 #(
    .INIT(2'h1)) 
    s_axi_arready_INST_0
       (.I0(ram_full_i),
        .O(s_axi_arready));
endmodule
`ifndef GLBL
`define GLBL
`timescale  1 ps / 1 ps

module glbl ();

    parameter ROC_WIDTH = 100000;
    parameter TOC_WIDTH = 0;

//--------   STARTUP Globals --------------
    wire GSR;
    wire GTS;
    wire GWE;
    wire PRLD;
    tri1 p_up_tmp;
    tri (weak1, strong0) PLL_LOCKG = p_up_tmp;

    wire PROGB_GLBL;
    wire CCLKO_GLBL;
    wire FCSBO_GLBL;
    wire [3:0] DO_GLBL;
    wire [3:0] DI_GLBL;
   
    reg GSR_int;
    reg GTS_int;
    reg PRLD_int;

//--------   JTAG Globals --------------
    wire JTAG_TDO_GLBL;
    wire JTAG_TCK_GLBL;
    wire JTAG_TDI_GLBL;
    wire JTAG_TMS_GLBL;
    wire JTAG_TRST_GLBL;

    reg JTAG_CAPTURE_GLBL;
    reg JTAG_RESET_GLBL;
    reg JTAG_SHIFT_GLBL;
    reg JTAG_UPDATE_GLBL;
    reg JTAG_RUNTEST_GLBL;

    reg JTAG_SEL1_GLBL = 0;
    reg JTAG_SEL2_GLBL = 0 ;
    reg JTAG_SEL3_GLBL = 0;
    reg JTAG_SEL4_GLBL = 0;

    reg JTAG_USER_TDO1_GLBL = 1'bz;
    reg JTAG_USER_TDO2_GLBL = 1'bz;
    reg JTAG_USER_TDO3_GLBL = 1'bz;
    reg JTAG_USER_TDO4_GLBL = 1'bz;

    assign (strong1, weak0) GSR = GSR_int;
    assign (strong1, weak0) GTS = GTS_int;
    assign (weak1, weak0) PRLD = PRLD_int;

    initial begin
	GSR_int = 1'b1;
	PRLD_int = 1'b1;
	#(ROC_WIDTH)
	GSR_int = 1'b0;
	PRLD_int = 1'b0;
    end

    initial begin
	GTS_int = 1'b1;
	#(TOC_WIDTH)
	GTS_int = 1'b0;
    end

endmodule
`endif
