// (c) Copyright 1986-2022 Xilinx, Inc. All Rights Reserved.
// (c) Copyright 2022-2024 Advanced Micro Devices, Inc. All rights reserved.
// 
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and international copyright
// and other intellectual property laws.
// 
// DISCLAIMER
// This disclaimer is not a license and does not grant any
// rights to the materials distributed herewith. Except as
// otherwise provided in a valid license issued to you by
// AMD, and to the maximum extent permitted by applicable
// law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// WITH ALL FAULTS, AND AMD HEREBY DISCLAIMS ALL WARRANTIES
// AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// (2) AMD shall not be liable (whether in contract or tort,
// including negligence, or under any other theory of
// liability) for any loss or damage of any kind or nature
// related to, arising under or in connection with these
// materials, including for any direct, or any indirect,
// special, incidental, or consequential loss or damage
// (including loss of data, profits, goodwill, or any type of
// loss or damage suffered as a result of any action brought
// by a third party) even if such damage or loss was
// reasonably foreseeable or AMD had been advised of the
// possibility of the same.
// 
// CRITICAL APPLICATIONS
// AMD products are not designed or intended to be fail-
// safe, or for use in any application requiring fail-safe
// performance, such as life-support or safety devices or
// systems, Class III medical devices, nuclear facilities,
// applications related to the deployment of airbags, or any
// other applications that could lead to death, personal
// injury, or severe property or environmental damage
// (individually and collectively, "Critical
// Applications"). Customer assumes the sole risk and
// liability of any use of AMD products in Critical
// Applications, subject only to applicable laws and
// regulations governing limitations on product liability.
// 
// THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// PART OF THIS FILE AT ALL TIMES.
// 
// DO NOT MODIFY THIS FILE.


//------------------------------------------------------------------------------------
// Filename:    cl_clk_axil_xbar_stub.sv
// Description: This HDL file is intended to be used with following simulators only:
//
//   Vivado Simulator (XSim)
//   Cadence Xcelium Simulator
//
//------------------------------------------------------------------------------------
`timescale 1ps/1ps

`ifdef XILINX_SIMULATOR

`ifndef XILINX_SIMULATOR_BITASBOOL
`define XILINX_SIMULATOR_BITASBOOL
typedef bit bit_as_bool;
`endif

(* SC_MODULE_EXPORT *)
module cl_clk_axil_xbar (
  input bit_as_bool aclk,
  input bit_as_bool aresetn,
  input bit [31 : 0] s_axi_awaddr,
  input bit [2 : 0] s_axi_awprot,
  input bit [0 : 0] s_axi_awvalid,
  output bit [0 : 0] s_axi_awready,
  input bit [31 : 0] s_axi_wdata,
  input bit [3 : 0] s_axi_wstrb,
  input bit [0 : 0] s_axi_wvalid,
  output bit [0 : 0] s_axi_wready,
  output bit [1 : 0] s_axi_bresp,
  output bit [0 : 0] s_axi_bvalid,
  input bit [0 : 0] s_axi_bready,
  input bit [31 : 0] s_axi_araddr,
  input bit [2 : 0] s_axi_arprot,
  input bit [0 : 0] s_axi_arvalid,
  output bit [0 : 0] s_axi_arready,
  output bit [31 : 0] s_axi_rdata,
  output bit [1 : 0] s_axi_rresp,
  output bit [0 : 0] s_axi_rvalid,
  input bit [0 : 0] s_axi_rready,
  output bit [159 : 0] m_axi_awaddr,
  output bit [14 : 0] m_axi_awprot,
  output bit [4 : 0] m_axi_awvalid,
  input bit [4 : 0] m_axi_awready,
  output bit [159 : 0] m_axi_wdata,
  output bit [19 : 0] m_axi_wstrb,
  output bit [4 : 0] m_axi_wvalid,
  input bit [4 : 0] m_axi_wready,
  input bit [9 : 0] m_axi_bresp,
  input bit [4 : 0] m_axi_bvalid,
  output bit [4 : 0] m_axi_bready,
  output bit [159 : 0] m_axi_araddr,
  output bit [14 : 0] m_axi_arprot,
  output bit [4 : 0] m_axi_arvalid,
  input bit [4 : 0] m_axi_arready,
  input bit [159 : 0] m_axi_rdata,
  input bit [9 : 0] m_axi_rresp,
  input bit [4 : 0] m_axi_rvalid,
  output bit [4 : 0] m_axi_rready
);
endmodule
`endif

`ifdef XCELIUM
(* XMSC_MODULE_EXPORT *)
module cl_clk_axil_xbar (aclk,aresetn,s_axi_awaddr,s_axi_awprot,s_axi_awvalid,s_axi_awready,s_axi_wdata,s_axi_wstrb,s_axi_wvalid,s_axi_wready,s_axi_bresp,s_axi_bvalid,s_axi_bready,s_axi_araddr,s_axi_arprot,s_axi_arvalid,s_axi_arready,s_axi_rdata,s_axi_rresp,s_axi_rvalid,s_axi_rready,m_axi_awaddr,m_axi_awprot,m_axi_awvalid,m_axi_awready,m_axi_wdata,m_axi_wstrb,m_axi_wvalid,m_axi_wready,m_axi_bresp,m_axi_bvalid,m_axi_bready,m_axi_araddr,m_axi_arprot,m_axi_arvalid,m_axi_arready,m_axi_rdata,m_axi_rresp,m_axi_rvalid,m_axi_rready)
(* integer foreign = "SystemC";
*);
  input bit aclk;
  input bit aresetn;
  input bit [31 : 0] s_axi_awaddr;
  input bit [2 : 0] s_axi_awprot;
  input bit [0 : 0] s_axi_awvalid;
  output wire [0 : 0] s_axi_awready;
  input bit [31 : 0] s_axi_wdata;
  input bit [3 : 0] s_axi_wstrb;
  input bit [0 : 0] s_axi_wvalid;
  output wire [0 : 0] s_axi_wready;
  output wire [1 : 0] s_axi_bresp;
  output wire [0 : 0] s_axi_bvalid;
  input bit [0 : 0] s_axi_bready;
  input bit [31 : 0] s_axi_araddr;
  input bit [2 : 0] s_axi_arprot;
  input bit [0 : 0] s_axi_arvalid;
  output wire [0 : 0] s_axi_arready;
  output wire [31 : 0] s_axi_rdata;
  output wire [1 : 0] s_axi_rresp;
  output wire [0 : 0] s_axi_rvalid;
  input bit [0 : 0] s_axi_rready;
  output wire [159 : 0] m_axi_awaddr;
  output wire [14 : 0] m_axi_awprot;
  output wire [4 : 0] m_axi_awvalid;
  input bit [4 : 0] m_axi_awready;
  output wire [159 : 0] m_axi_wdata;
  output wire [19 : 0] m_axi_wstrb;
  output wire [4 : 0] m_axi_wvalid;
  input bit [4 : 0] m_axi_wready;
  input bit [9 : 0] m_axi_bresp;
  input bit [4 : 0] m_axi_bvalid;
  output wire [4 : 0] m_axi_bready;
  output wire [159 : 0] m_axi_araddr;
  output wire [14 : 0] m_axi_arprot;
  output wire [4 : 0] m_axi_arvalid;
  input bit [4 : 0] m_axi_arready;
  input bit [159 : 0] m_axi_rdata;
  input bit [9 : 0] m_axi_rresp;
  input bit [4 : 0] m_axi_rvalid;
  output wire [4 : 0] m_axi_rready;
endmodule
`endif
