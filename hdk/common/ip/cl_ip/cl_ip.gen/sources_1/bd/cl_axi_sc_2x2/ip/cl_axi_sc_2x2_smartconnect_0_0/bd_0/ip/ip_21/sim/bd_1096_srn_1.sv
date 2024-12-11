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


// IP VLNV: xilinx.com:ip:sc_node:1.0
// IP Revision: 16

`timescale 1ns/1ps

(* DowngradeIPIdentifiedWarnings = "yes" *)
module bd_1096_srn_1 (
  s_sc_aclk,
  s_sc_aresetn,
  s_sc_req,
  s_sc_info,
  s_sc_send,
  s_sc_recv,
  s_sc_payld,
  m_sc_aclk,
  m_sc_aresetn,
  m_sc_recv,
  m_sc_send,
  m_sc_req,
  m_sc_info,
  m_sc_payld
);

(* X_INTERFACE_PARAMETER = "XIL_INTERFACENAME aclk, ASSOCIATED_BUSIF S_AXIS_ARB:M_AXIS_ARB:S_SC, ASSOCIATED_RESET s_sc_aresetn, ASSOCIATED_CLKEN s_sc_aclken, FREQ_HZ 250000000, FREQ_TOLERANCE_HZ 0, PHASE 0.0, CLK_DOMAIN cl_axi_sc_2x2_aclk_250, INSERT_VIP 0" *)
(* X_INTERFACE_INFO = "xilinx.com:signal:clock:1.0 aclk CLK" *)
input wire s_sc_aclk;
(* X_INTERFACE_PARAMETER = "XIL_INTERFACENAME aresetn, POLARITY ACTIVE_LOW, INSERT_VIP 0" *)
(* X_INTERFACE_INFO = "xilinx.com:signal:reset:1.0 aresetn RST" *)
input wire s_sc_aresetn;
(* X_INTERFACE_INFO = "xilinx.com:interface:sc:1.0 S_SC REQ" *)
input wire [1 : 0] s_sc_req;
(* X_INTERFACE_INFO = "xilinx.com:interface:sc:1.0 S_SC INFO" *)
input wire [1 : 0] s_sc_info;
(* X_INTERFACE_INFO = "xilinx.com:interface:sc:1.0 S_SC SEND" *)
input wire [1 : 0] s_sc_send;
(* X_INTERFACE_INFO = "xilinx.com:interface:sc:1.0 S_SC RECV" *)
output wire [1 : 0] s_sc_recv;
(* X_INTERFACE_INFO = "xilinx.com:interface:sc:1.0 S_SC PAYLD" *)
input wire [534 : 0] s_sc_payld;
(* X_INTERFACE_PARAMETER = "XIL_INTERFACENAME m_sc_aclk, ASSOCIATED_BUSIF M_SC, ASSOCIATED_RESET m_sc_aresetn, ASSOCIATED_CLKEN m_sc_aclken, FREQ_HZ 250000000, FREQ_TOLERANCE_HZ 0, PHASE 0.0, CLK_DOMAIN cl_axi_sc_2x2_aclk_250, INSERT_VIP 0" *)
(* X_INTERFACE_INFO = "xilinx.com:signal:clock:1.0 m_sc_aclk CLK" *)
input wire m_sc_aclk;
(* X_INTERFACE_PARAMETER = "XIL_INTERFACENAME m_sc_aresetn, POLARITY ACTIVE_LOW, INSERT_VIP 0" *)
(* X_INTERFACE_INFO = "xilinx.com:signal:reset:1.0 m_sc_aresetn RST" *)
input wire m_sc_aresetn;
(* X_INTERFACE_INFO = "xilinx.com:interface:sc:1.0 M_SC RECV" *)
input wire [0 : 0] m_sc_recv;
(* X_INTERFACE_INFO = "xilinx.com:interface:sc:1.0 M_SC SEND" *)
output wire [0 : 0] m_sc_send;
(* X_INTERFACE_INFO = "xilinx.com:interface:sc:1.0 M_SC REQ" *)
output wire [0 : 0] m_sc_req;
(* X_INTERFACE_INFO = "xilinx.com:interface:sc:1.0 M_SC INFO" *)
output wire [0 : 0] m_sc_info;
(* X_INTERFACE_INFO = "xilinx.com:interface:sc:1.0 M_SC PAYLD" *)
output wire [534 : 0] m_sc_payld;

  sc_node_v1_0_16_top #(
    .C_FAMILY("virtexuplusHBM"),
    .C_FIFO_IP(0),
    .C_DISABLE_IP(0),
    .C_FIFO_SIZE(9),
    .C_FIFO_TYPE(1),
    .C_FIFO_OUTPUT_REG(1),
    .C_ENABLE_PIPELINING(8'H01),
    .C_SYNCHRONIZATION_STAGES(3),
    .C_NUM_SI(2),
    .C_NUM_MI(1),
    .C_CHANNEL(0),
    .C_PAYLD_WIDTH(535),
    .C_S_NUM_BYTES_ARRAY(64'H0000004000000040),
    .C_M_NUM_BYTES_ARRAY(32'H00000040),
    .C_PRIORITY_ARB_ARRAY(2'B00),
    .C_USER_BITS_PER_BYTE(0),
    .C_ARBITER_MODE(1),
    .C_SC_ROUTE_WIDTH(2),
    .C_ID_WIDTH(4),
    .C_ADDR_WIDTH(64),
    .C_USER_WIDTH(512),
    .C_MAX_PAYLD_BYTES(64),
    .C_S_PIPELINE(0),
    .C_M_PIPELINE(0),
    .C_M_SEND_PIPELINE(0),
    .C_S_LATENCY(1),
    .C_NUM_OUTSTANDING(32),
    .C_ACLK_RELATIONSHIP(1),
    .C_ACLKEN_CONVERSION(0)
  ) inst (
    .s_sc_aclk(s_sc_aclk),
    .s_sc_aclken(1'H1),
    .s_sc_aresetn(s_sc_aresetn),
    .s_sc_req(s_sc_req),
    .s_sc_info(s_sc_info),
    .s_sc_send(s_sc_send),
    .s_sc_recv(s_sc_recv),
    .s_sc_payld(s_sc_payld),
    .m_sc_aclk(m_sc_aclk),
    .m_sc_aclken(1'H1),
    .m_sc_aresetn(m_sc_aresetn),
    .m_sc_recv(m_sc_recv),
    .m_sc_send(m_sc_send),
    .m_sc_req(m_sc_req),
    .m_sc_info(m_sc_info),
    .m_sc_payld(m_sc_payld),
    .m_axis_arb_tvalid(),
    .m_axis_arb_tready(1'H1),
    .m_axis_arb_tdata(),
    .s_axis_arb_tvalid(1'H0),
    .s_axis_arb_tready(),
    .s_axis_arb_tdata(16'B0)
  );
endmodule
