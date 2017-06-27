// (c) Copyright 1995-2017 Xilinx, Inc. All rights reserved.
// 
// This file contains confidential and proprietary information
// of Xilinx, Inc. and is protected under U.S. and
// international copyright and other intellectual property
// laws.
// 
// DISCLAIMER
// This disclaimer is not a license and does not grant any
// rights to the materials distributed herewith. Except as
// otherwise provided in a valid license issued to you by
// Xilinx, and to the maximum extent permitted by applicable
// law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// (2) Xilinx shall not be liable (whether in contract or tort,
// including negligence, or under any other theory of
// liability) for any loss or damage of any kind or nature
// related to, arising under or in connection with these
// materials, including for any direct, or any indirect,
// special, incidental, or consequential loss or damage
// (including loss of data, profits, goodwill, or any type of
// loss or damage suffered as a result of any action brought
// by a third party) even if such damage or loss was
// reasonably foreseeable or Xilinx had been advised of the
// possibility of the same.
// 
// CRITICAL APPLICATIONS
// Xilinx products are not designed or intended to be fail-
// safe, or for use in any application requiring fail-safe
// performance, such as life-support or safety devices or
// systems, Class III medical devices, nuclear facilities,
// applications related to the deployment of airbags, or any
// other applications that could lead to death, personal
// injury, or severe property or environmental damage
// (individually and collectively, "Critical
// Applications"). Customer assumes the sole risk and
// liability of any use of Xilinx products in Critical
// Applications, subject only to applicable laws and
// regulations governing limitations on product liability.
// 
// THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// PART OF THIS FILE AT ALL TIMES.
// 
// DO NOT MODIFY THIS FILE.


// IP VLNV: xilinx.com:ip:lut_buffer:2.0
// IP Revision: 0

`timescale 1ns/1ps

(* DowngradeIPIdentifiedWarnings = "yes" *)
module bd_a493_lut_buffer_0 (
  tdi_i,
  tms_i,
  tck_i,
  drck_i,
  sel_i,
  shift_i,
  update_i,
  capture_i,
  runtest_i,
  reset_i,
  bscanid_en_i,
  tdo_o,
  tdi_o,
  tms_o,
  tck_o,
  drck_o,
  sel_o,
  shift_o,
  update_o,
  capture_o,
  runtest_o,
  reset_o,
  bscanid_en_o,
  tdo_i
);

(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 s_bscan TDI" *)
input wire tdi_i;
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 s_bscan TMS" *)
input wire tms_i;
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 s_bscan TCK" *)
input wire tck_i;
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 s_bscan DRCK" *)
input wire drck_i;
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 s_bscan SEL" *)
input wire sel_i;
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 s_bscan SHIFT" *)
input wire shift_i;
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 s_bscan UPDATE" *)
input wire update_i;
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 s_bscan CAPTURE" *)
input wire capture_i;
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 s_bscan RUNTEST" *)
input wire runtest_i;
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 s_bscan RESET" *)
input wire reset_i;
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 s_bscan BSCANID_EN" *)
input wire bscanid_en_i;
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 s_bscan TDO" *)
output wire tdo_o;
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 m_bscan TDI" *)
output wire tdi_o;
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 m_bscan TMS" *)
output wire tms_o;
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 m_bscan TCK" *)
output wire tck_o;
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 m_bscan DRCK" *)
output wire drck_o;
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 m_bscan SEL" *)
output wire sel_o;
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 m_bscan SHIFT" *)
output wire shift_o;
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 m_bscan UPDATE" *)
output wire update_o;
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 m_bscan CAPTURE" *)
output wire capture_o;
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 m_bscan RUNTEST" *)
output wire runtest_o;
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 m_bscan RESET" *)
output wire reset_o;
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 m_bscan BSCANID_EN" *)
output wire bscanid_en_o;
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 m_bscan TDO" *)
input wire tdo_i;

  lut_buffer_v2_0_0_lut_buffer #(
    .C_EN_BSCANID_VEC(0)
  ) inst (
    .tdi_i(tdi_i),
    .tms_i(tms_i),
    .tck_i(tck_i),
    .drck_i(drck_i),
    .sel_i(sel_i),
    .shift_i(shift_i),
    .update_i(update_i),
    .capture_i(capture_i),
    .runtest_i(runtest_i),
    .reset_i(reset_i),
    .bscanid_en_i(bscanid_en_i),
    .tdo_o(tdo_o),
    .bscanid_o(),
    .tdi_o(tdi_o),
    .tms_o(tms_o),
    .tck_o(tck_o),
    .drck_o(drck_o),
    .sel_o(sel_o),
    .shift_o(shift_o),
    .update_o(update_o),
    .capture_o(capture_o),
    .runtest_o(runtest_o),
    .reset_o(reset_o),
    .bscanid_en_o(bscanid_en_o),
    .tdo_i(tdo_i),
    .bscanid_i(32'B0)
  );
endmodule
