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


// IP VLNV: xilinx.com:ip:debug_bridge:1.1
// IP Revision: 1

(* X_CORE_INFO = "bd_a493,Vivado 2016.4_sdx" *)
(* CHECK_LICENSE_TYPE = "cl_debug_bridge,bd_a493,{}" *)
(* CORE_GENERATION_INFO = "cl_debug_bridge,bd_a493,{x_ipProduct=Vivado 2016.4_sdx,x_ipVendor=xilinx.com,x_ipLibrary=ip,x_ipName=debug_bridge,x_ipVersion=1.1,x_ipCoreRevision=1,x_ipLanguage=VERILOG,x_ipSimLanguage=MIXED,C_DEBUG_MODE=1,C_USE_EXT_BSCAN=true,C_USE_STARTUP_CLK=false,C_ENABLE_CLK_DIVIDER=false,C_TWO_PRIM_MODE=false,C_USER_SCAN_CHAIN=1,C_CORE_TYPE=1,C_EN_INT_SIM=1,C_DCLK_HAS_RESET=0,C_USE_BUFR=0,C_XSDB_NUM_SLAVES=0,C_CORE_MINOR_ALPHA_VER=97,C_CORE_MINOR_VER=0,C_CORE_MAJOR_VER=1,C_BUILD_REVISION=0,C_MINOR_VERSION\
=1,C_MAJOR_VERSION=14,C_FIFO_STYLE=SUBCORE,Component_Name=cl_debug_bridge,C_CLK_INPUT_FREQ_HZ=300000000,C_S_AXI_DATA_WIDTH=32,C_S_AXI_ADDR_WIDTH=5,C_TCK_CLOCK_RATIO=8,C_USE_SOFTBSCAN=1,C_DEVICE_FAMILY=0,C_IR_WIDTH=0,C_CHIP_ID=0,C_IR_ID_INSTR=0,C_IR_USER1_INSTR=0}" *)
(* DowngradeIPIdentifiedWarnings = "yes" *)
module cl_debug_bridge (
  clk,
  drck,
  shift,
  tdi,
  update,
  sel,
  tdo,
  tms,
  tck,
  runtest,
  reset,
  capture,
  bscanid
);

(* X_INTERFACE_INFO = "xilinx.com:signal:clock:1.0 CLK.clk CLK" *)
input wire clk;
input wire drck;
input wire shift;
input wire tdi;
input wire update;
input wire sel;
output wire tdo;
input wire tms;
input wire tck;
input wire runtest;
input wire reset;
input wire capture;
output wire [31 : 0] bscanid;

  bd_a493 inst (
    .clk(clk),
    .drck(drck),
    .shift(shift),
    .tdi(tdi),
    .update(update),
    .sel(sel),
    .tdo(tdo),
    .tms(tms),
    .tck(tck),
    .runtest(runtest),
    .reset(reset),
    .capture(capture),
    .bscanid(bscanid)
  );
endmodule
