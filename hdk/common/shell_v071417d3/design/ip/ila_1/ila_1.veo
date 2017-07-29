// (c) Copyright 1995-2012 Xilinx, Inc. All rights reserved.
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


// The following must be inserted into your Verilog file for this
// core to be instantiated. Change the instance name and port connections
// (in parentheses) to your own signal names.

//----------- Begin Cut here for INSTANTIATION Template ---// INST_TAG

ila_1 your_instance_name (
	.clk(clk), // input wire clk


	.probe0(WREADY), // input wire [0:0] probe0  
	.probe1( AWADDR), // input wire [63:0]  probe1 
	.probe2( BRESP), // input wire [1:0]  probe2 
	.probe3( BVALID), // input wire [0:0]  probe3 
	.probe4( BREADY), // input wire [0:0]  probe4 
	.probe5( ARADDR), // input wire [63:0]  probe5 
	.probe6( RREADY), // input wire [0:0]  probe6 
	.probe7( WVALID), // input wire [0:0]  probe7 
	.probe8( ARVALID), // input wire [0:0]  probe8 
	.probe9( ARREADY), // input wire [0:0]  probe9 
	.probe10( RDATA), // input wire [511:0]  probe10 
	.probe11( AWVALID), // input wire [0:0]  probe11 
	.probe12( AWREADY), // input wire [0:0]  probe12 
	.probe13( RRESP), // input wire [1:0]  probe13 
	.probe14( WDATA), // input wire [511:0]  probe14 
	.probe15( WSTRB), // input wire [63:0]  probe15 
	.probe16( RVALID), // input wire [0:0]  probe16 
	.probe17( ARPROT), // input wire [2:0]  probe17 
	.probe18( AWPROT), // input wire [2:0]  probe18 
	.probe19( AWID), // input wire [4:0]  probe19 
	.probe20( BID), // input wire [4:0]  probe20 
	.probe21( AWLEN), // input wire [7:0]  probe21 
	.probe22( BUSER), // input wire [0:0]  probe22 
	.probe23( AWSIZE), // input wire [2:0]  probe23 
	.probe24( AWBURST), // input wire [1:0]  probe24 
	.probe25( ARID), // input wire [4:0]  probe25 
	.probe26( AWLOCK), // input wire [0:0]  probe26 
	.probe27( ARLEN), // input wire [7:0]  probe27 
	.probe28( ARSIZE), // input wire [2:0]  probe28 
	.probe29( ARBUSRT), // input wire [1:0]  probe29 
	.probe30( ARLOCK), // input wire [0:0]  probe30 
	.probe31( ARCACHE), // input wire [3:0]  probe31 
	.probe32( AWCACHE), // input wire [3:0]  probe32 
	.probe33( ARREGION), // input wire [3:0]  probe33 
	.probe34( ARQOS), // input wire [3:0]  probe34 
	.probe35( ARUSER), // input wire [0:0]  probe35 
	.probe36( AWREGION), // input wire [3:0]  probe36 
	.probe37( AWQOS), // input wire [3:0]  probe37 
	.probe38( RID), // input wire [4:0]  probe38 
	.probe39( AWUSER), // input wire [0:0]  probe39 
	.probe40( WID), // input wire [0:0]  probe40 
	.probe41( RLAST), // input wire [0:0]  probe41 
	.probe42( RUSER), // input wire [0:0]  probe42  
	.probe43( WLAST) // input wire [0:0]  probe43
);

// INST_TAG_END ------ End INSTANTIATION Template ---------

// You must compile the wrapper file ila_1 when simulating
// the core, ila_1. When compiling the wrapper file, be sure to
// reference the Verilog simulation library.


