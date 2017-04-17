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

// IP VLNV: xilinx.com:ip:ddr4:2.2
// IP Revision: 0

// The following must be inserted into your Verilog file for this
// core to be instantiated. Change the instance name and port connections
// (in parentheses) to your own signal names.

//----------- Begin Cut here for INSTANTIATION Template ---// INST_TAG
ddr4_core your_instance_name (
  .c0_init_calib_complete(c0_init_calib_complete),              // output wire c0_init_calib_complete
  .dbg_clk(dbg_clk),                                            // output wire dbg_clk
  .c0_sys_clk_p(c0_sys_clk_p),                                  // input wire c0_sys_clk_p
  .c0_sys_clk_n(c0_sys_clk_n),                                  // input wire c0_sys_clk_n
  .dbg_bus(dbg_bus),                                            // output wire [511 : 0] dbg_bus
  .c0_ddr4_adr(c0_ddr4_adr),                                    // output wire [16 : 0] c0_ddr4_adr
  .c0_ddr4_ba(c0_ddr4_ba),                                      // output wire [1 : 0] c0_ddr4_ba
  .c0_ddr4_cke(c0_ddr4_cke),                                    // output wire [0 : 0] c0_ddr4_cke
  .c0_ddr4_cs_n(c0_ddr4_cs_n),                                  // output wire [0 : 0] c0_ddr4_cs_n
  .c0_ddr4_dq(c0_ddr4_dq),                                      // inout wire [71 : 0] c0_ddr4_dq
  .c0_ddr4_dqs_c(c0_ddr4_dqs_c),                                // inout wire [17 : 0] c0_ddr4_dqs_c
  .c0_ddr4_dqs_t(c0_ddr4_dqs_t),                                // inout wire [17 : 0] c0_ddr4_dqs_t
  .c0_ddr4_odt(c0_ddr4_odt),                                    // output wire [0 : 0] c0_ddr4_odt
  .c0_ddr4_parity(c0_ddr4_parity),                              // output wire c0_ddr4_parity
  .c0_ddr4_bg(c0_ddr4_bg),                                      // output wire [1 : 0] c0_ddr4_bg
  .c0_ddr4_reset_n(c0_ddr4_reset_n),                            // output wire c0_ddr4_reset_n
  .c0_ddr4_act_n(c0_ddr4_act_n),                                // output wire c0_ddr4_act_n
  .c0_ddr4_ck_c(c0_ddr4_ck_c),                                  // output wire [0 : 0] c0_ddr4_ck_c
  .c0_ddr4_ck_t(c0_ddr4_ck_t),                                  // output wire [0 : 0] c0_ddr4_ck_t
  .c0_ddr4_ui_clk(c0_ddr4_ui_clk),                              // output wire c0_ddr4_ui_clk
  .c0_ddr4_ui_clk_sync_rst(c0_ddr4_ui_clk_sync_rst),            // output wire c0_ddr4_ui_clk_sync_rst
  .c0_ddr4_app_sref_req(c0_ddr4_app_sref_req),                  // input wire c0_ddr4_app_sref_req
  .c0_ddr4_app_sref_ack(c0_ddr4_app_sref_ack),                  // output wire c0_ddr4_app_sref_ack
  .c0_ddr4_app_restore_en(c0_ddr4_app_restore_en),              // input wire c0_ddr4_app_restore_en
  .c0_ddr4_app_restore_complete(c0_ddr4_app_restore_complete),  // input wire c0_ddr4_app_restore_complete
  .c0_ddr4_app_mem_init_skip(c0_ddr4_app_mem_init_skip),        // input wire c0_ddr4_app_mem_init_skip
  .c0_ddr4_app_xsdb_select(c0_ddr4_app_xsdb_select),            // input wire c0_ddr4_app_xsdb_select
  .c0_ddr4_app_xsdb_rd_en(c0_ddr4_app_xsdb_rd_en),              // input wire c0_ddr4_app_xsdb_rd_en
  .c0_ddr4_app_xsdb_wr_en(c0_ddr4_app_xsdb_wr_en),              // input wire c0_ddr4_app_xsdb_wr_en
  .c0_ddr4_app_xsdb_addr(c0_ddr4_app_xsdb_addr),                // input wire [15 : 0] c0_ddr4_app_xsdb_addr
  .c0_ddr4_app_xsdb_wr_data(c0_ddr4_app_xsdb_wr_data),          // input wire [8 : 0] c0_ddr4_app_xsdb_wr_data
  .c0_ddr4_app_xsdb_rd_data(c0_ddr4_app_xsdb_rd_data),          // output wire [8 : 0] c0_ddr4_app_xsdb_rd_data
  .c0_ddr4_app_xsdb_rdy(c0_ddr4_app_xsdb_rdy),                  // output wire c0_ddr4_app_xsdb_rdy
  .c0_ddr4_app_dbg_out(c0_ddr4_app_dbg_out),                    // output wire [31 : 0] c0_ddr4_app_dbg_out
  .c0_ddr4_aresetn(c0_ddr4_aresetn),                            // input wire c0_ddr4_aresetn
  .c0_ddr4_s_axi_ctrl_awvalid(c0_ddr4_s_axi_ctrl_awvalid),      // input wire c0_ddr4_s_axi_ctrl_awvalid
  .c0_ddr4_s_axi_ctrl_awready(c0_ddr4_s_axi_ctrl_awready),      // output wire c0_ddr4_s_axi_ctrl_awready
  .c0_ddr4_s_axi_ctrl_awaddr(c0_ddr4_s_axi_ctrl_awaddr),        // input wire [31 : 0] c0_ddr4_s_axi_ctrl_awaddr
  .c0_ddr4_s_axi_ctrl_wvalid(c0_ddr4_s_axi_ctrl_wvalid),        // input wire c0_ddr4_s_axi_ctrl_wvalid
  .c0_ddr4_s_axi_ctrl_wready(c0_ddr4_s_axi_ctrl_wready),        // output wire c0_ddr4_s_axi_ctrl_wready
  .c0_ddr4_s_axi_ctrl_wdata(c0_ddr4_s_axi_ctrl_wdata),          // input wire [31 : 0] c0_ddr4_s_axi_ctrl_wdata
  .c0_ddr4_s_axi_ctrl_bvalid(c0_ddr4_s_axi_ctrl_bvalid),        // output wire c0_ddr4_s_axi_ctrl_bvalid
  .c0_ddr4_s_axi_ctrl_bready(c0_ddr4_s_axi_ctrl_bready),        // input wire c0_ddr4_s_axi_ctrl_bready
  .c0_ddr4_s_axi_ctrl_bresp(c0_ddr4_s_axi_ctrl_bresp),          // output wire [1 : 0] c0_ddr4_s_axi_ctrl_bresp
  .c0_ddr4_s_axi_ctrl_arvalid(c0_ddr4_s_axi_ctrl_arvalid),      // input wire c0_ddr4_s_axi_ctrl_arvalid
  .c0_ddr4_s_axi_ctrl_arready(c0_ddr4_s_axi_ctrl_arready),      // output wire c0_ddr4_s_axi_ctrl_arready
  .c0_ddr4_s_axi_ctrl_araddr(c0_ddr4_s_axi_ctrl_araddr),        // input wire [31 : 0] c0_ddr4_s_axi_ctrl_araddr
  .c0_ddr4_s_axi_ctrl_rvalid(c0_ddr4_s_axi_ctrl_rvalid),        // output wire c0_ddr4_s_axi_ctrl_rvalid
  .c0_ddr4_s_axi_ctrl_rready(c0_ddr4_s_axi_ctrl_rready),        // input wire c0_ddr4_s_axi_ctrl_rready
  .c0_ddr4_s_axi_ctrl_rdata(c0_ddr4_s_axi_ctrl_rdata),          // output wire [31 : 0] c0_ddr4_s_axi_ctrl_rdata
  .c0_ddr4_s_axi_ctrl_rresp(c0_ddr4_s_axi_ctrl_rresp),          // output wire [1 : 0] c0_ddr4_s_axi_ctrl_rresp
  .c0_ddr4_interrupt(c0_ddr4_interrupt),                        // output wire c0_ddr4_interrupt
  .c0_ddr4_s_axi_awid(c0_ddr4_s_axi_awid),                      // input wire [15 : 0] c0_ddr4_s_axi_awid
  .c0_ddr4_s_axi_awaddr(c0_ddr4_s_axi_awaddr),                  // input wire [33 : 0] c0_ddr4_s_axi_awaddr
  .c0_ddr4_s_axi_awlen(c0_ddr4_s_axi_awlen),                    // input wire [7 : 0] c0_ddr4_s_axi_awlen
  .c0_ddr4_s_axi_awsize(c0_ddr4_s_axi_awsize),                  // input wire [2 : 0] c0_ddr4_s_axi_awsize
  .c0_ddr4_s_axi_awburst(c0_ddr4_s_axi_awburst),                // input wire [1 : 0] c0_ddr4_s_axi_awburst
  .c0_ddr4_s_axi_awlock(c0_ddr4_s_axi_awlock),                  // input wire [0 : 0] c0_ddr4_s_axi_awlock
  .c0_ddr4_s_axi_awcache(c0_ddr4_s_axi_awcache),                // input wire [3 : 0] c0_ddr4_s_axi_awcache
  .c0_ddr4_s_axi_awprot(c0_ddr4_s_axi_awprot),                  // input wire [2 : 0] c0_ddr4_s_axi_awprot
  .c0_ddr4_s_axi_awqos(c0_ddr4_s_axi_awqos),                    // input wire [3 : 0] c0_ddr4_s_axi_awqos
  .c0_ddr4_s_axi_awvalid(c0_ddr4_s_axi_awvalid),                // input wire c0_ddr4_s_axi_awvalid
  .c0_ddr4_s_axi_awready(c0_ddr4_s_axi_awready),                // output wire c0_ddr4_s_axi_awready
  .c0_ddr4_s_axi_wdata(c0_ddr4_s_axi_wdata),                    // input wire [511 : 0] c0_ddr4_s_axi_wdata
  .c0_ddr4_s_axi_wstrb(c0_ddr4_s_axi_wstrb),                    // input wire [63 : 0] c0_ddr4_s_axi_wstrb
  .c0_ddr4_s_axi_wlast(c0_ddr4_s_axi_wlast),                    // input wire c0_ddr4_s_axi_wlast
  .c0_ddr4_s_axi_wvalid(c0_ddr4_s_axi_wvalid),                  // input wire c0_ddr4_s_axi_wvalid
  .c0_ddr4_s_axi_wready(c0_ddr4_s_axi_wready),                  // output wire c0_ddr4_s_axi_wready
  .c0_ddr4_s_axi_bready(c0_ddr4_s_axi_bready),                  // input wire c0_ddr4_s_axi_bready
  .c0_ddr4_s_axi_bid(c0_ddr4_s_axi_bid),                        // output wire [15 : 0] c0_ddr4_s_axi_bid
  .c0_ddr4_s_axi_bresp(c0_ddr4_s_axi_bresp),                    // output wire [1 : 0] c0_ddr4_s_axi_bresp
  .c0_ddr4_s_axi_bvalid(c0_ddr4_s_axi_bvalid),                  // output wire c0_ddr4_s_axi_bvalid
  .c0_ddr4_s_axi_arid(c0_ddr4_s_axi_arid),                      // input wire [15 : 0] c0_ddr4_s_axi_arid
  .c0_ddr4_s_axi_araddr(c0_ddr4_s_axi_araddr),                  // input wire [33 : 0] c0_ddr4_s_axi_araddr
  .c0_ddr4_s_axi_arlen(c0_ddr4_s_axi_arlen),                    // input wire [7 : 0] c0_ddr4_s_axi_arlen
  .c0_ddr4_s_axi_arsize(c0_ddr4_s_axi_arsize),                  // input wire [2 : 0] c0_ddr4_s_axi_arsize
  .c0_ddr4_s_axi_arburst(c0_ddr4_s_axi_arburst),                // input wire [1 : 0] c0_ddr4_s_axi_arburst
  .c0_ddr4_s_axi_arlock(c0_ddr4_s_axi_arlock),                  // input wire [0 : 0] c0_ddr4_s_axi_arlock
  .c0_ddr4_s_axi_arcache(c0_ddr4_s_axi_arcache),                // input wire [3 : 0] c0_ddr4_s_axi_arcache
  .c0_ddr4_s_axi_arprot(c0_ddr4_s_axi_arprot),                  // input wire [2 : 0] c0_ddr4_s_axi_arprot
  .c0_ddr4_s_axi_arqos(c0_ddr4_s_axi_arqos),                    // input wire [3 : 0] c0_ddr4_s_axi_arqos
  .c0_ddr4_s_axi_arvalid(c0_ddr4_s_axi_arvalid),                // input wire c0_ddr4_s_axi_arvalid
  .c0_ddr4_s_axi_arready(c0_ddr4_s_axi_arready),                // output wire c0_ddr4_s_axi_arready
  .c0_ddr4_s_axi_rready(c0_ddr4_s_axi_rready),                  // input wire c0_ddr4_s_axi_rready
  .c0_ddr4_s_axi_rlast(c0_ddr4_s_axi_rlast),                    // output wire c0_ddr4_s_axi_rlast
  .c0_ddr4_s_axi_rvalid(c0_ddr4_s_axi_rvalid),                  // output wire c0_ddr4_s_axi_rvalid
  .c0_ddr4_s_axi_rresp(c0_ddr4_s_axi_rresp),                    // output wire [1 : 0] c0_ddr4_s_axi_rresp
  .c0_ddr4_s_axi_rid(c0_ddr4_s_axi_rid),                        // output wire [15 : 0] c0_ddr4_s_axi_rid
  .c0_ddr4_s_axi_rdata(c0_ddr4_s_axi_rdata),                    // output wire [511 : 0] c0_ddr4_s_axi_rdata
  .sys_rst(sys_rst)                                            // input wire sys_rst
);
// INST_TAG_END ------ End INSTANTIATION Template ---------

// You must compile the wrapper file ddr4_core.v when simulating
// the core, ddr4_core. When compiling the wrapper file, be sure to
// reference the Verilog simulation library.

