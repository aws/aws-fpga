// (c) Copyright 1995-2016 Xilinx, Inc. All rights reserved.
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

// IP VLNV: xilinx.com:ip:xdma:3.0
// IP Revision: 2

// The following must be inserted into your Verilog file for this
// core to be instantiated. Change the instance name and port connections
// (in parentheses) to your own signal names.

//----------- Begin Cut here for INSTANTIATION Template ---// INST_TAG
xdma_0 your_instance_name (
  .sys_clk(sys_clk),                                      // input wire sys_clk
  .sys_clk_gt(sys_clk_gt),                                // input wire sys_clk_gt
  .sys_rst_n(sys_rst_n),                                  // input wire sys_rst_n
  .user_lnk_up(user_lnk_up),                              // output wire user_lnk_up
  .pci_exp_txp(pci_exp_txp),                              // output wire [15 : 0] pci_exp_txp
  .pci_exp_txn(pci_exp_txn),                              // output wire [15 : 0] pci_exp_txn
  .pci_exp_rxp(pci_exp_rxp),                              // input wire [15 : 0] pci_exp_rxp
  .pci_exp_rxn(pci_exp_rxn),                              // input wire [15 : 0] pci_exp_rxn
  .axi_aclk(axi_aclk),                                    // output wire axi_aclk
  .axi_aresetn(axi_aresetn),                              // output wire axi_aresetn
  .usr_irq_req(usr_irq_req),                              // input wire [15 : 0] usr_irq_req
  .usr_irq_ack(usr_irq_ack),                              // output wire [15 : 0] usr_irq_ack
  .msi_enable(msi_enable),                                // output wire msi_enable
  .msi_vector_width(msi_vector_width),                    // output wire [2 : 0] msi_vector_width
  .m_axi_awready(m_axi_awready),                          // input wire m_axi_awready
  .m_axi_wready(m_axi_wready),                            // input wire m_axi_wready
  .m_axi_bid(m_axi_bid),                                  // input wire [4 : 0] m_axi_bid
  .m_axi_bresp(m_axi_bresp),                              // input wire [1 : 0] m_axi_bresp
  .m_axi_bvalid(m_axi_bvalid),                            // input wire m_axi_bvalid
  .m_axi_arready(m_axi_arready),                          // input wire m_axi_arready
  .m_axi_rid(m_axi_rid),                                  // input wire [4 : 0] m_axi_rid
  .m_axi_rdata(m_axi_rdata),                              // input wire [511 : 0] m_axi_rdata
  .m_axi_rresp(m_axi_rresp),                              // input wire [1 : 0] m_axi_rresp
  .m_axi_rlast(m_axi_rlast),                              // input wire m_axi_rlast
  .m_axi_rvalid(m_axi_rvalid),                            // input wire m_axi_rvalid
  .m_axi_awid(m_axi_awid),                                // output wire [4 : 0] m_axi_awid
  .m_axi_awaddr(m_axi_awaddr),                            // output wire [63 : 0] m_axi_awaddr
  .m_axi_awlen(m_axi_awlen),                              // output wire [7 : 0] m_axi_awlen
  .m_axi_awsize(m_axi_awsize),                            // output wire [2 : 0] m_axi_awsize
  .m_axi_awburst(m_axi_awburst),                          // output wire [1 : 0] m_axi_awburst
  .m_axi_awprot(m_axi_awprot),                            // output wire [2 : 0] m_axi_awprot
  .m_axi_awvalid(m_axi_awvalid),                          // output wire m_axi_awvalid
  .m_axi_awlock(m_axi_awlock),                            // output wire m_axi_awlock
  .m_axi_awcache(m_axi_awcache),                          // output wire [3 : 0] m_axi_awcache
  .m_axi_wdata(m_axi_wdata),                              // output wire [511 : 0] m_axi_wdata
  .m_axi_wstrb(m_axi_wstrb),                              // output wire [63 : 0] m_axi_wstrb
  .m_axi_wlast(m_axi_wlast),                              // output wire m_axi_wlast
  .m_axi_wvalid(m_axi_wvalid),                            // output wire m_axi_wvalid
  .m_axi_bready(m_axi_bready),                            // output wire m_axi_bready
  .m_axi_arid(m_axi_arid),                                // output wire [4 : 0] m_axi_arid
  .m_axi_araddr(m_axi_araddr),                            // output wire [63 : 0] m_axi_araddr
  .m_axi_arlen(m_axi_arlen),                              // output wire [7 : 0] m_axi_arlen
  .m_axi_arsize(m_axi_arsize),                            // output wire [2 : 0] m_axi_arsize
  .m_axi_arburst(m_axi_arburst),                          // output wire [1 : 0] m_axi_arburst
  .m_axi_arprot(m_axi_arprot),                            // output wire [2 : 0] m_axi_arprot
  .m_axi_arvalid(m_axi_arvalid),                          // output wire m_axi_arvalid
  .m_axi_arlock(m_axi_arlock),                            // output wire m_axi_arlock
  .m_axi_arcache(m_axi_arcache),                          // output wire [3 : 0] m_axi_arcache
  .m_axi_rready(m_axi_rready),                            // output wire m_axi_rready
  .m_axil_awaddr(m_axil_awaddr),                          // output wire [31 : 0] m_axil_awaddr
  .m_axil_awuser(m_axil_awuser),                          // output wire [10 : 0] m_axil_awuser
  .m_axil_awprot(m_axil_awprot),                          // output wire [2 : 0] m_axil_awprot
  .m_axil_awvalid(m_axil_awvalid),                        // output wire m_axil_awvalid
  .m_axil_awready(m_axil_awready),                        // input wire m_axil_awready
  .m_axil_wdata(m_axil_wdata),                            // output wire [31 : 0] m_axil_wdata
  .m_axil_wstrb(m_axil_wstrb),                            // output wire [3 : 0] m_axil_wstrb
  .m_axil_wvalid(m_axil_wvalid),                          // output wire m_axil_wvalid
  .m_axil_wready(m_axil_wready),                          // input wire m_axil_wready
  .m_axil_bvalid(m_axil_bvalid),                          // input wire m_axil_bvalid
  .m_axil_bresp(m_axil_bresp),                            // input wire [1 : 0] m_axil_bresp
  .m_axil_bready(m_axil_bready),                          // output wire m_axil_bready
  .m_axil_araddr(m_axil_araddr),                          // output wire [31 : 0] m_axil_araddr
  .m_axil_aruser(m_axil_aruser),                          // output wire [10 : 0] m_axil_aruser
  .m_axil_arprot(m_axil_arprot),                          // output wire [2 : 0] m_axil_arprot
  .m_axil_arvalid(m_axil_arvalid),                        // output wire m_axil_arvalid
  .m_axil_arready(m_axil_arready),                        // input wire m_axil_arready
  .m_axil_rdata(m_axil_rdata),                            // input wire [31 : 0] m_axil_rdata
  .m_axil_rresp(m_axil_rresp),                            // input wire [1 : 0] m_axil_rresp
  .m_axil_rvalid(m_axil_rvalid),                          // input wire m_axil_rvalid
  .m_axil_rready(m_axil_rready),                          // output wire m_axil_rready
  .cfg_mgmt_addr(cfg_mgmt_addr),                          // input wire [18 : 0] cfg_mgmt_addr
  .cfg_mgmt_write(cfg_mgmt_write),                        // input wire cfg_mgmt_write
  .cfg_mgmt_write_data(cfg_mgmt_write_data),              // input wire [31 : 0] cfg_mgmt_write_data
  .cfg_mgmt_byte_enable(cfg_mgmt_byte_enable),            // input wire [3 : 0] cfg_mgmt_byte_enable
  .cfg_mgmt_read(cfg_mgmt_read),                          // input wire cfg_mgmt_read
  .cfg_mgmt_read_data(cfg_mgmt_read_data),                // output wire [31 : 0] cfg_mgmt_read_data
  .cfg_mgmt_read_write_done(cfg_mgmt_read_write_done),    // output wire cfg_mgmt_read_write_done
  .drp_rdy(drp_rdy),                                      // output wire drp_rdy
  .drp_do(drp_do),                                        // output wire [15 : 0] drp_do
  .drp_clk(drp_clk),                                      // input wire drp_clk
  .drp_en(drp_en),                                        // input wire drp_en
  .drp_we(drp_we),                                        // input wire drp_we
  .drp_addr(drp_addr),                                    // input wire [10 : 0] drp_addr
  .drp_di(drp_di),                                        // input wire [15 : 0] drp_di
  .m_axib_awid(m_axib_awid),                              // output wire [4 : 0] m_axib_awid
  .m_axib_awaddr(m_axib_awaddr),                          // output wire [63 : 0] m_axib_awaddr
  .m_axib_awlen(m_axib_awlen),                            // output wire [7 : 0] m_axib_awlen
  .m_axib_awuser(m_axib_awuser),                          // output wire [7 : 0] m_axib_awuser
  .m_axib_awsize(m_axib_awsize),                          // output wire [2 : 0] m_axib_awsize
  .m_axib_awburst(m_axib_awburst),                        // output wire [1 : 0] m_axib_awburst
  .m_axib_awprot(m_axib_awprot),                          // output wire [2 : 0] m_axib_awprot
  .m_axib_awvalid(m_axib_awvalid),                        // output wire m_axib_awvalid
  .m_axib_awready(m_axib_awready),                        // input wire m_axib_awready
  .m_axib_awlock(m_axib_awlock),                          // output wire m_axib_awlock
  .m_axib_awcache(m_axib_awcache),                        // output wire [3 : 0] m_axib_awcache
  .m_axib_wdata(m_axib_wdata),                            // output wire [511 : 0] m_axib_wdata
  .m_axib_wstrb(m_axib_wstrb),                            // output wire [63 : 0] m_axib_wstrb
  .m_axib_wlast(m_axib_wlast),                            // output wire m_axib_wlast
  .m_axib_wvalid(m_axib_wvalid),                          // output wire m_axib_wvalid
  .m_axib_wready(m_axib_wready),                          // input wire m_axib_wready
  .m_axib_bid(m_axib_bid),                                // input wire [4 : 0] m_axib_bid
  .m_axib_bresp(m_axib_bresp),                            // input wire [1 : 0] m_axib_bresp
  .m_axib_bvalid(m_axib_bvalid),                          // input wire m_axib_bvalid
  .m_axib_bready(m_axib_bready),                          // output wire m_axib_bready
  .m_axib_arid(m_axib_arid),                              // output wire [4 : 0] m_axib_arid
  .m_axib_araddr(m_axib_araddr),                          // output wire [63 : 0] m_axib_araddr
  .m_axib_arlen(m_axib_arlen),                            // output wire [7 : 0] m_axib_arlen
  .m_axib_aruser(m_axib_aruser),                          // output wire [7 : 0] m_axib_aruser
  .m_axib_arsize(m_axib_arsize),                          // output wire [2 : 0] m_axib_arsize
  .m_axib_arburst(m_axib_arburst),                        // output wire [1 : 0] m_axib_arburst
  .m_axib_arprot(m_axib_arprot),                          // output wire [2 : 0] m_axib_arprot
  .m_axib_arvalid(m_axib_arvalid),                        // output wire m_axib_arvalid
  .m_axib_arready(m_axib_arready),                        // input wire m_axib_arready
  .m_axib_arlock(m_axib_arlock),                          // output wire m_axib_arlock
  .m_axib_arcache(m_axib_arcache),                        // output wire [3 : 0] m_axib_arcache
  .m_axib_rid(m_axib_rid),                                // input wire [4 : 0] m_axib_rid
  .m_axib_rdata(m_axib_rdata),                            // input wire [511 : 0] m_axib_rdata
  .m_axib_rresp(m_axib_rresp),                            // input wire [1 : 0] m_axib_rresp
  .m_axib_rlast(m_axib_rlast),                            // input wire m_axib_rlast
  .m_axib_rvalid(m_axib_rvalid),                          // input wire m_axib_rvalid
  .m_axib_rready(m_axib_rready),                          // output wire m_axib_rready
  .s_axil_awaddr(s_axil_awaddr),                          // input wire [31 : 0] s_axil_awaddr
  .s_axil_awprot(s_axil_awprot),                          // input wire [2 : 0] s_axil_awprot
  .s_axil_awvalid(s_axil_awvalid),                        // input wire s_axil_awvalid
  .s_axil_awready(s_axil_awready),                        // output wire s_axil_awready
  .s_axil_wdata(s_axil_wdata),                            // input wire [31 : 0] s_axil_wdata
  .s_axil_wstrb(s_axil_wstrb),                            // input wire [3 : 0] s_axil_wstrb
  .s_axil_wvalid(s_axil_wvalid),                          // input wire s_axil_wvalid
  .s_axil_wready(s_axil_wready),                          // output wire s_axil_wready
  .s_axil_bvalid(s_axil_bvalid),                          // output wire s_axil_bvalid
  .s_axil_bresp(s_axil_bresp),                            // output wire [1 : 0] s_axil_bresp
  .s_axil_bready(s_axil_bready),                          // input wire s_axil_bready
  .s_axil_araddr(s_axil_araddr),                          // input wire [31 : 0] s_axil_araddr
  .s_axil_arprot(s_axil_arprot),                          // input wire [2 : 0] s_axil_arprot
  .s_axil_arvalid(s_axil_arvalid),                        // input wire s_axil_arvalid
  .s_axil_arready(s_axil_arready),                        // output wire s_axil_arready
  .s_axil_rdata(s_axil_rdata),                            // output wire [31 : 0] s_axil_rdata
  .s_axil_rresp(s_axil_rresp),                            // output wire [1 : 0] s_axil_rresp
  .s_axil_rvalid(s_axil_rvalid),                          // output wire s_axil_rvalid
  .s_axil_rready(s_axil_rready),                          // input wire s_axil_rready
  .c2h_sts_0(c2h_sts_0),                                  // output wire [7 : 0] c2h_sts_0
  .h2c_sts_0(h2c_sts_0),                                  // output wire [7 : 0] h2c_sts_0
  .c2h_sts_1(c2h_sts_1),                                  // output wire [7 : 0] c2h_sts_1
  .h2c_sts_1(h2c_sts_1),                                  // output wire [7 : 0] h2c_sts_1
  .c2h_sts_2(c2h_sts_2),                                  // output wire [7 : 0] c2h_sts_2
  .h2c_sts_2(h2c_sts_2),                                  // output wire [7 : 0] h2c_sts_2
  .c2h_sts_3(c2h_sts_3),                                  // output wire [7 : 0] c2h_sts_3
  .h2c_sts_3(h2c_sts_3),                                  // output wire [7 : 0] h2c_sts_3
  .gt_pcieuserratedone(gt_pcieuserratedone),              // input wire [15 : 0] gt_pcieuserratedone
  .gt_loopback(gt_loopback),                              // input wire [47 : 0] gt_loopback
  .gt_txprbsforceerr(gt_txprbsforceerr),                  // input wire [15 : 0] gt_txprbsforceerr
  .gt_txinhibit(gt_txinhibit),                            // input wire [15 : 0] gt_txinhibit
  .gt_txprbssel(gt_txprbssel),                            // input wire [63 : 0] gt_txprbssel
  .gt_rxprbssel(gt_rxprbssel),                            // input wire [63 : 0] gt_rxprbssel
  .gt_rxprbscntreset(gt_rxprbscntreset),                  // input wire [15 : 0] gt_rxprbscntreset
  .gt_txelecidle(gt_txelecidle),                          // output wire [15 : 0] gt_txelecidle
  .gt_txresetdone(gt_txresetdone),                        // output wire [15 : 0] gt_txresetdone
  .gt_rxresetdone(gt_rxresetdone),                        // output wire [15 : 0] gt_rxresetdone
  .gt_rxpmaresetdone(gt_rxpmaresetdone),                  // output wire [15 : 0] gt_rxpmaresetdone
  .gt_txphaligndone(gt_txphaligndone),                    // output wire [15 : 0] gt_txphaligndone
  .gt_txphinitdone(gt_txphinitdone),                      // output wire [15 : 0] gt_txphinitdone
  .gt_txdlysresetdone(gt_txdlysresetdone),                // output wire [15 : 0] gt_txdlysresetdone
  .gt_rxphaligndone(gt_rxphaligndone),                    // output wire [15 : 0] gt_rxphaligndone
  .gt_rxdlysresetdone(gt_rxdlysresetdone),                // output wire [15 : 0] gt_rxdlysresetdone
  .gt_rxsyncdone(gt_rxsyncdone),                          // output wire [15 : 0] gt_rxsyncdone
  .gt_eyescandataerror(gt_eyescandataerror),              // output wire [15 : 0] gt_eyescandataerror
  .gt_rxprbserr(gt_rxprbserr),                            // output wire [15 : 0] gt_rxprbserr
  .gt_dmonfiforeset(gt_dmonfiforeset),                    // input wire [15 : 0] gt_dmonfiforeset
  .gt_dmonitorclk(gt_dmonitorclk),                        // input wire [15 : 0] gt_dmonitorclk
  .gt_dmonitorout(gt_dmonitorout),                        // output wire [271 : 0] gt_dmonitorout
  .gt_rxcommadet(gt_rxcommadet),                          // output wire [15 : 0] gt_rxcommadet
  .gt_phystatus(gt_phystatus),                            // output wire [15 : 0] gt_phystatus
  .gt_rxvalid(gt_rxvalid),                                // output wire [15 : 0] gt_rxvalid
  .gt_rxcdrlock(gt_rxcdrlock),                            // output wire [15 : 0] gt_rxcdrlock
  .gt_pcierateidle(gt_pcierateidle),                      // output wire [15 : 0] gt_pcierateidle
  .gt_pcieuserratestart(gt_pcieuserratestart),            // output wire [15 : 0] gt_pcieuserratestart
  .gt_gtpowergood(gt_gtpowergood),                        // output wire [15 : 0] gt_gtpowergood
  .gt_cplllock(gt_cplllock),                              // output wire [15 : 0] gt_cplllock
  .gt_rxoutclk(gt_rxoutclk),                              // output wire [15 : 0] gt_rxoutclk
  .gt_rxrecclkout(gt_rxrecclkout),                        // output wire [15 : 0] gt_rxrecclkout
  .gt_qpll1lock(gt_qpll1lock),                            // output wire [2 : 0] gt_qpll1lock
  .gt_rxstatus(gt_rxstatus),                              // output wire [47 : 0] gt_rxstatus
  .gt_rxbufstatus(gt_rxbufstatus),                        // output wire [47 : 0] gt_rxbufstatus
  .gt_bufgtdiv(gt_bufgtdiv),                              // output wire [8 : 0] gt_bufgtdiv
  .phy_txeq_ctrl(phy_txeq_ctrl),                          // output wire [31 : 0] phy_txeq_ctrl
  .phy_txeq_preset(phy_txeq_preset),                      // output wire [63 : 0] phy_txeq_preset
  .phy_rst_fsm(phy_rst_fsm),                              // output wire [3 : 0] phy_rst_fsm
  .phy_txeq_fsm(phy_txeq_fsm),                            // output wire [47 : 0] phy_txeq_fsm
  .phy_rxeq_fsm(phy_rxeq_fsm),                            // output wire [47 : 0] phy_rxeq_fsm
  .phy_rst_idle(phy_rst_idle),                            // output wire phy_rst_idle
  .phy_rrst_n(phy_rrst_n),                                // output wire phy_rrst_n
  .phy_prst_n(phy_prst_n),                                // output wire phy_prst_n
  .cfg_ext_read_received(cfg_ext_read_received),          // output wire cfg_ext_read_received
  .cfg_ext_write_received(cfg_ext_write_received),        // output wire cfg_ext_write_received
  .cfg_ext_register_number(cfg_ext_register_number),      // output wire [9 : 0] cfg_ext_register_number
  .cfg_ext_function_number(cfg_ext_function_number),      // output wire [7 : 0] cfg_ext_function_number
  .cfg_ext_write_data(cfg_ext_write_data),                // output wire [31 : 0] cfg_ext_write_data
  .cfg_ext_write_byte_enable(cfg_ext_write_byte_enable),  // output wire [3 : 0] cfg_ext_write_byte_enable
  .cfg_ext_read_data(cfg_ext_read_data),                  // input wire [31 : 0] cfg_ext_read_data
  .cfg_ext_read_data_valid(cfg_ext_read_data_valid),      // input wire cfg_ext_read_data_valid
  .gt_qpll0lock(gt_qpll0lock),                            // output wire [3 : 0] gt_qpll0lock
  .gt_gen34_eios_det(gt_gen34_eios_det),                  // output wire [15 : 0] gt_gen34_eios_det
  .gt_txoutclk(gt_txoutclk),                              // output wire [15 : 0] gt_txoutclk
  .gt_txoutclkfabric(gt_txoutclkfabric),                  // output wire [15 : 0] gt_txoutclkfabric
  .gt_rxoutclkfabric(gt_rxoutclkfabric),                  // output wire [15 : 0] gt_rxoutclkfabric
  .gt_txoutclkpcs(gt_txoutclkpcs),                        // output wire [15 : 0] gt_txoutclkpcs
  .gt_rxoutclkpcs(gt_rxoutclkpcs),                        // output wire [15 : 0] gt_rxoutclkpcs
  .gt_txpmareset(gt_txpmareset),                          // input wire [15 : 0] gt_txpmareset
  .gt_rxpmareset(gt_rxpmareset),                          // input wire [15 : 0] gt_rxpmareset
  .gt_txpcsreset(gt_txpcsreset),                          // input wire [15 : 0] gt_txpcsreset
  .gt_rxpcsreset(gt_rxpcsreset),                          // input wire [15 : 0] gt_rxpcsreset
  .gt_rxbufreset(gt_rxbufreset),                          // input wire [15 : 0] gt_rxbufreset
  .gt_rxcdrreset(gt_rxcdrreset),                          // input wire [15 : 0] gt_rxcdrreset
  .gt_rxdfelpmreset(gt_rxdfelpmreset),                    // input wire [15 : 0] gt_rxdfelpmreset
  .gt_txprogdivresetdone(gt_txprogdivresetdone),          // output wire [15 : 0] gt_txprogdivresetdone
  .gt_txpmaresetdone(gt_txpmaresetdone),                  // output wire [15 : 0] gt_txpmaresetdone
  .gt_txsyncdone(gt_txsyncdone),                          // output wire [15 : 0] gt_txsyncdone
  .gt_rxprbslocked(gt_rxprbslocked),                      // output wire [15 : 0] gt_rxprbslocked
  .pipe_tx0_rcvr_det(pipe_tx0_rcvr_det),                  // output wire pipe_tx0_rcvr_det
  .pipe_clk(pipe_clk),                                    // output wire pipe_clk
  .sys_clk_bufg(sys_clk_bufg),                            // output wire sys_clk_bufg
  .pipe_tx0_powerdown(pipe_tx0_powerdown),                // output wire [1 : 0] pipe_tx0_powerdown
  .interrupt_out(interrupt_out),                          // output wire interrupt_out
  .s_axi_awid(s_axi_awid),                                // input wire [4 : 0] s_axi_awid
  .s_axi_awaddr(s_axi_awaddr),                            // input wire [63 : 0] s_axi_awaddr
  .s_axi_awregion(s_axi_awregion),                        // input wire [3 : 0] s_axi_awregion
  .s_axi_awlen(s_axi_awlen),                              // input wire [7 : 0] s_axi_awlen
  .s_axi_awsize(s_axi_awsize),                            // input wire [2 : 0] s_axi_awsize
  .s_axi_awburst(s_axi_awburst),                          // input wire [1 : 0] s_axi_awburst
  .s_axi_awvalid(s_axi_awvalid),                          // input wire s_axi_awvalid
  .s_axi_wdata(s_axi_wdata),                              // input wire [511 : 0] s_axi_wdata
  .s_axi_wstrb(s_axi_wstrb),                              // input wire [63 : 0] s_axi_wstrb
  .s_axi_wlast(s_axi_wlast),                              // input wire s_axi_wlast
  .s_axi_wvalid(s_axi_wvalid),                            // input wire s_axi_wvalid
  .s_axi_bready(s_axi_bready),                            // input wire s_axi_bready
  .s_axi_arid(s_axi_arid),                                // input wire [4 : 0] s_axi_arid
  .s_axi_araddr(s_axi_araddr),                            // input wire [63 : 0] s_axi_araddr
  .s_axi_arregion(s_axi_arregion),                        // input wire [3 : 0] s_axi_arregion
  .s_axi_arlen(s_axi_arlen),                              // input wire [7 : 0] s_axi_arlen
  .s_axi_arsize(s_axi_arsize),                            // input wire [2 : 0] s_axi_arsize
  .s_axi_arburst(s_axi_arburst),                          // input wire [1 : 0] s_axi_arburst
  .s_axi_arvalid(s_axi_arvalid),                          // input wire s_axi_arvalid
  .s_axi_rready(s_axi_rready),                            // input wire s_axi_rready
  .s_axi_awready(s_axi_awready),                          // output wire s_axi_awready
  .s_axi_wready(s_axi_wready),                            // output wire s_axi_wready
  .s_axi_bid(s_axi_bid),                                  // output wire [4 : 0] s_axi_bid
  .s_axi_bresp(s_axi_bresp),                              // output wire [1 : 0] s_axi_bresp
  .s_axi_bvalid(s_axi_bvalid),                            // output wire s_axi_bvalid
  .s_axi_arready(s_axi_arready),                          // output wire s_axi_arready
  .s_axi_rid(s_axi_rid),                                  // output wire [4 : 0] s_axi_rid
  .s_axi_rdata(s_axi_rdata),                              // output wire [511 : 0] s_axi_rdata
  .s_axi_rresp(s_axi_rresp),                              // output wire [1 : 0] s_axi_rresp
  .s_axi_rlast(s_axi_rlast),                              // output wire s_axi_rlast
  .s_axi_rvalid(s_axi_rvalid),                            // output wire s_axi_rvalid
  .cfg_ltssm_state(cfg_ltssm_state),                      // output wire [5 : 0] cfg_ltssm_state
  .cfg_function_status(cfg_function_status),              // output wire [15 : 0] cfg_function_status
  .cfg_max_read_req(cfg_max_read_req),                    // output wire [2 : 0] cfg_max_read_req
  .cfg_max_payload(cfg_max_payload),                      // output wire [1 : 0] cfg_max_payload
  .cfg_err_uncor_in(cfg_err_uncor_in),                    // input wire cfg_err_uncor_in
  .cfg_flr_in_process(cfg_flr_in_process),                // output wire [3 : 0] cfg_flr_in_process
  .cfg_flr_done(cfg_flr_done),                            // input wire [3 : 0] cfg_flr_done
  .cfg_vf_flr_in_process(cfg_vf_flr_in_process),          // output wire [251 : 0] cfg_vf_flr_in_process
  .cfg_vf_flr_func_num(cfg_vf_flr_func_num),              // input wire [7 : 0] cfg_vf_flr_func_num
  .cfg_vf_flr_done(cfg_vf_flr_done)                      // input wire [0 : 0] cfg_vf_flr_done
);
// INST_TAG_END ------ End INSTANTIATION Template ---------

// You must compile the wrapper file xdma_0.v when simulating
// the core, xdma_0. When compiling the wrapper file, be sure to
// reference the Verilog simulation library.

