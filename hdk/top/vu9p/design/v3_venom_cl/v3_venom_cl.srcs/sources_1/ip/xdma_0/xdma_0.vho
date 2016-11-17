-- (c) Copyright 1995-2016 Xilinx, Inc. All rights reserved.
-- 
-- This file contains confidential and proprietary information
-- of Xilinx, Inc. and is protected under U.S. and
-- international copyright and other intellectual property
-- laws.
-- 
-- DISCLAIMER
-- This disclaimer is not a license and does not grant any
-- rights to the materials distributed herewith. Except as
-- otherwise provided in a valid license issued to you by
-- Xilinx, and to the maximum extent permitted by applicable
-- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
-- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
-- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
-- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
-- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
-- (2) Xilinx shall not be liable (whether in contract or tort,
-- including negligence, or under any other theory of
-- liability) for any loss or damage of any kind or nature
-- related to, arising under or in connection with these
-- materials, including for any direct, or any indirect,
-- special, incidental, or consequential loss or damage
-- (including loss of data, profits, goodwill, or any type of
-- loss or damage suffered as a result of any action brought
-- by a third party) even if such damage or loss was
-- reasonably foreseeable or Xilinx had been advised of the
-- possibility of the same.
-- 
-- CRITICAL APPLICATIONS
-- Xilinx products are not designed or intended to be fail-
-- safe, or for use in any application requiring fail-safe
-- performance, such as life-support or safety devices or
-- systems, Class III medical devices, nuclear facilities,
-- applications related to the deployment of airbags, or any
-- other applications that could lead to death, personal
-- injury, or severe property or environmental damage
-- (individually and collectively, "Critical
-- Applications"). Customer assumes the sole risk and
-- liability of any use of Xilinx products in Critical
-- Applications, subject only to applicable laws and
-- regulations governing limitations on product liability.
-- 
-- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
-- PART OF THIS FILE AT ALL TIMES.
-- 
-- DO NOT MODIFY THIS FILE.

-- IP VLNV: xilinx.com:ip:xdma:3.0
-- IP Revision: 2

-- The following code must appear in the VHDL architecture header.

------------- Begin Cut here for COMPONENT Declaration ------ COMP_TAG
COMPONENT xdma_0
  PORT (
    sys_clk : IN STD_LOGIC;
    sys_clk_gt : IN STD_LOGIC;
    sys_rst_n : IN STD_LOGIC;
    user_lnk_up : OUT STD_LOGIC;
    pci_exp_txp : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    pci_exp_txn : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    pci_exp_rxp : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
    pci_exp_rxn : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
    axi_aclk : OUT STD_LOGIC;
    axi_aresetn : OUT STD_LOGIC;
    usr_irq_req : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
    usr_irq_ack : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    msi_enable : OUT STD_LOGIC;
    msi_vector_width : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
    m_axi_awready : IN STD_LOGIC;
    m_axi_wready : IN STD_LOGIC;
    m_axi_bid : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
    m_axi_bresp : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
    m_axi_bvalid : IN STD_LOGIC;
    m_axi_arready : IN STD_LOGIC;
    m_axi_rid : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
    m_axi_rdata : IN STD_LOGIC_VECTOR(511 DOWNTO 0);
    m_axi_rresp : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
    m_axi_rlast : IN STD_LOGIC;
    m_axi_rvalid : IN STD_LOGIC;
    m_axi_awid : OUT STD_LOGIC_VECTOR(4 DOWNTO 0);
    m_axi_awaddr : OUT STD_LOGIC_VECTOR(63 DOWNTO 0);
    m_axi_awlen : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
    m_axi_awsize : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
    m_axi_awburst : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
    m_axi_awprot : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
    m_axi_awvalid : OUT STD_LOGIC;
    m_axi_awlock : OUT STD_LOGIC;
    m_axi_awcache : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
    m_axi_wdata : OUT STD_LOGIC_VECTOR(511 DOWNTO 0);
    m_axi_wstrb : OUT STD_LOGIC_VECTOR(63 DOWNTO 0);
    m_axi_wlast : OUT STD_LOGIC;
    m_axi_wvalid : OUT STD_LOGIC;
    m_axi_bready : OUT STD_LOGIC;
    m_axi_arid : OUT STD_LOGIC_VECTOR(4 DOWNTO 0);
    m_axi_araddr : OUT STD_LOGIC_VECTOR(63 DOWNTO 0);
    m_axi_arlen : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
    m_axi_arsize : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
    m_axi_arburst : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
    m_axi_arprot : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
    m_axi_arvalid : OUT STD_LOGIC;
    m_axi_arlock : OUT STD_LOGIC;
    m_axi_arcache : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
    m_axi_rready : OUT STD_LOGIC;
    m_axil_awaddr : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
    m_axil_awuser : OUT STD_LOGIC_VECTOR(10 DOWNTO 0);
    m_axil_awprot : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
    m_axil_awvalid : OUT STD_LOGIC;
    m_axil_awready : IN STD_LOGIC;
    m_axil_wdata : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
    m_axil_wstrb : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
    m_axil_wvalid : OUT STD_LOGIC;
    m_axil_wready : IN STD_LOGIC;
    m_axil_bvalid : IN STD_LOGIC;
    m_axil_bresp : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
    m_axil_bready : OUT STD_LOGIC;
    m_axil_araddr : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
    m_axil_aruser : OUT STD_LOGIC_VECTOR(10 DOWNTO 0);
    m_axil_arprot : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
    m_axil_arvalid : OUT STD_LOGIC;
    m_axil_arready : IN STD_LOGIC;
    m_axil_rdata : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
    m_axil_rresp : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
    m_axil_rvalid : IN STD_LOGIC;
    m_axil_rready : OUT STD_LOGIC;
    cfg_mgmt_addr : IN STD_LOGIC_VECTOR(18 DOWNTO 0);
    cfg_mgmt_write : IN STD_LOGIC;
    cfg_mgmt_write_data : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
    cfg_mgmt_byte_enable : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
    cfg_mgmt_read : IN STD_LOGIC;
    cfg_mgmt_read_data : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
    cfg_mgmt_read_write_done : OUT STD_LOGIC;
    drp_rdy : OUT STD_LOGIC;
    drp_do : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    drp_clk : IN STD_LOGIC;
    drp_en : IN STD_LOGIC;
    drp_we : IN STD_LOGIC;
    drp_addr : IN STD_LOGIC_VECTOR(10 DOWNTO 0);
    drp_di : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
    m_axib_awid : OUT STD_LOGIC_VECTOR(4 DOWNTO 0);
    m_axib_awaddr : OUT STD_LOGIC_VECTOR(63 DOWNTO 0);
    m_axib_awlen : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
    m_axib_awuser : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
    m_axib_awsize : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
    m_axib_awburst : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
    m_axib_awprot : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
    m_axib_awvalid : OUT STD_LOGIC;
    m_axib_awready : IN STD_LOGIC;
    m_axib_awlock : OUT STD_LOGIC;
    m_axib_awcache : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
    m_axib_wdata : OUT STD_LOGIC_VECTOR(511 DOWNTO 0);
    m_axib_wstrb : OUT STD_LOGIC_VECTOR(63 DOWNTO 0);
    m_axib_wlast : OUT STD_LOGIC;
    m_axib_wvalid : OUT STD_LOGIC;
    m_axib_wready : IN STD_LOGIC;
    m_axib_bid : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
    m_axib_bresp : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
    m_axib_bvalid : IN STD_LOGIC;
    m_axib_bready : OUT STD_LOGIC;
    m_axib_arid : OUT STD_LOGIC_VECTOR(4 DOWNTO 0);
    m_axib_araddr : OUT STD_LOGIC_VECTOR(63 DOWNTO 0);
    m_axib_arlen : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
    m_axib_aruser : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
    m_axib_arsize : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
    m_axib_arburst : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
    m_axib_arprot : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
    m_axib_arvalid : OUT STD_LOGIC;
    m_axib_arready : IN STD_LOGIC;
    m_axib_arlock : OUT STD_LOGIC;
    m_axib_arcache : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
    m_axib_rid : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
    m_axib_rdata : IN STD_LOGIC_VECTOR(511 DOWNTO 0);
    m_axib_rresp : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
    m_axib_rlast : IN STD_LOGIC;
    m_axib_rvalid : IN STD_LOGIC;
    m_axib_rready : OUT STD_LOGIC;
    s_axil_awaddr : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
    s_axil_awprot : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
    s_axil_awvalid : IN STD_LOGIC;
    s_axil_awready : OUT STD_LOGIC;
    s_axil_wdata : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
    s_axil_wstrb : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
    s_axil_wvalid : IN STD_LOGIC;
    s_axil_wready : OUT STD_LOGIC;
    s_axil_bvalid : OUT STD_LOGIC;
    s_axil_bresp : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
    s_axil_bready : IN STD_LOGIC;
    s_axil_araddr : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
    s_axil_arprot : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
    s_axil_arvalid : IN STD_LOGIC;
    s_axil_arready : OUT STD_LOGIC;
    s_axil_rdata : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
    s_axil_rresp : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
    s_axil_rvalid : OUT STD_LOGIC;
    s_axil_rready : IN STD_LOGIC;
    c2h_sts_0 : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
    h2c_sts_0 : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
    c2h_sts_1 : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
    h2c_sts_1 : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
    c2h_sts_2 : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
    h2c_sts_2 : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
    c2h_sts_3 : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
    h2c_sts_3 : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
    gt_pcieuserratedone : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_loopback : IN STD_LOGIC_VECTOR(47 DOWNTO 0);
    gt_txprbsforceerr : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_txinhibit : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_txprbssel : IN STD_LOGIC_VECTOR(63 DOWNTO 0);
    gt_rxprbssel : IN STD_LOGIC_VECTOR(63 DOWNTO 0);
    gt_rxprbscntreset : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_txelecidle : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_txresetdone : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_rxresetdone : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_rxpmaresetdone : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_txphaligndone : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_txphinitdone : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_txdlysresetdone : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_rxphaligndone : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_rxdlysresetdone : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_rxsyncdone : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_eyescandataerror : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_rxprbserr : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_dmonfiforeset : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_dmonitorclk : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_dmonitorout : OUT STD_LOGIC_VECTOR(271 DOWNTO 0);
    gt_rxcommadet : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_phystatus : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_rxvalid : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_rxcdrlock : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_pcierateidle : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_pcieuserratestart : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_gtpowergood : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_cplllock : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_rxoutclk : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_rxrecclkout : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_qpll1lock : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
    gt_rxstatus : OUT STD_LOGIC_VECTOR(47 DOWNTO 0);
    gt_rxbufstatus : OUT STD_LOGIC_VECTOR(47 DOWNTO 0);
    gt_bufgtdiv : OUT STD_LOGIC_VECTOR(8 DOWNTO 0);
    phy_txeq_ctrl : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
    phy_txeq_preset : OUT STD_LOGIC_VECTOR(63 DOWNTO 0);
    phy_rst_fsm : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
    phy_txeq_fsm : OUT STD_LOGIC_VECTOR(47 DOWNTO 0);
    phy_rxeq_fsm : OUT STD_LOGIC_VECTOR(47 DOWNTO 0);
    phy_rst_idle : OUT STD_LOGIC;
    phy_rrst_n : OUT STD_LOGIC;
    phy_prst_n : OUT STD_LOGIC;
    cfg_ext_read_received : OUT STD_LOGIC;
    cfg_ext_write_received : OUT STD_LOGIC;
    cfg_ext_register_number : OUT STD_LOGIC_VECTOR(9 DOWNTO 0);
    cfg_ext_function_number : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
    cfg_ext_write_data : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
    cfg_ext_write_byte_enable : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
    cfg_ext_read_data : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
    cfg_ext_read_data_valid : IN STD_LOGIC;
    gt_qpll0lock : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
    gt_gen34_eios_det : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_txoutclk : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_txoutclkfabric : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_rxoutclkfabric : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_txoutclkpcs : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_rxoutclkpcs : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_txpmareset : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_rxpmareset : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_txpcsreset : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_rxpcsreset : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_rxbufreset : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_rxcdrreset : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_rxdfelpmreset : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_txprogdivresetdone : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_txpmaresetdone : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_txsyncdone : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    gt_rxprbslocked : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    pipe_tx0_rcvr_det : OUT STD_LOGIC;
    pipe_clk : OUT STD_LOGIC;
    sys_clk_bufg : OUT STD_LOGIC;
    pipe_tx0_powerdown : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
    interrupt_out : OUT STD_LOGIC;
    s_axi_awid : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
    s_axi_awaddr : IN STD_LOGIC_VECTOR(63 DOWNTO 0);
    s_axi_awregion : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
    s_axi_awlen : IN STD_LOGIC_VECTOR(7 DOWNTO 0);
    s_axi_awsize : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
    s_axi_awburst : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
    s_axi_awvalid : IN STD_LOGIC;
    s_axi_wdata : IN STD_LOGIC_VECTOR(511 DOWNTO 0);
    s_axi_wstrb : IN STD_LOGIC_VECTOR(63 DOWNTO 0);
    s_axi_wlast : IN STD_LOGIC;
    s_axi_wvalid : IN STD_LOGIC;
    s_axi_bready : IN STD_LOGIC;
    s_axi_arid : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
    s_axi_araddr : IN STD_LOGIC_VECTOR(63 DOWNTO 0);
    s_axi_arregion : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
    s_axi_arlen : IN STD_LOGIC_VECTOR(7 DOWNTO 0);
    s_axi_arsize : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
    s_axi_arburst : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
    s_axi_arvalid : IN STD_LOGIC;
    s_axi_rready : IN STD_LOGIC;
    s_axi_awready : OUT STD_LOGIC;
    s_axi_wready : OUT STD_LOGIC;
    s_axi_bid : OUT STD_LOGIC_VECTOR(4 DOWNTO 0);
    s_axi_bresp : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
    s_axi_bvalid : OUT STD_LOGIC;
    s_axi_arready : OUT STD_LOGIC;
    s_axi_rid : OUT STD_LOGIC_VECTOR(4 DOWNTO 0);
    s_axi_rdata : OUT STD_LOGIC_VECTOR(511 DOWNTO 0);
    s_axi_rresp : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
    s_axi_rlast : OUT STD_LOGIC;
    s_axi_rvalid : OUT STD_LOGIC;
    cfg_ltssm_state : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
    cfg_function_status : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    cfg_max_read_req : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
    cfg_max_payload : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
    cfg_err_uncor_in : IN STD_LOGIC;
    cfg_flr_in_process : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
    cfg_flr_done : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
    cfg_vf_flr_in_process : OUT STD_LOGIC_VECTOR(251 DOWNTO 0);
    cfg_vf_flr_func_num : IN STD_LOGIC_VECTOR(7 DOWNTO 0);
    cfg_vf_flr_done : IN STD_LOGIC_VECTOR(0 DOWNTO 0)
  );
END COMPONENT;
-- COMP_TAG_END ------ End COMPONENT Declaration ------------

-- The following code must appear in the VHDL architecture
-- body. Substitute your own instance name and net names.

------------- Begin Cut here for INSTANTIATION Template ----- INST_TAG
your_instance_name : xdma_0
  PORT MAP (
    sys_clk => sys_clk,
    sys_clk_gt => sys_clk_gt,
    sys_rst_n => sys_rst_n,
    user_lnk_up => user_lnk_up,
    pci_exp_txp => pci_exp_txp,
    pci_exp_txn => pci_exp_txn,
    pci_exp_rxp => pci_exp_rxp,
    pci_exp_rxn => pci_exp_rxn,
    axi_aclk => axi_aclk,
    axi_aresetn => axi_aresetn,
    usr_irq_req => usr_irq_req,
    usr_irq_ack => usr_irq_ack,
    msi_enable => msi_enable,
    msi_vector_width => msi_vector_width,
    m_axi_awready => m_axi_awready,
    m_axi_wready => m_axi_wready,
    m_axi_bid => m_axi_bid,
    m_axi_bresp => m_axi_bresp,
    m_axi_bvalid => m_axi_bvalid,
    m_axi_arready => m_axi_arready,
    m_axi_rid => m_axi_rid,
    m_axi_rdata => m_axi_rdata,
    m_axi_rresp => m_axi_rresp,
    m_axi_rlast => m_axi_rlast,
    m_axi_rvalid => m_axi_rvalid,
    m_axi_awid => m_axi_awid,
    m_axi_awaddr => m_axi_awaddr,
    m_axi_awlen => m_axi_awlen,
    m_axi_awsize => m_axi_awsize,
    m_axi_awburst => m_axi_awburst,
    m_axi_awprot => m_axi_awprot,
    m_axi_awvalid => m_axi_awvalid,
    m_axi_awlock => m_axi_awlock,
    m_axi_awcache => m_axi_awcache,
    m_axi_wdata => m_axi_wdata,
    m_axi_wstrb => m_axi_wstrb,
    m_axi_wlast => m_axi_wlast,
    m_axi_wvalid => m_axi_wvalid,
    m_axi_bready => m_axi_bready,
    m_axi_arid => m_axi_arid,
    m_axi_araddr => m_axi_araddr,
    m_axi_arlen => m_axi_arlen,
    m_axi_arsize => m_axi_arsize,
    m_axi_arburst => m_axi_arburst,
    m_axi_arprot => m_axi_arprot,
    m_axi_arvalid => m_axi_arvalid,
    m_axi_arlock => m_axi_arlock,
    m_axi_arcache => m_axi_arcache,
    m_axi_rready => m_axi_rready,
    m_axil_awaddr => m_axil_awaddr,
    m_axil_awuser => m_axil_awuser,
    m_axil_awprot => m_axil_awprot,
    m_axil_awvalid => m_axil_awvalid,
    m_axil_awready => m_axil_awready,
    m_axil_wdata => m_axil_wdata,
    m_axil_wstrb => m_axil_wstrb,
    m_axil_wvalid => m_axil_wvalid,
    m_axil_wready => m_axil_wready,
    m_axil_bvalid => m_axil_bvalid,
    m_axil_bresp => m_axil_bresp,
    m_axil_bready => m_axil_bready,
    m_axil_araddr => m_axil_araddr,
    m_axil_aruser => m_axil_aruser,
    m_axil_arprot => m_axil_arprot,
    m_axil_arvalid => m_axil_arvalid,
    m_axil_arready => m_axil_arready,
    m_axil_rdata => m_axil_rdata,
    m_axil_rresp => m_axil_rresp,
    m_axil_rvalid => m_axil_rvalid,
    m_axil_rready => m_axil_rready,
    cfg_mgmt_addr => cfg_mgmt_addr,
    cfg_mgmt_write => cfg_mgmt_write,
    cfg_mgmt_write_data => cfg_mgmt_write_data,
    cfg_mgmt_byte_enable => cfg_mgmt_byte_enable,
    cfg_mgmt_read => cfg_mgmt_read,
    cfg_mgmt_read_data => cfg_mgmt_read_data,
    cfg_mgmt_read_write_done => cfg_mgmt_read_write_done,
    drp_rdy => drp_rdy,
    drp_do => drp_do,
    drp_clk => drp_clk,
    drp_en => drp_en,
    drp_we => drp_we,
    drp_addr => drp_addr,
    drp_di => drp_di,
    m_axib_awid => m_axib_awid,
    m_axib_awaddr => m_axib_awaddr,
    m_axib_awlen => m_axib_awlen,
    m_axib_awuser => m_axib_awuser,
    m_axib_awsize => m_axib_awsize,
    m_axib_awburst => m_axib_awburst,
    m_axib_awprot => m_axib_awprot,
    m_axib_awvalid => m_axib_awvalid,
    m_axib_awready => m_axib_awready,
    m_axib_awlock => m_axib_awlock,
    m_axib_awcache => m_axib_awcache,
    m_axib_wdata => m_axib_wdata,
    m_axib_wstrb => m_axib_wstrb,
    m_axib_wlast => m_axib_wlast,
    m_axib_wvalid => m_axib_wvalid,
    m_axib_wready => m_axib_wready,
    m_axib_bid => m_axib_bid,
    m_axib_bresp => m_axib_bresp,
    m_axib_bvalid => m_axib_bvalid,
    m_axib_bready => m_axib_bready,
    m_axib_arid => m_axib_arid,
    m_axib_araddr => m_axib_araddr,
    m_axib_arlen => m_axib_arlen,
    m_axib_aruser => m_axib_aruser,
    m_axib_arsize => m_axib_arsize,
    m_axib_arburst => m_axib_arburst,
    m_axib_arprot => m_axib_arprot,
    m_axib_arvalid => m_axib_arvalid,
    m_axib_arready => m_axib_arready,
    m_axib_arlock => m_axib_arlock,
    m_axib_arcache => m_axib_arcache,
    m_axib_rid => m_axib_rid,
    m_axib_rdata => m_axib_rdata,
    m_axib_rresp => m_axib_rresp,
    m_axib_rlast => m_axib_rlast,
    m_axib_rvalid => m_axib_rvalid,
    m_axib_rready => m_axib_rready,
    s_axil_awaddr => s_axil_awaddr,
    s_axil_awprot => s_axil_awprot,
    s_axil_awvalid => s_axil_awvalid,
    s_axil_awready => s_axil_awready,
    s_axil_wdata => s_axil_wdata,
    s_axil_wstrb => s_axil_wstrb,
    s_axil_wvalid => s_axil_wvalid,
    s_axil_wready => s_axil_wready,
    s_axil_bvalid => s_axil_bvalid,
    s_axil_bresp => s_axil_bresp,
    s_axil_bready => s_axil_bready,
    s_axil_araddr => s_axil_araddr,
    s_axil_arprot => s_axil_arprot,
    s_axil_arvalid => s_axil_arvalid,
    s_axil_arready => s_axil_arready,
    s_axil_rdata => s_axil_rdata,
    s_axil_rresp => s_axil_rresp,
    s_axil_rvalid => s_axil_rvalid,
    s_axil_rready => s_axil_rready,
    c2h_sts_0 => c2h_sts_0,
    h2c_sts_0 => h2c_sts_0,
    c2h_sts_1 => c2h_sts_1,
    h2c_sts_1 => h2c_sts_1,
    c2h_sts_2 => c2h_sts_2,
    h2c_sts_2 => h2c_sts_2,
    c2h_sts_3 => c2h_sts_3,
    h2c_sts_3 => h2c_sts_3,
    gt_pcieuserratedone => gt_pcieuserratedone,
    gt_loopback => gt_loopback,
    gt_txprbsforceerr => gt_txprbsforceerr,
    gt_txinhibit => gt_txinhibit,
    gt_txprbssel => gt_txprbssel,
    gt_rxprbssel => gt_rxprbssel,
    gt_rxprbscntreset => gt_rxprbscntreset,
    gt_txelecidle => gt_txelecidle,
    gt_txresetdone => gt_txresetdone,
    gt_rxresetdone => gt_rxresetdone,
    gt_rxpmaresetdone => gt_rxpmaresetdone,
    gt_txphaligndone => gt_txphaligndone,
    gt_txphinitdone => gt_txphinitdone,
    gt_txdlysresetdone => gt_txdlysresetdone,
    gt_rxphaligndone => gt_rxphaligndone,
    gt_rxdlysresetdone => gt_rxdlysresetdone,
    gt_rxsyncdone => gt_rxsyncdone,
    gt_eyescandataerror => gt_eyescandataerror,
    gt_rxprbserr => gt_rxprbserr,
    gt_dmonfiforeset => gt_dmonfiforeset,
    gt_dmonitorclk => gt_dmonitorclk,
    gt_dmonitorout => gt_dmonitorout,
    gt_rxcommadet => gt_rxcommadet,
    gt_phystatus => gt_phystatus,
    gt_rxvalid => gt_rxvalid,
    gt_rxcdrlock => gt_rxcdrlock,
    gt_pcierateidle => gt_pcierateidle,
    gt_pcieuserratestart => gt_pcieuserratestart,
    gt_gtpowergood => gt_gtpowergood,
    gt_cplllock => gt_cplllock,
    gt_rxoutclk => gt_rxoutclk,
    gt_rxrecclkout => gt_rxrecclkout,
    gt_qpll1lock => gt_qpll1lock,
    gt_rxstatus => gt_rxstatus,
    gt_rxbufstatus => gt_rxbufstatus,
    gt_bufgtdiv => gt_bufgtdiv,
    phy_txeq_ctrl => phy_txeq_ctrl,
    phy_txeq_preset => phy_txeq_preset,
    phy_rst_fsm => phy_rst_fsm,
    phy_txeq_fsm => phy_txeq_fsm,
    phy_rxeq_fsm => phy_rxeq_fsm,
    phy_rst_idle => phy_rst_idle,
    phy_rrst_n => phy_rrst_n,
    phy_prst_n => phy_prst_n,
    cfg_ext_read_received => cfg_ext_read_received,
    cfg_ext_write_received => cfg_ext_write_received,
    cfg_ext_register_number => cfg_ext_register_number,
    cfg_ext_function_number => cfg_ext_function_number,
    cfg_ext_write_data => cfg_ext_write_data,
    cfg_ext_write_byte_enable => cfg_ext_write_byte_enable,
    cfg_ext_read_data => cfg_ext_read_data,
    cfg_ext_read_data_valid => cfg_ext_read_data_valid,
    gt_qpll0lock => gt_qpll0lock,
    gt_gen34_eios_det => gt_gen34_eios_det,
    gt_txoutclk => gt_txoutclk,
    gt_txoutclkfabric => gt_txoutclkfabric,
    gt_rxoutclkfabric => gt_rxoutclkfabric,
    gt_txoutclkpcs => gt_txoutclkpcs,
    gt_rxoutclkpcs => gt_rxoutclkpcs,
    gt_txpmareset => gt_txpmareset,
    gt_rxpmareset => gt_rxpmareset,
    gt_txpcsreset => gt_txpcsreset,
    gt_rxpcsreset => gt_rxpcsreset,
    gt_rxbufreset => gt_rxbufreset,
    gt_rxcdrreset => gt_rxcdrreset,
    gt_rxdfelpmreset => gt_rxdfelpmreset,
    gt_txprogdivresetdone => gt_txprogdivresetdone,
    gt_txpmaresetdone => gt_txpmaresetdone,
    gt_txsyncdone => gt_txsyncdone,
    gt_rxprbslocked => gt_rxprbslocked,
    pipe_tx0_rcvr_det => pipe_tx0_rcvr_det,
    pipe_clk => pipe_clk,
    sys_clk_bufg => sys_clk_bufg,
    pipe_tx0_powerdown => pipe_tx0_powerdown,
    interrupt_out => interrupt_out,
    s_axi_awid => s_axi_awid,
    s_axi_awaddr => s_axi_awaddr,
    s_axi_awregion => s_axi_awregion,
    s_axi_awlen => s_axi_awlen,
    s_axi_awsize => s_axi_awsize,
    s_axi_awburst => s_axi_awburst,
    s_axi_awvalid => s_axi_awvalid,
    s_axi_wdata => s_axi_wdata,
    s_axi_wstrb => s_axi_wstrb,
    s_axi_wlast => s_axi_wlast,
    s_axi_wvalid => s_axi_wvalid,
    s_axi_bready => s_axi_bready,
    s_axi_arid => s_axi_arid,
    s_axi_araddr => s_axi_araddr,
    s_axi_arregion => s_axi_arregion,
    s_axi_arlen => s_axi_arlen,
    s_axi_arsize => s_axi_arsize,
    s_axi_arburst => s_axi_arburst,
    s_axi_arvalid => s_axi_arvalid,
    s_axi_rready => s_axi_rready,
    s_axi_awready => s_axi_awready,
    s_axi_wready => s_axi_wready,
    s_axi_bid => s_axi_bid,
    s_axi_bresp => s_axi_bresp,
    s_axi_bvalid => s_axi_bvalid,
    s_axi_arready => s_axi_arready,
    s_axi_rid => s_axi_rid,
    s_axi_rdata => s_axi_rdata,
    s_axi_rresp => s_axi_rresp,
    s_axi_rlast => s_axi_rlast,
    s_axi_rvalid => s_axi_rvalid,
    cfg_ltssm_state => cfg_ltssm_state,
    cfg_function_status => cfg_function_status,
    cfg_max_read_req => cfg_max_read_req,
    cfg_max_payload => cfg_max_payload,
    cfg_err_uncor_in => cfg_err_uncor_in,
    cfg_flr_in_process => cfg_flr_in_process,
    cfg_flr_done => cfg_flr_done,
    cfg_vf_flr_in_process => cfg_vf_flr_in_process,
    cfg_vf_flr_func_num => cfg_vf_flr_func_num,
    cfg_vf_flr_done => cfg_vf_flr_done
  );
-- INST_TAG_END ------ End INSTANTIATION Template ---------

-- You must compile the wrapper file xdma_0.vhd when simulating
-- the core, xdma_0. When compiling the wrapper file, be sure to
-- reference the VHDL simulation library.

