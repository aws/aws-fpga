-- (c) Copyright 1986-2022 Xilinx, Inc. All Rights Reserved.
-- (c) Copyright 2022-2024 Advanced Micro Devices, Inc. All rights reserved.
-- 
-- This file contains confidential and proprietary information
-- of AMD and is protected under U.S. and international copyright
-- and other intellectual property laws.
-- 
-- DISCLAIMER
-- This disclaimer is not a license and does not grant any
-- rights to the materials distributed herewith. Except as
-- otherwise provided in a valid license issued to you by
-- AMD, and to the maximum extent permitted by applicable
-- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
-- WITH ALL FAULTS, AND AMD HEREBY DISCLAIMS ALL WARRANTIES
-- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
-- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
-- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
-- (2) AMD shall not be liable (whether in contract or tort,
-- including negligence, or under any other theory of
-- liability) for any loss or damage of any kind or nature
-- related to, arising under or in connection with these
-- materials, including for any direct, or any indirect,
-- special, incidental, or consequential loss or damage
-- (including loss of data, profits, goodwill, or any type of
-- loss or damage suffered as a result of any action brought
-- by a third party) even if such damage or loss was
-- reasonably foreseeable or AMD had been advised of the
-- possibility of the same.
-- 
-- CRITICAL APPLICATIONS
-- AMD products are not designed or intended to be fail-
-- safe, or for use in any application requiring fail-safe
-- performance, such as life-support or safety devices or
-- systems, Class III medical devices, nuclear facilities,
-- applications related to the deployment of airbags, or any
-- other applications that could lead to death, personal
-- injury, or severe property or environmental damage
-- (individually and collectively, "Critical
-- Applications"). Customer assumes the sole risk and
-- liability of any use of AMD products in Critical
-- Applications, subject only to applicable laws and
-- regulations governing limitations on product liability.
-- 
-- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
-- PART OF THIS FILE AT ALL TIMES.
-- 
-- DO NOT MODIFY THIS FILE.
-- IP VLNV: xilinx.com:ip:xdma:4.1
-- IP Revision: 29

-- The following code must appear in the VHDL architecture header.

------------- Begin Cut here for COMPONENT Declaration ------ COMP_TAG
COMPONENT pcie_bridge_rc
  PORT (
    sys_clk : IN STD_LOGIC;
    sys_clk_gt : IN STD_LOGIC;
    sys_rst_n : IN STD_LOGIC;
    cfg_ltssm_state : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
    user_lnk_up : OUT STD_LOGIC;
    pci_exp_txp : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
    pci_exp_txn : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
    pci_exp_rxp : IN STD_LOGIC_VECTOR(7 DOWNTO 0);
    pci_exp_rxn : IN STD_LOGIC_VECTOR(7 DOWNTO 0);
    axi_aclk : OUT STD_LOGIC;
    axi_aresetn : OUT STD_LOGIC;
    axi_ctl_aresetn : OUT STD_LOGIC;
    common_commands_in : IN STD_LOGIC_VECTOR(25 DOWNTO 0);
    pipe_rx_0_sigs : IN STD_LOGIC_VECTOR(83 DOWNTO 0);
    pipe_rx_1_sigs : IN STD_LOGIC_VECTOR(83 DOWNTO 0);
    pipe_rx_2_sigs : IN STD_LOGIC_VECTOR(83 DOWNTO 0);
    pipe_rx_3_sigs : IN STD_LOGIC_VECTOR(83 DOWNTO 0);
    pipe_rx_4_sigs : IN STD_LOGIC_VECTOR(83 DOWNTO 0);
    pipe_rx_5_sigs : IN STD_LOGIC_VECTOR(83 DOWNTO 0);
    pipe_rx_6_sigs : IN STD_LOGIC_VECTOR(83 DOWNTO 0);
    pipe_rx_7_sigs : IN STD_LOGIC_VECTOR(83 DOWNTO 0);
    pipe_rx_8_sigs : IN STD_LOGIC_VECTOR(83 DOWNTO 0);
    pipe_rx_9_sigs : IN STD_LOGIC_VECTOR(83 DOWNTO 0);
    pipe_rx_10_sigs : IN STD_LOGIC_VECTOR(83 DOWNTO 0);
    pipe_rx_11_sigs : IN STD_LOGIC_VECTOR(83 DOWNTO 0);
    pipe_rx_12_sigs : IN STD_LOGIC_VECTOR(83 DOWNTO 0);
    pipe_rx_13_sigs : IN STD_LOGIC_VECTOR(83 DOWNTO 0);
    pipe_rx_14_sigs : IN STD_LOGIC_VECTOR(83 DOWNTO 0);
    pipe_rx_15_sigs : IN STD_LOGIC_VECTOR(83 DOWNTO 0);
    common_commands_out : OUT STD_LOGIC_VECTOR(25 DOWNTO 0);
    pipe_tx_0_sigs : OUT STD_LOGIC_VECTOR(83 DOWNTO 0);
    pipe_tx_1_sigs : OUT STD_LOGIC_VECTOR(83 DOWNTO 0);
    pipe_tx_2_sigs : OUT STD_LOGIC_VECTOR(83 DOWNTO 0);
    pipe_tx_3_sigs : OUT STD_LOGIC_VECTOR(83 DOWNTO 0);
    pipe_tx_4_sigs : OUT STD_LOGIC_VECTOR(83 DOWNTO 0);
    pipe_tx_5_sigs : OUT STD_LOGIC_VECTOR(83 DOWNTO 0);
    pipe_tx_6_sigs : OUT STD_LOGIC_VECTOR(83 DOWNTO 0);
    pipe_tx_7_sigs : OUT STD_LOGIC_VECTOR(83 DOWNTO 0);
    pipe_tx_8_sigs : OUT STD_LOGIC_VECTOR(83 DOWNTO 0);
    pipe_tx_9_sigs : OUT STD_LOGIC_VECTOR(83 DOWNTO 0);
    pipe_tx_10_sigs : OUT STD_LOGIC_VECTOR(83 DOWNTO 0);
    pipe_tx_11_sigs : OUT STD_LOGIC_VECTOR(83 DOWNTO 0);
    pipe_tx_12_sigs : OUT STD_LOGIC_VECTOR(83 DOWNTO 0);
    pipe_tx_13_sigs : OUT STD_LOGIC_VECTOR(83 DOWNTO 0);
    pipe_tx_14_sigs : OUT STD_LOGIC_VECTOR(83 DOWNTO 0);
    pipe_tx_15_sigs : OUT STD_LOGIC_VECTOR(83 DOWNTO 0);
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
    interrupt_out : OUT STD_LOGIC;
    s_axib_awid : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
    s_axib_awaddr : IN STD_LOGIC_VECTOR(63 DOWNTO 0);
    s_axib_awregion : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
    s_axib_awlen : IN STD_LOGIC_VECTOR(7 DOWNTO 0);
    s_axib_awsize : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
    s_axib_awburst : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
    s_axib_awvalid : IN STD_LOGIC;
    s_axib_wdata : IN STD_LOGIC_VECTOR(511 DOWNTO 0);
    s_axib_wstrb : IN STD_LOGIC_VECTOR(63 DOWNTO 0);
    s_axib_wlast : IN STD_LOGIC;
    s_axib_wvalid : IN STD_LOGIC;
    s_axib_bready : IN STD_LOGIC;
    s_axib_arid : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
    s_axib_araddr : IN STD_LOGIC_VECTOR(63 DOWNTO 0);
    s_axib_arregion : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
    s_axib_arlen : IN STD_LOGIC_VECTOR(7 DOWNTO 0);
    s_axib_arsize : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
    s_axib_arburst : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
    s_axib_arvalid : IN STD_LOGIC;
    s_axib_rready : IN STD_LOGIC;
    s_axib_awready : OUT STD_LOGIC;
    s_axib_wready : OUT STD_LOGIC;
    s_axib_bid : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    s_axib_bresp : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
    s_axib_bvalid : OUT STD_LOGIC;
    s_axib_arready : OUT STD_LOGIC;
    s_axib_rid : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    s_axib_rdata : OUT STD_LOGIC_VECTOR(511 DOWNTO 0);
    s_axib_rresp : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
    s_axib_rlast : OUT STD_LOGIC;
    s_axib_rvalid : OUT STD_LOGIC 
  );
END COMPONENT;
-- COMP_TAG_END ------ End COMPONENT Declaration ------------

-- The following code must appear in the VHDL architecture
-- body. Substitute your own instance name and net names.

------------- Begin Cut here for INSTANTIATION Template ----- INST_TAG
your_instance_name : pcie_bridge_rc
  PORT MAP (
    sys_clk => sys_clk,
    sys_clk_gt => sys_clk_gt,
    sys_rst_n => sys_rst_n,
    cfg_ltssm_state => cfg_ltssm_state,
    user_lnk_up => user_lnk_up,
    pci_exp_txp => pci_exp_txp,
    pci_exp_txn => pci_exp_txn,
    pci_exp_rxp => pci_exp_rxp,
    pci_exp_rxn => pci_exp_rxn,
    axi_aclk => axi_aclk,
    axi_aresetn => axi_aresetn,
    axi_ctl_aresetn => axi_ctl_aresetn,
    common_commands_in => common_commands_in,
    pipe_rx_0_sigs => pipe_rx_0_sigs,
    pipe_rx_1_sigs => pipe_rx_1_sigs,
    pipe_rx_2_sigs => pipe_rx_2_sigs,
    pipe_rx_3_sigs => pipe_rx_3_sigs,
    pipe_rx_4_sigs => pipe_rx_4_sigs,
    pipe_rx_5_sigs => pipe_rx_5_sigs,
    pipe_rx_6_sigs => pipe_rx_6_sigs,
    pipe_rx_7_sigs => pipe_rx_7_sigs,
    pipe_rx_8_sigs => pipe_rx_8_sigs,
    pipe_rx_9_sigs => pipe_rx_9_sigs,
    pipe_rx_10_sigs => pipe_rx_10_sigs,
    pipe_rx_11_sigs => pipe_rx_11_sigs,
    pipe_rx_12_sigs => pipe_rx_12_sigs,
    pipe_rx_13_sigs => pipe_rx_13_sigs,
    pipe_rx_14_sigs => pipe_rx_14_sigs,
    pipe_rx_15_sigs => pipe_rx_15_sigs,
    common_commands_out => common_commands_out,
    pipe_tx_0_sigs => pipe_tx_0_sigs,
    pipe_tx_1_sigs => pipe_tx_1_sigs,
    pipe_tx_2_sigs => pipe_tx_2_sigs,
    pipe_tx_3_sigs => pipe_tx_3_sigs,
    pipe_tx_4_sigs => pipe_tx_4_sigs,
    pipe_tx_5_sigs => pipe_tx_5_sigs,
    pipe_tx_6_sigs => pipe_tx_6_sigs,
    pipe_tx_7_sigs => pipe_tx_7_sigs,
    pipe_tx_8_sigs => pipe_tx_8_sigs,
    pipe_tx_9_sigs => pipe_tx_9_sigs,
    pipe_tx_10_sigs => pipe_tx_10_sigs,
    pipe_tx_11_sigs => pipe_tx_11_sigs,
    pipe_tx_12_sigs => pipe_tx_12_sigs,
    pipe_tx_13_sigs => pipe_tx_13_sigs,
    pipe_tx_14_sigs => pipe_tx_14_sigs,
    pipe_tx_15_sigs => pipe_tx_15_sigs,
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
    interrupt_out => interrupt_out,
    s_axib_awid => s_axib_awid,
    s_axib_awaddr => s_axib_awaddr,
    s_axib_awregion => s_axib_awregion,
    s_axib_awlen => s_axib_awlen,
    s_axib_awsize => s_axib_awsize,
    s_axib_awburst => s_axib_awburst,
    s_axib_awvalid => s_axib_awvalid,
    s_axib_wdata => s_axib_wdata,
    s_axib_wstrb => s_axib_wstrb,
    s_axib_wlast => s_axib_wlast,
    s_axib_wvalid => s_axib_wvalid,
    s_axib_bready => s_axib_bready,
    s_axib_arid => s_axib_arid,
    s_axib_araddr => s_axib_araddr,
    s_axib_arregion => s_axib_arregion,
    s_axib_arlen => s_axib_arlen,
    s_axib_arsize => s_axib_arsize,
    s_axib_arburst => s_axib_arburst,
    s_axib_arvalid => s_axib_arvalid,
    s_axib_rready => s_axib_rready,
    s_axib_awready => s_axib_awready,
    s_axib_wready => s_axib_wready,
    s_axib_bid => s_axib_bid,
    s_axib_bresp => s_axib_bresp,
    s_axib_bvalid => s_axib_bvalid,
    s_axib_arready => s_axib_arready,
    s_axib_rid => s_axib_rid,
    s_axib_rdata => s_axib_rdata,
    s_axib_rresp => s_axib_rresp,
    s_axib_rlast => s_axib_rlast,
    s_axib_rvalid => s_axib_rvalid
  );
-- INST_TAG_END ------ End INSTANTIATION Template ---------

-- You must compile the wrapper file pcie_bridge_rc.vhd when simulating
-- the core, pcie_bridge_rc. When compiling the wrapper file, be sure to
-- reference the VHDL simulation library.



