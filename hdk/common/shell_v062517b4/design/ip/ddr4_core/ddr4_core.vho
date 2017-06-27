-- (c) Copyright 1995-2017 Xilinx, Inc. All rights reserved.
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

-- IP VLNV: xilinx.com:ip:ddr4:2.2
-- IP Revision: 0

-- The following code must appear in the VHDL architecture header.

------------- Begin Cut here for COMPONENT Declaration ------ COMP_TAG
COMPONENT ddr4_core
  PORT (
    c0_init_calib_complete : OUT STD_LOGIC;
    dbg_clk : OUT STD_LOGIC;
    c0_sys_clk_p : IN STD_LOGIC;
    c0_sys_clk_n : IN STD_LOGIC;
    dbg_bus : OUT STD_LOGIC_VECTOR(511 DOWNTO 0);
    c0_ddr4_adr : OUT STD_LOGIC_VECTOR(16 DOWNTO 0);
    c0_ddr4_ba : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
    c0_ddr4_cke : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
    c0_ddr4_cs_n : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
    c0_ddr4_dq : INOUT STD_LOGIC_VECTOR(71 DOWNTO 0);
    c0_ddr4_dqs_c : INOUT STD_LOGIC_VECTOR(17 DOWNTO 0);
    c0_ddr4_dqs_t : INOUT STD_LOGIC_VECTOR(17 DOWNTO 0);
    c0_ddr4_odt : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
    c0_ddr4_parity : OUT STD_LOGIC;
    c0_ddr4_bg : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
    c0_ddr4_reset_n : OUT STD_LOGIC;
    c0_ddr4_act_n : OUT STD_LOGIC;
    c0_ddr4_ck_c : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
    c0_ddr4_ck_t : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
    c0_ddr4_ui_clk : OUT STD_LOGIC;
    c0_ddr4_ui_clk_sync_rst : OUT STD_LOGIC;
    c0_ddr4_app_sref_req : IN STD_LOGIC;
    c0_ddr4_app_sref_ack : OUT STD_LOGIC;
    c0_ddr4_app_restore_en : IN STD_LOGIC;
    c0_ddr4_app_restore_complete : IN STD_LOGIC;
    c0_ddr4_app_mem_init_skip : IN STD_LOGIC;
    c0_ddr4_app_xsdb_select : IN STD_LOGIC;
    c0_ddr4_app_xsdb_rd_en : IN STD_LOGIC;
    c0_ddr4_app_xsdb_wr_en : IN STD_LOGIC;
    c0_ddr4_app_xsdb_addr : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
    c0_ddr4_app_xsdb_wr_data : IN STD_LOGIC_VECTOR(8 DOWNTO 0);
    c0_ddr4_app_xsdb_rd_data : OUT STD_LOGIC_VECTOR(8 DOWNTO 0);
    c0_ddr4_app_xsdb_rdy : OUT STD_LOGIC;
    c0_ddr4_app_dbg_out : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
    c0_ddr4_aresetn : IN STD_LOGIC;
    c0_ddr4_s_axi_ctrl_awvalid : IN STD_LOGIC;
    c0_ddr4_s_axi_ctrl_awready : OUT STD_LOGIC;
    c0_ddr4_s_axi_ctrl_awaddr : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
    c0_ddr4_s_axi_ctrl_wvalid : IN STD_LOGIC;
    c0_ddr4_s_axi_ctrl_wready : OUT STD_LOGIC;
    c0_ddr4_s_axi_ctrl_wdata : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
    c0_ddr4_s_axi_ctrl_bvalid : OUT STD_LOGIC;
    c0_ddr4_s_axi_ctrl_bready : IN STD_LOGIC;
    c0_ddr4_s_axi_ctrl_bresp : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
    c0_ddr4_s_axi_ctrl_arvalid : IN STD_LOGIC;
    c0_ddr4_s_axi_ctrl_arready : OUT STD_LOGIC;
    c0_ddr4_s_axi_ctrl_araddr : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
    c0_ddr4_s_axi_ctrl_rvalid : OUT STD_LOGIC;
    c0_ddr4_s_axi_ctrl_rready : IN STD_LOGIC;
    c0_ddr4_s_axi_ctrl_rdata : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
    c0_ddr4_s_axi_ctrl_rresp : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
    c0_ddr4_interrupt : OUT STD_LOGIC;
    c0_ddr4_s_axi_awid : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
    c0_ddr4_s_axi_awaddr : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
    c0_ddr4_s_axi_awlen : IN STD_LOGIC_VECTOR(7 DOWNTO 0);
    c0_ddr4_s_axi_awsize : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
    c0_ddr4_s_axi_awburst : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
    c0_ddr4_s_axi_awlock : IN STD_LOGIC_VECTOR(0 DOWNTO 0);
    c0_ddr4_s_axi_awcache : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
    c0_ddr4_s_axi_awprot : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
    c0_ddr4_s_axi_awqos : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
    c0_ddr4_s_axi_awvalid : IN STD_LOGIC;
    c0_ddr4_s_axi_awready : OUT STD_LOGIC;
    c0_ddr4_s_axi_wdata : IN STD_LOGIC_VECTOR(511 DOWNTO 0);
    c0_ddr4_s_axi_wstrb : IN STD_LOGIC_VECTOR(63 DOWNTO 0);
    c0_ddr4_s_axi_wlast : IN STD_LOGIC;
    c0_ddr4_s_axi_wvalid : IN STD_LOGIC;
    c0_ddr4_s_axi_wready : OUT STD_LOGIC;
    c0_ddr4_s_axi_bready : IN STD_LOGIC;
    c0_ddr4_s_axi_bid : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    c0_ddr4_s_axi_bresp : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
    c0_ddr4_s_axi_bvalid : OUT STD_LOGIC;
    c0_ddr4_s_axi_arid : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
    c0_ddr4_s_axi_araddr : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
    c0_ddr4_s_axi_arlen : IN STD_LOGIC_VECTOR(7 DOWNTO 0);
    c0_ddr4_s_axi_arsize : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
    c0_ddr4_s_axi_arburst : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
    c0_ddr4_s_axi_arlock : IN STD_LOGIC_VECTOR(0 DOWNTO 0);
    c0_ddr4_s_axi_arcache : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
    c0_ddr4_s_axi_arprot : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
    c0_ddr4_s_axi_arqos : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
    c0_ddr4_s_axi_arvalid : IN STD_LOGIC;
    c0_ddr4_s_axi_arready : OUT STD_LOGIC;
    c0_ddr4_s_axi_rready : IN STD_LOGIC;
    c0_ddr4_s_axi_rlast : OUT STD_LOGIC;
    c0_ddr4_s_axi_rvalid : OUT STD_LOGIC;
    c0_ddr4_s_axi_rresp : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
    c0_ddr4_s_axi_rid : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    c0_ddr4_s_axi_rdata : OUT STD_LOGIC_VECTOR(511 DOWNTO 0);
    sys_rst : IN STD_LOGIC
  );
END COMPONENT;
-- COMP_TAG_END ------ End COMPONENT Declaration ------------

-- The following code must appear in the VHDL architecture
-- body. Substitute your own instance name and net names.

------------- Begin Cut here for INSTANTIATION Template ----- INST_TAG
your_instance_name : ddr4_core
  PORT MAP (
    c0_init_calib_complete => c0_init_calib_complete,
    dbg_clk => dbg_clk,
    c0_sys_clk_p => c0_sys_clk_p,
    c0_sys_clk_n => c0_sys_clk_n,
    dbg_bus => dbg_bus,
    c0_ddr4_adr => c0_ddr4_adr,
    c0_ddr4_ba => c0_ddr4_ba,
    c0_ddr4_cke => c0_ddr4_cke,
    c0_ddr4_cs_n => c0_ddr4_cs_n,
    c0_ddr4_dq => c0_ddr4_dq,
    c0_ddr4_dqs_c => c0_ddr4_dqs_c,
    c0_ddr4_dqs_t => c0_ddr4_dqs_t,
    c0_ddr4_odt => c0_ddr4_odt,
    c0_ddr4_parity => c0_ddr4_parity,
    c0_ddr4_bg => c0_ddr4_bg,
    c0_ddr4_reset_n => c0_ddr4_reset_n,
    c0_ddr4_act_n => c0_ddr4_act_n,
    c0_ddr4_ck_c => c0_ddr4_ck_c,
    c0_ddr4_ck_t => c0_ddr4_ck_t,
    c0_ddr4_ui_clk => c0_ddr4_ui_clk,
    c0_ddr4_ui_clk_sync_rst => c0_ddr4_ui_clk_sync_rst,
    c0_ddr4_app_sref_req => c0_ddr4_app_sref_req,
    c0_ddr4_app_sref_ack => c0_ddr4_app_sref_ack,
    c0_ddr4_app_restore_en => c0_ddr4_app_restore_en,
    c0_ddr4_app_restore_complete => c0_ddr4_app_restore_complete,
    c0_ddr4_app_mem_init_skip => c0_ddr4_app_mem_init_skip,
    c0_ddr4_app_xsdb_select => c0_ddr4_app_xsdb_select,
    c0_ddr4_app_xsdb_rd_en => c0_ddr4_app_xsdb_rd_en,
    c0_ddr4_app_xsdb_wr_en => c0_ddr4_app_xsdb_wr_en,
    c0_ddr4_app_xsdb_addr => c0_ddr4_app_xsdb_addr,
    c0_ddr4_app_xsdb_wr_data => c0_ddr4_app_xsdb_wr_data,
    c0_ddr4_app_xsdb_rd_data => c0_ddr4_app_xsdb_rd_data,
    c0_ddr4_app_xsdb_rdy => c0_ddr4_app_xsdb_rdy,
    c0_ddr4_app_dbg_out => c0_ddr4_app_dbg_out,
    c0_ddr4_aresetn => c0_ddr4_aresetn,
    c0_ddr4_s_axi_ctrl_awvalid => c0_ddr4_s_axi_ctrl_awvalid,
    c0_ddr4_s_axi_ctrl_awready => c0_ddr4_s_axi_ctrl_awready,
    c0_ddr4_s_axi_ctrl_awaddr => c0_ddr4_s_axi_ctrl_awaddr,
    c0_ddr4_s_axi_ctrl_wvalid => c0_ddr4_s_axi_ctrl_wvalid,
    c0_ddr4_s_axi_ctrl_wready => c0_ddr4_s_axi_ctrl_wready,
    c0_ddr4_s_axi_ctrl_wdata => c0_ddr4_s_axi_ctrl_wdata,
    c0_ddr4_s_axi_ctrl_bvalid => c0_ddr4_s_axi_ctrl_bvalid,
    c0_ddr4_s_axi_ctrl_bready => c0_ddr4_s_axi_ctrl_bready,
    c0_ddr4_s_axi_ctrl_bresp => c0_ddr4_s_axi_ctrl_bresp,
    c0_ddr4_s_axi_ctrl_arvalid => c0_ddr4_s_axi_ctrl_arvalid,
    c0_ddr4_s_axi_ctrl_arready => c0_ddr4_s_axi_ctrl_arready,
    c0_ddr4_s_axi_ctrl_araddr => c0_ddr4_s_axi_ctrl_araddr,
    c0_ddr4_s_axi_ctrl_rvalid => c0_ddr4_s_axi_ctrl_rvalid,
    c0_ddr4_s_axi_ctrl_rready => c0_ddr4_s_axi_ctrl_rready,
    c0_ddr4_s_axi_ctrl_rdata => c0_ddr4_s_axi_ctrl_rdata,
    c0_ddr4_s_axi_ctrl_rresp => c0_ddr4_s_axi_ctrl_rresp,
    c0_ddr4_interrupt => c0_ddr4_interrupt,
    c0_ddr4_s_axi_awid => c0_ddr4_s_axi_awid,
    c0_ddr4_s_axi_awaddr => c0_ddr4_s_axi_awaddr,
    c0_ddr4_s_axi_awlen => c0_ddr4_s_axi_awlen,
    c0_ddr4_s_axi_awsize => c0_ddr4_s_axi_awsize,
    c0_ddr4_s_axi_awburst => c0_ddr4_s_axi_awburst,
    c0_ddr4_s_axi_awlock => c0_ddr4_s_axi_awlock,
    c0_ddr4_s_axi_awcache => c0_ddr4_s_axi_awcache,
    c0_ddr4_s_axi_awprot => c0_ddr4_s_axi_awprot,
    c0_ddr4_s_axi_awqos => c0_ddr4_s_axi_awqos,
    c0_ddr4_s_axi_awvalid => c0_ddr4_s_axi_awvalid,
    c0_ddr4_s_axi_awready => c0_ddr4_s_axi_awready,
    c0_ddr4_s_axi_wdata => c0_ddr4_s_axi_wdata,
    c0_ddr4_s_axi_wstrb => c0_ddr4_s_axi_wstrb,
    c0_ddr4_s_axi_wlast => c0_ddr4_s_axi_wlast,
    c0_ddr4_s_axi_wvalid => c0_ddr4_s_axi_wvalid,
    c0_ddr4_s_axi_wready => c0_ddr4_s_axi_wready,
    c0_ddr4_s_axi_bready => c0_ddr4_s_axi_bready,
    c0_ddr4_s_axi_bid => c0_ddr4_s_axi_bid,
    c0_ddr4_s_axi_bresp => c0_ddr4_s_axi_bresp,
    c0_ddr4_s_axi_bvalid => c0_ddr4_s_axi_bvalid,
    c0_ddr4_s_axi_arid => c0_ddr4_s_axi_arid,
    c0_ddr4_s_axi_araddr => c0_ddr4_s_axi_araddr,
    c0_ddr4_s_axi_arlen => c0_ddr4_s_axi_arlen,
    c0_ddr4_s_axi_arsize => c0_ddr4_s_axi_arsize,
    c0_ddr4_s_axi_arburst => c0_ddr4_s_axi_arburst,
    c0_ddr4_s_axi_arlock => c0_ddr4_s_axi_arlock,
    c0_ddr4_s_axi_arcache => c0_ddr4_s_axi_arcache,
    c0_ddr4_s_axi_arprot => c0_ddr4_s_axi_arprot,
    c0_ddr4_s_axi_arqos => c0_ddr4_s_axi_arqos,
    c0_ddr4_s_axi_arvalid => c0_ddr4_s_axi_arvalid,
    c0_ddr4_s_axi_arready => c0_ddr4_s_axi_arready,
    c0_ddr4_s_axi_rready => c0_ddr4_s_axi_rready,
    c0_ddr4_s_axi_rlast => c0_ddr4_s_axi_rlast,
    c0_ddr4_s_axi_rvalid => c0_ddr4_s_axi_rvalid,
    c0_ddr4_s_axi_rresp => c0_ddr4_s_axi_rresp,
    c0_ddr4_s_axi_rid => c0_ddr4_s_axi_rid,
    c0_ddr4_s_axi_rdata => c0_ddr4_s_axi_rdata,
    sys_rst => sys_rst
  );
-- INST_TAG_END ------ End INSTANTIATION Template ---------

-- You must compile the wrapper file ddr4_core.vhd when simulating
-- the core, ddr4_core. When compiling the wrapper file, be sure to
-- reference the VHDL simulation library.

