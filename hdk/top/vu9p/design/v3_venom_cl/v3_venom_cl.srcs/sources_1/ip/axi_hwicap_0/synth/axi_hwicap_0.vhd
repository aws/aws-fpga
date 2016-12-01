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

-- IP VLNV: xilinx.com:ip:axi_hwicap:3.0
-- IP Revision: 14

LIBRARY ieee;
USE ieee.std_logic_1164.ALL;
USE ieee.numeric_std.ALL;

LIBRARY axi_hwicap_v3_0_14;
USE axi_hwicap_v3_0_14.axi_hwicap;

ENTITY axi_hwicap_0 IS
  PORT (
    icap_clk : IN STD_LOGIC;
    eos_in : IN STD_LOGIC;
    s_axi_aclk : IN STD_LOGIC;
    s_axi_aresetn : IN STD_LOGIC;
    s_axi_awaddr : IN STD_LOGIC_VECTOR(8 DOWNTO 0);
    s_axi_awvalid : IN STD_LOGIC;
    s_axi_awready : OUT STD_LOGIC;
    s_axi_wdata : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
    s_axi_wstrb : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
    s_axi_wvalid : IN STD_LOGIC;
    s_axi_wready : OUT STD_LOGIC;
    s_axi_bresp : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
    s_axi_bvalid : OUT STD_LOGIC;
    s_axi_bready : IN STD_LOGIC;
    s_axi_araddr : IN STD_LOGIC_VECTOR(8 DOWNTO 0);
    s_axi_arvalid : IN STD_LOGIC;
    s_axi_arready : OUT STD_LOGIC;
    s_axi_rdata : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
    s_axi_rresp : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
    s_axi_rvalid : OUT STD_LOGIC;
    s_axi_rready : IN STD_LOGIC;
    ip2intc_irpt : OUT STD_LOGIC
  );
END axi_hwicap_0;

ARCHITECTURE axi_hwicap_0_arch OF axi_hwicap_0 IS
  ATTRIBUTE DowngradeIPIdentifiedWarnings : STRING;
  ATTRIBUTE DowngradeIPIdentifiedWarnings OF axi_hwicap_0_arch: ARCHITECTURE IS "yes";
  COMPONENT axi_hwicap IS
    GENERIC (
      C_S_AXI_DATA_WIDTH : INTEGER;
      C_SHARED_STARTUP : INTEGER;
      C_ICAP_EXTERNAL : INTEGER;
      C_INCLUDE_STARTUP : INTEGER;
      C_ENABLE_ASYNC : INTEGER;
      C_S_AXI_ADDR_WIDTH : INTEGER;
      C_WRITE_FIFO_DEPTH : INTEGER;
      C_READ_FIFO_DEPTH : INTEGER;
      C_ICAP_WIDTH_S : STRING;
      C_DEVICE_ID : STD_LOGIC_VECTOR;
      C_MODE : INTEGER;
      C_NOREAD : INTEGER;
      C_SIMULATION : INTEGER;
      C_BRAM_SRL_FIFO_TYPE : INTEGER;
      C_FAMILY : STRING;
      C_OPERATION : INTEGER
    );
    PORT (
      icap_clk : IN STD_LOGIC;
      eos_in : IN STD_LOGIC;
      s_axi_aclk : IN STD_LOGIC;
      s_axi_aresetn : IN STD_LOGIC;
      s_axi_awaddr : IN STD_LOGIC_VECTOR(8 DOWNTO 0);
      s_axi_awvalid : IN STD_LOGIC;
      s_axi_awready : OUT STD_LOGIC;
      s_axi_wdata : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
      s_axi_wstrb : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
      s_axi_wvalid : IN STD_LOGIC;
      s_axi_wready : OUT STD_LOGIC;
      s_axi_bresp : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
      s_axi_bvalid : OUT STD_LOGIC;
      s_axi_bready : IN STD_LOGIC;
      s_axi_araddr : IN STD_LOGIC_VECTOR(8 DOWNTO 0);
      s_axi_arvalid : IN STD_LOGIC;
      s_axi_arready : OUT STD_LOGIC;
      s_axi_rdata : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
      s_axi_rresp : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
      s_axi_rvalid : OUT STD_LOGIC;
      s_axi_rready : IN STD_LOGIC;
      ip2intc_irpt : OUT STD_LOGIC;
      icap_csib : OUT STD_LOGIC;
      icap_rdwrb : OUT STD_LOGIC;
      cap_req : OUT STD_LOGIC;
      icap_i : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
      icap_o : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
      cap_gnt : IN STD_LOGIC;
      icap_avail : IN STD_LOGIC;
      cap_rel : IN STD_LOGIC;
      cfgclk : OUT STD_LOGIC;
      cfgmclk : OUT STD_LOGIC;
      preq : OUT STD_LOGIC;
      gsr : IN STD_LOGIC;
      gts : IN STD_LOGIC;
      clk : IN STD_LOGIC;
      keyclearb : IN STD_LOGIC;
      pack : IN STD_LOGIC;
      usrcclko : IN STD_LOGIC;
      usrcclkts : IN STD_LOGIC;
      usrdoneo : IN STD_LOGIC;
      usrdonets : IN STD_LOGIC
    );
  END COMPONENT axi_hwicap;
  ATTRIBUTE X_CORE_INFO : STRING;
  ATTRIBUTE X_CORE_INFO OF axi_hwicap_0_arch: ARCHITECTURE IS "axi_hwicap,Vivado 2016.3_EA1659323";
  ATTRIBUTE CHECK_LICENSE_TYPE : STRING;
  ATTRIBUTE CHECK_LICENSE_TYPE OF axi_hwicap_0_arch : ARCHITECTURE IS "axi_hwicap_0,axi_hwicap,{}";
  ATTRIBUTE CORE_GENERATION_INFO : STRING;
  ATTRIBUTE CORE_GENERATION_INFO OF axi_hwicap_0_arch: ARCHITECTURE IS "axi_hwicap_0,axi_hwicap,{x_ipProduct=Vivado 2016.3_EA1659323,x_ipVendor=xilinx.com,x_ipLibrary=ip,x_ipName=axi_hwicap,x_ipVersion=3.0,x_ipCoreRevision=14,x_ipLanguage=VERILOG,x_ipSimLanguage=MIXED,C_S_AXI_DATA_WIDTH=32,C_SHARED_STARTUP=0,C_ICAP_EXTERNAL=0,C_INCLUDE_STARTUP=0,C_ENABLE_ASYNC=1,C_S_AXI_ADDR_WIDTH=9,C_WRITE_FIFO_DEPTH=1024,C_READ_FIFO_DEPTH=128,C_ICAP_WIDTH_S=X32,C_DEVICE_ID=0x04224093,C_MODE=0,C_NOREAD=0,C_SIMULATION=2,C_BRAM_SRL_FIFO_TYPE=1,C_FAMILY=virtexuplus,C_OPERATION=0}";
  ATTRIBUTE X_INTERFACE_INFO : STRING;
  ATTRIBUTE X_INTERFACE_INFO OF icap_clk: SIGNAL IS "xilinx.com:signal:clock:1.0 ICAP_CLK CLK";
  ATTRIBUTE X_INTERFACE_INFO OF s_axi_aclk: SIGNAL IS "xilinx.com:signal:clock:1.0 S_AXI_ACLK CLK";
  ATTRIBUTE X_INTERFACE_INFO OF s_axi_aresetn: SIGNAL IS "xilinx.com:signal:reset:1.0 S_AXI_ARESETN RST";
  ATTRIBUTE X_INTERFACE_INFO OF s_axi_awaddr: SIGNAL IS "xilinx.com:interface:aximm:1.0 S_AXI_LITE AWADDR";
  ATTRIBUTE X_INTERFACE_INFO OF s_axi_awvalid: SIGNAL IS "xilinx.com:interface:aximm:1.0 S_AXI_LITE AWVALID";
  ATTRIBUTE X_INTERFACE_INFO OF s_axi_awready: SIGNAL IS "xilinx.com:interface:aximm:1.0 S_AXI_LITE AWREADY";
  ATTRIBUTE X_INTERFACE_INFO OF s_axi_wdata: SIGNAL IS "xilinx.com:interface:aximm:1.0 S_AXI_LITE WDATA";
  ATTRIBUTE X_INTERFACE_INFO OF s_axi_wstrb: SIGNAL IS "xilinx.com:interface:aximm:1.0 S_AXI_LITE WSTRB";
  ATTRIBUTE X_INTERFACE_INFO OF s_axi_wvalid: SIGNAL IS "xilinx.com:interface:aximm:1.0 S_AXI_LITE WVALID";
  ATTRIBUTE X_INTERFACE_INFO OF s_axi_wready: SIGNAL IS "xilinx.com:interface:aximm:1.0 S_AXI_LITE WREADY";
  ATTRIBUTE X_INTERFACE_INFO OF s_axi_bresp: SIGNAL IS "xilinx.com:interface:aximm:1.0 S_AXI_LITE BRESP";
  ATTRIBUTE X_INTERFACE_INFO OF s_axi_bvalid: SIGNAL IS "xilinx.com:interface:aximm:1.0 S_AXI_LITE BVALID";
  ATTRIBUTE X_INTERFACE_INFO OF s_axi_bready: SIGNAL IS "xilinx.com:interface:aximm:1.0 S_AXI_LITE BREADY";
  ATTRIBUTE X_INTERFACE_INFO OF s_axi_araddr: SIGNAL IS "xilinx.com:interface:aximm:1.0 S_AXI_LITE ARADDR";
  ATTRIBUTE X_INTERFACE_INFO OF s_axi_arvalid: SIGNAL IS "xilinx.com:interface:aximm:1.0 S_AXI_LITE ARVALID";
  ATTRIBUTE X_INTERFACE_INFO OF s_axi_arready: SIGNAL IS "xilinx.com:interface:aximm:1.0 S_AXI_LITE ARREADY";
  ATTRIBUTE X_INTERFACE_INFO OF s_axi_rdata: SIGNAL IS "xilinx.com:interface:aximm:1.0 S_AXI_LITE RDATA";
  ATTRIBUTE X_INTERFACE_INFO OF s_axi_rresp: SIGNAL IS "xilinx.com:interface:aximm:1.0 S_AXI_LITE RRESP";
  ATTRIBUTE X_INTERFACE_INFO OF s_axi_rvalid: SIGNAL IS "xilinx.com:interface:aximm:1.0 S_AXI_LITE RVALID";
  ATTRIBUTE X_INTERFACE_INFO OF s_axi_rready: SIGNAL IS "xilinx.com:interface:aximm:1.0 S_AXI_LITE RREADY";
  ATTRIBUTE X_INTERFACE_INFO OF ip2intc_irpt: SIGNAL IS "xilinx.com:signal:interrupt:1.0 IP2INTC_IRPT INTERRUPT";
BEGIN
  U0 : axi_hwicap
    GENERIC MAP (
      C_S_AXI_DATA_WIDTH => 32,
      C_SHARED_STARTUP => 0,
      C_ICAP_EXTERNAL => 0,
      C_INCLUDE_STARTUP => 0,
      C_ENABLE_ASYNC => 1,
      C_S_AXI_ADDR_WIDTH => 9,
      C_WRITE_FIFO_DEPTH => 1024,
      C_READ_FIFO_DEPTH => 128,
      C_ICAP_WIDTH_S => "X32",
      C_DEVICE_ID => X"04224093",
      C_MODE => 0,
      C_NOREAD => 0,
      C_SIMULATION => 2,
      C_BRAM_SRL_FIFO_TYPE => 1,
      C_FAMILY => "virtexuplus",
      C_OPERATION => 0
    )
    PORT MAP (
      icap_clk => icap_clk,
      eos_in => eos_in,
      s_axi_aclk => s_axi_aclk,
      s_axi_aresetn => s_axi_aresetn,
      s_axi_awaddr => s_axi_awaddr,
      s_axi_awvalid => s_axi_awvalid,
      s_axi_awready => s_axi_awready,
      s_axi_wdata => s_axi_wdata,
      s_axi_wstrb => s_axi_wstrb,
      s_axi_wvalid => s_axi_wvalid,
      s_axi_wready => s_axi_wready,
      s_axi_bresp => s_axi_bresp,
      s_axi_bvalid => s_axi_bvalid,
      s_axi_bready => s_axi_bready,
      s_axi_araddr => s_axi_araddr,
      s_axi_arvalid => s_axi_arvalid,
      s_axi_arready => s_axi_arready,
      s_axi_rdata => s_axi_rdata,
      s_axi_rresp => s_axi_rresp,
      s_axi_rvalid => s_axi_rvalid,
      s_axi_rready => s_axi_rready,
      ip2intc_irpt => ip2intc_irpt,
      icap_i => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 32)),
      cap_gnt => '0',
      icap_avail => '0',
      cap_rel => '0',
      gsr => '0',
      gts => '0',
      clk => '0',
      keyclearb => '0',
      pack => '0',
      usrcclko => '0',
      usrcclkts => '0',
      usrdoneo => '0',
      usrdonets => '0'
    );
END axi_hwicap_0_arch;
