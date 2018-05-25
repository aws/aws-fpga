-- (c) Copyright 1995-2018 Xilinx, Inc. All rights reserved.
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

-- IP VLNV: xilinx.com:ip:proc_sys_reset:5.0
-- IP Revision: 12

LIBRARY ieee;
USE ieee.std_logic_1164.ALL;
USE ieee.numeric_std.ALL;

LIBRARY proc_sys_reset_v5_0_12;
USE proc_sys_reset_v5_0_12.proc_sys_reset;

ENTITY bd_bf3f_rst_0_0 IS
  PORT (
    slowest_sync_clk : IN STD_LOGIC;
    ext_reset_in : IN STD_LOGIC;
    aux_reset_in : IN STD_LOGIC;
    mb_debug_sys_rst : IN STD_LOGIC;
    dcm_locked : IN STD_LOGIC;
    mb_reset : OUT STD_LOGIC;
    bus_struct_reset : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
    peripheral_reset : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
    interconnect_aresetn : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
    peripheral_aresetn : OUT STD_LOGIC_VECTOR(0 DOWNTO 0)
  );
END bd_bf3f_rst_0_0;

ARCHITECTURE bd_bf3f_rst_0_0_arch OF bd_bf3f_rst_0_0 IS
  ATTRIBUTE DowngradeIPIdentifiedWarnings : STRING;
  ATTRIBUTE DowngradeIPIdentifiedWarnings OF bd_bf3f_rst_0_0_arch: ARCHITECTURE IS "yes";
  COMPONENT proc_sys_reset IS
    GENERIC (
      C_FAMILY : STRING;
      C_EXT_RST_WIDTH : INTEGER;
      C_AUX_RST_WIDTH : INTEGER;
      C_EXT_RESET_HIGH : STD_LOGIC;
      C_AUX_RESET_HIGH : STD_LOGIC;
      C_NUM_BUS_RST : INTEGER;
      C_NUM_PERP_RST : INTEGER;
      C_NUM_INTERCONNECT_ARESETN : INTEGER;
      C_NUM_PERP_ARESETN : INTEGER
    );
    PORT (
      slowest_sync_clk : IN STD_LOGIC;
      ext_reset_in : IN STD_LOGIC;
      aux_reset_in : IN STD_LOGIC;
      mb_debug_sys_rst : IN STD_LOGIC;
      dcm_locked : IN STD_LOGIC;
      mb_reset : OUT STD_LOGIC;
      bus_struct_reset : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
      peripheral_reset : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
      interconnect_aresetn : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
      peripheral_aresetn : OUT STD_LOGIC_VECTOR(0 DOWNTO 0)
    );
  END COMPONENT proc_sys_reset;
  ATTRIBUTE X_CORE_INFO : STRING;
  ATTRIBUTE X_CORE_INFO OF bd_bf3f_rst_0_0_arch: ARCHITECTURE IS "proc_sys_reset,Vivado 2017.4.op";
  ATTRIBUTE CHECK_LICENSE_TYPE : STRING;
  ATTRIBUTE CHECK_LICENSE_TYPE OF bd_bf3f_rst_0_0_arch : ARCHITECTURE IS "bd_bf3f_rst_0_0,proc_sys_reset,{}";
  ATTRIBUTE CORE_GENERATION_INFO : STRING;
  ATTRIBUTE CORE_GENERATION_INFO OF bd_bf3f_rst_0_0_arch: ARCHITECTURE IS "bd_bf3f_rst_0_0,proc_sys_reset,{x_ipProduct=Vivado 2017.4.op,x_ipVendor=xilinx.com,x_ipLibrary=ip,x_ipName=proc_sys_reset,x_ipVersion=5.0,x_ipCoreRevision=12,x_ipLanguage=VERILOG,x_ipSimLanguage=MIXED,C_FAMILY=virtexuplus,C_EXT_RST_WIDTH=4,C_AUX_RST_WIDTH=4,C_EXT_RESET_HIGH=1,C_AUX_RESET_HIGH=0,C_NUM_BUS_RST=1,C_NUM_PERP_RST=1,C_NUM_INTERCONNECT_ARESETN=1,C_NUM_PERP_ARESETN=1}";
  ATTRIBUTE X_INTERFACE_INFO : STRING;
  ATTRIBUTE X_INTERFACE_PARAMETER : STRING;
  ATTRIBUTE X_INTERFACE_PARAMETER OF peripheral_aresetn: SIGNAL IS "XIL_INTERFACENAME peripheral_low_rst, POLARITY ACTIVE_LOW, TYPE PERIPHERAL";
  ATTRIBUTE X_INTERFACE_INFO OF peripheral_aresetn: SIGNAL IS "xilinx.com:signal:reset:1.0 peripheral_low_rst RST";
  ATTRIBUTE X_INTERFACE_PARAMETER OF interconnect_aresetn: SIGNAL IS "XIL_INTERFACENAME interconnect_low_rst, POLARITY ACTIVE_LOW, TYPE INTERCONNECT";
  ATTRIBUTE X_INTERFACE_INFO OF interconnect_aresetn: SIGNAL IS "xilinx.com:signal:reset:1.0 interconnect_low_rst RST";
  ATTRIBUTE X_INTERFACE_PARAMETER OF peripheral_reset: SIGNAL IS "XIL_INTERFACENAME peripheral_high_rst, POLARITY ACTIVE_HIGH, TYPE PERIPHERAL";
  ATTRIBUTE X_INTERFACE_INFO OF peripheral_reset: SIGNAL IS "xilinx.com:signal:reset:1.0 peripheral_high_rst RST";
  ATTRIBUTE X_INTERFACE_PARAMETER OF bus_struct_reset: SIGNAL IS "XIL_INTERFACENAME bus_struct_reset, POLARITY ACTIVE_HIGH, TYPE INTERCONNECT";
  ATTRIBUTE X_INTERFACE_INFO OF bus_struct_reset: SIGNAL IS "xilinx.com:signal:reset:1.0 bus_struct_reset RST";
  ATTRIBUTE X_INTERFACE_PARAMETER OF mb_reset: SIGNAL IS "XIL_INTERFACENAME mb_rst, POLARITY ACTIVE_HIGH, TYPE PROCESSOR";
  ATTRIBUTE X_INTERFACE_INFO OF mb_reset: SIGNAL IS "xilinx.com:signal:reset:1.0 mb_rst RST";
  ATTRIBUTE X_INTERFACE_PARAMETER OF mb_debug_sys_rst: SIGNAL IS "XIL_INTERFACENAME dbg_reset, POLARITY ACTIVE_HIGH";
  ATTRIBUTE X_INTERFACE_INFO OF mb_debug_sys_rst: SIGNAL IS "xilinx.com:signal:reset:1.0 dbg_reset RST";
  ATTRIBUTE X_INTERFACE_PARAMETER OF aux_reset_in: SIGNAL IS "XIL_INTERFACENAME aux_reset, POLARITY ACTIVE_LOW";
  ATTRIBUTE X_INTERFACE_INFO OF aux_reset_in: SIGNAL IS "xilinx.com:signal:reset:1.0 aux_reset RST";
  ATTRIBUTE X_INTERFACE_PARAMETER OF ext_reset_in: SIGNAL IS "XIL_INTERFACENAME ext_reset, BOARD.ASSOCIATED_PARAM RESET_BOARD_INTERFACE, POLARITY ACTIVE_HIGH";
  ATTRIBUTE X_INTERFACE_INFO OF ext_reset_in: SIGNAL IS "xilinx.com:signal:reset:1.0 ext_reset RST";
  ATTRIBUTE X_INTERFACE_PARAMETER OF slowest_sync_clk: SIGNAL IS "XIL_INTERFACENAME clock, ASSOCIATED_RESET mb_reset:bus_struct_reset:interconnect_aresetn:peripheral_aresetn:peripheral_reset, FREQ_HZ 100000000, PHASE 0.000";
  ATTRIBUTE X_INTERFACE_INFO OF slowest_sync_clk: SIGNAL IS "xilinx.com:signal:clock:1.0 clock CLK";
BEGIN
  U0 : proc_sys_reset
    GENERIC MAP (
      C_FAMILY => "virtexuplus",
      C_EXT_RST_WIDTH => 4,
      C_AUX_RST_WIDTH => 4,
      C_EXT_RESET_HIGH => '1',
      C_AUX_RESET_HIGH => '0',
      C_NUM_BUS_RST => 1,
      C_NUM_PERP_RST => 1,
      C_NUM_INTERCONNECT_ARESETN => 1,
      C_NUM_PERP_ARESETN => 1
    )
    PORT MAP (
      slowest_sync_clk => slowest_sync_clk,
      ext_reset_in => ext_reset_in,
      aux_reset_in => aux_reset_in,
      mb_debug_sys_rst => mb_debug_sys_rst,
      dcm_locked => dcm_locked,
      mb_reset => mb_reset,
      bus_struct_reset => bus_struct_reset,
      peripheral_reset => peripheral_reset,
      interconnect_aresetn => interconnect_aresetn,
      peripheral_aresetn => peripheral_aresetn
    );
END bd_bf3f_rst_0_0_arch;
