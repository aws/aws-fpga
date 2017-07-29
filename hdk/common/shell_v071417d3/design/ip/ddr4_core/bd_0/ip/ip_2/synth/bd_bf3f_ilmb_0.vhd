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

-- IP VLNV: xilinx.com:ip:lmb_v10:3.0
-- IP Revision: 9

LIBRARY ieee;
USE ieee.std_logic_1164.ALL;
USE ieee.numeric_std.ALL;

LIBRARY lmb_v10_v3_0_9;
USE lmb_v10_v3_0_9.lmb_v10;

ENTITY bd_bf3f_ilmb_0 IS
  PORT (
    LMB_Clk : IN STD_LOGIC;
    SYS_Rst : IN STD_LOGIC;
    LMB_Rst : OUT STD_LOGIC;
    M_ABus : IN STD_LOGIC_VECTOR(0 TO 31);
    M_ReadStrobe : IN STD_LOGIC;
    M_WriteStrobe : IN STD_LOGIC;
    M_AddrStrobe : IN STD_LOGIC;
    M_DBus : IN STD_LOGIC_VECTOR(0 TO 31);
    M_BE : IN STD_LOGIC_VECTOR(0 TO 3);
    Sl_DBus : IN STD_LOGIC_VECTOR(0 TO 63);
    Sl_Ready : IN STD_LOGIC_VECTOR(0 TO 1);
    Sl_Wait : IN STD_LOGIC_VECTOR(0 TO 1);
    Sl_UE : IN STD_LOGIC_VECTOR(0 TO 1);
    Sl_CE : IN STD_LOGIC_VECTOR(0 TO 1);
    LMB_ABus : OUT STD_LOGIC_VECTOR(0 TO 31);
    LMB_ReadStrobe : OUT STD_LOGIC;
    LMB_WriteStrobe : OUT STD_LOGIC;
    LMB_AddrStrobe : OUT STD_LOGIC;
    LMB_ReadDBus : OUT STD_LOGIC_VECTOR(0 TO 31);
    LMB_WriteDBus : OUT STD_LOGIC_VECTOR(0 TO 31);
    LMB_Ready : OUT STD_LOGIC;
    LMB_Wait : OUT STD_LOGIC;
    LMB_UE : OUT STD_LOGIC;
    LMB_CE : OUT STD_LOGIC;
    LMB_BE : OUT STD_LOGIC_VECTOR(0 TO 3)
  );
END bd_bf3f_ilmb_0;

ARCHITECTURE bd_bf3f_ilmb_0_arch OF bd_bf3f_ilmb_0 IS
  ATTRIBUTE DowngradeIPIdentifiedWarnings : STRING;
  ATTRIBUTE DowngradeIPIdentifiedWarnings OF bd_bf3f_ilmb_0_arch: ARCHITECTURE IS "yes";
  COMPONENT lmb_v10 IS
    GENERIC (
      C_LMB_NUM_SLAVES : INTEGER;
      C_LMB_DWIDTH : INTEGER;
      C_LMB_AWIDTH : INTEGER;
      C_EXT_RESET_HIGH : INTEGER
    );
    PORT (
      LMB_Clk : IN STD_LOGIC;
      SYS_Rst : IN STD_LOGIC;
      LMB_Rst : OUT STD_LOGIC;
      M_ABus : IN STD_LOGIC_VECTOR(0 TO 31);
      M_ReadStrobe : IN STD_LOGIC;
      M_WriteStrobe : IN STD_LOGIC;
      M_AddrStrobe : IN STD_LOGIC;
      M_DBus : IN STD_LOGIC_VECTOR(0 TO 31);
      M_BE : IN STD_LOGIC_VECTOR(0 TO 3);
      Sl_DBus : IN STD_LOGIC_VECTOR(0 TO 63);
      Sl_Ready : IN STD_LOGIC_VECTOR(0 TO 1);
      Sl_Wait : IN STD_LOGIC_VECTOR(0 TO 1);
      Sl_UE : IN STD_LOGIC_VECTOR(0 TO 1);
      Sl_CE : IN STD_LOGIC_VECTOR(0 TO 1);
      LMB_ABus : OUT STD_LOGIC_VECTOR(0 TO 31);
      LMB_ReadStrobe : OUT STD_LOGIC;
      LMB_WriteStrobe : OUT STD_LOGIC;
      LMB_AddrStrobe : OUT STD_LOGIC;
      LMB_ReadDBus : OUT STD_LOGIC_VECTOR(0 TO 31);
      LMB_WriteDBus : OUT STD_LOGIC_VECTOR(0 TO 31);
      LMB_Ready : OUT STD_LOGIC;
      LMB_Wait : OUT STD_LOGIC;
      LMB_UE : OUT STD_LOGIC;
      LMB_CE : OUT STD_LOGIC;
      LMB_BE : OUT STD_LOGIC_VECTOR(0 TO 3)
    );
  END COMPONENT lmb_v10;
  ATTRIBUTE X_CORE_INFO : STRING;
  ATTRIBUTE X_CORE_INFO OF bd_bf3f_ilmb_0_arch: ARCHITECTURE IS "lmb_v10,Vivado 2017.1_sdxop";
  ATTRIBUTE CHECK_LICENSE_TYPE : STRING;
  ATTRIBUTE CHECK_LICENSE_TYPE OF bd_bf3f_ilmb_0_arch : ARCHITECTURE IS "bd_bf3f_ilmb_0,lmb_v10,{}";
  ATTRIBUTE CORE_GENERATION_INFO : STRING;
  ATTRIBUTE CORE_GENERATION_INFO OF bd_bf3f_ilmb_0_arch: ARCHITECTURE IS "bd_bf3f_ilmb_0,lmb_v10,{x_ipProduct=Vivado 2017.1_sdxop,x_ipVendor=xilinx.com,x_ipLibrary=ip,x_ipName=lmb_v10,x_ipVersion=3.0,x_ipCoreRevision=9,x_ipLanguage=VERILOG,x_ipSimLanguage=MIXED,C_LMB_NUM_SLAVES=2,C_LMB_DWIDTH=32,C_LMB_AWIDTH=32,C_EXT_RESET_HIGH=1}";
  ATTRIBUTE X_INTERFACE_INFO : STRING;
  ATTRIBUTE X_INTERFACE_INFO OF LMB_Clk: SIGNAL IS "xilinx.com:signal:clock:1.0 CLK.LMB_Clk CLK";
  ATTRIBUTE X_INTERFACE_INFO OF SYS_Rst: SIGNAL IS "xilinx.com:signal:reset:1.0 RST.SYS_Rst RST";
  ATTRIBUTE X_INTERFACE_INFO OF LMB_Rst: SIGNAL IS "xilinx.com:interface:lmb:1.0 LMB_Sl_0 RST, xilinx.com:interface:lmb:1.0 LMB_Sl_1 RST, xilinx.com:interface:lmb:1.0 LMB_M RST";
  ATTRIBUTE X_INTERFACE_INFO OF M_ABus: SIGNAL IS "xilinx.com:interface:lmb:1.0 LMB_M ABUS";
  ATTRIBUTE X_INTERFACE_INFO OF M_ReadStrobe: SIGNAL IS "xilinx.com:interface:lmb:1.0 LMB_M READSTROBE";
  ATTRIBUTE X_INTERFACE_INFO OF M_WriteStrobe: SIGNAL IS "xilinx.com:interface:lmb:1.0 LMB_M WRITESTROBE";
  ATTRIBUTE X_INTERFACE_INFO OF M_AddrStrobe: SIGNAL IS "xilinx.com:interface:lmb:1.0 LMB_M ADDRSTROBE";
  ATTRIBUTE X_INTERFACE_INFO OF M_DBus: SIGNAL IS "xilinx.com:interface:lmb:1.0 LMB_M WRITEDBUS";
  ATTRIBUTE X_INTERFACE_INFO OF M_BE: SIGNAL IS "xilinx.com:interface:lmb:1.0 LMB_M BE";
  ATTRIBUTE X_INTERFACE_INFO OF Sl_DBus: SIGNAL IS "xilinx.com:interface:lmb:1.0 LMB_Sl_0 READDBUS [0:31] [0:31], xilinx.com:interface:lmb:1.0 LMB_Sl_1 READDBUS [0:31] [32:63]";
  ATTRIBUTE X_INTERFACE_INFO OF Sl_Ready: SIGNAL IS "xilinx.com:interface:lmb:1.0 LMB_Sl_0 READY [0:0] [0:0], xilinx.com:interface:lmb:1.0 LMB_Sl_1 READY [0:0] [1:1]";
  ATTRIBUTE X_INTERFACE_INFO OF Sl_Wait: SIGNAL IS "xilinx.com:interface:lmb:1.0 LMB_Sl_0 WAIT [0:0] [0:0], xilinx.com:interface:lmb:1.0 LMB_Sl_1 WAIT [0:0] [1:1]";
  ATTRIBUTE X_INTERFACE_INFO OF Sl_UE: SIGNAL IS "xilinx.com:interface:lmb:1.0 LMB_Sl_0 UE [0:0] [0:0], xilinx.com:interface:lmb:1.0 LMB_Sl_1 UE [0:0] [1:1]";
  ATTRIBUTE X_INTERFACE_INFO OF Sl_CE: SIGNAL IS "xilinx.com:interface:lmb:1.0 LMB_Sl_0 CE [0:0] [0:0], xilinx.com:interface:lmb:1.0 LMB_Sl_1 CE [0:0] [1:1]";
  ATTRIBUTE X_INTERFACE_INFO OF LMB_ABus: SIGNAL IS "xilinx.com:interface:lmb:1.0 LMB_Sl_0 ABUS, xilinx.com:interface:lmb:1.0 LMB_Sl_1 ABUS";
  ATTRIBUTE X_INTERFACE_INFO OF LMB_ReadStrobe: SIGNAL IS "xilinx.com:interface:lmb:1.0 LMB_Sl_0 READSTROBE, xilinx.com:interface:lmb:1.0 LMB_Sl_1 READSTROBE";
  ATTRIBUTE X_INTERFACE_INFO OF LMB_WriteStrobe: SIGNAL IS "xilinx.com:interface:lmb:1.0 LMB_Sl_0 WRITESTROBE, xilinx.com:interface:lmb:1.0 LMB_Sl_1 WRITESTROBE";
  ATTRIBUTE X_INTERFACE_INFO OF LMB_AddrStrobe: SIGNAL IS "xilinx.com:interface:lmb:1.0 LMB_Sl_0 ADDRSTROBE, xilinx.com:interface:lmb:1.0 LMB_Sl_1 ADDRSTROBE";
  ATTRIBUTE X_INTERFACE_INFO OF LMB_ReadDBus: SIGNAL IS "xilinx.com:interface:lmb:1.0 LMB_M READDBUS";
  ATTRIBUTE X_INTERFACE_INFO OF LMB_WriteDBus: SIGNAL IS "xilinx.com:interface:lmb:1.0 LMB_Sl_0 WRITEDBUS, xilinx.com:interface:lmb:1.0 LMB_Sl_1 WRITEDBUS";
  ATTRIBUTE X_INTERFACE_INFO OF LMB_Ready: SIGNAL IS "xilinx.com:interface:lmb:1.0 LMB_M READY";
  ATTRIBUTE X_INTERFACE_INFO OF LMB_Wait: SIGNAL IS "xilinx.com:interface:lmb:1.0 LMB_M WAIT";
  ATTRIBUTE X_INTERFACE_INFO OF LMB_UE: SIGNAL IS "xilinx.com:interface:lmb:1.0 LMB_M UE";
  ATTRIBUTE X_INTERFACE_INFO OF LMB_CE: SIGNAL IS "xilinx.com:interface:lmb:1.0 LMB_M CE";
  ATTRIBUTE X_INTERFACE_INFO OF LMB_BE: SIGNAL IS "xilinx.com:interface:lmb:1.0 LMB_Sl_0 BE, xilinx.com:interface:lmb:1.0 LMB_Sl_1 BE";
BEGIN
  U0 : lmb_v10
    GENERIC MAP (
      C_LMB_NUM_SLAVES => 2,
      C_LMB_DWIDTH => 32,
      C_LMB_AWIDTH => 32,
      C_EXT_RESET_HIGH => 1
    )
    PORT MAP (
      LMB_Clk => LMB_Clk,
      SYS_Rst => SYS_Rst,
      LMB_Rst => LMB_Rst,
      M_ABus => M_ABus,
      M_ReadStrobe => M_ReadStrobe,
      M_WriteStrobe => M_WriteStrobe,
      M_AddrStrobe => M_AddrStrobe,
      M_DBus => M_DBus,
      M_BE => M_BE,
      Sl_DBus => Sl_DBus,
      Sl_Ready => Sl_Ready,
      Sl_Wait => Sl_Wait,
      Sl_UE => Sl_UE,
      Sl_CE => Sl_CE,
      LMB_ABus => LMB_ABus,
      LMB_ReadStrobe => LMB_ReadStrobe,
      LMB_WriteStrobe => LMB_WriteStrobe,
      LMB_AddrStrobe => LMB_AddrStrobe,
      LMB_ReadDBus => LMB_ReadDBus,
      LMB_WriteDBus => LMB_WriteDBus,
      LMB_Ready => LMB_Ready,
      LMB_Wait => LMB_Wait,
      LMB_UE => LMB_UE,
      LMB_CE => LMB_CE,
      LMB_BE => LMB_BE
    );
END bd_bf3f_ilmb_0_arch;
