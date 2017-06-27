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

-- IP VLNV: xilinx.com:ip:iomodule:3.1
-- IP Revision: 0

LIBRARY ieee;
USE ieee.std_logic_1164.ALL;
USE ieee.numeric_std.ALL;

LIBRARY iomodule_v3_1_0;
USE iomodule_v3_1_0.iomodule;

ENTITY bd_bf3f_iomodule_0_0 IS
  PORT (
    Clk : IN STD_LOGIC;
    Rst : IN STD_LOGIC;
    IO_Addr_Strobe : OUT STD_LOGIC;
    IO_Read_Strobe : OUT STD_LOGIC;
    IO_Write_Strobe : OUT STD_LOGIC;
    IO_Address : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
    IO_Byte_Enable : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
    IO_Write_Data : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
    IO_Read_Data : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
    IO_Ready : IN STD_LOGIC;
    LMB_ABus : IN STD_LOGIC_VECTOR(0 TO 31);
    LMB_WriteDBus : IN STD_LOGIC_VECTOR(0 TO 31);
    LMB_AddrStrobe : IN STD_LOGIC;
    LMB_ReadStrobe : IN STD_LOGIC;
    LMB_WriteStrobe : IN STD_LOGIC;
    LMB_BE : IN STD_LOGIC_VECTOR(0 TO 3);
    Sl_DBus : OUT STD_LOGIC_VECTOR(0 TO 31);
    Sl_Ready : OUT STD_LOGIC;
    Sl_Wait : OUT STD_LOGIC;
    Sl_UE : OUT STD_LOGIC;
    Sl_CE : OUT STD_LOGIC
  );
END bd_bf3f_iomodule_0_0;

ARCHITECTURE bd_bf3f_iomodule_0_0_arch OF bd_bf3f_iomodule_0_0 IS
  ATTRIBUTE DowngradeIPIdentifiedWarnings : STRING;
  ATTRIBUTE DowngradeIPIdentifiedWarnings OF bd_bf3f_iomodule_0_0_arch: ARCHITECTURE IS "yes";
  COMPONENT iomodule IS
    GENERIC (
      C_FAMILY : STRING;
      C_FREQ : INTEGER;
      C_INSTANCE : STRING;
      C_USE_CONFIG_RESET : INTEGER;
      C_AVOID_PRIMITIVES : INTEGER;
      C_TMR : INTEGER;
      C_USE_TMR_DISABLE : INTEGER;
      C_HIGHADDR : STD_LOGIC_VECTOR;
      C_BASEADDR : STD_LOGIC_VECTOR;
      C_MASK : STD_LOGIC_VECTOR;
      C_IO_HIGHADDR : STD_LOGIC_VECTOR;
      C_IO_BASEADDR : STD_LOGIC_VECTOR;
      C_IO_MASK : STD_LOGIC_VECTOR;
      C_LMB_AWIDTH : INTEGER;
      C_LMB_DWIDTH : INTEGER;
      C_USE_IO_BUS : INTEGER;
      C_USE_UART_RX : INTEGER;
      C_USE_UART_TX : INTEGER;
      C_UART_BAUDRATE : INTEGER;
      C_UART_DATA_BITS : INTEGER;
      C_UART_USE_PARITY : INTEGER;
      C_UART_ODD_PARITY : INTEGER;
      C_UART_RX_INTERRUPT : INTEGER;
      C_UART_TX_INTERRUPT : INTEGER;
      C_UART_ERROR_INTERRUPT : INTEGER;
      C_UART_PROG_BAUDRATE : INTEGER;
      C_USE_FIT1 : INTEGER;
      C_FIT1_No_CLOCKS : INTEGER;
      C_FIT1_INTERRUPT : INTEGER;
      C_USE_FIT2 : INTEGER;
      C_FIT2_No_CLOCKS : INTEGER;
      C_FIT2_INTERRUPT : INTEGER;
      C_USE_FIT3 : INTEGER;
      C_FIT3_No_CLOCKS : INTEGER;
      C_FIT3_INTERRUPT : INTEGER;
      C_USE_FIT4 : INTEGER;
      C_FIT4_No_CLOCKS : INTEGER;
      C_FIT4_INTERRUPT : INTEGER;
      C_USE_PIT1 : INTEGER;
      C_PIT1_SIZE : INTEGER;
      C_PIT1_READABLE : INTEGER;
      C_PIT1_PRESCALER : INTEGER;
      C_PIT1_INTERRUPT : INTEGER;
      C_USE_PIT2 : INTEGER;
      C_PIT2_SIZE : INTEGER;
      C_PIT2_READABLE : INTEGER;
      C_PIT2_PRESCALER : INTEGER;
      C_PIT2_INTERRUPT : INTEGER;
      C_USE_PIT3 : INTEGER;
      C_PIT3_SIZE : INTEGER;
      C_PIT3_READABLE : INTEGER;
      C_PIT3_PRESCALER : INTEGER;
      C_PIT3_INTERRUPT : INTEGER;
      C_USE_PIT4 : INTEGER;
      C_PIT4_SIZE : INTEGER;
      C_PIT4_READABLE : INTEGER;
      C_PIT4_PRESCALER : INTEGER;
      C_PIT4_INTERRUPT : INTEGER;
      C_USE_GPO1 : INTEGER;
      C_GPO1_SIZE : INTEGER;
      C_GPO1_INIT : STD_LOGIC_VECTOR(31 DOWNTO 0);
      C_USE_GPO2 : INTEGER;
      C_GPO2_SIZE : INTEGER;
      C_GPO2_INIT : STD_LOGIC_VECTOR(31 DOWNTO 0);
      C_USE_GPO3 : INTEGER;
      C_GPO3_SIZE : INTEGER;
      C_GPO3_INIT : STD_LOGIC_VECTOR(31 DOWNTO 0);
      C_USE_GPO4 : INTEGER;
      C_GPO4_SIZE : INTEGER;
      C_GPO4_INIT : STD_LOGIC_VECTOR(31 DOWNTO 0);
      C_USE_GPI1 : INTEGER;
      C_GPI1_SIZE : INTEGER;
      C_GPI1_INTERRUPT : INTEGER;
      C_USE_GPI2 : INTEGER;
      C_GPI2_SIZE : INTEGER;
      C_GPI2_INTERRUPT : INTEGER;
      C_USE_GPI3 : INTEGER;
      C_GPI3_SIZE : INTEGER;
      C_GPI3_INTERRUPT : INTEGER;
      C_USE_GPI4 : INTEGER;
      C_GPI4_SIZE : INTEGER;
      C_GPI4_INTERRUPT : INTEGER;
      C_INTC_USE_EXT_INTR : INTEGER;
      C_INTC_INTR_SIZE : INTEGER;
      C_INTC_LEVEL_EDGE : STD_LOGIC_VECTOR(15 DOWNTO 0);
      C_INTC_POSITIVE : STD_LOGIC_VECTOR(15 DOWNTO 0);
      C_INTC_HAS_FAST : INTEGER;
      C_INTC_ADDR_WIDTH : INTEGER;
      C_INTC_BASE_VECTORS : STD_LOGIC_VECTOR;
      C_INTC_ASYNC_INTR : STD_LOGIC_VECTOR(15 DOWNTO 0);
      C_INTC_NUM_SYNC_FF : INTEGER
    );
    PORT (
      Clk : IN STD_LOGIC;
      Rst : IN STD_LOGIC;
      Config_Reset : IN STD_LOGIC;
      TMR_Rst : IN STD_LOGIC;
      TMR_Disable : IN STD_LOGIC;
      ToVote : OUT STD_LOGIC_VECTOR(1023 DOWNTO 0);
      FromAVote : IN STD_LOGIC_VECTOR(1023 DOWNTO 0);
      FromBVote : IN STD_LOGIC_VECTOR(1023 DOWNTO 0);
      IO_Addr_Strobe : OUT STD_LOGIC;
      IO_Read_Strobe : OUT STD_LOGIC;
      IO_Write_Strobe : OUT STD_LOGIC;
      IO_Address : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
      IO_Byte_Enable : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
      IO_Write_Data : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
      IO_Read_Data : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
      IO_Ready : IN STD_LOGIC;
      UART_Rx : IN STD_LOGIC;
      UART_Tx : OUT STD_LOGIC;
      UART_Interrupt : OUT STD_LOGIC;
      FIT1_Interrupt : OUT STD_LOGIC;
      FIT1_Toggle : OUT STD_LOGIC;
      FIT2_Interrupt : OUT STD_LOGIC;
      FIT2_Toggle : OUT STD_LOGIC;
      FIT3_Interrupt : OUT STD_LOGIC;
      FIT3_Toggle : OUT STD_LOGIC;
      FIT4_Interrupt : OUT STD_LOGIC;
      FIT4_Toggle : OUT STD_LOGIC;
      PIT1_Enable : IN STD_LOGIC;
      PIT1_Interrupt : OUT STD_LOGIC;
      PIT1_Toggle : OUT STD_LOGIC;
      PIT2_Enable : IN STD_LOGIC;
      PIT2_Interrupt : OUT STD_LOGIC;
      PIT2_Toggle : OUT STD_LOGIC;
      PIT3_Enable : IN STD_LOGIC;
      PIT3_Interrupt : OUT STD_LOGIC;
      PIT3_Toggle : OUT STD_LOGIC;
      PIT4_Enable : IN STD_LOGIC;
      PIT4_Interrupt : OUT STD_LOGIC;
      PIT4_Toggle : OUT STD_LOGIC;
      GPO1 : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
      GPO2 : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
      GPO3 : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
      GPO4 : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
      GPI1 : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
      GPI1_Interrupt : OUT STD_LOGIC;
      GPI2 : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
      GPI2_Interrupt : OUT STD_LOGIC;
      GPI3 : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
      GPI3_Interrupt : OUT STD_LOGIC;
      GPI4 : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
      GPI4_Interrupt : OUT STD_LOGIC;
      INTC_Interrupt : IN STD_LOGIC_VECTOR(0 DOWNTO 0);
      INTC_IRQ : OUT STD_LOGIC;
      INTC_Processor_Ack : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
      INTC_Interrupt_Address : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
      INTC_IRQ_OUT : OUT STD_LOGIC;
      LMB_ABus : IN STD_LOGIC_VECTOR(0 TO 31);
      LMB_WriteDBus : IN STD_LOGIC_VECTOR(0 TO 31);
      LMB_AddrStrobe : IN STD_LOGIC;
      LMB_ReadStrobe : IN STD_LOGIC;
      LMB_WriteStrobe : IN STD_LOGIC;
      LMB_BE : IN STD_LOGIC_VECTOR(0 TO 3);
      Sl_DBus : OUT STD_LOGIC_VECTOR(0 TO 31);
      Sl_Ready : OUT STD_LOGIC;
      Sl_Wait : OUT STD_LOGIC;
      Sl_UE : OUT STD_LOGIC;
      Sl_CE : OUT STD_LOGIC
    );
  END COMPONENT iomodule;
  ATTRIBUTE X_CORE_INFO : STRING;
  ATTRIBUTE X_CORE_INFO OF bd_bf3f_iomodule_0_0_arch: ARCHITECTURE IS "iomodule,Vivado 2017.1_sdxop";
  ATTRIBUTE CHECK_LICENSE_TYPE : STRING;
  ATTRIBUTE CHECK_LICENSE_TYPE OF bd_bf3f_iomodule_0_0_arch : ARCHITECTURE IS "bd_bf3f_iomodule_0_0,iomodule,{}";
  ATTRIBUTE CORE_GENERATION_INFO : STRING;
  ATTRIBUTE CORE_GENERATION_INFO OF bd_bf3f_iomodule_0_0_arch: ARCHITECTURE IS "bd_bf3f_iomodule_0_0,iomodule,{x_ipProduct=Vivado 2017.1_sdxop,x_ipVendor=xilinx.com,x_ipLibrary=ip,x_ipName=iomodule,x_ipVersion=3.1,x_ipCoreRevision=0,x_ipLanguage=VERILOG,x_ipSimLanguage=MIXED,C_FAMILY=virtexuplus,C_FREQ=100000000,C_INSTANCE=iomodule,C_USE_CONFIG_RESET=0,C_AVOID_PRIMITIVES=0,C_TMR=0,C_USE_TMR_DISABLE=0,C_HIGHADDR=0x000000008000FFFF,C_BASEADDR=0x0000000080000000,C_MASK=0x00000000C0000000,C_IO_HIGHADDR=0x00000000FFFFFFFF,C_IO_BASEADDR=0x00000000C0000000,C_IO_MASK=0x00000000C000" & 
"0000,C_LMB_AWIDTH=32,C_LMB_DWIDTH=32,C_USE_IO_BUS=1,C_USE_UART_RX=0,C_USE_UART_TX=0,C_UART_BAUDRATE=9600,C_UART_DATA_BITS=8,C_UART_USE_PARITY=0,C_UART_ODD_PARITY=0,C_UART_RX_INTERRUPT=0,C_UART_TX_INTERRUPT=0,C_UART_ERROR_INTERRUPT=0,C_UART_PROG_BAUDRATE=0,C_USE_FIT1=0,C_FIT1_No_CLOCKS=6216,C_FIT1_INTERRUPT=0,C_USE_FIT2=0,C_FIT2_No_CLOCKS=6216,C_FIT2_INTERRUPT=0,C_USE_FIT3=0,C_FIT3_No_CLOCKS=6216,C_FIT3_INTERRUPT=0,C_USE_FIT4=0,C_FIT4_No_CLOCKS=6216,C_FIT4_INTERRUPT=0,C_USE_PIT1=0,C_PIT1_SIZE=32," & 
"C_PIT1_READABLE=1,C_PIT1_PRESCALER=0,C_PIT1_INTERRUPT=0,C_USE_PIT2=0,C_PIT2_SIZE=32,C_PIT2_READABLE=1,C_PIT2_PRESCALER=0,C_PIT2_INTERRUPT=0,C_USE_PIT3=0,C_PIT3_SIZE=32,C_PIT3_READABLE=1,C_PIT3_PRESCALER=0,C_PIT3_INTERRUPT=0,C_USE_PIT4=0,C_PIT4_SIZE=32,C_PIT4_READABLE=1,C_PIT4_PRESCALER=0,C_PIT4_INTERRUPT=0,C_USE_GPO1=0,C_GPO1_SIZE=32,C_GPO1_INIT=0x00000000,C_USE_GPO2=0,C_GPO2_SIZE=32,C_GPO2_INIT=0x00000000,C_USE_GPO3=0,C_GPO3_SIZE=32,C_GPO3_INIT=0x00000000,C_USE_GPO4=0,C_GPO4_SIZE=32,C_GPO4_INIT" & 
"=0x00000000,C_USE_GPI1=0,C_GPI1_SIZE=32,C_GPI1_INTERRUPT=0,C_USE_GPI2=0,C_GPI2_SIZE=32,C_GPI2_INTERRUPT=0,C_USE_GPI3=0,C_GPI3_SIZE=32,C_GPI3_INTERRUPT=0,C_USE_GPI4=0,C_GPI4_SIZE=32,C_GPI4_INTERRUPT=0,C_INTC_USE_EXT_INTR=0,C_INTC_INTR_SIZE=1,C_INTC_LEVEL_EDGE=0x0000,C_INTC_POSITIVE=0xFFFF,C_INTC_HAS_FAST=1,C_INTC_ADDR_WIDTH=17,C_INTC_BASE_VECTORS=0x00000000,C_INTC_ASYNC_INTR=0xFFFF,C_INTC_NUM_SYNC_FF=2}";
  ATTRIBUTE X_INTERFACE_INFO : STRING;
  ATTRIBUTE X_INTERFACE_INFO OF Clk: SIGNAL IS "xilinx.com:signal:clock:1.0 CLK.CLK CLK";
  ATTRIBUTE X_INTERFACE_INFO OF Rst: SIGNAL IS "xilinx.com:signal:reset:1.0 RST.Rst RST";
  ATTRIBUTE X_INTERFACE_INFO OF IO_Addr_Strobe: SIGNAL IS "xilinx.com:interface:mcsio_bus:1.0 IO_BUS ADDR_STROBE";
  ATTRIBUTE X_INTERFACE_INFO OF IO_Read_Strobe: SIGNAL IS "xilinx.com:interface:mcsio_bus:1.0 IO_BUS READ_STROBE";
  ATTRIBUTE X_INTERFACE_INFO OF IO_Write_Strobe: SIGNAL IS "xilinx.com:interface:mcsio_bus:1.0 IO_BUS WRITE_STROBE";
  ATTRIBUTE X_INTERFACE_INFO OF IO_Address: SIGNAL IS "xilinx.com:interface:mcsio_bus:1.0 IO_BUS ADDRESS";
  ATTRIBUTE X_INTERFACE_INFO OF IO_Byte_Enable: SIGNAL IS "xilinx.com:interface:mcsio_bus:1.0 IO_BUS BYTE_ENABLE";
  ATTRIBUTE X_INTERFACE_INFO OF IO_Write_Data: SIGNAL IS "xilinx.com:interface:mcsio_bus:1.0 IO_BUS WRITE_DATA";
  ATTRIBUTE X_INTERFACE_INFO OF IO_Read_Data: SIGNAL IS "xilinx.com:interface:mcsio_bus:1.0 IO_BUS READ_DATA";
  ATTRIBUTE X_INTERFACE_INFO OF IO_Ready: SIGNAL IS "xilinx.com:interface:mcsio_bus:1.0 IO_BUS READY";
  ATTRIBUTE X_INTERFACE_INFO OF LMB_ABus: SIGNAL IS "xilinx.com:interface:lmb:1.0 SLMB ABUS";
  ATTRIBUTE X_INTERFACE_INFO OF LMB_WriteDBus: SIGNAL IS "xilinx.com:interface:lmb:1.0 SLMB WRITEDBUS";
  ATTRIBUTE X_INTERFACE_INFO OF LMB_AddrStrobe: SIGNAL IS "xilinx.com:interface:lmb:1.0 SLMB ADDRSTROBE";
  ATTRIBUTE X_INTERFACE_INFO OF LMB_ReadStrobe: SIGNAL IS "xilinx.com:interface:lmb:1.0 SLMB READSTROBE";
  ATTRIBUTE X_INTERFACE_INFO OF LMB_WriteStrobe: SIGNAL IS "xilinx.com:interface:lmb:1.0 SLMB WRITESTROBE";
  ATTRIBUTE X_INTERFACE_INFO OF LMB_BE: SIGNAL IS "xilinx.com:interface:lmb:1.0 SLMB BE";
  ATTRIBUTE X_INTERFACE_INFO OF Sl_DBus: SIGNAL IS "xilinx.com:interface:lmb:1.0 SLMB READDBUS";
  ATTRIBUTE X_INTERFACE_INFO OF Sl_Ready: SIGNAL IS "xilinx.com:interface:lmb:1.0 SLMB READY";
  ATTRIBUTE X_INTERFACE_INFO OF Sl_Wait: SIGNAL IS "xilinx.com:interface:lmb:1.0 SLMB WAIT";
  ATTRIBUTE X_INTERFACE_INFO OF Sl_UE: SIGNAL IS "xilinx.com:interface:lmb:1.0 SLMB UE";
  ATTRIBUTE X_INTERFACE_INFO OF Sl_CE: SIGNAL IS "xilinx.com:interface:lmb:1.0 SLMB CE";
BEGIN
  U0 : iomodule
    GENERIC MAP (
      C_FAMILY => "virtexuplus",
      C_FREQ => 100000000,
      C_INSTANCE => "iomodule",
      C_USE_CONFIG_RESET => 0,
      C_AVOID_PRIMITIVES => 0,
      C_TMR => 0,
      C_USE_TMR_DISABLE => 0,
      C_HIGHADDR => X"000000008000FFFF",
      C_BASEADDR => X"0000000080000000",
      C_MASK => X"00000000C0000000",
      C_IO_HIGHADDR => X"00000000FFFFFFFF",
      C_IO_BASEADDR => X"00000000C0000000",
      C_IO_MASK => X"00000000C0000000",
      C_LMB_AWIDTH => 32,
      C_LMB_DWIDTH => 32,
      C_USE_IO_BUS => 1,
      C_USE_UART_RX => 0,
      C_USE_UART_TX => 0,
      C_UART_BAUDRATE => 9600,
      C_UART_DATA_BITS => 8,
      C_UART_USE_PARITY => 0,
      C_UART_ODD_PARITY => 0,
      C_UART_RX_INTERRUPT => 0,
      C_UART_TX_INTERRUPT => 0,
      C_UART_ERROR_INTERRUPT => 0,
      C_UART_PROG_BAUDRATE => 0,
      C_USE_FIT1 => 0,
      C_FIT1_No_CLOCKS => 6216,
      C_FIT1_INTERRUPT => 0,
      C_USE_FIT2 => 0,
      C_FIT2_No_CLOCKS => 6216,
      C_FIT2_INTERRUPT => 0,
      C_USE_FIT3 => 0,
      C_FIT3_No_CLOCKS => 6216,
      C_FIT3_INTERRUPT => 0,
      C_USE_FIT4 => 0,
      C_FIT4_No_CLOCKS => 6216,
      C_FIT4_INTERRUPT => 0,
      C_USE_PIT1 => 0,
      C_PIT1_SIZE => 32,
      C_PIT1_READABLE => 1,
      C_PIT1_PRESCALER => 0,
      C_PIT1_INTERRUPT => 0,
      C_USE_PIT2 => 0,
      C_PIT2_SIZE => 32,
      C_PIT2_READABLE => 1,
      C_PIT2_PRESCALER => 0,
      C_PIT2_INTERRUPT => 0,
      C_USE_PIT3 => 0,
      C_PIT3_SIZE => 32,
      C_PIT3_READABLE => 1,
      C_PIT3_PRESCALER => 0,
      C_PIT3_INTERRUPT => 0,
      C_USE_PIT4 => 0,
      C_PIT4_SIZE => 32,
      C_PIT4_READABLE => 1,
      C_PIT4_PRESCALER => 0,
      C_PIT4_INTERRUPT => 0,
      C_USE_GPO1 => 0,
      C_GPO1_SIZE => 32,
      C_GPO1_INIT => X"00000000",
      C_USE_GPO2 => 0,
      C_GPO2_SIZE => 32,
      C_GPO2_INIT => X"00000000",
      C_USE_GPO3 => 0,
      C_GPO3_SIZE => 32,
      C_GPO3_INIT => X"00000000",
      C_USE_GPO4 => 0,
      C_GPO4_SIZE => 32,
      C_GPO4_INIT => X"00000000",
      C_USE_GPI1 => 0,
      C_GPI1_SIZE => 32,
      C_GPI1_INTERRUPT => 0,
      C_USE_GPI2 => 0,
      C_GPI2_SIZE => 32,
      C_GPI2_INTERRUPT => 0,
      C_USE_GPI3 => 0,
      C_GPI3_SIZE => 32,
      C_GPI3_INTERRUPT => 0,
      C_USE_GPI4 => 0,
      C_GPI4_SIZE => 32,
      C_GPI4_INTERRUPT => 0,
      C_INTC_USE_EXT_INTR => 0,
      C_INTC_INTR_SIZE => 1,
      C_INTC_LEVEL_EDGE => X"0000",
      C_INTC_POSITIVE => X"FFFF",
      C_INTC_HAS_FAST => 1,
      C_INTC_ADDR_WIDTH => 17,
      C_INTC_BASE_VECTORS => X"00000000",
      C_INTC_ASYNC_INTR => X"FFFF",
      C_INTC_NUM_SYNC_FF => 2
    )
    PORT MAP (
      Clk => Clk,
      Rst => Rst,
      Config_Reset => '0',
      TMR_Rst => '0',
      TMR_Disable => '0',
      FromAVote => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 1024)),
      FromBVote => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 1024)),
      IO_Addr_Strobe => IO_Addr_Strobe,
      IO_Read_Strobe => IO_Read_Strobe,
      IO_Write_Strobe => IO_Write_Strobe,
      IO_Address => IO_Address,
      IO_Byte_Enable => IO_Byte_Enable,
      IO_Write_Data => IO_Write_Data,
      IO_Read_Data => IO_Read_Data,
      IO_Ready => IO_Ready,
      UART_Rx => '0',
      PIT1_Enable => '0',
      PIT2_Enable => '0',
      PIT3_Enable => '0',
      PIT4_Enable => '0',
      GPI1 => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 32)),
      GPI2 => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 32)),
      GPI3 => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 32)),
      GPI4 => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 32)),
      INTC_Interrupt => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 1)),
      INTC_Processor_Ack => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 2)),
      LMB_ABus => LMB_ABus,
      LMB_WriteDBus => LMB_WriteDBus,
      LMB_AddrStrobe => LMB_AddrStrobe,
      LMB_ReadStrobe => LMB_ReadStrobe,
      LMB_WriteStrobe => LMB_WriteStrobe,
      LMB_BE => LMB_BE,
      Sl_DBus => Sl_DBus,
      Sl_Ready => Sl_Ready,
      Sl_Wait => Sl_Wait,
      Sl_UE => Sl_UE,
      Sl_CE => Sl_CE
    );
END bd_bf3f_iomodule_0_0_arch;
