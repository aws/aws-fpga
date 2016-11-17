-------------------------------------------------------------------------------
-- ipic_if.vhd - entity/architecture pair

-------------------------------------------------------------------------------
-- (c) Copyright 2010 - 2011 Xilinx, Inc. All rights reserved.
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
-------------------------------------------------------------------------------
-- Filename:        ipic_if.vhd
-- Version :        v7.01a
-- Description:     This module provides the interface to the ICAP & the 
--                  AXI-LITE
--
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-- Naming Conventions:
--      active low signals:                     "*_n"
--      clock signals:                          "clk", "clk_div#", "clk_#x"
--      reset signals:                          "rst", "rst_n"
--      generics:                               "C_*"
--      user defined types:                     "*_TYPE"
--      state machine next state:               "*_ns"
--      state machine current state:            "*_cs"
--      combinatorial signals:                  "*_com"
--      pipelined or register delay signals:    "*_d#"
--      counter signals:                        "*cnt*"
--      clock enable signals:                   "*_ce"
--      internal version of output port         "*_i"
--      device pins:                            "*_pin"
--      ports:                                  - Names begin with Uppercase
--      processes:                              "*_PROCESS"
--      component instantiations:               "<ENTITY_>I_<#|FUNC>
-------------------------------------------------------------------------------
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

library unisim;
use unisim.vcomponents.all;

library lib_fifo_v1_0_6;
    use lib_fifo_v1_0_6.async_fifo_fg;

library lib_cdc_v1_0_2;
library lib_pkg_v1_0_2;
use lib_pkg_v1_0_2.lib_pkg.all;
use ieee.std_logic_unsigned."+";
use ieee.std_logic_unsigned."-";


-------------------------------------------------------------------------------
-- Definition of Generics:
--  C_SAXI_DWIDTH         -- Processor Data Bus Width
--  C_WRITE_FIFO_DEPTH    -- Write Fifo Depth
--  C_READ_FIFO_DEPTH     -- Read Fifo Depth
--  ICAP_DWIDTH           -- Icap Data Width
--  C_BRAM_SRL_FIFO_TYPE  -- type of the FIFO either distributed RAM or BRAM
--  C_FAMILY              -- Family of FPGA
--
-- Definition of Ports:
--  ICAP_Clk              -- ICAP Clock
--  ICAP_Reset            -- ICAP Reset
--
--  Bus2IP_Clk            -- Clock
--  Bus2IP_Reset          -- Reset
--  Bus2IP_cs             -- Chip select
--  Bus2IP_BE             -- Byte enables
--  Bus2IP_rnw            -- Read Not Write
--  Bus2IP_wrce           -- Write ce
--  Bus2IP_rdce           -- Read ce
--  Bus2IP_Data           -- Bus2ip data
--  Send_done             -- Read done
--  Reset_cr              -- Reset the control register
--  Icap_out              -- ICAP data out
--  Icap_status           -- ICAP status
--  Abort_in_progress     -- Abort in progress
--  Wrfifo_rden           -- Write fifo rden
--  Rdfifo_wren           -- Read fifo wren
--  Rdfifo_datain         -- Read fifo data in
--  Wrfifo_dataout        -- Write fifo data out
--  IP2Bus_Data           -- IP2 Bus data
--  Writefifo_full        -- Write fifo full
--  Writefifo_empty       -- Write fifo empty
--  Readfifo_full         -- Read fifo full
--  Readfifo_empty        -- Read fifo empty
--  Rnc                   -- Read not configure
--  Size                  -- Size of data transfer in words
--  IP2Bus_RdAck          -- IP2 Bus Read Ack
--  IP2Bus_WrAck          -- IP2 Bus Write Ack
--  IP2Bus_AddrAck        -- IP2 Bus Address Ack
--  IP2Bus_errAck         -- IP2 Bus error Ack
--  Intr_rst              -- Intrrupt control logic reset
--  IP2Bus_Intr           -- IP2 Bus interrupt
-------------------------------------------------------------------------------
-- Port declarations
-------------------------------------------------------------------------------

entity ipic_if is
    generic (
        C_ENABLE_ASYNC       : integer := 0;
        C_MODE               : integer := 0; 
        C_NOREAD             : integer := 0;
        C_INCLUDE_STARTUP    : integer := 0;
        C_SAXI_DWIDTH        : integer;
        C_WRITE_FIFO_DEPTH   : integer:= 16;
        C_READ_FIFO_DEPTH    : integer:= 16;
        C_SHARED_STARTUP     : integer range 0 to 1 := 0;
        ICAP_DWIDTH          : integer := 16;
        C_BRAM_SRL_FIFO_TYPE : integer := 1;  -- default BRAM
        C_FAMILY             : string  := "virtex7");
    port (
        ICAP_Clk             : in  std_logic;
        ICAP_Reset           : in  std_logic;
        Bus2IP_Clk           : in  std_logic;
        Bus2IP_Reset         : in  std_logic;
        Bus2IP_cs            : in  std_logic;
        Bus2IP_BE            : in  std_logic_vector(0 to C_SAXI_DWIDTH/8-1);
        Bus2IP_rnw           : in  std_logic;
        Bus2IP_wrce          : in  std_logic_vector(0 to 7);
        Bus2IP_rdce          : in  std_logic_vector(0 to 7);
        Bus2IP_Data          : in  std_logic_vector(0 to C_SAXI_DWIDTH-1);
        Send_done            : in  std_logic;
        Reset_cr             : in  std_logic;
        Icap_out             : in  std_logic_vector(0 to ICAP_DWIDTH-1);
        Icap_status          : in  std_logic_vector(0 to 31);
        Abort_in_progress    : in  std_logic;
        Wrfifo_rden          : in  std_logic;
        Rdfifo_wren          : in  std_logic;
        Hang_status          : in  std_logic; 
        Eos_in               : in  std_logic;
        icap_available       : in  std_logic; 
        Rdfifo_datain        : in  std_logic_vector(0 to ICAP_DWIDTH-1);
        Wrfifo_dataout       : out std_logic_vector(0 to ICAP_DWIDTH-1);
        IP2Bus_Data          : out std_logic_vector(0 to C_SAXI_DWIDTH-1);
        Writefifo_full       : out std_logic;
        Writefifo_empty      : out std_logic;
        Readfifo_full        : out std_logic;
        Readfifo_empty       : out std_logic;
        Abort                : out std_logic;
        Rnc                  : out std_logic_vector(0 to 1);
        Status_read          : out std_logic;
        Size                 : out std_logic_vector(0 to 11);
        Size_counter         : in  std_logic_vector(0 to 11);
        IP2Bus_RdAck         : out std_logic;
        IP2Bus_WrAck         : out std_logic;
        IP2Bus_AddrAck       : out std_logic;
        IP2Bus_errAck        : out std_logic;
        Intr_rst             : out std_logic;
        Gate_icap            : out std_logic;
        Gate_icap_p          : out std_logic;
        IP2Bus_Intr          : out std_logic_vector(0 to 3);
        CFGCLK : out std_logic;
        CFGMCLK : out std_logic;
        PREQ : out std_logic;
        CLK : in std_logic;
        GSR : in std_logic;
        GTS : in std_logic;
        KEYCLEARB : in std_logic;
        PACK : in std_logic;
        USRCCLKO : in std_logic;
        USRCCLKTS : in std_logic;
        USRDONEO : in std_logic;
        USRDONETS : in std_logic
    );
end entity ipic_if;

-------------------------------------------------------------------------------
-- Architecture section
-------------------------------------------------------------------------------

architecture imp of ipic_if is
  attribute DowngradeIPIdentifiedWarnings: string;
  attribute DowngradeIPIdentifiedWarnings of imp : architecture is "yes";


constant MTBF_STAGES : integer := 4;
constant Z : std_logic_vector(0 to 99) := (others => '0');
constant FGEN_CNT_WIDTH_WR     : integer := log2(C_WRITE_FIFO_DEPTH);
constant ADJ_FGEN_CNT_WIDTH_WR : integer := FGEN_CNT_WIDTH_WR;
constant FGEN_CNT_WIDTH_RD     : integer := log2(C_READ_FIFO_DEPTH);
constant ADJ_FGEN_CNT_WIDTH_RD : integer := FGEN_CNT_WIDTH_RD;
constant ADJ_RDFIFO_DEPTH      : integer := C_READ_FIFO_DEPTH;
constant ADJ_WRFIFO_DEPTH      : integer := C_WRITE_FIFO_DEPTH;
constant HALF_WRFIFO_DEPTH     : integer := C_WRITE_FIFO_DEPTH/2;
constant HALF_RDFIFO_DEPTH     : integer := C_READ_FIFO_DEPTH/2;
constant RD_FIFO_ALMOST_FULL   : integer := C_READ_FIFO_DEPTH-4;
ATTRIBUTE async_reg                      : STRING;

-------------------------------------------------------------------------------
-- Signal Declaration
-------------------------------------------------------------------------------
signal wroccy            : std_logic_vector(0 to ADJ_FGEN_CNT_WIDTH_WR-1);
signal wrvacancy         : std_logic_vector(0 to ADJ_FGEN_CNT_WIDTH_WR-1);
signal wr_count         : std_logic_vector(0 to ADJ_FGEN_CNT_WIDTH_RD-1);
signal rd_occy_i         : std_logic_vector(0 to ADJ_FGEN_CNT_WIDTH_RD-1);
signal rdoccy            : std_logic_vector(0 to ADJ_FGEN_CNT_WIDTH_RD-1);
signal sz_i              : std_logic_vector(0 to 11);
signal Size_i_cdc_tig              : std_logic_vector(0 to 11);
signal Size_i2              : std_logic_vector(0 to 11);
signal Size_counter_i_cdc_tig              : std_logic_vector(0 to 11);
signal Size_counter_i2              : std_logic_vector(0 to 11);
signal Size_counter_i3              : std_logic_vector(0 to 11);
--  ATTRIBUTE async_reg OF Size_i_cdc_tig  : SIGNAL IS "true";
--  ATTRIBUTE async_reg OF Size_i2  : SIGNAL IS "true";
--  ATTRIBUTE async_reg OF Size_counter_i_cdc_tig  : SIGNAL IS "true";
--  ATTRIBUTE async_reg OF Size_counter_i2  : SIGNAL IS "true";
signal cr_i              : std_logic_vector(0 to 4);
signal sr_i              : std_logic_vector(0 to 31);
signal sr_icap2bus_1_cdc_tig     : std_logic_vector(0 to 31);
signal sr_icap2bus_2     : std_logic_vector(0 to 31);
--  ATTRIBUTE async_reg OF sr_icap2bus_1_cdc_tig  : SIGNAL IS "true";
--  ATTRIBUTE async_reg OF sr_icap2bus_2  : SIGNAL IS "true";

signal sr_icap2bus_3     : std_logic_vector(0 to 31);
signal fifo_rst          : std_logic;
signal wrfifo_occy       : std_logic;
signal rdfifo_occy       : std_logic;
signal fifo_clear        : std_logic;
signal sw_reset          : std_logic;
signal IP2Bus_Rderrack   : std_logic;
signal abort_onreset     : std_logic;
signal dt_fifo_wr_i      : std_logic;
signal read_en_qual      : std_logic;
signal wrfifo_full       : std_logic;
signal wrfifo_empty      : std_logic;
signal wrfifo_empty_int      : std_logic;
signal wrfifo_empty_cdc_tig : std_logic;
signal dt_fifo_rd_i      : std_logic;
signal rdfifo_dataout    : std_logic_vector(0 to ICAP_DWIDTH-1);
signal RdFifo_Dout       : std_logic_vector(0 to C_SAXI_DWIDTH-1);
signal rdfifo_full_int       : std_logic;
signal rdfifo_full_cdc_tig       : std_logic;
signal rdfifo_full       : std_logic;
signal rdfifo_empty      : std_logic;
signal rdfifo_rdack      : std_logic;
signal status_read_bus2icap : std_logic;
signal send_done_icap2bus: std_logic;
signal reset_cr_icap2bus : std_logic;
signal send_done_icap2bus_i_cdc_tig : std_logic;
signal reset_cr_icap2bus_i_cdc_tig : std_logic;

--  ATTRIBUTE async_reg OF rdfifo_full_cdc_tig  : SIGNAL IS "true";
--  ATTRIBUTE async_reg OF rdfifo_full  : SIGNAL IS "true";

--  ATTRIBUTE async_reg OF wrfifo_empty_cdc_tig  : SIGNAL IS "true";
--  ATTRIBUTE async_reg OF wrfifo_empty  : SIGNAL IS "true";

--  ATTRIBUTE async_reg OF send_done_icap2bus_i_cdc_tig  : SIGNAL IS "true";
--  ATTRIBUTE async_reg OF status_read_bus2icap  : SIGNAL IS "true";

--  ATTRIBUTE async_reg OF reset_cr_icap2bus_i_cdc_tig  : SIGNAL IS "true";
--  ATTRIBUTE async_reg OF reset_cr_icap2bus  : SIGNAL IS "true";
signal Abort_i_cdc_tig           : std_logic;
signal Abort_i2           : std_logic;
signal Rnc_i_cdc_tig             : std_logic_vector(0 to 1);
signal Rnc_i2             : std_logic_vector(0 to 1);

--  ATTRIBUTE async_reg OF Abort_i_cdc_tig  : SIGNAL IS "true";
--  ATTRIBUTE async_reg OF Abort_i2  : SIGNAL IS "true";
--  ATTRIBUTE async_reg OF Rnc_i_cdc_tig  : SIGNAL IS "true";
--  ATTRIBUTE async_reg OF Rnc_i2  : SIGNAL IS "true";
signal Status_read_i     : std_logic;
signal rdfifo_wren_q     : std_logic;
signal gate_s : std_logic;
signal gate_s_p : std_logic;
signal rdfifo_almost_full : std_logic;
signal gate_signal : std_logic;
signal gate_signal_p : std_logic;
signal rdfifo_half_wr : std_logic;
signal write_data : std_logic_vector(0 to ICAP_DWIDTH-1);
signal Wrfifo_dataout_int : std_logic_vector(0 to ICAP_DWIDTH-1);
signal fifo_full, fifo_empty : std_logic;
signal hang_status_i_cdc_tig, hang_status_i2 : std_logic;
signal ipbus_0, ipbus_1, ipbus_2 : std_logic;
signal ipbus_ack_fifo, ipbus_ack : std_logic;
signal busip_0, busip_1, busip_2 : std_logic;
signal busip_ack_fifo, busip_ack : std_logic;

signal eos_int : std_logic;
signal eos_status_i_cdc_tig : std_logic;
signal eos_status_i2 : std_logic;
signal full_int_1 : std_logic;
signal full_int_2 : std_logic;

signal fifo_full_mask : std_logic;
signal rdfifo_full_d1 : std_logic;
signal rdfifo_full_ip2bus : std_logic;
signal rdfifo_full_fall : std_logic;
--  ATTRIBUTE async_reg OF eos_status_i_cdc_tig  : SIGNAL IS "true";
--  ATTRIBUTE async_reg OF eos_status_i2  : SIGNAL IS "true";

--  ATTRIBUTE async_reg OF hang_status_i_cdc_tig  : SIGNAL IS "true";
--  ATTRIBUTE async_reg OF hang_status_i2  : SIGNAL IS "true";
--signal count_rdce : std_logic_vector (11 downto 0);
--signal count_wrce : std_logic_vector (11 downto 0);
--attribute keep : string;
--attribute keep of count_rdce : signal is "true";
--attribute keep of count_wrce : signal is "true";
-----------------------------------------------------------------------------
-- Begin architecture
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
--  Function Declarations
-------------------------------------------------------------------------------
----------------------------------------------------------------------------
-- Replicate sl into a std_logic_vector of width 32.
----------------------------------------------------------------------------
function r32(sl : std_logic) return std_logic_vector is
    variable slv : std_logic_vector(0 to 31) := (others => sl);
begin
    return slv;
end r32;
----------------------------------------------------------------------------
-- Bitwise OR of a std_logic_vector.
----------------------------------------------------------------------------
function or_reduce(slv : std_logic_vector) return std_logic is
    variable r : std_logic := '0';
begin
    for i in slv'range loop
        r := r or slv(i);
    end loop;
    return r;
end or_reduce;

begin -- architecture IMP

-- SIZE_REGISTER_PROCESS
-------------------------------------------------------------------------------
-- This process loads data from the PLB Bus into size register when the
-- corresponding write chip enable is high
-------------------------------------------------------------------------------
  SIZE_REGISTER_PROCESS:process (Bus2IP_Clk)
  begin
    if Bus2IP_Clk'event and Bus2IP_Clk = '1' then
      if sw_reset = '1' then
         sz_i <= (others => '0');
      elsif Bus2IP_wrce(2)= '1' then
         sz_i(0 to 11) <= Bus2IP_Data(20 to 31);
      else
         sz_i <= sz_i;
      end if;
    end if;
  end process SIZE_REGISTER_PROCESS;

BUS2ICAP_SIZE_REGISTER_PROCESS : entity lib_cdc_v1_0_2.cdc_sync
    generic map (
        C_CDC_TYPE                 => 1,
        C_RESET_STATE              => 0,
        C_SINGLE_BIT               => 0,
        C_VECTOR_WIDTH             => 12,
        C_MTBF_STAGES              => MTBF_STAGES
    )
    port map (
        prmry_aclk                 => Bus2IP_Clk,
        prmry_resetn               => '0',
        prmry_in                   => '0',
        prmry_vect_in              => sz_i,

        scndry_aclk                => ICAP_Clk,
        scndry_resetn              => '0',
        scndry_out                 => open, --awvalid_to,
        scndry_vect_out            => Size
    );



--  BUS2ICAP_SIZE_REGISTER_PROCESS:process (ICAP_Clk)
--  begin
--    if ICAP_Clk'event and ICAP_Clk = '1' then
--      Size_i_cdc_tig     <= sz_i;
--      Size_i2    <= Size_i_cdc_tig;
--      Size    <= Size_i2;
--    end if;
--  end process BUS2ICAP_SIZE_REGISTER_PROCESS;

-- CONTROL_REGISTER_PROCESS
-------------------------------------------------------------------------------
-- This process loads data from the PLB Bus into control register when the
-- corresponding write chip enable is high
-------------------------------------------------------------------------------
  CONTROL_REGISTER_PROCESS:process (Bus2IP_Clk)
  begin
    if Bus2IP_Clk'event and Bus2IP_Clk = '1' then
      if sw_reset = '1' or reset_cr_icap2bus = '1' then
         cr_i <= (others => '0');
      elsif Bus2IP_wrce(3)= '1' then
         cr_i(0 to 4) <= Bus2IP_Data(27 to 31);
      else
         cr_i <= cr_i;
      end if;
    end if;
  end process CONTROL_REGISTER_PROCESS;

-------------------------------------------------------------------------------
-- STATUS_REGISTER_PROCESS
-------------------------------------------------------------------------------
-- This process loads data from Icap_status when Abort_in_progress enabled else
-- loads the Icap_out data into status register
-------------------------------------------------------------------------------
  STATUS_REGISTER_PROCESS:process (ICAP_Clk)
  begin
    if ICAP_Clk'event and ICAP_Clk = '1' then
      if ICAP_Reset = '1' then
         sr_i <= (others => '0');
      elsif Abort_in_progress = '1' then
         sr_i <= Icap_status;
      else
         sr_i <= sr_i; --"00000000000000000000000" & Icap_out(ICAP_DWIDTH-8 to ICAP_DWIDTH-1);
      end if;
    end if;
  end process STATUS_REGISTER_PROCESS;


ICAP2BUS_STATUS_REGISTER_PROCESS : entity lib_cdc_v1_0_2.cdc_sync
    generic map (
        C_CDC_TYPE                 => 1,
        C_RESET_STATE              => 0,
        C_SINGLE_BIT               => 0,
        C_VECTOR_WIDTH             => 32,
        C_MTBF_STAGES              => MTBF_STAGES
    )
    port map (
        prmry_aclk                 => ICAP_Clk,
        prmry_resetn               => '0',
        prmry_in                   => '0',
        prmry_vect_in              => sr_i,

        scndry_aclk                => Bus2IP_Clk,
        scndry_resetn              => '0',
        scndry_out                 => open, --awvalid_to,
        scndry_vect_out            => sr_icap2bus_3
    );


--  ICAP2BUS_STATUS_REGISTER_PROCESS:process (Bus2IP_Clk)
--  begin
--    if Bus2IP_Clk'event and Bus2IP_Clk = '1' then
--       sr_icap2bus_1_cdc_tig <= sr_i;
--       sr_icap2bus_2 <= sr_icap2bus_1_cdc_tig;
--       sr_icap2bus_3 <= sr_icap2bus_2;
--    end if;
--  end process ICAP2BUS_STATUS_REGISTER_PROCESS;

-------------------------------------------------------------------------------
-- DATA FIFO INSTANTIATION
-------------------------------------------------------------------------------

WRFIFO : if (C_MODE = 0) generate
begin
   read_en_qual <= Wrfifo_rden and not wrfifo_empty_int;
   dt_fifo_wr_i <= Bus2IP_wrce(0) and not(wrfifo_full) and (busip_ack);



   WRDATA_FIFO_I: entity lib_fifo_v1_0_6.async_fifo_fg
     generic map(
       C_ALLOW_2N_DEPTH   => 1,  -- New paramter to leverage FIFO Gen 2**N depth
       C_FAMILY           => C_FAMILY,  -- new for FIFO Gen
       C_DATA_WIDTH       => ICAP_DWIDTH,
       C_ENABLE_RLOCS     => 0,  -- not supported in FG
       C_FIFO_DEPTH       => ADJ_WRFIFO_DEPTH,
       C_HAS_ALMOST_EMPTY => 1,
       C_HAS_ALMOST_FULL  => 1,
       C_HAS_RD_ACK       => 1,
       C_HAS_RD_COUNT     => 1,
       C_HAS_RD_ERR       => 0,
       C_EN_SAFETY_CKT    => 1,  
       C_USE_EMBEDDED_REG => 0,  
       C_HAS_WR_ACK       => 1,
       C_HAS_WR_COUNT     => 1,
       C_HAS_WR_ERR       => 0,
       C_RD_ACK_LOW       => 0,
       C_RD_COUNT_WIDTH   => ADJ_FGEN_CNT_WIDTH_WR,
       C_RD_ERR_LOW       => 0,
       C_USE_BLOCKMEM     => C_BRAM_SRL_FIFO_TYPE,  -- 0 = distributed RAM, 1 = BRAM
       C_WR_ACK_LOW       => 0,
       C_WR_COUNT_WIDTH   => ADJ_FGEN_CNT_WIDTH_WR,
       C_WR_ERR_LOW       => 0,
       C_SYNCHRONIZER_STAGE  =>  MTBF_STAGES 
     )
     port map(
       Din            => Bus2IP_Data(C_SAXI_DWIDTH-ICAP_DWIDTH to C_SAXI_DWIDTH-1),
       Wr_en          => dt_fifo_wr_i,
       Wr_clk         => Bus2IP_Clk,
       Rd_en          => read_en_qual,
       Rd_clk         => ICAP_Clk,
       Ainit          => fifo_clear,
       Dout           => Wrfifo_dataout,
       Full           => wrfifo_full,
       Empty          => wrfifo_empty_int,
       Almost_full    => open,
       Almost_empty   => open,
       Wr_count       => wroccy,
       Rd_count       => open,
       Rd_ack         => open,
       Rd_err         => open,
       Wr_ack         => open,
       Wr_err         => open
     );



   wrvacancy <= ((conv_std_logic_vector((C_WRITE_FIFO_DEPTH),(log2(C_WRITE_FIFO_DEPTH))) - (wroccy)) -1);

WREMPTY_SYNCH : entity lib_cdc_v1_0_2.cdc_sync
    generic map (
        C_CDC_TYPE                 => 1,
        C_RESET_STATE              => 0,
        C_SINGLE_BIT               => 1,
        C_VECTOR_WIDTH             => 32,
        C_MTBF_STAGES              => MTBF_STAGES
    )
    port map (
        prmry_aclk                 => ICAP_Clk,
        prmry_resetn               => '0',
        prmry_in                   => wrfifo_empty_int,
        prmry_vect_in              => (others => '0'),

        scndry_aclk                => Bus2IP_Clk,
        scndry_resetn              => '0',
        scndry_out                 => wrfifo_empty, --awvalid_to,
        scndry_vect_out            => open
    );



--  WREMPTY_SYNCH:process (Bus2IP_Clk)
--  begin
--    if Bus2IP_Clk'event and Bus2IP_Clk = '1' then
--       wrfifo_empty_cdc_tig <= wrfifo_empty_int;
--       wrfifo_empty <= wrfifo_empty_cdc_tig;
--
--    end if;
--  end process;


end generate WRFIFO;

NO_WRFIFO : if (C_MODE = 1) generate
begin
-- Write from AXI4-Lite
   read_en_qual <= Wrfifo_rden; -- and not wrfifo_empty;
   dt_fifo_wr_i <= Bus2IP_wrce(0); -- and not(wrfifo_full);

  WRT_PROCESS:process (fifo_clear, Bus2IP_Clk)
  begin
    if (fifo_clear = '1') then
        write_data <= (others => '0');
        wrfifo_full <= '0';
        fifo_empty <= '1'; 
        wrvacancy (ADJ_FGEN_CNT_WIDTH_WR-1) <= '1';
        wrvacancy (0 to ADJ_FGEN_CNT_WIDTH_WR-2) <= (others => '0'); 
    elsif Bus2IP_Clk'event and Bus2IP_Clk = '1' then
      if (dt_fifo_wr_i = '1') then
        write_data <= Bus2IP_Data(C_SAXI_DWIDTH-ICAP_DWIDTH to C_SAXI_DWIDTH-1); 
        wrfifo_full <= '1';
        wrvacancy <= (others => '0');
        fifo_empty <= '0'; 
      else
        write_data <= write_data;
        wrfifo_full <= wrfifo_full and fifo_full;
        wrvacancy <= wrvacancy; 
        fifo_empty <= fifo_empty; 
      end if;
    end if;
  end process WRT_PROCESS;


  RD_PROCESS:process (fifo_clear, ICAP_Clk)
  begin
    if (fifo_clear = '1') then
      Wrfifo_dataout_int <= (others => '0');
      wrfifo_empty <= '1';
      fifo_full <= '0';
    elsif ICAP_Clk'event and ICAP_Clk = '1' then
      if (read_en_qual = '1') then
        Wrfifo_dataout_int <= write_data;
        wrfifo_empty <= '1';
        fifo_full <= '0';
      else
        Wrfifo_dataout_int <= Wrfifo_dataout_int;
        wrfifo_empty <= fifo_empty and wrfifo_empty;
        fifo_full <= wrfifo_full;
      end if;
    end if;
  end process RD_PROCESS;

Wrfifo_dataout <= Wrfifo_dataout_int;

end generate NO_WRFIFO;

RD_FIFO : if (C_NOREAD = 0) generate
   rdfifo_wren_q <= Rdfifo_wren and (not rdfifo_full_int);


   RDDATA_FIFO_I: entity lib_fifo_v1_0_6.async_fifo_fg
     generic map(
       C_ALLOW_2N_DEPTH   => 1,  -- New paramter to leverage FIFO Gen 2**N depth
       C_FAMILY           => C_FAMILY,  -- new for FIFO Gen
       C_DATA_WIDTH       => ICAP_DWIDTH,
       C_ENABLE_RLOCS     => 0,  -- not supported in FG
       C_FIFO_DEPTH       => ADJ_RDFIFO_DEPTH,
       C_HAS_ALMOST_EMPTY => 1,
       C_HAS_ALMOST_FULL  => 1,
       C_HAS_RD_ACK       => 1,
       C_HAS_RD_COUNT     => 1,
       C_HAS_RD_ERR       => 0,
       C_HAS_WR_ACK       => 1,
       C_EN_SAFETY_CKT    => 1,  
       C_USE_EMBEDDED_REG => 0,  
       C_HAS_WR_COUNT     => 1,
       C_HAS_WR_ERR       => 0,
       C_RD_ACK_LOW       => 0,
       C_RD_COUNT_WIDTH   => ADJ_FGEN_CNT_WIDTH_RD,
       C_RD_ERR_LOW       => 0,
       C_USE_BLOCKMEM     => C_BRAM_SRL_FIFO_TYPE,  -- 0 = distributed RAM, 1 = BRAM
       C_WR_ACK_LOW       => 0,
       C_WR_COUNT_WIDTH   => ADJ_FGEN_CNT_WIDTH_RD,
       C_WR_ERR_LOW       => 0,
       C_SYNCHRONIZER_STAGE  =>  MTBF_STAGES
     )
     port map(
       Din            => Rdfifo_datain,
       Wr_en          => rdfifo_wren_q, --Rdfifo_wren,
       Wr_clk         => ICAP_Clk,
       Rd_en          => dt_fifo_rd_i,
       Rd_clk         => Bus2IP_Clk,
       Ainit          => fifo_clear,
       Dout           => rdfifo_dataout,
       Full           => rdfifo_full_int,
       Empty          => rdfifo_empty,
       Almost_full    => open,
       Almost_empty   => open,
       Wr_count       => wr_count,
       Rd_count       => rd_occy_i,
       Rd_ack         => rdfifo_rdack,
       Rd_err         => open,
       Wr_ack         => open,
       Wr_err         => open
     );


   rdoccy    <= rd_occy_i;

--   dt_fifo_rd_i <= Bus2IP_rdce(1) and not(rdfifo_empty) and (not rdfifo_rdack);
   dt_fifo_rd_i <= Bus2IP_rdce(1) and not(rdfifo_empty) and (ipbus_ack);

--  process (ICAP_Clk,fifo_clear)
--  begin
--    if (fifo_clear = '1') then
--      full_int_clear_1 <= '1';
--      full_int_clear_2 <= '1';
--    elsif ICAP_Clk'event and ICAP_Clk = '1' then
--      full_int_clear_1 <= '0';
--      full_int_clear_2 <= full_int_clear_1;
--    end if;
--  end process;

--   FIFO_FULL_PROCESS:process (ICAP_Clk,full_int_clear_2)
--  begin
--    if (fifo_int_clear_2 = '1') then
--      full_int_1 <= '1';
--      full_int_2 <= '0';
--    elsif ICAP_Clk'event and ICAP_Clk = '1' then
--      if ((full_int_1 = '1') and (rdfifo_full_int = '1'))  then
--        full_int_2 <= '0';
--      else
--        full_int_2 <= rdfifo_full_int;
--        full_int_1 <= '0';
--      end if;
--    end if;
--  end process FIFO_FULL_PROCESS;
  
   

RDFULL_SYNCH : entity lib_cdc_v1_0_2.cdc_sync
    generic map (
        C_CDC_TYPE                 => 1,
        C_RESET_STATE              => 0,
        C_SINGLE_BIT               => 1,
        C_VECTOR_WIDTH             => 32,
        C_MTBF_STAGES              => MTBF_STAGES-1
    )
    port map (
        prmry_aclk                 => ICAP_Clk,
        prmry_resetn               => '0',
        prmry_in                   => rdfifo_full_int,
        prmry_vect_in              => (others => '0'),

        scndry_aclk                => Bus2IP_Clk,
        scndry_resetn              => '0',
        scndry_out                 => rdfifo_full_ip2bus, --awvalid_to,
        scndry_vect_out            => open
    );


    process (Bus2IP_Clk)
    begin
      if (Bus2IP_Clk'event and Bus2IP_Clk = '1') then
               rdfifo_full_d1 <= rdfifo_full_ip2bus;
      end if;
    end process;

        rdfifo_full_fall <= rdfifo_full_d1 and (not rdfifo_full_ip2bus);

    process (Bus2IP_Clk)
    begin
      if (Bus2IP_Clk'event and Bus2IP_Clk = '1') then
          if (fifo_clear = '1') then
               fifo_full_mask <= '0';
          elsif (rdfifo_full_fall = '1') then
               fifo_full_mask <= '1';
          end if;
      end if;
    end process;

     rdfifo_full <= fifo_full_mask and rdfifo_full_d1;

--  RDFULL_SYNCH:process (Bus2IP_Clk)
--  begin
--    if Bus2IP_Clk'event and Bus2IP_Clk = '1' then
--       rdfifo_full_cdc_tig <= rdfifo_full_int;
--       rdfifo_full <= rdfifo_full_cdc_tig;
--
--    end if;
--  end process;

end generate RD_FIFO;

NORD_FIFO : if (C_NOREAD = 1) generate
begin

rdfifo_dataout <= (others => '0');
rdfifo_full <= '0';
rdfifo_empty <= '0';
wr_count <= (others => '0');
rdoccy <= (others => '0');
rdfifo_rdack <= '1'; -- to make sure read does not hang

end generate NORD_FIFO;
-- In order to gate the ICAP_Clk, a gating signal has to be generated
-- This signal is generated when RDFIFO is at RD_FIFO_ALMOST_FULL
-- This makes sure that the ICAP is gated at the right time such that
-- no data is lost and also the FIFO becomes full
-- The gating signal is them released when RDFIFO is HALF_RDFIFO_DEPTH
-- To be on the safer side, gating signal is driven on negedge of ICAP_Clk

   rdfifo_almost_full <= '1' when (wr_count >= RD_FIFO_ALMOST_FULL) else '0';
   rdfifo_half_wr <= '1' when (wr_count <= HALF_RDFIFO_DEPTH) else '0';


   gate_s <= rdfifo_almost_full;

   gate_stretch_process : process (ICAP_Clk)
   begin
      if ICAP_Clk'event and ICAP_Clk = '0' then
         if ICAP_Reset = '1' then
            gate_signal <= '0';
         elsif (gate_s = '1') then
            gate_signal <= '1';
         elsif (rdfifo_half_wr = '1') then
            gate_signal <= '0';
         else
            gate_signal <= gate_signal;
         end if;
      end if;
   end process;
          
   Gate_icap <= gate_signal;

-- A replica of gating signal is generated on posedge
-- This is required to make sure that extra or invalid 
-- wren are not generated for RDFIFO when the ICAP is
-- gated

   gate_s_p <= rdfifo_almost_full;

   gate_stretch_p_process : process (ICAP_Clk)
   begin
      if ICAP_Clk'event and ICAP_Clk = '1' then
         if ICAP_Reset = '1' then
            gate_signal_p <= '0';
         elsif (gate_s_p = '1') then
            gate_signal_p <= '1';
         elsif (rdfifo_half_wr = '1') then
            gate_signal_p <= '0';
         else
            gate_signal_p <= gate_signal_p;
         end if;
      end if;
   end process;
          
   Gate_icap_p <= gate_signal_p;



--   count_rdce_process : process (Bus2IP_Clk)
--   begin
--		if Bus2IP_Clk'event and Bus2IP_Clk = '1' then
--			if (dt_fifo_rd_i = '1') then
--                           count_rdce <= count_rdce + '1';
--                        end if;
--                 end if;
--   end process;
--   count_wrce_process : process (ICAP_Clk)
--   begin
--		if ICAP_Clk'event and ICAP_Clk = '1' then
--			if (rdfifo_wren_q = '1') then
--                           count_wrce <= count_wrce + '1';
--                        end if;
--                 end if;
--   end process;

-------------------------------------------------------------------------------
-- FIFO_RESET_PROCESS
-------------------------------------------------------------------------------
-- This process generates fifo reset signal based on status in control register
-------------------------------------------------------------------------------

  FIFO_RESET_PROCESS:process (Bus2IP_Clk)
  begin
    if Bus2IP_Clk'event and Bus2IP_Clk = '1' then
      if Bus2IP_Reset = '1' then
        abort_onreset<= '1';
        fifo_rst  <= '1';
        sw_reset  <= '1';
        Intr_rst  <= '1';
        Size_counter_i3 <= (others => '0'); 
      else
        abort_onreset<= (cr_i(0) and reset_cr_icap2bus);
        Intr_rst  <= cr_i(1);
        sw_reset  <= cr_i(1);
        fifo_rst  <= cr_i(2);
        Size_counter_i3 <= Size_counter_i2;
      end if;
    end if;
  end process FIFO_RESET_PROCESS;

  fifo_clear <= sw_reset or fifo_rst or abort_onreset;

-------------------------------------------------------------------------------
-- Interrupt generation
-------------------------------------------------------------------------------

wrfifo_occy <= '1' when wroccy <= HALF_WRFIFO_DEPTH else
                   '0';  -- generation of interupt based on PIRQ value
rdfifo_occy <= '1' when rdoccy >= HALF_RDFIFO_DEPTH else
                   '0';  -- generation of interupt based on PIRQ value

-------------------------------------------------------------------------------
-- Pasing out the interrupts
-------------------------------------------------------------------------------

  IP2Bus_Intr <= (others => '0') when sw_reset = '1' else
               wrfifo_occy & rdfifo_occy & wrfifo_empty & rdfifo_full;
-------------------------------------------------------------------------------
-- READ_REGISTER_PROCESS
-------------------------------------------------------------------------------
-- Process for IP2Bus_Data. This process is for reading data from the Control
-- register,FIFO, FIFO occupancy register and pirq register. This reading of
-- data depends on assertion of one of the bits of Bus2IP_rdce on rising edge
-- of Bus2IP_CLK. Reading of any of
-- these registers is accompanied by assertion of IP to Bus read acknowledge
-- signal.
-------------------------------------------------------------------------------

  READ_REGISTER_PROCESS : process(Bus2IP_CLK)
  begin
     if (Bus2IP_CLK'event and Bus2IP_CLK = '1') then
       if sw_reset = '1' then
         IP2Bus_Data <= (others=> '0');
         IP2Bus_RdAck<= '0';
         IP2Bus_Rderrack <= '0';
         IP2Bus_WrAck   <= '0';
       else
         IP2Bus_Data <=
              (r32(Bus2IP_rdce(1)) and (RdFifo_Dout))
           or (r32(Bus2IP_rdce(2)) and (Z(0 to 19) & Size_counter_i3(0 to 11)))
           or (r32(Bus2IP_rdce(3)) and (Z(0 to 26) & cr_i(0 to 4)))
           or (r32(Bus2IP_rdce(4)) and (Z(0 to 28) & eos_status_i2 & hang_status_i2 & send_done_icap2bus))
           or (r32(Bus2IP_rdce(5)) and (Z(0 to (31 -log2(C_WRITE_FIFO_DEPTH))) & wrvacancy(0 to log2(C_WRITE_FIFO_DEPTH)-1)))
           or (r32(Bus2IP_rdce(6)) and (Z(0 to (31 -log2(C_READ_FIFO_DEPTH))) & rdoccy(0 to log2(C_READ_FIFO_DEPTH)-1)))
           or (r32(Bus2IP_rdce(7)) and (sr_icap2bus_3));
         IP2Bus_RdAck   <= ((or_reduce(Bus2IP_rdce(2 to 7))) and ipbus_ack) or
                             (Bus2IP_rdce(1) and ipbus_ack_fifo);
         IP2Bus_Rderrack<= (Bus2IP_rdce(0));
         IP2Bus_WrAck   <= ((or_reduce(Bus2IP_wrce(1 to 7)) 
		                     or (Bus2IP_wrce(0) and (not (wrfifo_full))))
							  and busip_ack);
       end if;
     end if;
  end process READ_REGISTER_PROCESS;

-------------------------------------------------------------------------------
-- RdFifo_Dout
-------------------------------------------------------------------------------
RDFIFO_DATA: process (rdfifo_dataout) is
  begin
        RdFifo_Dout <= rdfifo_dataout;
  end process RDFIFO_DATA;

-------------------------------------------------------------------------------
-- IP2BUS_ACK
-------------------------------------------------------------------------------
-- IP2Bus_Ack on same cycle as data is taken.
-------------------------------------------------------------------------------
   ipbus_0 <= (or_reduce (Bus2IP_rdce(0 to 7)));

  IPBUS_SYNCH:process (Bus2IP_Clk)
  begin
    if Bus2IP_Clk'event and Bus2IP_Clk = '1' then
       ipbus_1 <= ipbus_0;
       ipbus_2 <= ipbus_1;
     
       ipbus_ack_fifo <= ipbus_ack;  
     
    end if;
  end process;

   ipbus_ack <= ipbus_1 and (not ipbus_2);

   busip_0 <= (or_reduce (Bus2IP_wrce(0 to 7)));

  BUSIP_SYNCH:process (Bus2IP_Clk)
  begin
    if Bus2IP_Clk'event and Bus2IP_Clk = '1' then
       busip_1 <= busip_0;
       busip_2 <= busip_1;
     
       busip_ack_fifo <= busip_ack;  
     
    end if;
  end process;

   busip_ack <= busip_0 and (not busip_1);
--   IP2Bus_RdAck   <= ((or_reduce(Bus2IP_rdce(2 to 7)))) or
--                             (Bus2IP_rdce(1) and rdfifo_rdack);

--   IP2Bus_RdAck   <= ((or_reduce(Bus2IP_rdce(2 to 7))) and ipbus_ack) or
--                             (Bus2IP_rdce(1) and ipbus_ack_fifo);

 --  IP2Bus_Rderrack<= (Bus2IP_rdce(0)or
  --                           Bus2IP_rdce(7));
--   IP2Bus_WrAck   <= or_reduce(Bus2IP_wrce(0 to 7) and busip_ack);
   IP2Bus_AddrAck <= or_reduce(Bus2IP_wrce(0 to 7)) or 
                     (or_reduce(Bus2IP_rdce(0 to 7)));

   IP2Bus_errAck <= '0'; --Bus2IP_wrce(1) or or_reduce(Bus2IP_wrce(4 to 7)) or
                         --  IP2Bus_Rderrack;

   Writefifo_full <=  wrfifo_full;
WRFIFO_INCL : if (C_MODE = 0) generate
begin
   Writefifo_empty<=  wrfifo_empty_int;
end generate WRFIFO_INCL;

WRFIFO_NOT_INCL : if (C_MODE = 1) generate
begin
   Writefifo_empty<=  wrfifo_empty;
end generate WRFIFO_NOT_INCL;

   Readfifo_full  <=  rdfifo_full_int;
   Readfifo_empty <=  rdfifo_empty;

-------------------------------------------------------------------------------
-- This process generates synchronizes signals from plb bus to ICAP clock
-------------------------------------------------------------------------------

PLB2ICAP_SYNCH1 : entity lib_cdc_v1_0_2.cdc_sync
    generic map (
        C_CDC_TYPE                 => 1,
        C_RESET_STATE              => 0,
        C_SINGLE_BIT               => 1,
        C_VECTOR_WIDTH             => 32,
        C_MTBF_STAGES              => MTBF_STAGES
    )
    port map (
        prmry_aclk                 => Bus2IP_Clk,
        prmry_resetn               => '0',
        prmry_in                   => cr_i(0),
        prmry_vect_in              => (others => '0'),

        scndry_aclk                => ICAP_Clk,
        scndry_resetn              => '0',
        scndry_out                 => Abort, --awvalid_to,
        scndry_vect_out            => open
    );

PLB2ICAP_SYNCH2 : entity lib_cdc_v1_0_2.cdc_sync
    generic map (
        C_CDC_TYPE                 => 1,
        C_RESET_STATE              => 0,
        C_SINGLE_BIT               => 1,
        C_VECTOR_WIDTH             => 32,
        C_MTBF_STAGES              => MTBF_STAGES
    )
    port map (
        prmry_aclk                 => Bus2IP_Clk,
        prmry_resetn               => '0',
        prmry_in                   => cr_i(3),
        prmry_vect_in              => (others => '0'),

        scndry_aclk                => ICAP_Clk,
        scndry_resetn              => '0',
        scndry_out                 => Rnc(0), --awvalid_to,
        scndry_vect_out            => open
    );

PLB2ICAP_SYNCH3 : entity lib_cdc_v1_0_2.cdc_sync
    generic map (
        C_CDC_TYPE                 => 1,
        C_RESET_STATE              => 0,
        C_SINGLE_BIT               => 1,
        C_VECTOR_WIDTH             => 32,
        C_MTBF_STAGES              => MTBF_STAGES
    )
    port map (
        prmry_aclk                 => Bus2IP_Clk,
        prmry_resetn               => '0',
        prmry_in                   => cr_i(4),
        prmry_vect_in              => (others => '0'),

        scndry_aclk                => ICAP_Clk,
        scndry_resetn              => '0',
        scndry_out                 => Rnc(1), --awvalid_to,
        scndry_vect_out            => open
    );




  PLB2ICAP_SYNCH:process (ICAP_Clk)
  begin
    if ICAP_Clk'event and ICAP_Clk = '1' then
--        Abort_i_cdc_tig      <= cr_i(0);
--        Rnc_i_cdc_tig        <= cr_i(3 to 4);
        Status_read_i<= status_read_bus2icap;
--        Abort_i2     <= Abort_i_cdc_tig;      
--        Abort        <= Abort_i2;      
--        Rnc_i2       <= Rnc_i_cdc_tig;        
--        Rnc          <= Rnc_i2;        
        Status_read  <= Status_read_i;
    end if;
  end process PLB2ICAP_SYNCH;

-------------------------------------------------------------------------------
-- This process generates synchronizes signals from ICAP clock to plb clock
-------------------------------------------------------------------------------

ICAP2PLB_SYNCH1 : entity lib_cdc_v1_0_2.cdc_sync
    generic map (
        C_CDC_TYPE                 => 1,
        C_RESET_STATE              => 0,
        C_SINGLE_BIT               => 1,
        C_VECTOR_WIDTH             => 32,
        C_MTBF_STAGES              => MTBF_STAGES
    )
    port map (
        prmry_aclk                 => ICAP_Clk,
        prmry_resetn               => '0',
        prmry_in                   => Send_done,
        prmry_vect_in              => (others => '0'),

        scndry_aclk                => Bus2IP_Clk,
        scndry_resetn              => '0',
        scndry_out                 => send_done_icap2bus,
        scndry_vect_out            => open
    );

ICAP2PLB_SYNCH2 : entity lib_cdc_v1_0_2.cdc_sync
    generic map (
        C_CDC_TYPE                 => 1,
        C_RESET_STATE              => 0,
        C_SINGLE_BIT               => 1,
        C_VECTOR_WIDTH             => 32,
        C_MTBF_STAGES              => MTBF_STAGES
    )
    port map (
        prmry_aclk                 => ICAP_Clk,
        prmry_resetn               => '0',
        prmry_in                   => Reset_cr,
        prmry_vect_in              => (others => '0'),

        scndry_aclk                => Bus2IP_Clk,
        scndry_resetn              => '0',
        scndry_out                 => reset_cr_icap2bus,
        scndry_vect_out            => open
    );


ICAP2PLB_SYNCH3 : entity lib_cdc_v1_0_2.cdc_sync
    generic map (
        C_CDC_TYPE                 => 1,
        C_RESET_STATE              => 0,
        C_SINGLE_BIT               => 1,
        C_VECTOR_WIDTH             => 32,
        C_MTBF_STAGES              => MTBF_STAGES
    )
    port map (
        prmry_aclk                 => ICAP_Clk,
        prmry_resetn               => '0',
        prmry_in                   => Hang_status,
        prmry_vect_in              => (others => '0'),

        scndry_aclk                => Bus2IP_Clk,
        scndry_resetn              => '0',
        scndry_out                 => hang_status_i2,
        scndry_vect_out            => open
    );

ICAP2PLB_SYNCH4 : entity lib_cdc_v1_0_2.cdc_sync
    generic map (
        C_CDC_TYPE                 => 1,
        C_RESET_STATE              => 0,
        C_SINGLE_BIT               => 1,
        C_VECTOR_WIDTH             => 32,
        C_MTBF_STAGES              => MTBF_STAGES
    )
    port map (
        prmry_aclk                 => ICAP_Clk,
        prmry_resetn               => '0',
        prmry_in                   => eos_int,
        prmry_vect_in              => (others => '0'),

        scndry_aclk                => Bus2IP_Clk,
        scndry_resetn              => '0',
        scndry_out                 => eos_status_i2,
        scndry_vect_out            => open
    );


ICAP2PLB_SYNCH5 : entity lib_cdc_v1_0_2.cdc_sync
    generic map (
        C_CDC_TYPE                 => 1,
        C_RESET_STATE              => 0,
        C_SINGLE_BIT               => 0,
        C_VECTOR_WIDTH             => 12,
        C_MTBF_STAGES              => MTBF_STAGES
    )
    port map (
        prmry_aclk                 => ICAP_Clk,
        prmry_resetn               => '0',
        prmry_in                   => '0',
        prmry_vect_in              => Size_counter,

        scndry_aclk                => Bus2IP_Clk,
        scndry_resetn              => '0',
        scndry_out                 => open,
        scndry_vect_out            => Size_counter_i2
    );

--  ICAP2PLB_SYNCH:process (Bus2IP_Clk)
--  begin
--    if Bus2IP_Clk'event and Bus2IP_Clk = '1' then
--        send_done_icap2bus_i_cdc_tig <= Send_done;
--        reset_cr_icap2bus_i_cdc_tig  <= Reset_cr;
--        send_done_icap2bus   <= send_done_icap2bus_i_cdc_tig;
--        reset_cr_icap2bus    <= reset_cr_icap2bus_i_cdc_tig;

--        hang_status_i_cdc_tig <= Hang_status;
--        hang_status_i2 <= hang_status_i_cdc_tig;

--        eos_status_i_cdc_tig <= eos_int;
--        eos_status_i2 <= eos_status_i_cdc_tig;

--        Size_counter_i_cdc_tig <= Size_counter;
--        Size_counter_i2 <= Size_counter_i_cdc_tig;
--    end if;
--  end process ICAP2PLB_SYNCH;

STARTUP_INCLUDE : if (C_INCLUDE_STARTUP = 1) generate
begin


GEN_7Series_STARTUP :  if (( C_SHARED_STARTUP = 0) and 
            ((C_FAMILY = "virtex7") or
            (C_FAMILY = "kintex7") or
            (C_FAMILY = "zynq") or
            (C_FAMILY = "spartan7") or
            (C_FAMILY = "artix7"))  
           )
generate

    STARTUPE2_inst : STARTUPE2
    generic map (
    PROG_USR => "FALSE", 
    SIM_CCLK_FREQ => 0.0 
    )
    port map (
    CFGCLK => open,
    CFGMCLK => open,
    EOS => eos_int,
    PREQ => open,
    CLK => '0',
    GSR => '0',
    GTS => '0',
    KEYCLEARB => '0',
    PACK => '0',
    USRCCLKO => '0',
    USRCCLKTS => '0',
    USRDONEO => '1',
    USRDONETS => '0'
);

end generate GEN_7Series_STARTUP;

GEN_7Series_SharedSTARTUP : if (( C_SHARED_STARTUP = 1) and 
            ((C_FAMILY = "virtex7") or
            (C_FAMILY = "kintex7") or
            (C_FAMILY = "zynq") or
            (C_FAMILY = "spartan7") or
            (C_FAMILY = "artix7"))  
           )
generate

    STARTUPE2_inst : STARTUPE2
    generic map (
    PROG_USR => "FALSE", 
    SIM_CCLK_FREQ => 0.0 
    )
    port map (
    CFGCLK => CFGCLK,
    CFGMCLK => CFGMCLK,
    EOS => eos_int,
    PREQ => PREQ,
    CLK => CLK,
    GSR => GSR,
    GTS => GTS,
    KEYCLEARB => KEYCLEARB,
    PACK => PACK,
    USRCCLKO => USRCCLKO,
    USRCCLKTS => USRCCLKTS,
    USRDONEO => USRDONEO,
    USRDONETS => USRDONETS
);

end generate GEN_7Series_SharedSTARTUP;

end generate STARTUP_INCLUDE;


NOSTARTUP_INCLUDE : if (C_INCLUDE_STARTUP = 0) generate
begin

GEN_7Series_NOSTARTUP : if ( 
            (C_FAMILY = "virtex7") or
            (C_FAMILY = "kintex7") or
            (C_FAMILY = "zynq") or
            (C_FAMILY = "spartan7") or
            (C_FAMILY = "artix7")  
           ) generate
begin
     eos_int <= Eos_in;

end generate GEN_7Series_NOSTARTUP;


GEN_8Series_NOSTARTUP : if ( 
                          (C_FAMILY /= "virtex7") and
                          (C_FAMILY /= "kintex7") and
                          (C_FAMILY /= "zynq") and
                          (C_FAMILY /= "spartan7") and
                          (C_FAMILY /= "artix7")
                           ) generate
begin

     eos_int <= icap_available;

end generate GEN_8Series_NOSTARTUP;

end generate NOSTARTUP_INCLUDE;

end imp;



-------------------------------------------------------------------------------
-- icap_statemachine.vhd - entity/architecture pair

-------------------------------------------------------------------------------
-- (c) Copyright 2010 - 2011 Xilinx, Inc. All rights reserved.
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
-------------------------------------------------------------------------------
-- Filename:        icap_statemachine.vhd
-- Version :        v7.01a
-- Description:     This module genrates the ce, we signals to ICAP
--                  based on busy signal,control register & FIFO flags
--
-------------------------------------------------------------------------------
-- Naming Conventions:
--      active low signals:                     "*_n"
--      clock signals:                          "clk", "clk_div#", "clk_#x"
--      reset signals:                          "rst", "rst_n"
--      generics:                               "C_*"
--      user defined types:                     "*_TYPE"
--      state machine next state:               "*_ns"
--      state machine current state:            "*_cs"
--      combinatorial signals:                  "*_com"
--      pipelined or register delay signals:    "*_d#"
--      counter signals:                        "*cnt*"
--      clock enable signals:                   "*_ce"
--      internal version of output port         "*_i"
--      device pins:                            "*_pin"
--      ports:                                  - Names begin with Uppercase
--      processes:                              "*_PROCESS"
--      component instantiations:               "<ENTITY_>I_<#|FUNC>
-------------------------------------------------------------------------------
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.std_logic_unsigned.all;

library axi_lite_ipif_v3_0_4;
library lib_pkg_v1_0_2;
use lib_pkg_v1_0_2.lib_pkg.all;
use axi_lite_ipif_v3_0_4.ipif_pkg.all;
-------------------------------------------------------------------------------
-- -- Generics
--  ICAP_DWIDTH         -- Icap Data Width;
--  C_FAMILY            -- Family of FPGA
-- -- Inputs
--  Clk                 -- Clock
--  Rst                 -- Reset
--  Wrfifo_dataout      -- Write fifo data read
--  Icap_dataout        -- ICAP data out
--  Wrfifo_empty        -- Write fifo empty
--  Wrfifo_full         -- Write fifo full
--  Rdfifo_empty        -- Read fifo empty
--  Rdfifo_full         -- Read fifo full
--  Icap_busy           -- ICAP busy
--  Rnc                 -- Read not configuration
--  Size                -- Size of data transfer in words
-- -- Outputs
--  Wrfifo_rden         -- Write fifo read enable
--  Rdfifo_wren         -- Read fifo write enable
--  Icap_ce             -- ICAP chip enable
--  Icap_we             -- ICAP write eneble
--  Send_done           -- Read done
--  Reset_cr            -- Reset the control register
--  Icap_datain         -- ICAP data in
--  Rdfifo_datain       -- Read fifo data in
-------------------------------------------------------------------------------

entity icap_statemachine is
  generic (
    ICAP_DWIDTH         : integer := 16;
    C_MODE              : integer := 0;
    C_FAMILY            : string  := "virtex7");
  port (
    Clk                 : in  std_logic;
    Rst                 : in  std_logic;
    Wrfifo_dataout      : in  std_logic_vector(0 to ICAP_DWIDTH-1);
    Icap_dataout        : in  std_logic_vector(0 to ICAP_DWIDTH-1);
    Wrfifo_full         : in  std_logic;
    Wrfifo_empty        : in  std_logic;
    Rdfifo_empty        : in  std_logic;
    Rdfifo_full         : in  std_logic;
    Icap_busy           : in  std_logic;
    Rnc                 : in  std_logic_vector(0 to 1);
    Abort               : in  std_logic;
    Size                : in  std_logic_vector(0 to 11);
    Status_read         : in  std_logic;
    Size_counter        : out std_logic_vector(0 to 11);
    Wrfifo_rden         : out std_logic;
    Rdfifo_wren         : out std_logic;
    Icap_ce             : out std_logic;
    Icap_we             : out std_logic;
    Send_done           : out std_logic;
    Reset_cr            : out std_logic;
    Abort_in_progress   : out std_logic;
    Hang_status         : out std_logic;
    Icap_status         : out std_logic_vector(0 to 31);
    Icap_datain         : out std_logic_vector(0 to ICAP_DWIDTH-1);
    Rdfifo_datain       : out std_logic_vector(0 to ICAP_DWIDTH-1)
    );

attribute KEEP : string;
attribute KEEP of Icap_ce : signal is "TRUE";
attribute KEEP of Icap_we : signal is "TRUE";
attribute KEEP of Icap_datain : signal is "TRUE";
attribute KEEP of Icap_dataout : signal is "TRUE";
attribute KEEP of Icap_busy : signal is "TRUE";

end entity icap_statemachine;

architecture imp of icap_statemachine is
  attribute DowngradeIPIdentifiedWarnings: string;
  attribute DowngradeIPIdentifiedWarnings of imp : architecture is "yes";

  -- icap state machine
  type  SM_TYPE is (ICAP_IDLE,ICAP_WRITE1,ICAP_WRITE2,ICAP_WRITE3,ICAP_WRITE4,
                    ICAP_WRITE5,ICAP_READ1,ICAP_ABORT0,ICAP_ABORT_HANG,ICAP_ABORT1,ICAP_ABORT2,
                    ICAP_ABORT3,ICAP_ABORT4,DONE);
  signal icap_nstate_ns, icap_nstate_cs : SM_TYPE;
  signal icap_ce_ns,icap_ce_cs,icap_ce_cs1  : std_logic;
  signal icap_we_ns,icap_we_cs,icap_we_cs1  : std_logic;
  signal rdfifo_wren_ns,rdfifo_wren_cs : std_logic;
  signal wrfifo_rden_ns : std_logic;
  signal Send_done_ns,Send_done_cs : std_logic;
  signal size_ns,size_cs : std_logic_vector(0 to 11);
  signal reset_cr_cs,reset_cr_ns: std_logic;
  signal abort_ns,abort_cs,abort_cs2 : std_logic;
  signal icap_status_i  : std_logic_vector(0 to 31);
  signal abort_i_ns,abort_i_cs,abort_i_cs2: std_logic;
  signal icap_dataout_i : std_logic_vector(0 to ICAP_DWIDTH-1);
  signal Wrfifo_empty_r,Wrfifo_empty_r1 : std_logic;
  signal tmp_datain_ns,tmp_datain_cs : std_logic_vector(0 to ICAP_DWIDTH-1);
  signal icap_datain_ns,icap_datain_cs, int1, int2 : std_logic_vector(0 to ICAP_DWIDTH-1);
  signal stm_skip : std_logic;
  signal count : std_logic_vector (2 downto 0);
  signal count_enable_ns, count_enable_cs : std_logic;
  signal count_reset_ns, count_reset_cs : std_logic;
  signal hang_status_ns, hang_status_cs : std_logic := '0';

begin


GEN_SKIP : if (C_MODE = 1) generate
begin
     stm_skip <= '1';
end generate GEN_SKIP;


GEN_NOSKIP : if (C_MODE = 0) generate
begin
     stm_skip <= '0';
end generate GEN_NOSKIP;


-------------------------------------------------------------------------------
-- ICAP FSM
-------------------------------------------------------------------------------
ICAP_FSM_NS : process (icap_nstate_cs,Rnc,Abort,Rdfifo_full,
              Size,size_cs,Wrfifo_empty,Wrfifo_empty_r,Wrfifo_empty_r1,
              Send_done_cs,Status_read,
              icap_ce_cs,icap_we_cs,Icap_busy,stm_skip,
              count_enable_cs, count_reset_cs, hang_status_cs, count)
      begin
            -- default
            rdfifo_wren_ns      <= '0';
            wrfifo_rden_ns      <= '0';
            Send_done_ns        <= Send_done_cs;
            reset_cr_ns         <= '0';
            icap_ce_ns          <= icap_ce_cs;
            icap_we_ns          <= icap_we_cs;
            icap_nstate_ns      <= icap_nstate_cs;
            size_ns             <= size_cs;
            abort_ns            <= '0';
            abort_i_ns          <= '0';
            count_enable_ns <= count_enable_cs;
            count_reset_ns <= count_reset_cs;
            hang_status_ns <= hang_status_cs;
--            tmp_datain_ns       <= tmp_datain_cs;
--            icap_datain_ns      <= icap_datain_cs;
         case icap_nstate_cs is

            when ICAP_IDLE      =>
               if Status_read = '1' then
                  abort_ns   <= '0';
                  count_enable_ns       <= '0';
               end if;   
               if Abort = '1' then
                  reset_cr_ns        <= '0';
	          icap_ce_ns         <= '0';
	          abort_i_ns         <= '1';
                  icap_nstate_ns     <= ICAP_ABORT0;
               elsif Rnc = "01" then
                  if Wrfifo_empty = '0'then
                    icap_nstate_ns   <= ICAP_WRITE1;
                    wrfifo_rden_ns   <= '1';
                    Send_done_ns     <= '0';
                    reset_cr_ns      <= '0';
                  else
                    icap_nstate_ns   <= ICAP_IDLE;
                  end if;
               elsif Rnc = "10" then
                  if Rdfifo_full = '0'then
                    icap_nstate_ns   <= ICAP_READ1;
                    Send_done_ns     <= '0';
                    reset_cr_ns      <= '0';
                    size_ns          <= Size;
                  else
                    icap_nstate_ns   <= ICAP_IDLE;
                  end if;
               else
                  Send_done_ns     <= '1';
                  reset_cr_ns      <= '0';
                  icap_nstate_ns   <= ICAP_IDLE;
               end if;
                  count_reset_ns <= '1';
                  count_enable_ns       <= '0';

            when ICAP_WRITE1    =>
--               tmp_datain_ns    <= Wrfifo_dataout;
               icap_we_ns       <= '0';
               if Wrfifo_empty = '1' then
                  icap_nstate_ns   <= ICAP_WRITE3;
                  wrfifo_rden_ns   <= '0';
               else 
                  icap_nstate_ns   <= ICAP_WRITE5;
                  wrfifo_rden_ns   <= '1';
               end if;   
            when ICAP_WRITE5    =>
               icap_ce_ns       <= '0';
               icap_we_ns       <= '0';
--               tmp_datain_ns    <= Wrfifo_dataout;
--               icap_datain_ns   <= tmp_datain_cs;
               icap_nstate_ns   <= ICAP_WRITE2;
               if Wrfifo_empty = '1' then
                  wrfifo_rden_ns   <= '0';
               else 
                  wrfifo_rden_ns   <= '1';
               end if;   
            
            when ICAP_WRITE2    =>
               if Status_read = '1' then
                  abort_ns   <= '0';
               end if;
               if Wrfifo_empty_r1 = '0' then
                  icap_ce_ns       <= '0';
                  icap_we_ns       <= '0';
--                  tmp_datain_ns    <= Wrfifo_dataout;
--                  icap_datain_ns   <= tmp_datain_cs;
                  if Abort = '1' and icap_ce_cs = '0'then
                     icap_nstate_ns    <= ICAP_ABORT1;
                     icap_we_ns        <= '1';
                     abort_i_ns        <= '1';                  
              --    elsif (Icap_busy = '0' and Wrfifo_empty_r = '0') then
                  elsif (Wrfifo_empty_r = '0') then
                     icap_nstate_ns   <= ICAP_WRITE2;
                     wrfifo_rden_ns   <= '1'; 
                  else 
                     icap_nstate_ns   <= ICAP_WRITE2;                  
                     wrfifo_rden_ns   <= '0'; 
                  end if;
               else
                  icap_nstate_ns   <= DONE;
	          Send_done_ns     <= '1';
	          reset_cr_ns      <= '1';
                  wrfifo_rden_ns   <= '0';
--                  tmp_datain_ns    <= (others => '0');
--                  icap_datain_ns   <= (others => '0');
                  icap_ce_ns       <= '1';
                  icap_we_ns       <= '0';
               end if;

            when ICAP_WRITE3 =>               
               icap_ce_ns       <= '0';
               icap_we_ns       <= '0';
--               icap_datain_ns   <= tmp_datain_cs;
               if (stm_skip = '1') then             -- Skipping to maintain single write on ICAP
                  icap_nstate_ns   <= DONE;         -- This is not required in actual h/w, and is more of simulation fix
               elsif (Icap_busy = '0') then
                  icap_nstate_ns   <= ICAP_WRITE4;
               else
                  icap_nstate_ns   <= ICAP_WRITE3;               
               end if;
               
            when ICAP_WRITE4 =>               
                  icap_nstate_ns   <= DONE;
	          Send_done_ns     <= '1';
	          reset_cr_ns      <= '1';
--                  tmp_datain_ns    <= (others => '0');
--                  icap_datain_ns   <= (others => '0');
                  icap_ce_ns       <= '1';
                  icap_we_ns       <= '0';

            when ICAP_READ1 =>
             if Status_read = '1' then
                abort_ns   <= '0';
             end if;   
             if Rdfifo_full = '0' then
                if (size_cs > 0) then
                  if Abort = '1' and icap_ce_cs = '0'then
                     icap_ce_ns         <= '0';
                     icap_we_ns         <= '1';
                     icap_we_ns        <= '0';
                     abort_i_ns        <= '1';
                     icap_nstate_ns    <= ICAP_ABORT1;
                     count_enable_ns      <= '0';
                     hang_status_ns    <= '0';
                  elsif Icap_busy = '0' then
                     if (size_cs = 1) then
                       icap_nstate_ns    <= DONE;
                       icap_ce_ns         <= '1';
                     else
                       icap_ce_ns         <= '0';
                       icap_nstate_ns    <= ICAP_READ1;
                     end if;
                     size_ns           <= size_cs - 1;
                     icap_we_ns         <= '1';
                     rdfifo_wren_ns    <= '1';
                     count_enable_ns      <= '0';
                     hang_status_ns <= '0';
                  else
                     icap_ce_ns         <= '0';
                     icap_we_ns         <= '1';
                     if (count = "111") then
                        hang_status_ns <= '1';
                        icap_nstate_ns    <= ICAP_ABORT_HANG;
                     else
                        icap_nstate_ns    <= ICAP_READ1;
                        hang_status_ns <= '0';
                     end if;
                     size_ns           <= size_cs;
                     rdfifo_wren_ns    <= '0';
                     count_enable_ns      <= '1';    -- This is used to increment timeout counter
                     count_reset_ns <= '0';
                  end if;
                else
                   icap_ce_ns         <= '1';
                   icap_we_ns         <= '1';
                   rdfifo_wren_ns     <= '0';
                   Send_done_ns       <= '1';
                   reset_cr_ns        <= '1';
                   count_enable_ns       <= '0';
                   icap_nstate_ns     <= DONE;
                end if;
             else
                rdfifo_wren_ns     <= '0';
                icap_ce_ns         <= '0'; -- Not aborting, only gating
                icap_we_ns         <= '1';
                count_enable_ns       <= '0';
                icap_nstate_ns     <= ICAP_READ1;
             end if;
            when ICAP_ABORT0    =>
               abort_i_ns          <= '1';
               icap_we_ns          <= '0';
               if Icap_busy = '1' and icap_ce_cs = '0' then
                  icap_nstate_ns     <= ICAP_ABORT2;
               else
                  icap_nstate_ns     <= ICAP_ABORT0;
               end if;

            when ICAP_ABORT_HANG    =>    -- Internally de-locking the ICAP
                  abort_i_ns         <= '0';
                  abort_ns           <= '0';
                  icap_ce_ns         <= '1';
                  icap_we_ns         <= '1';
                  count_reset_ns <= '1';
                  count_enable_ns <= '0';
                  hang_status_ns <= '1';
	          icap_nstate_ns     <= DONE;

            when ICAP_ABORT1    =>
               abort_i_ns             <= '1';
 --              if Icap_busy = '1' and icap_ce_cs = '0' then
                  icap_nstate_ns     <= ICAP_ABORT2;
 --              else
 --                 icap_nstate_ns     <= ICAP_ABORT1;
 --              end if;
            when ICAP_ABORT2    =>
                  abort_i_ns         <= '1';
                  abort_ns           <= '1';
	          icap_nstate_ns     <= ICAP_ABORT3;
	    when ICAP_ABORT3    =>
                  abort_i_ns         <= '1';
                  abort_ns           <= '1';
	          icap_nstate_ns     <= ICAP_ABORT4;
	    when ICAP_ABORT4    =>
                  abort_i_ns         <= '0'; -- Asserted for 4 clocks
                  abort_ns           <= '1';
	          icap_nstate_ns     <= DONE;
            when DONE =>
               if Status_read = '1' then
                  abort_ns   <= '0';
               end if;
               abort_i_ns         <= '0'; -- Asserted for 4 clocks
               icap_ce_ns            <= '1';
	       icap_we_ns            <= '1';
--               tmp_datain_ns    <= (others => '0');
--               icap_datain_ns   <= (others => '0');
	       Send_done_ns          <= '1';
	       reset_cr_ns           <= '1';
               count_reset_ns <= '0';
               count_enable_ns <= '0';
	       if Rnc = "00" and Abort = '0' then
	         icap_nstate_ns        <= ICAP_IDLE;
	       else
	         icap_nstate_ns        <= DONE;
	       end if;

            -- This part of the code never executes, because all of the
            -- combinations are used above. "When others =>" added to
            -- allow the synthesis tool to optimize the design well
            -- coverage off
            when others     =>
               icap_nstate_ns       <= ICAP_IDLE;
            -- coverage on
         end case;
      end process ICAP_FSM_NS;


-------------------------------------------------------------------------------
-- ICAP Timeout reg process
-------------------------------------------------------------------------------
ICAP_TIMEOUT_REG: process (Clk) is
       begin
          if (Clk'event and Clk = '1') then
             if (Rst = '1') then
                count <= (others => '0');
             elsif (count_reset_cs = '1') then
                count <= (others => '0');
             elsif (count_enable_cs = '1' and count < "111" ) then
                count <= count + '1';         
             end if;
        end if;
end process ICAP_TIMEOUT_REG;



-------------------------------------------------------------------------------
-- ICAP FSM reg process
-------------------------------------------------------------------------------
ICAP_FSM_REG: process (Clk) is
       begin
          if (Clk'event and Clk = '1') then
             if (Rst = '1') then
                  icap_nstate_cs            <= ICAP_IDLE;
                  Send_done_cs              <= '1';
                  icap_ce_cs                <= '1';
                  icap_we_cs                <= '1';
                  icap_ce_cs1                <= '1';
                  icap_we_cs1                <= '1';
                  size_cs                   <= (others =>'0');
               --   tmp_datain_cs             <= (others => '0');
                  icap_datain_cs            <= (others =>'0');
                  count_enable_cs             <= '0'; 
                  count_reset_cs             <= '0'; 
                  hang_status_cs             <= '0'; 
                  int1        <= (others => '0');
                  int2        <= (others => '0');
             else          
                  icap_nstate_cs            <= icap_nstate_ns;
                  Send_done_cs              <= Send_done_ns;
                  icap_ce_cs                <= icap_ce_ns;
                  icap_ce_cs1                <= icap_ce_cs;
                  icap_we_cs                <= icap_we_ns;
                  icap_we_cs1                <= icap_we_cs;
                  size_cs                   <= size_ns;
                --  tmp_datain_cs             <= tmp_datain_ns;
                  int1                     <= Wrfifo_dataout;
                  icap_datain_cs            <= int1; --icap_datain_ns;
                  count_enable_cs             <= count_enable_ns; 
                  count_reset_cs             <= count_reset_ns; 
                  hang_status_cs             <= hang_status_ns; 
             end if;
        end if;
end process ICAP_FSM_REG;

       Hang_status <= hang_status_cs;

ICAP_SIG_REG: process (Clk) is
       begin
          if (Clk'event and Clk = '1') then
            abort_cs                  <= abort_ns;
            abort_cs2                  <= abort_cs;
            reset_cr_cs               <= reset_cr_ns;
            abort_i_cs                <= abort_i_ns;
            abort_i_cs2               <= abort_i_cs;
            Wrfifo_empty_r            <= Wrfifo_empty;
            Wrfifo_empty_r1           <= Wrfifo_empty_r;
            rdfifo_wren_cs            <= rdfifo_wren_ns;
        end if;
end process ICAP_SIG_REG;


S1:     Rdfifo_wren           <= rdfifo_wren_cs;
S2:     Wrfifo_rden           <= wrfifo_rden_ns;
S3:     Send_done             <= Send_done_cs;
S4:     Icap_ce               <= icap_ce_cs;
S5:     Icap_we               <= icap_we_cs;
S6:     Reset_cr              <= reset_cr_cs;
S7:     Size_counter          <= size_cs;
S8:     Abort_in_progress     <= abort_cs2;
S9:     Icap_status           <= icap_status_i;
-----------------------------------------------------------------------------
-- Need to do bit swapping within each byte but not for Virtex4 in 32-bit mode
-------------------------------------------------------------------------------
SWAP_BITS: process (icap_datain_cs) is
  begin  -- process Swap_bit_Order
        for byte in 0 to (ICAP_DWIDTH/8-1) loop
          for bit in 0 to 7 loop
            Icap_datain(byte*8 + (7-bit))    <= icap_datain_cs(byte*8 + bit);
--            Rdfifo_datain (byte*8 + (7-bit)) <= icap_dataout_i(byte*8 + bit);
          end loop;  -- Bit
        end loop;  -- Byte
  end process SWAP_BITS;

SWAP_BITS_IN: process (icap_dataout_i) is
  begin  -- process Swap_bit_Order
        for byte in 0 to (ICAP_DWIDTH/8-1) loop
          for bit in 0 to 7 loop
       --     Icap_datain(byte*8 + (7-bit))    <= icap_datain_cs(byte*8 + bit);
            Rdfifo_datain (byte*8 + (7-bit)) <= icap_dataout_i(byte*8 + bit);
          end loop;  -- Bit
        end loop;  -- Byte
  end process SWAP_BITS_IN;


-------------------------------------------------------------------------------
-- UPDATE_STATUS_PROCESS
-------------------------------------------------------------------------------
-- This process loads data from Icap_dataout when abort_i_cs enabled
-------------------------------------------------------------------------------
  UPDATE_STATUS_PROCESS:process (Clk)
  begin
    if Clk'event and Clk = '1' then
      if (Rst = '1') then
         icap_status_i <= (others => '0');
      elsif abort_i_cs2 = '1' then 
         icap_status_i (0 to 7) <= Icap_dataout(ICAP_DWIDTH-8 to ICAP_DWIDTH-1);
         icap_status_i (8 to 15) <= icap_status_i (0 to 7);
         icap_status_i (16 to 23) <= icap_status_i (8 to 15);
         icap_status_i (24 to 31) <= icap_status_i (16 to 23);
      else
         icap_status_i <= icap_status_i;
      end if;
    end if;
  end process UPDATE_STATUS_PROCESS;
  
-------------------------------------------------------------------------------
-- This process registers ICAP data out 
-------------------------------------------------------------------------------

  ICAPDOUT_PROCESS:process (Clk)
  begin
    if Clk'event and Clk = '1' then
      icap_dataout_i <= Icap_dataout;
    end if;
  end process ICAPDOUT_PROCESS;


end architecture imp;


-------------------------------------------------------------------------------
-- icap_statemachine.vhd - entity/architecture pair

-------------------------------------------------------------------------------
-- (c) Copyright 2010 - 2011 Xilinx, Inc. All rights reserved.
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
-------------------------------------------------------------------------------
-- Filename:        icap_statemachine.vhd
-- Version :        v7.01a
-- Description:     This module genrates the ce, we signals to ICAP
--                  based on busy signal,control register & FIFO flags
--
-------------------------------------------------------------------------------
-- Naming Conventions:
--      active low signals:                     "*_n"
--      clock signals:                          "clk", "clk_div#", "clk_#x"
--      reset signals:                          "rst", "rst_n"
--      generics:                               "C_*"
--      user defined types:                     "*_TYPE"
--      state machine next state:               "*_ns"
--      state machine current state:            "*_cs"
--      combinatorial signals:                  "*_com"
--      pipelined or register delay signals:    "*_d#"
--      counter signals:                        "*cnt*"
--      clock enable signals:                   "*_ce"
--      internal version of output port         "*_i"
--      device pins:                            "*_pin"
--      ports:                                  - Names begin with Uppercase
--      processes:                              "*_PROCESS"
--      component instantiations:               "<ENTITY_>I_<#|FUNC>
-------------------------------------------------------------------------------
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.std_logic_unsigned.all;

library axi_lite_ipif_v3_0_4;
library lib_pkg_v1_0_2;
use lib_pkg_v1_0_2.lib_pkg.all;
use axi_lite_ipif_v3_0_4.ipif_pkg.all;
-------------------------------------------------------------------------------
-- -- Generics
--  ICAP_DWIDTH         -- Icap Data Width;
--  C_FAMILY            -- Family of FPGA
-- -- Inputs
--  Clk                 -- Clock
--  Rst                 -- Reset
--  Wrfifo_dataout      -- Write fifo data read
--  Icap_dataout        -- ICAP data out
--  Wrfifo_empty        -- Write fifo empty
--  Wrfifo_full         -- Write fifo full
--  Rdfifo_empty        -- Read fifo empty
--  Rdfifo_full         -- Read fifo full
--  Icap_busy           -- ICAP busy
--  Rnc                 -- Read not configuration
--  Size                -- Size of data transfer in words
-- -- Outputs
--  Wrfifo_rden         -- Write fifo read enable
--  Rdfifo_wren         -- Read fifo write enable
--  Icap_ce             -- ICAP chip enable
--  Icap_we             -- ICAP write eneble
--  Send_done           -- Read done
--  Reset_cr            -- Reset the control register
--  Icap_datain         -- ICAP data in
--  Rdfifo_datain       -- Read fifo data in
-------------------------------------------------------------------------------

entity icap_statemachine_shared is
  generic (
    ICAP_DWIDTH         : integer := 16;
    C_MODE              : integer := 0;
    C_FAMILY            : string  := "virtex7");
  port (
    Clk                 : in  std_logic;
    Rst                 : in  std_logic;
    Wrfifo_dataout      : in  std_logic_vector(0 to ICAP_DWIDTH-1);
    Icap_dataout        : in  std_logic_vector(0 to ICAP_DWIDTH-1);
    Wrfifo_full         : in  std_logic;
    Wrfifo_empty        : in  std_logic;
    Rdfifo_empty        : in  std_logic;
    Rdfifo_full         : in  std_logic;
    Icap_busy           : in  std_logic;
    Rnc                 : in  std_logic_vector(0 to 1);
    Abort               : in  std_logic;
    Size                : in  std_logic_vector(0 to 11);
    Status_read         : in  std_logic;
    Size_counter        : out std_logic_vector(0 to 11);
    Wrfifo_rden         : out std_logic;
    Rdfifo_wren         : out std_logic;
    Icap_ce             : out std_logic;
    Icap_we             : out std_logic;
    Send_done           : out std_logic;
    Reset_cr            : out std_logic;
    Abort_in_progress   : out std_logic;
    Hang_status         : out std_logic;
    Icap_status         : out std_logic_vector(0 to 31);
    Icap_datain         : out std_logic_vector(0 to ICAP_DWIDTH-1);
    Rdfifo_datain       : out std_logic_vector(0 to ICAP_DWIDTH-1);
    --icap_i                 : in  std_logic_vector(31 downto 0);  
    --icap_o                 : out std_logic_vector(31 downto 0);
   -- icap_csib              : out std_logic;
   -- icap_rdwrb             : out std_logic;
   -- icap_avail             : in std_logic ;
    icap_req               : out std_logic;  -- Request the ICAP port                      
    icap_gnt               : in  std_logic;  -- ICAP granted                               
    icap_rel               : in  std_logic 
   );

attribute KEEP : string;
attribute KEEP of Icap_ce : signal is "TRUE";
attribute KEEP of Icap_we : signal is "TRUE";
attribute KEEP of Icap_datain : signal is "TRUE";
attribute KEEP of Icap_dataout : signal is "TRUE";
attribute KEEP of Icap_busy : signal is "TRUE";

end entity icap_statemachine_shared;

architecture imp of icap_statemachine_shared is
  attribute DowngradeIPIdentifiedWarnings: string;
  attribute DowngradeIPIdentifiedWarnings of imp : architecture is "yes";

  -- icap state machine
  type  SM_TYPE is (ICAP_IDLE,ICAP_WRITE1,ICAP_WRITE2,ICAP_WRITE3,ICAP_WRITE4,
                    ICAP_WRITE5,ICAP_READ1,ICAP_ABORT0,ICAP_ABORT_HANG,ICAP_ABORT1,ICAP_ABORT2,
                    ICAP_ABORT3,ICAP_ABORT4,DONE);
  signal icap_nstate_ns, icap_nstate_cs : SM_TYPE;
  signal icap_ce_ns,icap_ce_cs,icap_ce_cs1  : std_logic;
  signal icap_we_ns,icap_we_cs,icap_we_cs1  : std_logic;
  signal rdfifo_wren_ns,rdfifo_wren_cs : std_logic;
  signal wrfifo_rden_ns : std_logic;
  signal Send_done_ns,Send_done_cs : std_logic;
  signal size_ns,size_cs : std_logic_vector(0 to 11);
  signal reset_cr_cs,reset_cr_ns: std_logic;
  signal abort_ns,abort_cs,abort_cs2 : std_logic;
  signal icap_status_i  : std_logic_vector(0 to 31);
  signal abort_i_ns,abort_i_cs,abort_i_cs2: std_logic;
  signal icap_dataout_i : std_logic_vector(0 to ICAP_DWIDTH-1);
  signal Wrfifo_empty_r,Wrfifo_empty_r1 : std_logic;
  signal tmp_datain_ns,tmp_datain_cs : std_logic_vector(0 to ICAP_DWIDTH-1);
  signal icap_datain_ns,icap_datain_cs, int1, int2 : std_logic_vector(0 to ICAP_DWIDTH-1);
  signal stm_skip : std_logic;
  signal icap_req_d : std_logic;
  signal icap_req_d1 : std_logic;
  signal count : std_logic_vector (2 downto 0);
  signal count_enable_ns, count_enable_cs : std_logic;
  signal count_reset_ns, count_reset_cs : std_logic;
  signal hang_status_ns, hang_status_cs : std_logic := '0';
  signal icap_rel_d1,icap_rel_d2,icap_rel_d3 : std_logic := '0';
begin
icap_req <= icap_req_d1;

GEN_SKIP : if (C_MODE = 1) generate
begin
     stm_skip <= '1';
end generate GEN_SKIP;


GEN_NOSKIP : if (C_MODE = 0) generate
begin
     stm_skip <= '0';
end generate GEN_NOSKIP;

ICAP_REL_D_GEN : process (Clk) begin
          if (Clk'event and Clk = '1') then
             if (Rst = '1') then
               icap_rel_d1 <= '0';
               icap_rel_d2 <= '0';
               icap_rel_d3 <= '0';
               icap_req_d <= '0';
              else
               icap_rel_d1 <= icap_rel;
               icap_rel_d2 <= icap_rel_d1;
               icap_rel_d3 <= icap_rel_d2;
               icap_req_d <= icap_req_d1;
             end if;
          end if;

end process ICAP_REL_D_GEN;


-------------------------------------------------------------------------------
-- ICAP FSM
-------------------------------------------------------------------------------
ICAP_FSM_NS : process (icap_nstate_cs,Rnc,Abort,Rdfifo_full,
              Size,size_cs,Wrfifo_empty,Wrfifo_empty_r,Wrfifo_empty_r1,
              Send_done_cs,Status_read,
              icap_ce_cs,icap_we_cs,Icap_busy,stm_skip,
              count_enable_cs, count_reset_cs, hang_status_cs, count,icap_gnt,icap_rel,icap_req_d,icap_rel_d2)
      begin
            -- default
            rdfifo_wren_ns      <= '0';
            wrfifo_rden_ns      <= '0';
            Send_done_ns        <= Send_done_cs;
            reset_cr_ns         <= '0';
            icap_ce_ns          <= icap_ce_cs;
            icap_we_ns          <= icap_we_cs;
            icap_nstate_ns      <= icap_nstate_cs;
            size_ns             <= size_cs;
            abort_ns            <= '0';
            abort_i_ns          <= '0';
            count_enable_ns <= count_enable_cs;
            count_reset_ns <= count_reset_cs;
            hang_status_ns <= hang_status_cs;
            icap_req_d1 <= icap_req_d;
--            tmp_datain_ns       <= tmp_datain_cs;
--            icap_datain_ns      <= icap_datain_cs;
         case icap_nstate_cs is

            when ICAP_IDLE      =>
               if Status_read = '1' then
                  abort_ns   <= '0';
                  count_enable_ns       <= '0';
               end if;   
               if Abort = '1' then
                  reset_cr_ns        <= '0';
	          icap_ce_ns         <= '0';
	          abort_i_ns         <= '1';
                  icap_nstate_ns     <= ICAP_ABORT0;
               elsif Rnc = "01" then
                  if (Wrfifo_empty = '0' and icap_gnt = '1' and icap_rel = '0') then
                    icap_nstate_ns   <= ICAP_WRITE1;
                    wrfifo_rden_ns   <= '1';
                    Send_done_ns     <= '0';
                    reset_cr_ns      <= '0';
                    icap_req_d1 <= '1';
                  else
                      if(icap_rel = '0' and icap_rel_d2 = '0') then 
                          icap_req_d1 <= '1';
                      else 
                          icap_req_d1 <= '0';
                    end if;
                      icap_nstate_ns   <= ICAP_IDLE;
                  end if;
               elsif Rnc = "10" then
                  if (Rdfifo_full = '0' and icap_gnt = '1' and icap_rel = '0') then
                    icap_nstate_ns   <= ICAP_READ1;
                    Send_done_ns     <= '0';
                    reset_cr_ns      <= '0';
                    size_ns          <= Size;
                    icap_req_d1 <= '1';
                  else
                    if(icap_rel = '0' and icap_rel_d2 = '0') then 
                          icap_req_d1 <= '1';
                      else 
                          icap_req_d1 <= '0';
                    end if;
                     icap_nstate_ns   <= ICAP_IDLE;
                  end if;
               else
                  Send_done_ns     <= '1';
                  reset_cr_ns      <= '0';
                  icap_nstate_ns   <= ICAP_IDLE;
                  icap_req_d1 <= '0';    -- When there is no request, releasing icap for shared IPs
               end if;
                  count_reset_ns <= '1';
                  count_enable_ns       <= '0';

            when ICAP_WRITE1    =>
--               tmp_datain_ns    <= Wrfifo_dataout;
               icap_we_ns       <= '0';
               if Wrfifo_empty = '1' then
                  icap_nstate_ns   <= ICAP_WRITE3;
                  wrfifo_rden_ns   <= '0';
               else 
                  icap_nstate_ns   <= ICAP_WRITE5;
                  wrfifo_rden_ns   <= '1';
               end if;   
            when ICAP_WRITE5    =>
               icap_ce_ns       <= '0';
               icap_we_ns       <= '0';
--               tmp_datain_ns    <= Wrfifo_dataout;
--               icap_datain_ns   <= tmp_datain_cs;
               icap_nstate_ns   <= ICAP_WRITE2;
               if Wrfifo_empty = '1' then
                  wrfifo_rden_ns   <= '0';
               else 
                  wrfifo_rden_ns   <= '1';
               end if;   
            
            when ICAP_WRITE2    =>
               if Status_read = '1' then
                  abort_ns   <= '0';
               end if;
               if Wrfifo_empty_r1 = '0' then
                  icap_ce_ns       <= '0';
                  icap_we_ns       <= '0';
--                  tmp_datain_ns    <= Wrfifo_dataout;
--                  icap_datain_ns   <= tmp_datain_cs;
                  if Abort = '1' and icap_ce_cs = '0'then
                     icap_nstate_ns    <= ICAP_ABORT1;
                     icap_we_ns        <= '1';
                     abort_i_ns        <= '1';                  
              --    elsif (Icap_busy = '0' and Wrfifo_empty_r = '0') then
                  elsif (Wrfifo_empty_r = '0') then
                     icap_nstate_ns   <= ICAP_WRITE2;
                     wrfifo_rden_ns   <= '1'; 
                  else 
                     icap_nstate_ns   <= ICAP_WRITE2;                  
                     wrfifo_rden_ns   <= '0'; 
                  end if;
               else
                  icap_nstate_ns   <= DONE;
	          Send_done_ns     <= '1';
	          reset_cr_ns      <= '1';
                  wrfifo_rden_ns   <= '0';
--                  tmp_datain_ns    <= (others => '0');
--                  icap_datain_ns   <= (others => '0');
                  icap_ce_ns       <= '1';
                  icap_we_ns       <= '0';
               end if;

            when ICAP_WRITE3 =>               
               icap_ce_ns       <= '0';
               icap_we_ns       <= '0';
--               icap_datain_ns   <= tmp_datain_cs;
               if (stm_skip = '1') then             -- Skipping to maintain single write on ICAP
                  icap_nstate_ns   <= DONE;         -- This is not required in actual h/w, and is more of simulation fix
               elsif (Icap_busy = '0') then
                  icap_nstate_ns   <= ICAP_WRITE4;
               else
                  icap_nstate_ns   <= ICAP_WRITE3;               
               end if;
               
            when ICAP_WRITE4 =>               
                  icap_nstate_ns   <= DONE;
	          Send_done_ns     <= '1';
	          reset_cr_ns      <= '1';
--                  tmp_datain_ns    <= (others => '0');
--                  icap_datain_ns   <= (others => '0');
                  icap_ce_ns       <= '1';
                  icap_we_ns       <= '0';

            when ICAP_READ1 =>
             if Status_read = '1' then
                abort_ns   <= '0';
             end if;   
             if Rdfifo_full = '0' then
                if (size_cs > 0) then
                  if Abort = '1' and icap_ce_cs = '0'then
                     icap_ce_ns         <= '0';
                     icap_we_ns         <= '1';
                     icap_we_ns        <= '0';
                     abort_i_ns        <= '1';
                     icap_nstate_ns    <= ICAP_ABORT1;
                     count_enable_ns      <= '0';
                     hang_status_ns    <= '0';
                  elsif Icap_busy = '0' then
                     if (size_cs = 1) then
                       icap_nstate_ns    <= DONE;
                       icap_ce_ns         <= '1';
                     else
                       icap_ce_ns         <= '0';
                       icap_nstate_ns    <= ICAP_READ1;
                     end if;
                     size_ns           <= size_cs - 1;
                     icap_we_ns         <= '1';
                     rdfifo_wren_ns    <= '1';
                     count_enable_ns      <= '0';
                     hang_status_ns <= '0';
                  else
                     icap_ce_ns         <= '0';
                     icap_we_ns         <= '1';
                     if (count = "111") then
                        hang_status_ns <= '1';
                        icap_nstate_ns    <= ICAP_ABORT_HANG;
                     else
                        icap_nstate_ns    <= ICAP_READ1;
                        hang_status_ns <= '0';
                     end if;
                     size_ns           <= size_cs;
                     rdfifo_wren_ns    <= '0';
                     count_enable_ns      <= '1';    -- This is used to increment timeout counter
                     count_reset_ns <= '0';
                  end if;
                else
                   icap_ce_ns         <= '1';
                   icap_we_ns         <= '1';
                   rdfifo_wren_ns     <= '0';
                   Send_done_ns       <= '1';
                   reset_cr_ns        <= '1';
                   count_enable_ns       <= '0';
                   icap_nstate_ns     <= DONE;
                end if;
             else
                rdfifo_wren_ns     <= '0';
                icap_ce_ns         <= '0'; -- Not aborting, only gating
                icap_we_ns         <= '1';
                count_enable_ns       <= '0';
                icap_nstate_ns     <= ICAP_READ1;
             end if;
            when ICAP_ABORT0    =>
               abort_i_ns          <= '1';
               icap_we_ns          <= '0';
               if Icap_busy = '1' and icap_ce_cs = '0' then
                  icap_nstate_ns     <= ICAP_ABORT2;
               else
                  icap_nstate_ns     <= ICAP_ABORT0;
               end if;

            when ICAP_ABORT_HANG    =>    -- Internally de-locking the ICAP
                  abort_i_ns         <= '0';
                  abort_ns           <= '0';
                  icap_ce_ns         <= '1';
                  icap_we_ns         <= '1';
                  count_reset_ns <= '1';
                  count_enable_ns <= '0';
                  hang_status_ns <= '1';
	          icap_nstate_ns     <= DONE;

            when ICAP_ABORT1    =>
               abort_i_ns             <= '1';
 --              if Icap_busy = '1' and icap_ce_cs = '0' then
                  icap_nstate_ns     <= ICAP_ABORT2;
 --              else
 --                 icap_nstate_ns     <= ICAP_ABORT1;
 --              end if;
            when ICAP_ABORT2    =>
                  abort_i_ns         <= '1';
                  abort_ns           <= '1';
	          icap_nstate_ns     <= ICAP_ABORT3;
	    when ICAP_ABORT3    =>
                  abort_i_ns         <= '1';
                  abort_ns           <= '1';
	          icap_nstate_ns     <= ICAP_ABORT4;
	    when ICAP_ABORT4    =>
                  abort_i_ns         <= '0'; -- Asserted for 4 clocks
                  abort_ns           <= '1';
	          icap_nstate_ns     <= DONE;
       when DONE =>
         if Status_read = '1' then
              abort_ns   <= '0';
         end if;
              abort_i_ns         <= '0'; -- Asserted for 4 clocks
              icap_ce_ns            <= '1';
	           icap_we_ns            <= '1';
--               tmp_datain_ns    <= (others => '0');
--               icap_datain_ns   <= (others => '0');
	       Send_done_ns          <= '1';
	       reset_cr_ns           <= '1';
               count_reset_ns <= '0';
               count_enable_ns <= '0';
	       if Rnc = "00" and Abort = '0' then
	         icap_nstate_ns        <= ICAP_IDLE;
	       else
	         icap_nstate_ns        <= DONE;
	       end if;

            -- This part of the code never executes, because all of the
            -- combinations are used above. "When others =>" added to
            -- allow the synthesis tool to optimize the design well
            -- coverage off
            when others     =>
               icap_nstate_ns       <= ICAP_IDLE;
            -- coverage on
         end case;
      end process ICAP_FSM_NS;


-------------------------------------------------------------------------------
-- ICAP Timeout reg process
-------------------------------------------------------------------------------
ICAP_TIMEOUT_REG: process (Clk) is
       begin
          if (Clk'event and Clk = '1') then
             if (Rst = '1') then
                count <= (others => '0');
             elsif (count_reset_cs = '1') then
                count <= (others => '0');
             elsif (count_enable_cs = '1' and count < "111" ) then
                count <= count + '1';         
             end if;
        end if;
end process ICAP_TIMEOUT_REG;



-------------------------------------------------------------------------------
-- ICAP FSM reg process
-------------------------------------------------------------------------------
ICAP_FSM_REG: process (Clk) is
       begin
          if (Clk'event and Clk = '1') then
             if (Rst = '1') then
                  icap_nstate_cs            <= ICAP_IDLE;
                  Send_done_cs              <= '1';
                  icap_ce_cs                <= '1';
                  icap_we_cs                <= '1';
                  icap_ce_cs1                <= '1';
                  icap_we_cs1                <= '1';
                  size_cs                   <= (others =>'0');
               --   tmp_datain_cs             <= (others => '0');
                  icap_datain_cs            <= (others =>'0');
                  count_enable_cs             <= '0'; 
                  count_reset_cs             <= '0'; 
                  hang_status_cs             <= '0'; 
                  int1        <= (others => '0');
                  int2        <= (others => '0');
             else          
                  icap_nstate_cs            <= icap_nstate_ns;
                  Send_done_cs              <= Send_done_ns;
                  icap_ce_cs                <= icap_ce_ns;
                  icap_ce_cs1                <= icap_ce_cs;
                  icap_we_cs                <= icap_we_ns;
                  icap_we_cs1                <= icap_we_cs;
                  size_cs                   <= size_ns;
                --  tmp_datain_cs             <= tmp_datain_ns;
                  int1                     <= Wrfifo_dataout;
                  icap_datain_cs            <= int1; --icap_datain_ns;
                  count_enable_cs             <= count_enable_ns; 
                  count_reset_cs             <= count_reset_ns; 
                  hang_status_cs             <= hang_status_ns; 
             end if;
        end if;
end process ICAP_FSM_REG;

       Hang_status <= hang_status_cs;

ICAP_SIG_REG: process (Clk) is
       begin
          if (Clk'event and Clk = '1') then
            abort_cs                  <= abort_ns;
            abort_cs2                  <= abort_cs;
            reset_cr_cs               <= reset_cr_ns;
            abort_i_cs                <= abort_i_ns;
            abort_i_cs2               <= abort_i_cs;
            Wrfifo_empty_r            <= Wrfifo_empty;
            Wrfifo_empty_r1           <= Wrfifo_empty_r;
            rdfifo_wren_cs            <= rdfifo_wren_ns;
        end if;
end process ICAP_SIG_REG;


S1:     Rdfifo_wren           <= rdfifo_wren_cs;
S2:     Wrfifo_rden           <= wrfifo_rden_ns;
S3:     Send_done             <= Send_done_cs;
S4:     Icap_ce               <= icap_ce_cs;
S5:     Icap_we               <= icap_we_cs;
S6:     Reset_cr              <= reset_cr_cs;
S7:     Size_counter          <= size_cs;
S8:     Abort_in_progress     <= abort_cs2;
S9:     Icap_status           <= icap_status_i;
-----------------------------------------------------------------------------
-- Need to do bit swapping within each byte but not for Virtex4 in 32-bit mode
-------------------------------------------------------------------------------
SWAP_BITS: process (icap_datain_cs) is
  begin  -- process Swap_bit_Order
        for byte in 0 to (ICAP_DWIDTH/8-1) loop
          for bit in 0 to 7 loop
            Icap_datain(byte*8 + (7-bit))    <= icap_datain_cs(byte*8 + bit);
--            Rdfifo_datain (byte*8 + (7-bit)) <= icap_dataout_i(byte*8 + bit);
          end loop;  -- Bit
        end loop;  -- Byte
  end process SWAP_BITS;

SWAP_BITS_IN: process (icap_dataout_i) is
  begin  -- process Swap_bit_Order
        for byte in 0 to (ICAP_DWIDTH/8-1) loop
          for bit in 0 to 7 loop
       --     Icap_datain(byte*8 + (7-bit))    <= icap_datain_cs(byte*8 + bit);
            Rdfifo_datain (byte*8 + (7-bit)) <= icap_dataout_i(byte*8 + bit);
          end loop;  -- Bit
        end loop;  -- Byte
  end process SWAP_BITS_IN;


-------------------------------------------------------------------------------
-- UPDATE_STATUS_PROCESS
-------------------------------------------------------------------------------
-- This process loads data from Icap_dataout when abort_i_cs enabled
-------------------------------------------------------------------------------
  UPDATE_STATUS_PROCESS:process (Clk)
  begin
    if Clk'event and Clk = '1' then
      if (Rst = '1') then
         icap_status_i <= (others => '0');
      elsif abort_i_cs2 = '1' then 
         icap_status_i (0 to 7) <= Icap_dataout(ICAP_DWIDTH-8 to ICAP_DWIDTH-1);
         icap_status_i (8 to 15) <= icap_status_i (0 to 7);
         icap_status_i (16 to 23) <= icap_status_i (8 to 15);
         icap_status_i (24 to 31) <= icap_status_i (16 to 23);
      else
         icap_status_i <= icap_status_i;
      end if;
    end if;
  end process UPDATE_STATUS_PROCESS;
  
-------------------------------------------------------------------------------
-- This process registers ICAP data out 
-------------------------------------------------------------------------------

  ICAPDOUT_PROCESS:process (Clk)
  begin
    if Clk'event and Clk = '1' then
      icap_dataout_i <= Icap_dataout;
    end if;
  end process ICAPDOUT_PROCESS;


end architecture imp;


-------------------------------------------------------------------------------
-- hwicap.vhd - entity/architecture pair

-------------------------------------------------------------------------------
-- (c) Copyright 2010 - 2011 Xilinx, Inc. All rights reserved.
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
-------------------------------------------------------------------------------
-- Filename:        hwicap.vhd
-- Description:
--
-- HWICAP module can configure the FPGA using ICAP.It has one write FIFO & one
-- read FIFO. The configuration bitstream will be written in to the write FIFO
-- & from whare the bit stream will be laoded in to the ICAP.
-- Similarly during reading the bitstream loaded in to the read FIFO, from
-- where the processor will read the bit stream. The ocuupany registers will
-- tell the ocupancy value in the FIFOs. The status register tells the status
-- of read. The control register chooses the read or write of configuration
-- bitstream & reseting the registers aswell as FIFOs
--
-------------------------------------------------------------------------------
-- Naming Conventions:
--      active low signals:                     "*_n"
--      clock signals:                          "clk", "clk_div#", "clk_#x"
--      reset signals:                          "rst", "rst_n"
--      generics:                               "C_*"
--      user defined types:                     "*_TYPE"
--      state machine next state:               "*_ns"
--      state machine current state:            "*_cs"
--      combinatorial signals:                  "*_com"
--      pipelined or register delay signals:    "*_d#"
--      counter signals:                        "*cnt*"
--      clock enable signals:                   "*_ce"
--      internal version of output port         "*_i"
--      device pins:                            "*_pin"
--      ports:                                  - Names begin with Uppercase
--      processes:                              "*_PROCESS"
--      component instantiations:               "<ENTITY_>I_<#|FUNC>
-------------------------------------------------------------------------------
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library axi_lite_ipif_v3_0_4;
library lib_cdc_v1_0_2;
library lib_pkg_v1_0_2;
use lib_pkg_v1_0_2.lib_pkg.all;
use axi_lite_ipif_v3_0_4.ipif_pkg.all;
use lib_cdc_v1_0_2.cdc_sync;

library unisim;
use unisim.vcomponents.all;

library axi_hwicap_v3_0_14;
use axi_hwicap_v3_0_14.all;
-------------------------------------------------------------------------------
-- Definition of Generics:
--  ICAP_DWIDTH         -- ICAP data width
--  C_SAXI_DWIDTH       -- AXI data width
--  C_SIMULATION        -- Parameter is TRUE for functional simulation
--  C_BRAM_SRL_FIFO_TYPE-- type of the FIFO either as distributer or BRAM
--  C_FAMILY            -- target FPGA family
-------------------------------------------------------------------------------
-- --inputs
--
--  ICAP_Clk            -- ICAP clock
--
--  Bus2IP_Clk          -- PLB clock
--  Bus2IP_Reset        -- PLB Reset
--  Bus2IP_BE           -- PLB Byte Enable
--  Bus2IP_Data         -- PLB data bus
--  Bus2IP_rnw          -- Bus to IP read not write signal
--  Bus2IP_cs           -- Bus to IP Chip select signal
--  Bus2IP_wrce         -- Bus to IP write chip enable
--  Bus2IP_rdce         -- Bus to IP read chip enable
-- --outputs
--
--  IP2Bus_Data         -- Slave Data Bus
--  IP2Bus_errAck       -- Slave error acknowledge
--  IP2Bus_RdAck        -- Slave Read Acknowledge
--  IP2Bus_WrAck        -- Slave Write Acknowledge
--  Intr_rst            -- Reset the interrupt controller
--  IP2Bus_AddrAck      -- Slave Address Acknowledge
-------------------------------------------------------------------------------
entity hwicap is
  generic (
    ICAP_DWIDTH         : integer := 16;
    C_WRITE_FIFO_DEPTH  : integer := 16;
    C_READ_FIFO_DEPTH   : integer := 16;
    C_SAXI_DWIDTH       : integer := 32;
    C_SIMULATION        : integer := 2;
    C_BRAM_SRL_FIFO_TYPE: integer := 1;  -- default BRAM
    C_ICAP_WIDTH        : string := "X8";
    C_INCLUDE_STARTUP   : integer := 0;
    C_SHARED_STARTUP    : integer range 0 to 1 := 0;
    C_MODE              : integer := 0;
    C_OPERATION         : integer := 0;
    C_NOREAD            : integer := 0;
    C_ENABLE_ASYNC      : integer := 0;  
    C_DEVICE_ID         : bit_vector := X"04224093";
    C_FAMILY            : string  := "virtex7");
  port(
    ICAP_Clk            : in std_logic;
    Eos_in              : in std_logic;
    Bus2IP_Clk          : in std_logic;
    Bus2IP_Reset        : in std_logic;
    Bus2IP_Addr         : in std_logic_vector(0 to 9-1);
    Bus2IP_BE           : in std_logic_vector(0 to C_SAXI_DWIDTH/8-1);
    Bus2IP_Data         : in std_logic_vector(0 to C_SAXI_DWIDTH-1);
    Bus2IP_rnw          : in std_logic;
    Bus2IP_cs           : in std_logic;
    Bus2IP_wrce         : in std_logic_vector(0 to 7);
    Bus2IP_rdce         : in std_logic_vector(0 to 7);
    IP2Bus_Data         : out std_logic_vector(0 to C_SAXI_DWIDTH-1);
    IP2Bus_errAck       : out std_logic;
    IP2Bus_RdAck        : out std_logic;
    IP2Bus_WrAck        : out std_logic;
    IP2Bus_AddrAck      : out std_logic;
    Intr_rst            : out std_logic;
    IP2Bus_Intr         : out std_logic_vector(0 to 3);
    CFGCLK : out std_logic;
    CFGMCLK : out std_logic;
    PREQ : out std_logic;
    CLK : in std_logic;
    GSR : in std_logic;
    GTS : in std_logic;
    KEYCLEARB : in std_logic;
    PACK : in std_logic;
    USRCCLKO : in std_logic;
    USRCCLKTS : in std_logic;
    USRDONEO : in std_logic;
    USRDONETS : in std_logic

);

end entity hwicap;

architecture imp of hwicap is
  attribute DowngradeIPIdentifiedWarnings: string;
  attribute DowngradeIPIdentifiedWarnings of imp : architecture is "yes";


--component axi_hwicap_v3_0_14_icap_test
--      port (
--        clk           : in std_logic;
--        csb           : in std_logic;
--        rdwrb         : in std_logic;
--        i             : in std_logic_vector (31 downto 0);
--        busy          : out std_logic;
--        o             : out std_logic_vector (31 downto 0));
--end component;
        


constant MTBF_STAGES : integer := 4;
-- signal declaration starts here ...
signal wrfifo_rden      : std_logic;
signal rdfifo_wren      : std_logic;
signal send_done        : std_logic;
signal rdfifo_datain    : std_logic_vector(0 to ICAP_DWIDTH-1);
signal wrfifo_dataout   : std_logic_vector(0 to ICAP_DWIDTH-1);
signal icap_datain      : std_logic_vector(0 to ICAP_DWIDTH-1);
signal icap_dataout     : std_logic_vector(0 to ICAP_DWIDTH-1);
signal writefifo_full   : std_logic;
signal writefifo_empty  : std_logic;
signal readfifo_full    : std_logic;
signal readfifo_empty   : std_logic;
signal rnc              : std_logic_vector(0 to 1);
signal size             : std_logic_vector(0 to 11);
signal icap_busy        : std_logic;
signal icap_ce          : std_logic;
signal icap_we          : std_logic;
signal reset_cr         : std_logic;
signal size_counter     : std_logic_vector(0 to 11);
signal abort            : std_logic;
signal abort_in_progress: std_logic;
signal status_read      : std_logic;
signal icap_status      : std_logic_vector(0 to 31);
signal ICAP_Reset : std_logic;
signal bus2icap_reset_trig_1 : std_logic;
signal bus2icap_reset_trig_2 : std_logic;
signal bus2icap_reset_trig_3 : std_logic;
signal gate_icap : std_logic;
signal gate_icap_p : std_logic;
signal gate_clk : std_logic;
signal gate_clk1 : std_logic;
signal rdfull : std_logic;
signal inv_gate : std_logic;

signal ce_del1 : std_logic;
signal ce_del2 : std_logic;
signal ce_del3 : std_logic;
signal rdwr_int1 : std_logic;
signal rdwr_int2 : std_logic;
signal abort_detect : std_logic;
signal abort_del1 : std_logic;
signal abort_del2 : std_logic;
signal abort_del3 : std_logic;
signal busy_abort : std_logic;
signal busy_int : std_logic;
signal same_cycle : std_logic;
signal hang_status : std_logic;
signal icap_dataout1 : std_logic_vector (0 to 31);
signal icap_datain1 : std_logic_vector (0 to 31);
signal icap_available : std_logic;


begin  -- architecture IMP

  -----------------------------------------------------------------------------
  -- IPIC Interface
  -----------------------------------------------------------------------------
  IPIC_IF_I : entity axi_hwicap_v3_0_14.ipic_if
    generic map (
      C_SAXI_DWIDTH       => C_SAXI_DWIDTH,
      C_WRITE_FIFO_DEPTH  => C_WRITE_FIFO_DEPTH,
      C_READ_FIFO_DEPTH   => C_READ_FIFO_DEPTH,
      ICAP_DWIDTH         => ICAP_DWIDTH,
      C_MODE              => C_MODE,
      C_NOREAD            => C_NOREAD,
      C_SHARED_STARTUP    => C_SHARED_STARTUP,
      C_ENABLE_ASYNC      => C_ENABLE_ASYNC,
      C_INCLUDE_STARTUP   => C_INCLUDE_STARTUP,
      C_BRAM_SRL_FIFO_TYPE=> C_BRAM_SRL_FIFO_TYPE,
      C_FAMILY            => C_FAMILY)
    port map (
      ICAP_Clk            => ICAP_Clk,
      ICAP_Reset          => ICAP_Reset,
      Bus2IP_Clk          => Bus2IP_Clk,
      Bus2IP_Reset        => Bus2IP_Reset,
      Send_done           => send_done,
      Reset_cr            => reset_cr,
      Icap_out            => icap_dataout,
      Bus2IP_cs           => Bus2IP_cs,
      Bus2IP_BE           => Bus2IP_BE,
      Bus2IP_rnw          => Bus2IP_rnw,
      Bus2IP_wrce         => Bus2IP_wrce,
      Bus2IP_rdce         => Bus2IP_rdce,
      Bus2IP_Data         => Bus2IP_Data,
      Wrfifo_rden         => wrfifo_rden,
      IP2Bus_Data         => IP2Bus_Data,
      Rdfifo_wren         => rdfifo_wren,
      Rdfifo_datain       => rdfifo_datain,
      Status_read         => status_read,
      Icap_status         => icap_status,
      Wrfifo_dataout      => wrfifo_dataout,
      Writefifo_full      => writefifo_full,
      Writefifo_empty     => writefifo_empty,
      Readfifo_full       => readfifo_full,
      Readfifo_empty      => readfifo_empty,
      Abort               => abort,
      Abort_in_progress   => abort_in_progress,
      Rnc                 => rnc,
      Hang_status         => hang_status,
      Eos_in              => Eos_in,
      icap_available      => icap_available,
      Size                => size,
      Size_counter        => size_counter,
      IP2Bus_RdAck        => IP2Bus_RdAck,
      IP2Bus_WrAck        => IP2Bus_WrAck,
      IP2Bus_AddrAck      => IP2Bus_AddrAck,
      IP2Bus_errAck       => IP2Bus_errAck,
      Intr_rst            => Intr_rst,
      Gate_icap           => gate_icap,
      Gate_icap_p         => gate_icap_p,
      IP2Bus_Intr         => IP2Bus_Intr,
      CFGCLK    => CFGCLK,
      CFGMCLK    => CFGMCLK,
      PREQ    => PREQ,
      CLK    => CLK,
      GSR    => GSR,
      GTS    => GTS,
      KEYCLEARB    => KEYCLEARB,
      PACK    => PACK,
      USRCCLKO    => USRCCLKO,
      USRCCLKTS    => USRCCLKTS,
      USRDONEO    => USRDONEO,
      USRDONETS    => USRDONETS
  );
-------------------------------------------------------------------------------
-- icap State Machine
-------------------------------------------------------------------------------

rdfull <= gate_icap_p;

  icap_statemachine_I1: entity axi_hwicap_v3_0_14.icap_statemachine
    generic map (
      ICAP_DWIDTH         => ICAP_DWIDTH,
      C_MODE              => C_MODE,
      C_FAMILY            => C_FAMILY)
    port map (
      Clk                 => ICAP_Clk,
      Rst                 => ICAP_Reset,
      Wrfifo_dataout      => wrfifo_dataout,
      Icap_dataout        => icap_dataout,
      Wrfifo_full         => writefifo_full,
      Wrfifo_empty        => writefifo_empty,
      Rdfifo_empty        => readfifo_empty,
      Rdfifo_full         => rdfull,
      Icap_busy           => icap_busy,
      Status_read         => status_read,
      Rnc                 => rnc,
      Abort               => abort,
      Size                => size,
      Size_counter        => size_counter,
      Wrfifo_rden         => wrfifo_rden,
      Rdfifo_wren         => rdfifo_wren,
      Icap_ce             => icap_ce,
      Icap_we             => icap_we,
      Abort_in_progress   => abort_in_progress,
      Icap_status         => icap_status,
      Send_done           => send_done,
      Reset_cr            => reset_cr,
      Hang_status         => hang_status,
      Icap_datain         => icap_datain,
      Rdfifo_datain       => rdfifo_datain);


--  GEN_BUS2ICAP_RESET:process (ICAP_Clk)
--  begin
--    if ICAP_Clk'event and ICAP_Clk = '1' then
--       -- generates three flip flop synchronizer bus2icap reset trigger signal
--       -- in ICAP_Clk
--       bus2icap_reset_trig_1 <= Bus2IP_Reset;
--       bus2icap_reset_trig_2 <= bus2icap_reset_trig_1;
--    end if;
--  end process GEN_BUS2ICAP_RESET;

GEN_BUS2ICAP_RESET : entity lib_cdc_v1_0_2.cdc_sync
    generic map (
        C_CDC_TYPE                 => 1,
        C_RESET_STATE              => 0,
        C_SINGLE_BIT               => 1,
        C_VECTOR_WIDTH             => 32,
        C_MTBF_STAGES              => MTBF_STAGES
    )
    port map (
        prmry_aclk                 => '0',
        prmry_resetn               => '0',
        prmry_in                   => Bus2IP_Reset,
        prmry_vect_in              => (others => '0'),

        scndry_aclk                => ICAP_Clk,
        scndry_resetn              => '0',
        scndry_out                 => bus2icap_reset_trig_2, --awvalid_to,
        scndry_vect_out            => open
    );


  ICAP_Reset <= bus2icap_reset_trig_2;

  -----------------------------------------------------------------------------
  -- simulation only using the FIFO model
  -----------------------------------------------------------------------------

-- gate_bufgce : BUFGCE
--              port map (
--                O => gate_clk,
--                I => ICAP_Clk,
--                CE => inv_gate);

BUFGCTRL_INST : if (C_OPERATION = 1) generate
begin
 
      inv_gate <= not gate_icap;


 gate_bfgctrl : BUFGCTRL 
               port map (
            
    O           => gate_clk,
    CE0         => inv_gate,
    CE1         => '0',
    I0          => ICAP_Clk,
    I1          => '1',
    IGNORE0     => '0',
    IGNORE1     => '1',
    S0          => '1',
    S1          => '0'
    );

end generate BUFGCTRL_INST;


NO_BUFGCTRL_INST : if (C_OPERATION = 0) generate
begin

    gate_clk <= ICAP_Clk; 

end generate NO_BUFGCTRL_INST;


  GEN_FUNCTIONAL : if C_SIMULATION = 1 generate
 --    ICAP_TEST_I : axi_hwicap_v3_0_14_icap_test
 --     port map (
 --      -- Rst               => ICAP_Reset,
 --       clk                => gate_clk,
 --       csb                => icap_ce, 
 --       rdwrb              => icap_we,
 --       i                  => icap_datain1,
 --       busy               => icap_busy,
 --       o                  => icap_dataout1);



  --     icap_dataout <= icap_dataout1;
  --     icap_datain1 <= icap_datain;


  end generate GEN_FUNCTIONAL;
  -----------------------------------------------------------------------------
  --implementation only code - Simulations using unisim model
  -----------------------------------------------------------------------------
  GEN_FUNCTIONAL_UNISIM : if C_SIMULATION = 2 generate
  begin

   GEN_VIRTEX7_ICAP : if ( 
            (C_FAMILY = "virtex7") or
            (C_FAMILY = "kintex7") or
            (C_FAMILY = "zynq") or
            (C_FAMILY = "spartan7") or
            (C_FAMILY = "artix7")  
           ) generate
    begin
       ICAP_VIRTEX7_I : ICAPE2
         generic map (
           DEVICE_ID         => C_DEVICE_ID,
           ICAP_WIDTH        => C_ICAP_WIDTH)
         port map (
           clk               => gate_clk,
           csib               => icap_ce,
           rdwrb             => icap_we,
           i                 => icap_datain,
       --    busy              => icap_busy,
           o                 => icap_dataout);

       icap_available <= '0';

   end generate GEN_VIRTEX7_ICAP;


   GEN_VIRTEXU_ICAP : if ( 
                          (C_FAMILY /= "virtex7") and
                          (C_FAMILY /= "kintex7") and
                          (C_FAMILY /= "zynq") and
                          (C_FAMILY /= "spartan7") and
                          (C_FAMILY /= "artix7")
                           ) generate
   begin

       ICAP_VIRTEXU_I : ICAPE3
         generic map ( 
           DEVICE_ID         => C_DEVICE_ID)
--           ICAP_WIDTH        => C_ICAP_WIDTH)
         port map (
           clk               => gate_clk,
           csib              => icap_ce,
           rdwrb             => icap_we,
           i                 => icap_datain,
           o                 => icap_dataout,
           prerror           => open,
           prdone            => open,
           avail             => icap_available);

--       icap_available <= '1';


   end generate GEN_VIRTEXU_ICAP;

-- The ICAPE2 does not have the busy pin, hence a dummy busy signal has to be
-- generated so that the same state machine can be used.
-- ICAPE2 works very similar to Virtex6 ICAP.
-- It is observed from Chipscope that the BUSY goes low after 3 clocks following
-- ce assertion for read.
-- Busy goes low immediately after ce, we assertion in case of write
-- A dummy BUSY will be generated by delaying the CE

 process (ICAP_Clk)
 begin
     if (ICAP_Clk'event and ICAP_Clk = '1') then
        if (ICAP_Reset = '1') then
          ce_del1 <= '0';
          ce_del2 <= '0';
          ce_del3 <= '0';
        else 
          ce_del1 <= icap_ce;
          ce_del2 <= ce_del1;
          ce_del3 <= ce_del2;
        end if;
     end if;
  end process;

-- A busy signal has to be genrated for ABORTs as well
-- Following process generates the busy during ABORTs

 process (ICAP_Clk)
 begin
     if (ICAP_Clk'event and ICAP_Clk = '1') then
        if (ICAP_Reset = '1') then
           rdwr_int1 <= '1';
           same_cycle <= '0';
        elsif (icap_ce = '0') then
           rdwr_int1 <= icap_we;
           same_cycle <= '1';
        else
           rdwr_int1 <= '1';
           same_cycle <= '0';
        end if;
     end if;
  end process;

 
 process (ICAP_Clk)
 begin
     if (ICAP_Clk'event and ICAP_Clk = '1') then
        if (ICAP_Reset = '1') then
           abort_detect <= '0';
        elsif (icap_ce = '0' and same_cycle = '1') then
           if (rdwr_int1 = icap_we) then
              abort_detect <= '0';
           else 
              abort_detect <= '1';
           end if;
        end if;
     end if;
 end process;

 process (ICAP_Clk)
 begin
     if (ICAP_Clk'event and ICAP_Clk = '1') then
        if (ICAP_Reset = '1') then
           abort_del1 <= '0';
           abort_del2 <= '0';
           abort_del3 <= '0';
        else
           abort_del1 <= abort_detect;
           abort_del2 <= abort_del1;
           abort_del3 <= abort_del2;
        end if;
    end if;
  end process;

  busy_abort <= abort_del1 or abort_del2 or abort_del3 or abort_detect;

-- Following generates busy for read transactions

  busy_int <= ce_del3 or icap_ce;

-- Following would take care of the busy for read as well as write
-- For a write transaction the "and icap_we" will drag the busy low immediately
-- for a read transaction since the icap_we is high, the final busy will be busy_int
  icap_busy <= (busy_int and icap_we) or busy_abort;
 

 
   
   end generate GEN_FUNCTIONAL_UNISIM;
   
end architecture imp;


-------------------------------------------------------------------------------
-- hwicap.vhd - entity/architecture pair

-------------------------------------------------------------------------------
-- (c) Copyright 2010 - 2011 Xilinx, Inc. All rights reserved.
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
-------------------------------------------------------------------------------
-- Filename:        hwicap.vhd
-- Description:
--
-- HWICAP module can configure the FPGA using ICAP.It has one write FIFO & one
-- read FIFO. The configuration bitstream will be written in to the write FIFO
-- & from whare the bit stream will be laoded in to the ICAP.
-- Similarly during reading the bitstream loaded in to the read FIFO, from
-- where the processor will read the bit stream. The ocuupany registers will
-- tell the ocupancy value in the FIFOs. The status register tells the status
-- of read. The control register chooses the read or write of configuration
-- bitstream & reseting the registers aswell as FIFOs
--
-------------------------------------------------------------------------------
-- Naming Conventions:
--      active low signals:                     "*_n"
--      clock signals:                          "clk", "clk_div#", "clk_#x"
--      reset signals:                          "rst", "rst_n"
--      generics:                               "C_*"
--      user defined types:                     "*_TYPE"
--      state machine next state:               "*_ns"
--      state machine current state:            "*_cs"
--      combinatorial signals:                  "*_com"
--      pipelined or register delay signals:    "*_d#"
--      counter signals:                        "*cnt*"
--      clock enable signals:                   "*_ce"
--      internal version of output port         "*_i"
--      device pins:                            "*_pin"
--      ports:                                  - Names begin with Uppercase
--      processes:                              "*_PROCESS"
--      component instantiations:               "<ENTITY_>I_<#|FUNC>
-------------------------------------------------------------------------------
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library axi_lite_ipif_v3_0_4;
library lib_cdc_v1_0_2;
library lib_pkg_v1_0_2;
use lib_pkg_v1_0_2.lib_pkg.all;
use axi_lite_ipif_v3_0_4.ipif_pkg.all;
use lib_cdc_v1_0_2.cdc_sync;

library unisim;
use unisim.vcomponents.all;

library axi_hwicap_v3_0_14;
use axi_hwicap_v3_0_14.all;
-------------------------------------------------------------------------------
-- Definition of Generics:
--  ICAP_DWIDTH         -- ICAP data width
--  C_SAXI_DWIDTH       -- AXI data width
--  C_SIMULATION        -- Parameter is TRUE for functional simulation
--  C_BRAM_SRL_FIFO_TYPE-- type of the FIFO either as distributer or BRAM
--  C_FAMILY            -- target FPGA family
-------------------------------------------------------------------------------
-- --inputs
--
--  ICAP_Clk            -- ICAP clock
--
--  Bus2IP_Clk          -- PLB clock
--  Bus2IP_Reset        -- PLB Reset
--  Bus2IP_BE           -- PLB Byte Enable
--  Bus2IP_Data         -- PLB data bus
--  Bus2IP_rnw          -- Bus to IP read not write signal
--  Bus2IP_cs           -- Bus to IP Chip select signal
--  Bus2IP_wrce         -- Bus to IP write chip enable
--  Bus2IP_rdce         -- Bus to IP read chip enable
-- --outputs
--
--  IP2Bus_Data         -- Slave Data Bus
--  IP2Bus_errAck       -- Slave error acknowledge
--  IP2Bus_RdAck        -- Slave Read Acknowledge
--  IP2Bus_WrAck        -- Slave Write Acknowledge
--  Intr_rst            -- Reset the interrupt controller
--  IP2Bus_AddrAck      -- Slave Address Acknowledge
-------------------------------------------------------------------------------
entity hwicap_shared is
  generic (
    ICAP_DWIDTH         : integer := 16;
    C_WRITE_FIFO_DEPTH  : integer := 16;
    C_READ_FIFO_DEPTH   : integer := 16;
    C_SAXI_DWIDTH       : integer := 32;
    C_SIMULATION        : integer := 2;
    C_BRAM_SRL_FIFO_TYPE: integer := 1;  -- default BRAM
    C_ICAP_WIDTH        : string := "X8";
    C_INCLUDE_STARTUP   : integer := 0;
    C_SHARED_STARTUP    : integer range 0 to 1 := 0;
    C_MODE              : integer range 0 to 1 := 0;
    C_ICAP_EXTERNAL     : integer := 0;
    C_OPERATION         : integer := 0;
    C_NOREAD            : integer := 0;
    C_ENABLE_ASYNC      : integer := 0;  
    C_DEVICE_ID         : bit_vector := X"04224093";
    C_FAMILY            : string  := "virtex7");
  port(
    ICAP_Clk            : in std_logic;
    Eos_in              : in std_logic;
    Bus2IP_Clk          : in std_logic;
    Bus2IP_Reset        : in std_logic;
    Bus2IP_Addr         : in std_logic_vector(0 to 9-1);
    Bus2IP_BE           : in std_logic_vector(0 to C_SAXI_DWIDTH/8-1);
    Bus2IP_Data         : in std_logic_vector(0 to C_SAXI_DWIDTH-1);
    Bus2IP_rnw          : in std_logic;
    Bus2IP_cs           : in std_logic;
    Bus2IP_wrce         : in std_logic_vector(0 to 7);
    Bus2IP_rdce         : in std_logic_vector(0 to 7);
    IP2Bus_Data         : out std_logic_vector(0 to C_SAXI_DWIDTH-1);
    IP2Bus_errAck       : out std_logic;
    IP2Bus_RdAck        : out std_logic;
    IP2Bus_WrAck        : out std_logic;
    IP2Bus_AddrAck      : out std_logic;
    Intr_rst            : out std_logic;
    IP2Bus_Intr         : out std_logic_vector(0 to 3);
    CFGCLK : out std_logic;
    CFGMCLK : out std_logic;
    PREQ : out std_logic;
    CLK : in std_logic;
    GSR : in std_logic;
    GTS : in std_logic;
    KEYCLEARB : in std_logic;
    PACK : in std_logic;
    USRCCLKO : in std_logic;
    USRCCLKTS : in std_logic;
    USRDONEO : in std_logic;
    USRDONETS : in std_logic;
    icap_i                 : in  std_logic_vector(31 downto 0);  
    icap_o                 : out std_logic_vector(31 downto 0);
    icap_csib              : out std_logic;
    icap_rdwrb             : out std_logic;
    icap_req               : out std_logic;  -- Request the ICAP port                      
    icap_gnt               : in  std_logic;  -- ICAP granted                               
    icap_rel               : in  std_logic; 
    icap_avail             : in  std_logic 

);

end entity hwicap_shared;

architecture imp of hwicap_shared is
  attribute DowngradeIPIdentifiedWarnings: string;
  attribute DowngradeIPIdentifiedWarnings of imp : architecture is "yes";


--component axi_hwicap_v3_0_14_icap_test
--      port (
--        clk           : in std_logic;
--        csb           : in std_logic;
--        rdwrb         : in std_logic;
--        i             : in std_logic_vector (31 downto 0);
--        busy          : out std_logic;
--        o             : out std_logic_vector (31 downto 0));
--end component;
        


constant MTBF_STAGES : integer := 4;
-- signal declaration starts here ...
signal wrfifo_rden      : std_logic;
signal rdfifo_wren      : std_logic;
signal send_done        : std_logic;
signal rdfifo_datain    : std_logic_vector(0 to ICAP_DWIDTH-1);
signal wrfifo_dataout   : std_logic_vector(0 to ICAP_DWIDTH-1);
signal icap_datain      : std_logic_vector(0 to ICAP_DWIDTH-1);
signal icap_dataout     : std_logic_vector(0 to ICAP_DWIDTH-1);
signal writefifo_full   : std_logic;
signal writefifo_empty  : std_logic;
signal readfifo_full    : std_logic;
signal readfifo_empty   : std_logic;
signal rnc              : std_logic_vector(0 to 1);
signal size             : std_logic_vector(0 to 11);
signal icap_busy        : std_logic;
signal icap_ce          : std_logic;
signal icap_we          : std_logic;
signal reset_cr         : std_logic;
signal size_counter     : std_logic_vector(0 to 11);
signal abort            : std_logic;
signal abort_in_progress: std_logic;
signal status_read      : std_logic;
signal icap_status      : std_logic_vector(0 to 31);
signal ICAP_Reset : std_logic;
signal bus2icap_reset_trig_1 : std_logic;
signal bus2icap_reset_trig_2 : std_logic;
signal bus2icap_reset_trig_3 : std_logic;
signal gate_icap : std_logic;
signal gate_icap_p : std_logic;
signal gate_clk : std_logic;
signal gate_clk1 : std_logic;
signal rdfull : std_logic;
signal inv_gate : std_logic;
signal icap_avail_int : std_logic := '0';
signal ce_del1 : std_logic;
signal ce_del2 : std_logic;
signal ce_del3 : std_logic;
signal rdwr_int1 : std_logic;
signal rdwr_int2 : std_logic;
signal abort_detect : std_logic;
signal abort_del1 : std_logic;
signal abort_del2 : std_logic;
signal abort_del3 : std_logic;
signal busy_abort : std_logic;
signal busy_int : std_logic;
signal same_cycle : std_logic;
signal hang_status : std_logic;
signal icap_dataout1 : std_logic_vector (0 to 31);
signal icap_datain1 : std_logic_vector (0 to 31);
signal icap_available : std_logic;


begin  -- architecture IMP
icap_avail_int <= icap_avail;
  -----------------------------------------------------------------------------
  -- IPIC Interface
  -----------------------------------------------------------------------------
  IPIC_IF_I : entity axi_hwicap_v3_0_14.ipic_if
    generic map (
      C_SAXI_DWIDTH       => C_SAXI_DWIDTH,
      C_WRITE_FIFO_DEPTH  => C_WRITE_FIFO_DEPTH,
      C_READ_FIFO_DEPTH   => C_READ_FIFO_DEPTH,
      ICAP_DWIDTH         => ICAP_DWIDTH,
      C_MODE              => C_MODE,
      C_NOREAD            => C_NOREAD,
      C_SHARED_STARTUP    => C_SHARED_STARTUP,
      C_ENABLE_ASYNC      => C_ENABLE_ASYNC,
      C_INCLUDE_STARTUP   => C_INCLUDE_STARTUP,
      C_BRAM_SRL_FIFO_TYPE=> C_BRAM_SRL_FIFO_TYPE,
      C_FAMILY            => C_FAMILY)
    port map (
      ICAP_Clk            => ICAP_Clk,
      ICAP_Reset          => ICAP_Reset,
      Bus2IP_Clk          => Bus2IP_Clk,
      Bus2IP_Reset        => Bus2IP_Reset,
      Send_done           => send_done,
      Reset_cr            => reset_cr,
      Icap_out            => icap_i,
      Bus2IP_cs           => Bus2IP_cs,
      Bus2IP_BE           => Bus2IP_BE,
      Bus2IP_rnw          => Bus2IP_rnw,
      Bus2IP_wrce         => Bus2IP_wrce,
      Bus2IP_rdce         => Bus2IP_rdce,
      Bus2IP_Data         => Bus2IP_Data,
      Wrfifo_rden         => wrfifo_rden,
      IP2Bus_Data         => IP2Bus_Data,
      Rdfifo_wren         => rdfifo_wren,
      Rdfifo_datain       => rdfifo_datain,
      Status_read         => status_read,
      Icap_status         => icap_status,
      Wrfifo_dataout      => wrfifo_dataout,
      Writefifo_full      => writefifo_full,
      Writefifo_empty     => writefifo_empty,
      Readfifo_full       => readfifo_full,
      Readfifo_empty      => readfifo_empty,
      Abort               => abort,
      Abort_in_progress   => abort_in_progress,
      Rnc                 => rnc,
      Hang_status         => hang_status,
      Eos_in              => Eos_in,
      icap_available      => icap_avail_int,
      Size                => size,
      Size_counter        => size_counter,
      IP2Bus_RdAck        => IP2Bus_RdAck,
      IP2Bus_WrAck        => IP2Bus_WrAck,
      IP2Bus_AddrAck      => IP2Bus_AddrAck,
      IP2Bus_errAck       => IP2Bus_errAck,
      Intr_rst            => Intr_rst,
      Gate_icap           => gate_icap,
      Gate_icap_p         => gate_icap_p,
      IP2Bus_Intr         => IP2Bus_Intr,
      CFGCLK    => CFGCLK,
      CFGMCLK    => CFGMCLK,
      PREQ    => PREQ,
      CLK    => CLK,
      GSR    => GSR,
      GTS    => GTS,
      KEYCLEARB    => KEYCLEARB,
      PACK    => PACK,
      USRCCLKO    => USRCCLKO,
      USRCCLKTS    => USRCCLKTS,
      USRDONEO    => USRDONEO,
      USRDONETS    => USRDONETS
      --icap_req    => icap_req,
      --icap_rel  => icap_rel,
      --icap_gnt  => icap_gnt
      --icap_i  => icap_i,
      --icap_o => icap_o
     -- icap_csib => icap_csib,
     -- icap_rdwrb => icap_rdwrb
  );
-------------------------------------------------------------------------------
-- icap State Machine
-------------------------------------------------------------------------------

rdfull <= gate_icap_p;

  icap_statemachine_I1: entity axi_hwicap_v3_0_14.icap_statemachine_shared
    generic map (
      ICAP_DWIDTH         => ICAP_DWIDTH,
      C_MODE              => C_MODE,
      C_FAMILY            => C_FAMILY)
    port map (
      Clk                 => ICAP_Clk,
      Rst                 => ICAP_Reset,
      Wrfifo_dataout      => wrfifo_dataout,
      Icap_dataout        => icap_i,
      Wrfifo_full         => writefifo_full,
      Wrfifo_empty        => writefifo_empty,
      Rdfifo_empty        => readfifo_empty,
      Rdfifo_full         => rdfull,
      Icap_busy           => icap_busy,
      Status_read         => status_read,
      Rnc                 => rnc,
      Abort               => abort,
      Size                => size,
      Size_counter        => size_counter,
      Wrfifo_rden         => wrfifo_rden,
      Rdfifo_wren         => rdfifo_wren,
      Icap_ce             => icap_ce,
      Icap_we             => icap_we,
      Abort_in_progress   => abort_in_progress,
      Icap_status         => icap_status,
      Send_done           => send_done,
      Reset_cr            => reset_cr,
      Hang_status         => hang_status,
      Icap_datain         => icap_o,
      Rdfifo_datain       => rdfifo_datain,
      icap_req    => icap_req,
      icap_rel  => icap_rel,
      icap_gnt  => icap_gnt
      --icap_i  => icap_i,
      --icap_o => icap_i
     -- icap_csib => icap_csib,
      --icap_rdwrb => icap_rdwrb
  );
icap_csib <= icap_ce;
icap_rdwrb <= icap_we;

--  GEN_BUS2ICAP_RESET:process (ICAP_Clk)
--  begin
--    if ICAP_Clk'event and ICAP_Clk = '1' then
--       -- generates three flip flop synchronizer bus2icap reset trigger signal
--       -- in ICAP_Clk
--       bus2icap_reset_trig_1 <= Bus2IP_Reset;
--       bus2icap_reset_trig_2 <= bus2icap_reset_trig_1;
--    end if;
--  end process GEN_BUS2ICAP_RESET;

GEN_BUS2ICAP_RESET : entity lib_cdc_v1_0_2.cdc_sync
    generic map (
        C_CDC_TYPE                 => 1,
        C_RESET_STATE              => 0,
        C_SINGLE_BIT               => 1,
        C_VECTOR_WIDTH             => 32,
        C_MTBF_STAGES              => MTBF_STAGES
    )
    port map (
        prmry_aclk                 => '0',
        prmry_resetn               => '0',
        prmry_in                   => Bus2IP_Reset,
        prmry_vect_in              => (others => '0'),

        scndry_aclk                => ICAP_Clk,
        scndry_resetn              => '0',
        scndry_out                 => bus2icap_reset_trig_2, --awvalid_to,
        scndry_vect_out            => open
    );


  ICAP_Reset <= bus2icap_reset_trig_2;

  -----------------------------------------------------------------------------
  -- simulation only using the FIFO model
  -----------------------------------------------------------------------------

-- gate_bufgce : BUFGCE
--              port map (
--                O => gate_clk,
--                I => ICAP_Clk,
--                CE => inv_gate);

--BUFGCTRL_INST : if (C_OPERATION = 1) generate
--begin
-- 
--      inv_gate <= not gate_icap;
--
--
-- gate_bfgctrl : BUFGCTRL 
--               port map (
--            
--    O           => gate_clk,
--    CE0         => inv_gate,
--    CE1         => '0',
--    I0          => ICAP_Clk,
--    I1          => '1',
--    IGNORE0     => '0',
--    IGNORE1     => '1',
--    S0          => '1',
--    S1          => '0'
--    );
--
--end generate BUFGCTRL_INST;
--
--
--NO_BUFGCTRL_INST : if (C_OPERATION = 0) generate
--begin
--
--    gate_clk <= ICAP_Clk; 
--
--end generate NO_BUFGCTRL_INST;


--  GEN_FUNCTIONAL : if C_SIMULATION = 1 generate
-- --    ICAP_TEST_I : axi_hwicap_v3_0_14_icap_test
-- --     port map (
-- --      -- Rst               => ICAP_Reset,
-- --       clk                => gate_clk,
-- --       csb                => icap_ce, 
-- --       rdwrb              => icap_we,
-- --       i                  => icap_datain1,
-- --       busy               => icap_busy,
-- --       o                  => icap_dataout1);
--
--
--
--  --     icap_dataout <= icap_dataout1;
--  --     icap_datain1 <= icap_datain;
--
--
--  end generate GEN_FUNCTIONAL;
--  -----------------------------------------------------------------------------
--  --implementation only code - Simulations using unisim model
--  -----------------------------------------------------------------------------
--  GEN_FUNCTIONAL_UNISIM : if C_SIMULATION = 2 generate
--  begin
--
--   GEN_VIRTEX7_ICAP : if ( 
--            (C_FAMILY = "virtex7") or
--            (C_FAMILY = "kintex7") or
--            (C_FAMILY = "zynq") or
--            (C_FAMILY = "artix7")  
--           ) generate
--    begin
--       ICAP_VIRTEX7_I : ICAPE2
--         generic map (
--           DEVICE_ID         => C_DEVICE_ID,
--           ICAP_WIDTH        => C_ICAP_WIDTH)
--         port map (
--           clk               => gate_clk,
--           csib               => icap_ce,
--           rdwrb             => icap_we,
--           i                 => icap_datain,
--       --    busy              => icap_busy,
--           o                 => icap_dataout);
--
--       icap_available <= '0';
--
--   end generate GEN_VIRTEX7_ICAP;
--
--
--   GEN_VIRTEXU_ICAP : if ( 
--                          (C_FAMILY /= "virtex7") and
--                          (C_FAMILY /= "kintex7") and
--                          (C_FAMILY /= "zynq") and
--                          (C_FAMILY /= "artix7")
--                           ) generate
--   begin
--
--       ICAP_VIRTEXU_I : ICAPE3
--         generic map ( 
--           DEVICE_ID         => C_DEVICE_ID)
----           ICAP_WIDTH        => C_ICAP_WIDTH)
--         port map (
--           clk               => gate_clk,
--           csib              => icap_ce,
--           rdwrb             => icap_we,
--           i                 => icap_datain,
--           o                 => icap_dataout,
--           prerror           => open,
--           prdone            => open,
--           avail             => icap_available);
--
----       icap_available <= '1';
--
--
--   end generate GEN_VIRTEXU_ICAP;

-- The ICAPE2 does not have the busy pin, hence a dummy busy signal has to be
-- generated so that the same state machine can be used.
-- ICAPE2 works very similar to Virtex6 ICAP.
-- It is observed from Chipscope that the BUSY goes low after 3 clocks following
-- ce assertion for read.
-- Busy goes low immediately after ce, we assertion in case of write
-- A dummy BUSY will be generated by delaying the CE

 process (ICAP_Clk)
 begin
     if (ICAP_Clk'event and ICAP_Clk = '1') then
        if (ICAP_Reset = '1') then
          ce_del1 <= '0';
          ce_del2 <= '0';
          ce_del3 <= '0';
        else 
          ce_del1 <= icap_ce;
          ce_del2 <= ce_del1;
          ce_del3 <= ce_del2;
        end if;
     end if;
  end process;

-- A busy signal has to be genrated for ABORTs as well
-- Following process generates the busy during ABORTs

 process (ICAP_Clk)
 begin
     if (ICAP_Clk'event and ICAP_Clk = '1') then
        if (ICAP_Reset = '1') then
           rdwr_int1 <= '1';
           same_cycle <= '0';
        elsif (icap_ce = '0') then
           rdwr_int1 <= icap_we;
           same_cycle <= '1';
        else
           rdwr_int1 <= '1';
           same_cycle <= '0';
        end if;
     end if;
  end process;

 
 process (ICAP_Clk)
 begin
     if (ICAP_Clk'event and ICAP_Clk = '1') then
        if (ICAP_Reset = '1') then
           abort_detect <= '0';
        elsif (icap_ce = '0' and same_cycle = '1') then
           if (rdwr_int1 = icap_we) then
              abort_detect <= '0';
           else 
              abort_detect <= '1';
           end if;
        end if;
     end if;
 end process;

 process (ICAP_Clk)
 begin
     if (ICAP_Clk'event and ICAP_Clk = '1') then
        if (ICAP_Reset = '1') then
           abort_del1 <= '0';
           abort_del2 <= '0';
           abort_del3 <= '0';
        else
           abort_del1 <= abort_detect;
           abort_del2 <= abort_del1;
           abort_del3 <= abort_del2;
        end if;
    end if;
  end process;

  busy_abort <= abort_del1 or abort_del2 or abort_del3 or abort_detect;

-- Following generates busy for read transactions

  busy_int <= ce_del3 or icap_ce;

-- Following would take care of the busy for read as well as write
-- For a write transaction the "and icap_we" will drag the busy low immediately
-- for a read transaction since the icap_we is high, the final busy will be busy_int
  icap_busy <= (busy_int and icap_we) or busy_abort;
 

 
   
 --  end generate GEN_FUNCTIONAL_UNISIM;
   
end architecture imp;


-------------------------------------------------------------------------------
-- axi_hwicap.vhd - entity/architecture pair

-------------------------------------------------------------------------------
-- (c) Copyright 2010 - 2011 Xilinx, Inc. All rights reserved.
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
-------------------------------------------------------------------------------
-- Filename:    axi_hwicap.vhd
-- Version:     v2.00a
-- Description: Provides the interface between the processor & ICAP
--                  
-- VHDL-Standard:   VHDL'93
-------------------------------------------------------------------------------
-- Naming Conventions:
--      active low signals:                     "*_n"
--      clock signals:                          "clk", "clk_div#", "clk_#x"
--      reset signals:                          "rst", "rst_n"
--      generics:                               "C_*"
--      user defined types:                     "*_TYPE"
--      state machine next state:               "*_ns"
--      state machine current state:            "*_cs"
--      combinatorial signals:                  "*_com"
--      pipelined or register delay signals:    "*_d#"
--      counter signals:                        "*cnt*"
--      clock enable signals:                   "*_ce"
--      internal version of output port         "*_i"
--      device pins:                            "*_pin"
--      ports:                                  - Names begin with Uppercase
--      processes:                              "*_PROCESS"
--      component instantiations:               "<ENTITY_>I_<#|FUNC>
-------------------------------------------------------------------------------
library ieee;
use ieee.std_logic_1164.all;

library axi_lite_ipif_v3_0_4;
library lib_pkg_v1_0_2;
use lib_pkg_v1_0_2.lib_pkg.all;
use axi_lite_ipif_v3_0_4.ipif_pkg.all;
use axi_lite_ipif_v3_0_4.axi_lite_ipif;

library unisim;
use unisim.all;


library interrupt_control_v3_1_4;
use interrupt_control_v3_1_4.interrupt_control;

library axi_hwicap_v3_0_14;
use axi_hwicap_v3_0_14.hwicap;

-------------------------------------------------------------------------------
-- Definition of Generics:
-- C_BASEADDR               -- Base address of the core
-- C_HIGHADDR               -- Permits alias of address space
-- C_S_AXI_DATA_WIDTH       -- AXI data bus width
-- C_S_AXI_ADDR_WIDTH       -- AXI address bus width
-- C_WRITE_FIFO_DEPTH       -- Write FIFO depth
-- C_READ_FIFO_DEPTH        -- Read FIFO depth
-- C_ICAP_DWIDTH            -- ICAP/ICAPE2 Data Width
-- C_SIMULATION             -- Parameter is TRUE for functional simulation
-- C_BRAM_SRL_FIFO_TYPE     -- type of the FIFO either as distributer or BRAM
-- C_FAMILY                 -- target FPGA family
-------------------------------------------------------------------------------
-- Definition of Ports:
--  ICAP_Clk                 -- ICAP clock
-- PLB Interface
-- S_AXI_ACLK                -- AXI Clock
-- S_AXI_ARESETN             -- AXI Reset
-- S_AXI_AWADDR              -- AXI Write address
-- S_AXI_AWVALID             -- Write address valid
-- S_AXI_AWREADY             -- Write address ready
-- S_AXI_WDATA               -- Write data
-- S_AXI_WSTRB               -- Write strobes
-- S_AXI_WVALID              -- Write valid
-- S_AXI_WREADY              -- Write ready
-- S_AXI_BRESP               -- Write response
-- S_AXI_BVALID              -- Write response valid
-- S_AXI_BREADY              -- Response ready
-- S_AXI_ARADDR              -- Read address
-- S_AXI_ARVALID             -- Read address valid
-- S_AXI_ARREADY             -- Read address ready
-- S_AXI_RDATA               -- Read data
-- S_AXI_RRESP               -- Read response
-- S_AXI_RVALID              -- Read valid
-- S_AXI_RREADY              -- Read ready
-----------------------------------------------------------------------------
-- Entity section
-----------------------------------------------------------------------------
entity axi_hwicap is
  -- Generics to be set by user
  generic (
--    C_BASEADDR          : std_logic_vector(31 downto 0) := X"FFFF_FFFF";
--    C_HIGHADDR          : std_logic_vector(31 downto 0) := X"0000_0000";
    C_ENABLE_ASYNC      : integer range 0 to 1 := 0;
    C_S_AXI_DATA_WIDTH  : integer  range 32 to 32   := 32;
    C_INCLUDE_STARTUP   : integer range 0 to 1 := 0;
    C_S_AXI_ADDR_WIDTH  : integer                   := 9;
    C_WRITE_FIFO_DEPTH  : integer range 64 to 1024:= 256;
    C_READ_FIFO_DEPTH   : integer range 32 to 256:= 256;
    C_ICAP_WIDTH_S      : string := "X8";
    C_DEVICE_ID         : std_logic_vector := X"04224093";
    C_MODE              : integer := 0;
    C_SHARED_STARTUP    : integer range 0 to 1 := 0;
    C_OPERATION         : integer := 0;
    C_NOREAD            : integer := 0;
    C_SIMULATION        : integer range 0 to 2 := 2;
    C_BRAM_SRL_FIFO_TYPE: integer range 0 to 1 := 1;  -- default BRAM
    C_ICAP_EXTERNAL     : integer range 0 to 1 := 0;  
    C_FAMILY            : string  := "virtex7");
  port
    (
      icap_clk          : in  std_logic;
      eos_in            : in  std_logic;
      s_axi_aclk        : in  std_logic;
      s_axi_aresetn     : in  std_logic;
      s_axi_awaddr      : in  std_logic_vector(C_S_AXI_ADDR_WIDTH-1 downto 0);
      s_axi_awvalid     : in  std_logic;
      s_axi_awready     : out std_logic;
      s_axi_wdata       : in  std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0);
      s_axi_wstrb       : in  std_logic_vector((C_S_AXI_DATA_WIDTH/8)-1 downto 0);
      s_axi_wvalid      : in  std_logic;
      s_axi_wready      : out std_logic;
      s_axi_bresp       : out std_logic_vector(1 downto 0);
      s_axi_bvalid      : out std_logic;
      s_axi_bready      : in  std_logic;
      s_axi_araddr      : in  std_logic_vector(C_S_AXI_ADDR_WIDTH-1 downto 0);
      s_axi_arvalid     : in  std_logic;
      s_axi_arready     : out std_logic;
      s_axi_rdata       : out std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0);
      s_axi_rresp       : out std_logic_vector(1 downto 0);
      s_axi_rvalid      : out std_logic;
      s_axi_rready      : in  std_logic;
      ip2intc_irpt      : out std_logic;
      cfgclk            : out std_logic;
      cfgmclk           : out std_logic;
      preq              : out std_logic;
      clk               : in std_logic;
      gsr               : in std_logic;
      gts               : in std_logic;
      keyclearb         : in std_logic;
      pack              : in std_logic;
      usrcclko          : in std_logic;
      usrcclkts         : in std_logic;
      usrdoneo          : in std_logic;
      usrdonets         : in std_logic;
      icap_i            : in  std_logic_vector(31 downto 0); 
      icap_o            : out std_logic_vector(31 downto 0):= (others => '0'); 
      icap_csib         : out std_logic;
      icap_rdwrb        : out std_logic;
      cap_req          : out std_logic;  -- Request the ICAP port                      
      cap_gnt          : in  std_logic;  -- ICAP granted                               
      cap_rel          : in  std_logic;   -- Release the ICAP at the first opportunity  
      icap_avail        : in  std_logic 
      );
 end axi_hwicap;
-------------------------------------------------------------------------------
-- Architecture
-------------------------------------------------------------------------------
architecture implementation of axi_hwicap is
  attribute DowngradeIPIdentifiedWarnings: string;
  attribute DowngradeIPIdentifiedWarnings of implementation : architecture is "yes";


--  constant C_CORE_GENERATION_INFO : string := C_INSTANCE & ",axi_hwicap,{"
--      & "c_family="               & C_FAMILY
--      & ",c_instance="            & C_INSTANCE
--      & ",c_icap_width_s="        & C_ICAP_WIDTH_S
--      & ",c_write_fifo_depth="    & integer'image(C_WRITE_FIFO_DEPTH)
--      & ",c_read_fifo_depth="     & integer'image(C_READ_FIFO_DEPTH)
--      & ",c_saxi_dwidth="         & integer'image(C_S_AXI_DATA_WIDTH)
--      & ",c_simulation="          & integer'image(C_SIMULATION)
--      & ",c_bram_srl_fifo_type="  & integer'image(C_BRAM_SRL_FIFO_TYPE)
--      & ",c_mode="                & integer'image(C_MODE)
--      & ",c_noread="              & integer'image(C_NOREAD)
--      & ",c_operation="           & integer'image(C_OPERATION)
--      & ",c_include_startup="     & integer'image(C_INCLUDE_STARTUP)
--      & "}";
--  attribute CORE_GENERATION_INFO : string;
--  attribute CORE_GENERATION_INFO of implementation : architecture is C_CORE_GENERATION_INFO;


  --IPIF Generics that must remain at these values for the DAC
  constant C_BASEADDR : std_logic_vector := X"00000000";
  constant  C_DEVICE_ID_B : bit_vector := to_bitvector (C_DEVICE_ID); 
  constant  ZEROES             : std_logic_vector := X"00000000";
  constant  NUM_INTR           : integer     := 4;
  constant  C_INTR_TYPE        : integer     := 3;
--  constant  INTR_HI_ADDR       : std_logic_vector := C_BASEADDR or X"0000003F";
--  constant  HWICAP_REG_B_ADR   : std_logic_vector := C_BASEADDR or X"00000100";
--  constant  HWICAP_REG_H_ADR   : std_logic_vector := C_BASEADDR or X"0000011F";
  constant  INTR_HI_ADDR       : std_logic_vector := X"0000003F";
  constant  HWICAP_REG_B_ADR   : std_logic_vector := X"00000100";
  constant  HWICAP_REG_H_ADR   : std_logic_vector := X"0000011F";
  constant  C_S_AXI_MIN_SIZE   :std_logic_vector(31 downto 0):= X"000001FF";
  constant  C_USE_WSTRB        :integer := 0;
  constant  C_DPHASE_TIMEOUT   :integer range 0 to 256   := 16;  

  -- No interrupt from PLBv46 Slave Single, but made 1 to meet the port
  -- width requirement of IPIF_Lvl_Interrupts signal.
  constant NUM_IPIF_IRPT_SRC       : integer      := 1;

  constant IP_INTR_MODE_ARRAY      : integer_array_type := 
         populate_intr_mode_array(NUM_INTR, C_INTR_TYPE);
  constant ARD_ID_ARRAY  : INTEGER_ARRAY_TYPE
                              := ( IPIF_INTR, --Interrupt module
                                   USER_00
                                   );
  constant ARD_ADDR_RANGE_ARRAY : SLV64_ARRAY_TYPE :=
      ( ZEROES & C_BASEADDR,
        ZEROES & INTR_HI_ADDR,
        ZEROES & HWICAP_REG_B_ADR,-- HWICAP base address
        ZEROES & HWICAP_REG_H_ADR -- HWICAP high address
        );
  constant ARD_NUM_CE_ARRAY     : INTEGER_ARRAY_TYPE:= (16,8);
  constant Number_of_CE_signals : integer := 23;

-------------------------------------------------------------------------------
-- update ICAP_DWIDTH based on FPGA families those supports ICAP             --
-------------------------------------------------------------------------------
--function gen_icap_dwidth(family : string) return integer is
  --  variable r : integer := 16;
--begin
  -- if supported(C_FAMILY, (u_ICAPE2)) = true then
    --  r := 32;
   --else
     -- r := 32;
   --end if;
   --return r;
--end gen_icap_dwidth;

--constant ICAP_DWIDTH : integer := gen_icap_dwidth(C_FAMILY);
constant ICAP_DWIDTH : integer := 32; 
-------------------------------------------------------------------------------
-- Bitwise OR of a std_logic_vector.
-------------------------------------------------------------------------------
function or_reduce(slv : std_logic_vector) return std_logic is
    variable r : std_logic := '0';
begin
    for i in slv'range loop
        r := r or slv(i);
    end loop;
    return r;
end or_reduce;

-------------------------------------------------------------------------------
-- Signal and Type Declarations
-------------------------------------------------------------------------------

--  signal bus2ip_be           : std_logic_vector(0 to (C_S_AXI_DATA_WIDTH/8) - 1);
  signal bus2ip_be           : std_logic_vector(0 to (C_S_AXI_DATA_WIDTH/8) - 1);
  signal bus2ip_rnw          : std_logic;
  signal bus2ip_cs           : std_logic_vector(0 to 1);
  signal bus2ip_rdce         : std_logic_vector(23 downto 0);
  signal bus2ip_wrce         : std_logic_vector(23 downto 0);
  signal bus2ip_rdce_int     : std_logic_vector(0 to 23);
  signal bus2ip_wrce_int     : std_logic_vector(0 to 23);
  signal bus2ip_data         : std_logic_vector(0 to C_S_AXI_DATA_WIDTH-1);
  signal bus2ip_addr         : std_logic_vector(0 to C_S_AXI_ADDR_WIDTH-1);
  signal ip2bus_data_i       : std_logic_vector(0 to C_S_AXI_DATA_WIDTH-1);
  signal ip2bus_data         : std_logic_vector(0 to C_S_AXI_DATA_WIDTH-1);
  signal ip2bus_wrack        : std_logic;
  signal ip2bus_rdack        : std_logic;
  signal bus2ip_clk          : std_logic;
  signal bus2ip_reset        : std_logic;
  signal bus2ip_resetn       : std_logic;
  signal ip2bus_intr         : std_logic_vector(0 to NUM_INTR - 1);
  signal ip2bus_error_i      : std_logic;
  signal intr2bus_data       : std_logic_vector(0 to C_S_AXI_DATA_WIDTH-1);
  signal intr2bus_wrack      : std_logic;
  signal intr2bus_rdack      : std_logic;
  signal intr2bus_error      : std_logic;
  signal ip2bus_err          : std_logic;
  signal ip2bus_wrack_i      : std_logic;
  signal ip2bus_rdack_i      : std_logic;
  signal ip2bus_addrack      : std_logic;
  signal errack_reserved     : std_logic_vector(0 to 1) := (others => '0');
  signal intr_rst            : std_logic;
  signal ipif_lvl_interrupts : std_logic_vector(0 to NUM_IPIF_IRPT_SRC-1):=
                                                               (others => '0');
  signal wr_or               : std_logic;
  signal rd_or               : std_logic;
  signal ICAP_Clk_int        : std_logic;
 
begin  -- architecture IMP

 --  C_DEVICE_ID_B <= to_bitvector (C_DEVICE_ID);

   
            
 --    assert (supported (C_FAMILY, (u_ICAPE2))) 
 --   report "ICAPE2 component is not supported by C_FAMILY Device"
 --   severity error;

--     assert (supported (C_FAMILY, (u_ICAPE3))) 
--    report "ICAPE3 component is not supported by C_FAMILY Device"
--    severity error;

-------------------------------------------------------------------------------
-- Component Instantiations
-------------------------------------------------------------------------------
---------------------------------------------------------------------------
-- INSTANTIATE AXI Lite IPIF
---------------------------------------------------------------------------
  XI4_LITE_I : entity axi_lite_ipif_v3_0_4.axi_lite_ipif
        generic map(C_S_AXI_DATA_WIDTH    => C_S_AXI_DATA_WIDTH,
                    C_S_AXI_ADDR_WIDTH    => C_S_AXI_ADDR_WIDTH,
                    C_S_AXI_MIN_SIZE      => C_S_AXI_MIN_SIZE,
                    C_USE_WSTRB           => C_USE_WSTRB,
                    C_DPHASE_TIMEOUT      => C_DPHASE_TIMEOUT,
                    C_ARD_ADDR_RANGE_ARRAY=> ARD_ADDR_RANGE_ARRAY,
                    C_ARD_NUM_CE_ARRAY    => ARD_NUM_CE_ARRAY,
                    C_FAMILY              => C_FAMILY
                    )
        port map(
                    S_AXI_ACLK            => s_axi_aclk,
                    S_AXI_ARESETN         => s_axi_aresetn,
                    S_AXI_AWADDR          => s_axi_awaddr,
                    S_AXI_AWVALID         => s_axi_awvalid,
                    S_AXI_AWREADY         => s_axi_awready,
                    S_AXI_WDATA           => s_axi_wdata,
                    S_AXI_WSTRB           => s_axi_wstrb,
                    S_AXI_WVALID          => s_axi_wvalid,
                    S_AXI_WREADY          => s_axi_wready,
                    S_AXI_BRESP           => s_axi_bresp,
                    S_AXI_BVALID          => s_axi_bvalid,
                    S_AXI_BREADY          => s_axi_bready,
                    S_AXI_ARADDR          => s_axi_araddr,
                    S_AXI_ARVALID         => s_axi_arvalid,
                    S_AXI_ARREADY         => s_axi_arready,
                    S_AXI_RDATA           => s_axi_rdata,
                    S_AXI_RRESP           => s_axi_rresp,
                    S_AXI_RVALID          => s_axi_rvalid,
                    S_AXI_RREADY          => s_axi_rready,
  -- IP Interconnect (IPIC) port signals -------------------------------
                    Bus2IP_Clk            => bus2ip_clk,
                    Bus2IP_Resetn         => bus2ip_resetn,
                    IP2Bus_Data           => ip2bus_data_i,
                    IP2Bus_WrAck          => ip2bus_wrack_i,
                    IP2Bus_RdAck          => ip2bus_rdack_i,
                    IP2Bus_Error          => ip2bus_error_i,
                    Bus2IP_Addr           => bus2ip_addr,
                    Bus2IP_Data           => bus2ip_data,
                    Bus2IP_RNW            => bus2ip_rnw,
                    Bus2IP_BE             => bus2ip_be,
                    Bus2IP_CS             => bus2ip_cs,
                    Bus2IP_RdCE           => bus2ip_rdce,
                    Bus2IP_WrCE           => bus2ip_wrce 
                );						  
  -----------------------------------------------------------------------------
  -- Instantiate the HWICAP Controller
  -----------------------------------------------------------------------------
                    bus2ip_rdce_int <= bus2ip_rdce;

	      	    -- 23 downto 0 assigned to 0 to 23;

                    bus2ip_wrce_int <= bus2ip_wrce; 

ICAP_NOT_SHARED : if (C_ICAP_EXTERNAL = 0) generate
begin
  HWICAP_CTRL_I : entity axi_hwicap_v3_0_14.hwicap
        generic map(ICAP_DWIDTH              => ICAP_DWIDTH,
                    C_SAXI_DWIDTH            => C_S_AXI_DATA_WIDTH,
                    C_WRITE_FIFO_DEPTH       => C_WRITE_FIFO_DEPTH,
                    C_INCLUDE_STARTUP        => C_INCLUDE_STARTUP,
                    C_READ_FIFO_DEPTH        => C_READ_FIFO_DEPTH,
                    C_SIMULATION             => C_SIMULATION,
                    C_BRAM_SRL_FIFO_TYPE     => C_BRAM_SRL_FIFO_TYPE, -- default BRAM
                    C_ICAP_WIDTH             => C_ICAP_WIDTH_S,
                    C_MODE                   => C_MODE,
                    C_SHARED_STARTUP         => C_SHARED_STARTUP,
                    C_OPERATION              => C_OPERATION,
                    C_NOREAD                 => C_NOREAD,
                    C_DEVICE_ID              => C_DEVICE_ID_B,
                    C_ENABLE_ASYNC           => C_ENABLE_ASYNC,
                    C_FAMILY                 => C_FAMILY)
        port map (  ICAP_Clk                 => ICAP_Clk_int,
                    Eos_in                   => eos_in,
                    Bus2IP_Clk               => bus2ip_clk,
                    Bus2IP_Reset             => bus2ip_reset,
                    Bus2IP_Addr              => bus2ip_addr,
                    Bus2IP_BE                => bus2ip_be,
                    Bus2IP_Data              => bus2ip_data,
                    Bus2IP_RNW               => bus2ip_rnw,
                    Bus2IP_cs                => bus2ip_cs(1),
                    Bus2IP_RdCe              => bus2ip_rdce_int (16 to 23),
                    Bus2IP_WrCe              => bus2ip_wrce_int (16 to 23),
                    IP2Bus_Data              => ip2bus_data,
                    IP2Bus_errAck            => ip2bus_err,
                    IP2Bus_RdAck             => ip2bus_rdack,
                    IP2Bus_WrAck             => ip2bus_wrack,
                    IP2Bus_AddrAck           => ip2bus_addrack,
                    Intr_rst                 => intr_rst,
                    IP2Bus_Intr              => ip2bus_intr,
                    CFGCLK    => cfgclk,
                    CFGMCLK    => cfgmclk,
                    PREQ    => preq,
                    CLK    => clk,
                    GSR    => gsr,
                    GTS    => gts,
                    KEYCLEARB    => keyclearb,
                    PACK    => pack,
                    USRCCLKO    => usrcclko,
                    USRCCLKTS    => usrcclkts,
                    USRDONEO    => usrdoneo,
                    USRDONETS    => usrdonets
                    );
    end generate ICAP_NOT_SHARED;

ICAP_SHARED : if (C_ICAP_EXTERNAL = 1) generate
begin
  HWICAP_CTRL_I : entity axi_hwicap_v3_0_14.hwicap_shared
        generic map(ICAP_DWIDTH              => ICAP_DWIDTH,
                    C_SAXI_DWIDTH            => C_S_AXI_DATA_WIDTH,
                    C_WRITE_FIFO_DEPTH       => C_WRITE_FIFO_DEPTH,
                    C_INCLUDE_STARTUP        => C_INCLUDE_STARTUP,
                    C_READ_FIFO_DEPTH        => C_READ_FIFO_DEPTH,
                    C_SIMULATION             => C_SIMULATION,
                    C_BRAM_SRL_FIFO_TYPE     => C_BRAM_SRL_FIFO_TYPE, -- default BRAM
                    C_ICAP_WIDTH             => C_ICAP_WIDTH_S,
                    C_MODE                   => C_MODE,
                    C_SHARED_STARTUP         => C_SHARED_STARTUP,
                    C_OPERATION              => C_OPERATION,
                    C_NOREAD                 => C_NOREAD,
                    C_DEVICE_ID              => C_DEVICE_ID_B,
                    C_ENABLE_ASYNC           => C_ENABLE_ASYNC,
                    C_FAMILY                 => C_FAMILY)
        port map (  ICAP_Clk                 => ICAP_Clk_int,
                    Eos_in                   => eos_in,
                    Bus2IP_Clk               => bus2ip_clk,
                    Bus2IP_Reset             => bus2ip_reset,
                    Bus2IP_Addr              => bus2ip_addr,
                    Bus2IP_BE                => bus2ip_be,
                    Bus2IP_Data              => bus2ip_data,
                    Bus2IP_RNW               => bus2ip_rnw,
                    Bus2IP_cs                => bus2ip_cs(1),
                    Bus2IP_RdCe              => bus2ip_rdce_int (16 to 23),
                    Bus2IP_WrCe              => bus2ip_wrce_int (16 to 23),
                    IP2Bus_Data              => ip2bus_data,
                    IP2Bus_errAck            => ip2bus_err,
                    IP2Bus_RdAck             => ip2bus_rdack,
                    IP2Bus_WrAck             => ip2bus_wrack,
                    IP2Bus_AddrAck           => ip2bus_addrack,
                    Intr_rst                 => intr_rst,
                    IP2Bus_Intr              => ip2bus_intr,
                    CFGCLK    => cfgclk,
                    CFGMCLK    => cfgmclk,
                    PREQ    => preq,
                    CLK    => clk,
                    GSR    => gsr,
                    GTS    => gts,
                    KEYCLEARB    => keyclearb,
                    PACK    => pack,
                    USRCCLKO    => usrcclko,
                    USRCCLKTS    => usrcclkts,
                    USRDONEO    => usrdoneo,
                    USRDONETS    => usrdonets,
                    icap_req    => cap_req,
                    icap_rel  => cap_rel,
                    icap_gnt  => cap_gnt,
                    icap_i  => icap_i,
                    icap_o => icap_o,
                    icap_csib => icap_csib,
                    icap_rdwrb => icap_rdwrb,
                    icap_avail => icap_avail
                    );
    end generate ICAP_SHARED;



bus2ip_reset <= not bus2ip_resetn;    
  -----------------------------------------------------------------------------
   -- Interrupts
   -- ALS - added interrupts from Read and Write FIFOs
   -- ALS - added code to allow C_INCLUDE_DEV_ISC and C_INCLUDE_DEV_PENCODER to
   --       come from dependent props array
   ----------------------------------------------------------------------------
  INTERRUPT_CONTROL_I : entity interrupt_control_v3_1_4.interrupt_control
        generic map(C_NUM_CE                 => 16,
                    C_NUM_IPIF_IRPT_SRC      => NUM_IPIF_IRPT_SRC,
                    C_IP_INTR_MODE_ARRAY     => IP_INTR_MODE_ARRAY,
                    C_INCLUDE_DEV_PENCODER   => false,
                    C_INCLUDE_DEV_ISC        => false,
                    C_IPIF_DWIDTH            => C_S_AXI_DATA_WIDTH)
        port map   (Bus2IP_Clk               => bus2ip_clk,
                    Bus2IP_Reset             => intr_rst,
                    Bus2IP_Data              => bus2ip_data,
                    Bus2IP_BE                => bus2ip_be,
                    Interrupt_RdCE           => bus2ip_rdce_int(0 to 15),
                    Interrupt_WrCE           => bus2ip_wrce_int(0 to 15),
                    IPIF_Reg_Interrupts      => errack_reserved,
                    IPIF_Lvl_Interrupts      => ipif_lvl_interrupts,
                    IP2Bus_IntrEvent         => ip2bus_intr,
                    Intr2Bus_DevIntr         => ip2intc_irpt,
                    Intr2Bus_DBus            => intr2bus_data,
                    Intr2Bus_WrAck           => intr2bus_wrack,
                    Intr2Bus_RdAck           => intr2bus_rdack,
                    Intr2Bus_Error           => intr2bus_error,
                    Intr2Bus_Retry           => open,
                    Intr2Bus_ToutSup         => open
                    );

wr_or <= or_reduce(bus2ip_wrce_int(0 to 23));
rd_or <= or_reduce(bus2ip_rdce_int(0 to 23));

process (bus2ip_clk)
begin
    if (bus2ip_clk'event and bus2ip_clk = '1') then
       if (bus2ip_reset = '1') then
          ip2bus_wrack_i <= '0';
       elsif (wr_or = '1') then
           ip2bus_wrack_i <= ip2bus_wrack or intr2bus_wrack;
       else
          ip2bus_wrack_i <= '0';
       end if;    
    end if;
end process; 


process (bus2ip_clk)
begin
    if (bus2ip_clk'event and bus2ip_clk = '1') then
       if (bus2ip_reset = '1') then
          ip2bus_rdack_i <= '0';
          ip2bus_data_i <= (others => '0');
       elsif (rd_or = '1') then
          ip2bus_rdack_i <= intr2bus_rdack or ip2bus_rdack;
          ip2bus_data_i  <= intr2bus_data or ip2bus_data;
       else
          ip2bus_rdack_i <= '0';
          ip2bus_data_i <= (others => '0');
       end if;
    end if;
end process; 



process (bus2ip_clk)
begin
    if (bus2ip_clk'event and bus2ip_clk = '1') then
       if (bus2ip_reset = '1') then
          ip2bus_error_i <= '0';
       elsif (rd_or = '1' or wr_or = '1') then
          ip2bus_error_i <= intr2bus_error or ip2bus_err;
       else 
          ip2bus_error_i <= '0';
       end if;
    end if;
end process; 


SYNC_MODE : if (C_ENABLE_ASYNC = 0) generate
begin
   ICAP_Clk_int <= s_axi_aclk; 

end generate SYNC_MODE;


ASYNC_MODE : if (C_ENABLE_ASYNC = 1) generate
begin

   ICAP_Clk_int <= icap_clk; 

end generate ASYNC_MODE;

--ip2bus_wrack_i <= ip2bus_wrack or intr2bus_wrack 
--                  when or_reduce(bus2ip_wrce_int(0 to 23)) = '1' else
 --                 '0';
--ip2bus_rdack_i <= intr2bus_rdack or ip2bus_rdack
 --                 when or_reduce(bus2ip_rdce_int(0 to 23)) = '1' else
 --                 '0';
--ip2bus_data_i  <= intr2bus_data or ip2bus_data
 --                 when or_reduce(bus2ip_rdce_int(0 to 23))= '1' else
  --                (others => '0');
--ip2bus_error_i <= intr2bus_error or ip2bus_err
 --                 when (or_reduce(bus2ip_rdce_int(0 to 23)) or 
  --                or_reduce(bus2ip_wrce_int(0 to 23))) = '1' else
    --              '0';
end implementation;


