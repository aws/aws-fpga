-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-- upcnt_n - entity/architecture pair
-------------------------------------------------------------------------------
--
-- ************************************************************************
-- ** DISCLAIMER OF LIABILITY                                            **
-- **                                                                    **
-- ** This file contains proprietary and confidential information of     **
-- ** Xilinx, Inc. ("Xilinx"), that is distributed under a license       **
-- ** from Xilinx, and may be used, copied and/or disclosed only         **
-- ** pursuant to the terms of a valid license agreement with Xilinx.    **
-- **                                                                    **
-- ** XILINX IS PROVIDING THIS DESIGN, CODE, OR INFORMATION              **
-- ** ("MATERIALS") "AS IS" WITHOUT WARRANTY OF ANY KIND, EITHER         **
-- ** EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING WITHOUT                **
-- ** LIMITATION, ANY WARRANTY WITH RESPECT TO NONINFRINGEMENT,          **
-- ** MERCHANTABILITY OR FITNESS FOR ANY PARTICULAR PURPOSE. Xilinx      **
-- ** does not warrant that functions included in the Materials will     **
-- ** meet the requirements of Licensee, or that the operation of the    **
-- ** Materials will be uninterrupted or error-free, or that defects     **
-- ** in the Materials will be corrected. Furthermore, Xilinx does       **
-- ** not warrant or make any representations regarding use, or the      **
-- ** results of the use, of the Materials in terms of correctness,      **
-- ** accuracy, reliability or otherwise.                                **
-- **                                                                    **
-- ** Xilinx products are not designed or intended to be fail-safe,      **
-- ** or for use in any application requiring fail-safe performance,     **
-- ** such as life-support or safety devices or systems, Class III       **
-- ** medical devices, nuclear facilities, applications related to       **
-- ** the deployment of airbags, or any other applications that could    **
-- ** lead to death, personal injury or severe property or               **
-- ** environmental damage (individually and collectively, "critical     **
-- ** applications"). Customer assumes the sole risk and liability       **
-- ** of any use of Xilinx products in critical applications,            **
-- ** subject only to applicable laws and regulations governing          **
-- ** limitations on product liability.                                  **
-- **                                                                    **
-- ** Copyright 2010 Xilinx, Inc.                                        **
-- ** All rights reserved.                                               **
-- **                                                                    **
-- ** This disclaimer and copyright notice must be retained as part      **
-- ** of this file at all times.                                         **
-- ************************************************************************
--
-------------------------------------------------------------------------------
-- Filename:        upcnt_n.vhd
-- Version:         v4.00a
-- Description:     Parameterizeable top level processor reset module.
-- VHDL-Standard:   VHDL'93
-------------------------------------------------------------------------------
-- Structure:   This section should show the hierarchical structure of the
--              designs.Separate lines with blank lines if necessary to improve
--              readability.
--
--              proc_sys_reset.vhd
--                  upcnt_n.vhd
--                  lpf.vhd
--                  sequence.vhd
-------------------------------------------------------------------------------
-- Author:      Kurt Conover
-- History:
--  Kurt Conover      11/07/01      -- First Release
--
-- ~~~~~~~
--  SK          03/11/10
-- ^^^^^^^
-- 1. Updated the core so support the active low "Interconnect_aresetn" and
--    "Peripheral_aresetn" signals.
-- ^^^^^^^
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
use IEEE.std_logic_arith.all;
-------------------------------------------------------------------------------
-- Port Declaration
-------------------------------------------------------------------------------
-- Definition of Generics:
--          C_SIZE    -- Number of bits in counter
--                          
--
-- Definition of Ports:
--          Data       -- parallel data input
--          Cnt_en     -- count enable
--          Load       -- Load Data
--          Clr        -- reset
--          Clk        -- Clock
--          Qout       -- Count output
--
-------------------------------------------------------------------------------
entity upcnt_n is
   generic(
           C_SIZE : Integer
          );
      
	port(
	     Data    : in  STD_LOGIC_VECTOR (C_SIZE-1 downto 0); 
	     Cnt_en  : in  STD_LOGIC;                            
	     Load    : in  STD_LOGIC;                            
 	     Clr     : in  STD_LOGIC;                            
	     Clk     : in  STD_LOGIC;                            
	     Qout    : out STD_LOGIC_VECTOR (C_SIZE-1 downto 0)
	    );
		
end upcnt_n;

architecture imp of upcnt_n is

constant CLEAR : std_logic := '0';

signal q_int : UNSIGNED (C_SIZE-1 downto 0) := (others => '1');

begin
   process(Clk)
   begin
	       
      if (Clk'event) and Clk = '1' then
          -- Clear output register
         if (Clr = CLEAR) then
            q_int <= (others => '0');
	       -- Load in start value
         elsif (Load = '1') then
            q_int <= UNSIGNED(Data);
	       -- If count enable is high
         elsif Cnt_en = '1' then
		      q_int <= q_int + 1;
         end if;
      end if;
   end process;

   Qout <= STD_LOGIC_VECTOR(q_int);

end imp;
  



-------------------------------------------------------------------------------
-- sequence - entity/architecture pair
-------------------------------------------------------------------------------
--
-- ************************************************************************
-- ** DISCLAIMER OF LIABILITY                                            **
-- **                                                                    **
-- ** This file contains proprietary and confidential information of     **
-- ** Xilinx, Inc. ("Xilinx"), that is distributed under a license       **
-- ** from Xilinx, and may be used, copied and/or disclosed only         **
-- ** pursuant to the terms of a valid license agreement with Xilinx.    **
-- **                                                                    **
-- ** XILINX IS PROVIDING THIS DESIGN, CODE, OR INFORMATION              **
-- ** ("MATERIALS") "AS IS" WITHOUT WARRANTY OF ANY KIND, EITHER         **
-- ** EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING WITHOUT                **
-- ** LIMITATION, ANY WARRANTY WITH RESPECT TO NONINFRINGEMENT,          **
-- ** MERCHANTABILITY OR FITNESS FOR ANY PARTICULAR PURPOSE. Xilinx      **
-- ** does not warrant that functions included in the Materials will     **
-- ** meet the requirements of Licensee, or that the operation of the    **
-- ** Materials will be uninterrupted or error-free, or that defects     **
-- ** in the Materials will be corrected. Furthermore, Xilinx does       **
-- ** not warrant or make any representations regarding use, or the      **
-- ** results of the use, of the Materials in terms of correctness,      **
-- ** accuracy, reliability or otherwise.                                **
-- **                                                                    **
-- ** Xilinx products are not designed or intended to be fail-safe,      **
-- ** or for use in any application requiring fail-safe performance,     **
-- ** such as life-support or safety devices or systems, Class III       **
-- ** medical devices, nuclear facilities, applications related to       **
-- ** the deployment of airbags, or any other applications that could    **
-- ** lead to death, personal injury or severe property or               **
-- ** environmental damage (individually and collectively, "critical     **
-- ** applications"). Customer assumes the sole risk and liability       **
-- ** of any use of Xilinx products in critical applications,            **
-- ** subject only to applicable laws and regulations governing          **
-- ** limitations on product liability.                                  **
-- **                                                                    **
-- ** Copyright 2012 Xilinx, Inc.                                        **
-- ** All rights reserved.                                               **
-- **                                                                    **
-- ** This disclaimer and copyright notice must be retained as part      **
-- ** of this file at all times.                                         **
-- ************************************************************************
--
-------------------------------------------------------------------------------
-- Filename:        proc_sys_reset.vhd
-- Version:         v4.00a
-- Description:     Parameterizeable top level processor reset module.
-- VHDL-Standard:   VHDL'93
-------------------------------------------------------------------------------
-- Structure:   This section should show the hierarchical structure of the
--              designs.Separate lines with blank lines if necessary to improve
--              readability.
--              -- proc_sys_reset.vhd
--                 -- upcnt_n.vhd
--                 -- lpf.vhd
--                 -- sequence.vhd
-------------------------------------------------------------------------------
-- Filename:        sequence.vhd
--
-- Description:
--                  This file control the sequencing coming out of a reset.
--                  The sequencing is as follows:
--                  Bus_Struct_Reset comes out of reset first.  Either when the
--                     external or auxiliary reset goes inactive or 16 clocks
--                     after a PPC Chip_Reset_Request, or 30 clocks after a PPC
--                     System_Reset_Request.
--                  Peripheral_Reset comes out of reset 16 clocks after
--                     Bus_Struct_Reset.
--                  The PPC resetcore, comes out of reset
--                     16 clocks after Peripheral_Reset.
--                  The PPC resetchip and resetsystem come out of reset
--                     at the same time as Bus_Struct_Reset.
-------------------------------------------------------------------------------
-- Author:      Kurt Conover
-- History:
--  Kurt Conover      11/12/01      -- First Release
--  LC Whittle	     10/11/2004	-- Update for NCSim
--  rolandp          04/16/2007         -- v2.00a
--
-- ~~~~~~~
--  SK          03/11/10
-- ^^^^^^^
-- 1. Updated the core so support the active low "Interconnect_aresetn" and
--    "Peripheral_aresetn" signals.
-- ^^^^^^^
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
use IEEE.std_logic_arith.all;
library unisim;
use unisim.vcomponents.all;
library proc_sys_reset_v5_0_10;

-------------------------------------------------------------------------------
-- Port Declaration
-------------------------------------------------------------------------------
-- Definition of Generics:
--
-- Definition of Ports:
--          Lpf_reset            -- Low Pass Filtered in
--          System_Reset_Req     -- System Reset Request
--          Chip_Reset_Req       -- Chip Reset Request
--          Slowest_Sync_Clk     -- Clock
--          Bsr_out              -- Bus Structure Reset out
--          Pr_out               -- Peripheral Reset out
--          Core_out             -- Core reset out
--          Chip_out             -- Chip reset out
--          Sys_out              -- System reset out
--          MB_out               -- MB reset out
--
-------------------------------------------------------------------------------
entity sequence_psr is
  port(
    Lpf_reset         : in  std_logic;
    -- System_Reset_Req  : in  std_logic;
    -- Chip_Reset_Req    : in  std_logic;
    Slowest_Sync_Clk  : in  std_logic;
    Bsr_out           : out std_logic;
    Pr_out            : out std_logic;
    -- Core_out          : out std_logic;
    -- Chip_out          : out std_logic;
    -- Sys_out           : out std_logic;
    MB_out            : out std_logic
  );
end sequence_psr;

architecture imp of sequence_psr is

constant CLEAR             : std_logic := '0';
constant BSR_END_LPF_CHIP  : std_logic_vector(5 downto 0) := "001100";  -- 12
constant BSR_END_SYS       : std_logic_vector(5 downto 0) := "011001";  -- 25
constant PR_END_LPF_CHIP   : std_logic_vector(5 downto 0) := "011100";  -- 28
constant PR_END_SYS        : std_logic_vector(5 downto 0) := "101001";  -- 41
constant CORE_END_LPF_CHIP : std_logic_vector(5 downto 0) := "101100";  -- 44
constant CORE_END_SYS      : std_logic_vector(5 downto 0) := "111001";  -- 57
constant CHIP_END_LPF_CHIP : std_logic_vector(5 downto 0) := BSR_END_LPF_CHIP;
constant CHIP_END_SYS      : std_logic_vector(5 downto 0) := BSR_END_SYS;
constant SYS_END_LPF       : std_logic_vector(5 downto 0) := BSR_END_LPF_CHIP;
constant SYS_END_SYS       : std_logic_vector(5 downto 0) := BSR_END_SYS;

signal bsr                 : std_logic := '0';
signal bsr_dec             : std_logic_vector(2 downto 0) := (others => '0');
signal pr                  : std_logic := '0';
signal pr_dec              : std_logic_vector(2 downto 0) := (others => '0');
signal Core                : std_logic := '0';
signal core_dec            : std_logic_vector(2 downto 0) := (others => '0');
signal Chip                : std_logic := '0';
signal chip_dec            : std_logic_vector(2 downto 0) := (others => '0');
signal Sys                 : std_logic := '0';
signal sys_dec             : std_logic_vector(2 downto 0) := (others => '0');
signal chip_Reset_Req_d1   : std_logic := '0';  -- delayed Chip_Reset_Req
signal chip_Reset_Req_d2   : std_logic := '0';  -- delayed Chip_Reset_Req
signal chip_Reset_Req_d3   : std_logic := '0';  -- delayed Chip_Reset_Req
signal system_Reset_Req_d1 : std_logic := '0';  -- delayed System_Reset_Req
signal system_Reset_Req_d2 : std_logic := '0';  -- delayed System_Reset_Req
signal system_Reset_Req_d3 : std_logic := '0';  -- delayed System_Reset_Req
signal seq_cnt             : std_logic_vector(5 downto 0);
signal seq_cnt_en          : std_logic := '0';
signal seq_clr             : std_logic := '0';

signal ris_edge            : std_logic := '0';
signal sys_edge            : std_logic := '0';
signal from_sys            : std_logic;

-------------------------------------------------------------------------------
-- Component Declarations
-------------------------------------------------------------------------------

begin

   Pr_out   <= pr;
   Bsr_out  <= bsr;
   MB_out   <= core;
   -- Core_out <= core;
   -- Chip_out <= chip or sys;
   -- Sys_out  <= sys;
   
-------------------------------------------------------------------------------
-- This process remembers that the reset was caused be 
-- System_Reset_Req
-------------------------------------------------------------------------------
  SYS_FROM_PROCESS: process (Slowest_sync_clk)
  begin
    if (Slowest_sync_clk'event and Slowest_sync_clk = '1') then
      --if Lpf_reset='1' or system_reset_req_d3='1' then
      if (Lpf_reset = '1') then
        from_sys <= '1';
      --elsif Chip_Reset_Req_d3='1' then
      --  from_sys <= '0';
      elsif (Core = '0') then
        from_sys <='0';
      end if;
    end if;
  end process;

-------------------------------------------------------------------------------
-- This instantiates a counter to control the sequencing
-------------------------------------------------------------------------------
   SEQ_COUNTER : entity proc_sys_reset_v5_0_10.UPCNT_N
   generic map (C_SIZE => 6)
   port map(
     Data     => "000000",
     Cnt_en   => seq_cnt_en,
     Load     => '0',
     Clr      => seq_clr,
     Clk      => Slowest_sync_clk,
     Qout     => seq_cnt
   );

-------------------------------------------------------------------------------
-- SEQ_CNT_EN_PROCESS
-------------------------------------------------------------------------------
--  This generates the reset pulse and the count enable to core reset counter
--  count until all outputs are inactive
-------------------------------------------------------------------------------
  SEQ_CNT_EN_PROCESS: process (Slowest_sync_clk)
  begin
    if (Slowest_sync_clk'event and Slowest_sync_clk = '1') then
      if (Lpf_reset='1'           --or 
          --System_Reset_Req_d3='1' or
          --Chip_Reset_Req_d3='1'   or 
	  --ris_edge = '1'
	  ) then
        seq_cnt_en <= '1';
      elsif  (Core='0') then              -- Core always present and always last 
        seq_cnt_en <= '0';
      end if;
    end if;
  end process;

-------------------------------------------------------------------------------
-- SEQ_CLR_PROCESS
-------------------------------------------------------------------------------
--  This generates the reset to the sequence counter
--  Clear the counter on a rising edge of chip or system request or low pass
--  filter output
-------------------------------------------------------------------------------
  SEQ_CLR_PROCESS: process (Slowest_sync_clk)
  begin
    if (Slowest_sync_clk'event and Slowest_sync_clk = '1') then
      -- if  ris_edge = '1' or Lpf_reset = '1' then
      if (Lpf_reset = '1') then
        seq_clr <= '0';
      else
        seq_clr <= '1';
      end if;
    end if;
  end process;

-------------------------------------------------------------------------------
-- This process defines the Peripheral_Reset output signal
-------------------------------------------------------------------------------
  PR_PROCESS: process (Slowest_sync_clk)
  begin
    if (Slowest_sync_clk'event and Slowest_sync_clk = '1') then
      --if  ris_edge = '1' or Lpf_reset = '1' then
      if (Lpf_reset = '1') then
        pr <= '1';
      elsif (pr_dec(2) = '1') then
        pr <= '0';
      end if;
    end if;
  end process;

-------------------------------------------------------------------------------
-- This process decodes the sequence counter for PR to use
-------------------------------------------------------------------------------
  PR_DECODE_PROCESS: process (Slowest_sync_clk)
  begin
    if (Slowest_sync_clk'event and Slowest_sync_clk = '1') then
      if (
          (seq_cnt(5 downto 3) = PR_END_LPF_CHIP(5 downto 3) and from_sys = '0')  
	  or
          (seq_cnt(5 downto 3) = PR_END_SYS(5 downto 3)  and from_sys = '1')
	  ) then
         pr_dec(0) <= '1';
      else
         pr_dec(0) <= '0';
      end if;
      if (
          (seq_cnt(2 downto 0) = PR_END_LPF_CHIP(2 downto 0) and from_sys = '0') 
          or
          (seq_cnt(2 downto 0) = PR_END_SYS(2 downto 0) and from_sys = '1')
	  )then
         pr_dec(1) <= '1';
      else
         pr_dec(1) <= '0';
      end if;
      pr_dec(2) <= pr_dec(1) and pr_dec(0);
    end if;
  end process;

-------------------------------------------------------------------------------
-- This process defines the Bus_Struct_Reset output signal
-------------------------------------------------------------------------------
  BSR_PROCESS: process (Slowest_sync_clk)
  begin
    if (Slowest_sync_clk'event and Slowest_sync_clk = '1') then
      --if ris_edge = '1' or Lpf_reset = '1' then
      if (Lpf_reset = '1') then
        bsr <= '1';
      elsif (bsr_dec(2) = '1') then
        bsr <= '0';
      end if;
    end if;
  end process;

-------------------------------------------------------------------------------
-- This process decodes the sequence counter for BSR to use
-------------------------------------------------------------------------------
  BSR_DECODE_PROCESS: process (Slowest_sync_clk)
  begin
    if (Slowest_sync_clk'event and Slowest_sync_clk = '1') then
      if (
          (seq_cnt(5 downto 3) = BSR_END_LPF_CHIP(5 downto 3) and from_sys = '0')  
	  or
          (seq_cnt(5 downto 3) = BSR_END_SYS(5 downto 3) and from_sys = '1')
	 )then
         bsr_dec(0) <= '1';
      else
         bsr_dec(0) <= '0';
      end if;
      if (
          (seq_cnt(2 downto 0) = BSR_END_LPF_CHIP(2 downto 0) and from_sys = '0') 
	  or
          (seq_cnt(2 downto 0) = BSR_END_SYS(2 downto 0) and from_sys = '1')
	  )then
         bsr_dec(1) <= '1';
      else
         bsr_dec(1) <= '0';
      end if;
      bsr_dec(2) <= bsr_dec(1) and bsr_dec(0);
    end if;
  end process;


-------------------------------------------------------------------------------
-- This process defines the Peripheral_Reset output signal
-------------------------------------------------------------------------------
  CORE_PROCESS: process (Slowest_sync_clk)
  begin
    if (Slowest_sync_clk'event and Slowest_sync_clk = '1') then
      -- if  ris_edge = '1' or Lpf_reset = '1' then
      if (Lpf_reset = '1') then
        core <= '1';
      elsif (core_dec(2) = '1') then
        core <= '0';
      end if;
    end if;
  end process;

-------------------------------------------------------------------------------
-- This process decodes the sequence counter for PR to use
-------------------------------------------------------------------------------
  CORE_DECODE_PROCESS: process (Slowest_sync_clk)
  begin
    if (Slowest_sync_clk'event and Slowest_sync_clk = '1') then
      if (
          (seq_cnt(5 downto 3) = CORE_END_LPF_CHIP(5 downto 3) and from_sys = '0')  
	  or
          (seq_cnt(5 downto 3) = CORE_END_SYS(5 downto 3) and from_sys = '1')
	  )then
         core_dec(0) <= '1';
      else
         core_dec(0) <= '0';
      end if;
      if (
          (seq_cnt(2 downto 0) = CORE_END_LPF_CHIP(2 downto 0) and from_sys = '0') 
	  or
          (seq_cnt(2 downto 0) = CORE_END_SYS(2 downto 0) and from_sys = '1')
	  )then
         core_dec(1) <= '1';
      else
         core_dec(1) <= '0';
      end if;
      core_dec(2) <= core_dec(1) and core_dec(0);
    end if;
  end process;

---------------------------------------------------------------------------------
---- This process defines the Chip output signal
---------------------------------------------------------------------------------
--  CHIP_PROCESS: process (Slowest_sync_clk)
--  begin
--    if (Slowest_sync_clk'event and Slowest_sync_clk = '1') then
--      -- if ris_edge = '1' or Lpf_reset = '1' then
--      if Lpf_reset = '1' then
--        chip <= '1';
--      elsif chip_dec(2) = '1' then
--        chip <= '0';
--      end if;
--    end if;
--  end process;
--
---------------------------------------------------------------------------------
---- This process decodes the sequence counter for Chip to use
---- sys is overlapping the chip reset and thus no need to decode this here
---------------------------------------------------------------------------------
--  CHIP_DECODE_PROCESS: process (Slowest_sync_clk)
--  begin
--    if (Slowest_sync_clk'event and Slowest_sync_clk = '1') then
--      if (seq_cnt(5 downto 2) = CHIP_END_LPF_CHIP(5 downto 2))  then
--         chip_dec(0) <= '1';
--      else
--         chip_dec(0) <= '0';
--      end if;
--      if (seq_cnt(1 downto 0) = CHIP_END_LPF_CHIP(1 downto 0)) then
--         chip_dec(1) <= '1';
--      else
--         chip_dec(1) <= '0';
--      end if;
--      chip_dec(2) <= chip_dec(1) and chip_dec(0);
--    end if;
--  end process;
  
---------------------------------------------------------------------------------
---- This process defines the Sys output signal
---------------------------------------------------------------------------------
--  SYS_PROCESS: process (Slowest_sync_clk)
--  begin
--    if (Slowest_sync_clk'event and Slowest_sync_clk = '1') then
--      if sys_edge = '1' or Lpf_reset = '1' then
--        sys <= '1';
--      elsif sys_dec(2) = '1' then
--        sys <= '0';
--      end if;
--    end if;
--  end process;
--  
---------------------------------------------------------------------------------
---- This process decodes the sequence counter for Sys to use
---------------------------------------------------------------------------------
--  SYS_DECODE_PROCESS: process (Slowest_sync_clk)
--  begin
--    if (Slowest_sync_clk'event and Slowest_sync_clk = '1') then
--      if (seq_cnt(5 downto 3) = SYS_END_LPF(5 downto 3) and from_sys = '0') or
--         (seq_cnt(5 downto 3) = SYS_END_SYS(5 downto 3) and from_sys = '1')  then
--        sys_dec(0) <= '1';
--      else
--        sys_dec(0) <= '0';
--      end if;
--      if (seq_cnt(2 downto 0) = SYS_END_LPF(2 downto 0) and from_sys = '0') or
--         (seq_cnt(2 downto 0) = SYS_END_SYS(2 downto 0) and from_sys = '1')  then
--        sys_dec(1) <= '1';
--      else
--        sys_dec(1) <= '0';
--      end if;
--      sys_dec(2) <= sys_dec(1) and sys_dec(0);
--    end if;
--  end process;
--
---------------------------------------------------------------------------------
---- This process delays signals so the the edge can be detected and used
---------------------------------------------------------------------------------
--  DELAY_PROCESS: process (Slowest_sync_clk)
--  begin
--    if (Slowest_sync_clk'event and Slowest_sync_clk = '1') then
--      chip_reset_req_d1   <= Chip_Reset_Req  ;
--      chip_reset_req_d2   <= chip_Reset_Req_d1  ;
--      chip_reset_req_d3   <= chip_Reset_Req_d2  ;
--      system_reset_req_d1 <= System_Reset_Req;
--      system_reset_req_d2 <= system_Reset_Req_d1;
--      system_reset_req_d3 <= system_Reset_Req_d2;
--    end if;
--  end process;

-------------------------------------------------------------------------------
-- This process creates a signal that goes high on the rising edge of either
-- Chip_Reset_Req or System_Reset_Req
-------------------------------------------------------------------------------
--  RIS_EDGE_PROCESS: process (Slowest_sync_clk)
--  begin
--    if (Slowest_sync_clk'event and Slowest_sync_clk = '1') then
--      if (chip_reset_req_d3='0'   and chip_Reset_Req_d2= '1') -- rising edge
--         or (system_reset_req_d3='0' and system_Reset_Req_d2='1') then
--        ris_edge <= '1';
--      else
--        ris_edge <='0';
--      end if;
--    end if;
--  end process;

-------------------------------------------------------------------------------
-- This process creates a signal that goes high on the rising edge of
-- System_Reset_Req
-------------------------------------------------------------------------------
--  SYS_EDGE_PROCESS: process (Slowest_sync_clk)
--  begin
--    if (Slowest_sync_clk'event and Slowest_sync_clk = '1') then
--      if (system_reset_req_d3='0' and system_reset_req_d2='1') then
--         sys_edge <= '1';
--      else
--         sys_edge <='0';
--      end if;
--    end if;
--  end process;



end architecture imp;




-------------------------------------------------------------------------------
-- lpf - entity/architecture pair
-------------------------------------------------------------------------------
--
-- ************************************************************************
-- ** DISCLAIMER OF LIABILITY                                            **
-- **                                                                    **
-- ** This file contains proprietary and confidential information of     **
-- ** Xilinx, Inc. ("Xilinx"), that is distributed under a license       **
-- ** from Xilinx, and may be used, copied and/or disclosed only         **
-- ** pursuant to the terms of a valid license agreement with Xilinx.    **
-- **                                                                    **
-- ** XILINX IS PROVIDING THIS DESIGN, CODE, OR INFORMATION              **
-- ** ("MATERIALS") "AS IS" WITHOUT WARRANTY OF ANY KIND, EITHER         **
-- ** EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING WITHOUT                **
-- ** LIMITATION, ANY WARRANTY WITH RESPECT TO NONINFRINGEMENT,          **
-- ** MERCHANTABILITY OR FITNESS FOR ANY PARTICULAR PURPOSE. Xilinx      **
-- ** does not warrant that functions included in the Materials will     **
-- ** meet the requirements of Licensee, or that the operation of the    **
-- ** Materials will be uninterrupted or error-free, or that defects     **
-- ** in the Materials will be corrected. Furthermore, Xilinx does       **
-- ** not warrant or make any representations regarding use, or the      **
-- ** results of the use, of the Materials in terms of correctness,      **
-- ** accuracy, reliability or otherwise.                                **
-- **                                                                    **
-- ** Xilinx products are not designed or intended to be fail-safe,      **
-- ** or for use in any application requiring fail-safe performance,     **
-- ** such as life-support or safety devices or systems, Class III       **
-- ** medical devices, nuclear facilities, applications related to       **
-- ** the deployment of airbags, or any other applications that could    **
-- ** lead to death, personal injury or severe property or               **
-- ** environmental damage (individually and collectively, "critical     **
-- ** applications"). Customer assumes the sole risk and liability       **
-- ** of any use of Xilinx products in critical applications,            **
-- ** subject only to applicable laws and regulations governing          **
-- ** limitations on product liability.                                  **
-- **                                                                    **
-- ** Copyright 2012 Xilinx, Inc.                                        **
-- ** All rights reserved.                                               **
-- **                                                                    **
-- ** This disclaimer and copyright notice must be retained as part      **
-- ** of this file at all times.                                         **
-- ************************************************************************
--
-------------------------------------------------------------------------------
-- Filename:        lpf.vhd
-- Version:         v4.00a
-- Description:     Parameterizeable top level processor reset module.
-- VHDL-Standard:   VHDL'93
-------------------------------------------------------------------------------
-- Structure:   This section should show the hierarchical structure of the
--              designs.Separate lines with blank lines if necessary to improve
--              readability.
--
--              proc_sys_reset.vhd
--                  upcnt_n.vhd
--                  lpf.vhd
--                  sequence.vhd
-------------------------------------------------------------------------------
-- Author:      Kurt Conover
-- History:
--  Kurt Conover      11/08/01      -- First Release
--
--  KC                02/25/2002    -- Added Dcm_locked as an input
--                                  -- Added Power on reset srl_time_out
--
--  KC                08/26/2003    -- Added attribute statements for power on 
--                                     reset SRL
--
-- ~~~~~~~
--  SK          03/11/10
-- ^^^^^^^
-- 1. Updated the core so support the active low "Interconnect_aresetn" and
--    "Peripheral_aresetn" signals.
-- ^^^^^^^
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
    use IEEE.std_logic_arith.all;
library lib_cdc_v1_0_2;
--use lib_cdc_v1_0_2.all;
library Unisim; 
    use Unisim.all; 
-------------------------------------------------------------------------------
-- Port Declaration
-------------------------------------------------------------------------------
-- Definition of Generics:
--          C_EXT_RST_WIDTH       -- External Reset Low Pass Filter setting
--          C_AUX_RST_WIDTH       -- Auxiliary Reset Low Pass Filter setting   
--          C_EXT_RESET_HIGH      -- External Reset Active High or Active Low
--          C_AUX_RESET_HIGH      -= Auxiliary Reset Active High or Active Low
--
-- Definition of Ports:
--          Slowest_sync_clk       -- Clock 
--          External_System_Reset  -- External Reset Input
--          Auxiliary_System_Reset -- Auxiliary Reset Input
--          Dcm_locked             -- DCM Locked, hold system in reset until 1
--          Lpf_reset              -- Low Pass Filtered Output
--
-------------------------------------------------------------------------------
entity lpf is
   generic(
           C_EXT_RST_WIDTH    : Integer;
           C_AUX_RST_WIDTH    : Integer;
           C_EXT_RESET_HIGH   : std_logic;
           C_AUX_RESET_HIGH   : std_logic 
          );
      
   port(
        MB_Debug_Sys_Rst         : in  std_logic;
        Dcm_locked               : in  std_logic;
        External_System_Reset    : in  std_logic; 
        Auxiliary_System_Reset   : in  std_logic;                         
        Slowest_Sync_Clk         : in  std_logic; 
        Lpf_reset                : out std_logic                          
       );
      
end lpf;

architecture imp of lpf is

component SRL16 is 
-- synthesis translate_off 
  generic ( 
        INIT : bit_vector ); 
-- synthesis translate_on 
  port (D    : in  std_logic; 
        CLK  : in  std_logic; 
        A0   : in  std_logic; 
        A1   : in  std_logic; 
        A2   : in  std_logic; 
        A3   : in  std_logic; 
        Q    : out std_logic); 
end component SRL16; 


constant CLEAR : std_logic := '0';

signal exr_d1        : std_logic := '0'; -- delayed External_System_Reset
signal exr_lpf       : std_logic_vector(0 to C_EXT_RST_WIDTH - 1)
                             := (others => '0'); -- LPF DFF
                             
signal asr_d1        : std_logic := '0'; -- delayed Auxiliary_System_Reset
signal asr_lpf       : std_logic_vector(0 to C_AUX_RST_WIDTH - 1)
                             := (others => '0'); -- LPF DFF
                             
signal exr_and       : std_logic := '0'; -- varible input width "and" gate
signal exr_nand      : std_logic := '0'; -- vaiable input width "and" gate
                     
signal asr_and       : std_logic := '0'; -- varible input width "and" gate
signal asr_nand      : std_logic := '0'; -- vaiable input width "and" gate
                     
signal lpf_int       : std_logic := '0'; -- internal Lpf_reset
signal lpf_exr       : std_logic := '0';
signal lpf_asr       : std_logic := '0';
                     
signal srl_time_out  : std_logic;

attribute INIT             : string;
attribute INIT of POR_SRL_I: label is "FFFF";


begin

   Lpf_reset <= lpf_int;
   
-------------------------------------------------------------------------------
-- Power On Reset Generation
-------------------------------------------------------------------------------
--  This generates a reset for the first 16 clocks after a power up
-------------------------------------------------------------------------------
  POR_SRL_I: SRL16 
-- synthesis translate_off 
    generic map ( 
      INIT => X"FFFF") 
-- synthesis translate_on 
    port map ( 
      D   => '0', 
      CLK => Slowest_sync_clk, 
      A0  => '1', 
      A1  => '1', 
      A2  => '1', 
      A3  => '1', 
      Q   => srl_time_out); 
   
-------------------------------------------------------------------------------
-- LPF_OUTPUT_PROCESS
-------------------------------------------------------------------------------
--  This generates the reset pulse and the count enable to core reset counter
--
--ACTIVE_HIGH_LPF_EXT: if  (C_EXT_RESET_HIGH = '1') generate  
--begin
LPF_OUTPUT_PROCESS: process (Slowest_sync_clk)
begin
    if (Slowest_sync_clk'event and Slowest_sync_clk = '1') then
       lpf_int <= lpf_exr or lpf_asr or srl_time_out or not Dcm_locked;
    end if;
end process LPF_OUTPUT_PROCESS;
--end generate ACTIVE_HIGH_LPF_EXT;

--ACTIVE_LOW_LPF_EXT: if  (C_EXT_RESET_HIGH = '0') generate  
--begin
--LPF_OUTPUT_PROCESS: process (Slowest_sync_clk)
--   begin
--      if (Slowest_sync_clk'event and Slowest_sync_clk = '1') then
--         lpf_int <= not (lpf_exr      or 
--	                 lpf_asr      or 
--			 srl_time_out)or 
--			 not Dcm_locked;
--      end if;
--   end process;
--end generate ACTIVE_LOW_LPF_EXT;

EXR_OUTPUT_PROCESS: process (Slowest_sync_clk)
begin
   if (Slowest_sync_clk'event and Slowest_sync_clk = '1') then
      if exr_and = '1' then
         lpf_exr <= '1';
      elsif (exr_and = '0' and exr_nand = '1') then
         lpf_exr <= '0';
      end if;
   end if;
end process EXR_OUTPUT_PROCESS;

ASR_OUTPUT_PROCESS: process (Slowest_sync_clk)
begin
   if (Slowest_sync_clk'event and Slowest_sync_clk = '1') then
      if asr_and = '1' then
         lpf_asr <= '1';
      elsif (asr_and = '0' and asr_nand = '1') then
         lpf_asr <= '0';
      end if;
   end if;
end process ASR_OUTPUT_PROCESS;
-------------------------------------------------------------------------------
-- This If-generate selects an active high input for External System Reset 
-------------------------------------------------------------------------------
ACTIVE_HIGH_EXT: if (C_EXT_RESET_HIGH /= '0') generate  
begin
   -----------------------------------
exr_d1 <= External_System_Reset or MB_Debug_Sys_Rst;

ACT_HI_EXT: entity lib_cdc_v1_0_2.cdc_sync
  generic map (
    C_CDC_TYPE           => 1,
    C_RESET_STATE        => 0,
    C_SINGLE_BIT         => 1,
    C_FLOP_INPUT         => 0,
    C_VECTOR_WIDTH       => 2,
    C_MTBF_STAGES        => 4
            )
  port map(
    prmry_aclk            => '1',
    prmry_resetn          => '1',--S_AXI_ARESETN,
    prmry_in              => exr_d1,
    prmry_ack             => open,
    scndry_out            => exr_lpf(0),
    scndry_aclk           => Slowest_Sync_Clk,
    scndry_resetn         => '1', --S_AXIS_ARESETN,
    prmry_vect_in         => "00",
    scndry_vect_out       => open
     );

-----------------------------------
end generate ACTIVE_HIGH_EXT;
-------------------------------------------------------------------------------
-- This If-generate selects an active low input for External System Reset 
-------------------------------------------------------------------------------
ACTIVE_LOW_EXT: if  (C_EXT_RESET_HIGH = '0') generate  
begin
exr_d1 <= not External_System_Reset or MB_Debug_Sys_Rst;
   -------------------------------------

ACT_LO_EXT: entity lib_cdc_v1_0_2.cdc_sync
  generic map (
    C_CDC_TYPE           => 1,
    C_RESET_STATE        => 0,
    C_SINGLE_BIT         => 1,
    C_FLOP_INPUT         => 0,
    C_VECTOR_WIDTH       => 2,
    C_MTBF_STAGES        => 4
            )
  port map(
    prmry_aclk            => '1',
    prmry_resetn          => '1',--S_AXI_ARESETN,
    prmry_in              => exr_d1,
    prmry_ack             => open,
    scndry_out            => exr_lpf(0),
    scndry_aclk           => Slowest_Sync_Clk,
    scndry_resetn         => '1', --S_AXIS_ARESETN,
    prmry_vect_in         => "00",
    scndry_vect_out       => open
     );
-------------------------------------
end generate ACTIVE_LOW_EXT;

-------------------------------------------------------------------------------
-- This If-generate selects an active high input for Auxiliary System Reset 
-------------------------------------------------------------------------------
ACTIVE_HIGH_AUX: if (C_AUX_RESET_HIGH /= '0') generate  
begin
asr_d1 <= Auxiliary_System_Reset;
-------------------------------------

ACT_HI_AUX: entity lib_cdc_v1_0_2.cdc_sync
  generic map (
    C_CDC_TYPE           => 1,
    C_RESET_STATE        => 0,
    C_SINGLE_BIT         => 1,
    C_FLOP_INPUT         => 0,
    C_VECTOR_WIDTH       => 2,
    C_MTBF_STAGES        => 4
            )
  port map(
    prmry_aclk            => '1',
    prmry_resetn          => '1',--S_AXI_ARESETN,
    prmry_in              => asr_d1,
    prmry_ack             => open,
    scndry_out            => asr_lpf(0),
    scndry_aclk           => Slowest_Sync_Clk,
    scndry_resetn         => '1', --S_AXIS_ARESETN,
    prmry_vect_in         => "00",
    scndry_vect_out       => open
     );
   -------------------------------------
end generate ACTIVE_HIGH_AUX;
-------------------------------------------------------------------------------
-- This If-generate selects an active low input for Auxiliary System Reset 
-------------------------------------------------------------------------------
ACTIVE_LOW_AUX: if (C_AUX_RESET_HIGH = '0') generate  
begin
   -------------------------------------
asr_d1 <= not Auxiliary_System_Reset;

ACT_LO_AUX: entity lib_cdc_v1_0_2.cdc_sync
  generic map (
    C_CDC_TYPE           => 1,
    C_RESET_STATE        => 0,
    C_SINGLE_BIT         => 1,
    C_FLOP_INPUT         => 0,
    C_VECTOR_WIDTH       => 2,
    C_MTBF_STAGES        => 4
            )
  port map(
    prmry_aclk            => '1',
    prmry_resetn          => '1',--S_AXI_ARESETN,
    prmry_in              => asr_d1,
    prmry_ack             => open,
    scndry_out            => asr_lpf(0),
    scndry_aclk           => Slowest_Sync_Clk,
    scndry_resetn         => '1', --S_AXIS_ARESETN,
    prmry_vect_in         => "00",
    scndry_vect_out       => open
     );
   -------------------------------------
end generate ACTIVE_LOW_AUX;

-------------------------------------------------------------------------------
-- This For-generate creates the low pass filter D-Flip Flops
-------------------------------------------------------------------------------
EXT_LPF: for i in 1 to C_EXT_RST_WIDTH - 1 generate
begin
   ----------------------------------------
   EXT_LPF_DFF : process (Slowest_Sync_Clk)
   begin
      if (Slowest_Sync_Clk'event) and Slowest_Sync_Clk = '1' then
         exr_lpf(i) <= exr_lpf(i-1);
      end if;
   end process;
   ----------------------------------------
end generate EXT_LPF;
------------------------------------------------------------------------------------------
-- Implement the 'AND' function on the for the LPF
------------------------------------------------------------------------------------------
EXT_LPF_AND : process (exr_lpf)
Variable loop_and  : std_logic;
Variable loop_nand : std_logic;
Begin
   loop_and  := '1';
   loop_nand := '1';
   for j in 0 to C_EXT_RST_WIDTH - 1 loop
      loop_and  := loop_and and      exr_lpf(j);
      loop_nand := loop_nand and not exr_lpf(j);
   End loop;
  
   exr_and  <= loop_and;
   exr_nand <= loop_nand;

end process; 

-------------------------------------------------------------------------------
-- This For-generate creates the low pass filter D-Flip Flops
-------------------------------------------------------------------------------
AUX_LPF: for k in 1 to C_AUX_RST_WIDTH - 1 generate
begin
   ----------------------------------------
   AUX_LPF_DFF : process (Slowest_Sync_Clk)
   begin
      if (Slowest_Sync_Clk'event) and Slowest_Sync_Clk = '1' then
         asr_lpf(k) <= asr_lpf(k-1);
      end if;
   end process;
   ----------------------------------------
end generate AUX_LPF;
------------------------------------------------------------------------------------------
-- Implement the 'AND' function on the for the LPF
------------------------------------------------------------------------------------------
AUX_LPF_AND : process (asr_lpf)
Variable aux_loop_and  : std_logic;
Variable aux_loop_nand : std_logic;
Begin
   aux_loop_and  := '1';
   aux_loop_nand := '1';
   for m in 0 to C_AUX_RST_WIDTH - 1 loop
      aux_loop_and  := aux_loop_and and      asr_lpf(m);
      aux_loop_nand := aux_loop_nand and not asr_lpf(m);
   End loop;
  
   asr_and  <= aux_loop_and;
   asr_nand <= aux_loop_nand;

end process; 

end imp;
  



-------------------------------------------------------------------------------
-- proc_sys_reset - entity/architecture pair
-------------------------------------------------------------------------------
--
-- ************************************************************************
-- ** DISCLAIMER OF LIABILITY                                            **
-- **                                                                    **
-- ** This file contains proprietary and confidential information of     **
-- ** Xilinx, Inc. ("Xilinx"), that is distributed under a license       **
-- ** from Xilinx, and may be used, copied and/or disclosed only         **
-- ** pursuant to the terms of a valid license agreement with Xilinx.    **
-- **                                                                    **
-- ** XILINX IS PROVIDING THIS DESIGN, CODE, OR INFORMATION              **
-- ** ("MATERIALS") "AS IS" WITHOUT WARRANTY OF ANY KIND, EITHER         **
-- ** EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING WITHOUT                **
-- ** LIMITATION, ANY WARRANTY WITH RESPECT TO NONINFRINGEMENT,          **
-- ** MERCHANTABILITY OR FITNESS FOR ANY PARTICULAR PURPOSE. Xilinx      **
-- ** does not warrant that functions included in the Materials will     **
-- ** meet the requirements of Licensee, or that the operation of the    **
-- ** Materials will be uninterrupted or error-free, or that defects     **
-- ** in the Materials will be corrected. Furthermore, Xilinx does       **
-- ** not warrant or make any representations regarding use, or the      **
-- ** results of the use, of the Materials in terms of correctness,      **
-- ** accuracy, reliability or otherwise.                                **
-- **                                                                    **
-- ** Xilinx products are not designed or intended to be fail-safe,      **
-- ** or for use in any application requiring fail-safe performance,     **
-- ** such as life-support or safety devices or systems, Class III       **
-- ** medical devices, nuclear facilities, applications related to       **
-- ** the deployment of airbags, or any other applications that could    **
-- ** lead to death, personal injury or severe property or               **
-- ** environmental damage (individually and collectively, "critical     **
-- ** applications"). Customer assumes the sole risk and liability       **
-- ** of any use of Xilinx products in critical applications,            **
-- ** subject only to applicable laws and regulations governing          **
-- ** limitations on product liability.                                  **
-- **                                                                    **
-- ** Copyright 2012 Xilinx, Inc.                                        **
-- ** All rights reserved.                                               **
-- **                                                                    **
-- ** This disclaimer and copyright notice must be retained as part      **
-- ** of this file at all times.                                         **
-- ************************************************************************
--
-------------------------------------------------------------------------------
-- Filename:        proc_sys_reset.vhd
-- Version:         v4.00a
-- Description:     Parameterizeable top level processor reset module.
-- VHDL-Standard:   VHDL'93
-------------------------------------------------------------------------------
-- Structure:   This section should show the hierarchical structure of the
--              designs.Separate lines with blank lines if necessary to improve
--              readability.
--
--              proc_sys_reset.vhd
--                  upcnt_n.vhd
--                  lpf.vhd
--                  sequence.vhd
-------------------------------------------------------------------------------
-- Author:      rolandp
-- History:
--  kc           11/07/01      -- First version
--
--  kc           02/25/2002    -- Changed generic names C_EXT_RST_ACTIVE to
--                                C_EXT_RESET_HIGH and C_AUX_RST_ACTIVE to
--                                C_AUX_RESET_HIGH to match generics used in
--                                MicroBlaze.  Added the DCM Lock as an input
--                                to keep reset active until after the Lock
--                                is valid.
-- lcw          10/11/2004  -- Updated for NCSim
-- Ravi         09/14/2006  -- Added Attributes for synthesis
-- rolandp      04/16/2007  -- version 2.00a
-- ~~~~~~~
--  SK          03/11/10
-- ^^^^^^^
-- 1. Updated the core so support the active low "Interconnect_aresetn" and
--    "Peripheral_aresetn" signals.
-- ^^^^^^^
-- ~~~~~~~
--  SK          05/12/11
-- ^^^^^^^
-- 1. Updated the core so remove the support for PPC related functionality.
-- ^^^^^^^
-------------------------------------------------------------------------------
-- Naming Conventions:
--      active low signals:                     "*_n"
--      clock signals:                          "clk", "clk_div#", "clk_#x"
--      reset signals:                          "rst", "rst_n"
--      generics:                               "C_*"
--      user defined types:                     "*_TYPE"
--      state machine next state:               "*_ns"
--      state machine current state:            "*_cs"
--      combinatorial signals:                  "*_cmb"
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
library unisim;
    use unisim.vcomponents.all;
library proc_sys_reset_v5_0_10;
    use proc_sys_reset_v5_0_10.all;

-------------------------------------------------------------------------------
-- Port Declaration
-------------------------------------------------------------------------------
-- Definition of Generics:
--      C_EXT_RST_WIDTH       -- External Reset Low Pass Filter setting
--      C_AUX_RST_WIDTH       -- Auxiliary Reset Low Pass Filter setting

--      C_EXT_RESET_HIGH      -- External Reset Active High or Active Low
--      C_AUX_RESET_HIGH      -= Auxiliary Reset Active High or Active Low

--      C_NUM_BUS_RST         -- Number of Bus Structures reset to generate
--      C_NUM_PERP_RST        -- Number of Peripheral resets to generate
--
--      C_NUM_INTERCONNECT_ARESETN -- No. of Active low reset to interconnect
--      C_NUM_PERP_ARESETN         -- No. of Active low reset to peripheral

-- Definition of Ports:
--      slowest_sync_clk       -- Clock
--      ext_reset_in           -- External Reset Input
--      aux_reset_in           -- Auxiliary Reset Input
--      mb_debug_sys_rst       -- MDM Reset Input
--      dcm_locked             -- DCM Locked, hold system in reset until 1
--      mb_reset               -- MB core reset out
--      bus_struct_reset       -- Bus structure reset out
--      peripheral_reset       -- Peripheral reset out

--      interconnect_aresetn   -- Interconnect Bus structure registered rst out
--      peripheral_aresetn     -- Active Low Peripheral registered reset out
-------------------------------------------------------------------------------

entity proc_sys_reset is
  generic (
    C_FAMILY                 : string    := "virtex7";
    C_EXT_RST_WIDTH          : integer   := 4;
    C_AUX_RST_WIDTH          : integer   := 4;
    C_EXT_RESET_HIGH         : std_logic := '0'; -- High active input
    C_AUX_RESET_HIGH         : std_logic := '1'; -- High active input
    C_NUM_BUS_RST            : integer   := 1;
    C_NUM_PERP_RST           : integer   := 1;

    C_NUM_INTERCONNECT_ARESETN : integer   := 1; -- 3/15/2010
    C_NUM_PERP_ARESETN         : integer   := 1  -- 3/15/2010
  );
  port (
    slowest_sync_clk     : in  std_logic;

    ext_reset_in         : in  std_logic;
    aux_reset_in         : in  std_logic;

    -- from MDM
    mb_debug_sys_rst     : in  std_logic;
    -- DCM locked information
    dcm_locked           : in  std_logic := '1';

    -- -- from PPC
    -- Core_Reset_Req_0     : in  std_logic;
    -- Chip_Reset_Req_0     : in  std_logic;
    -- System_Reset_Req_0   : in  std_logic;
    -- Core_Reset_Req_1     : in  std_logic;
    -- Chip_Reset_Req_1     : in  std_logic;
    -- System_Reset_Req_1   : in  std_logic;

    -- RstcPPCresetcore_0   : out std_logic := '0';
    -- RstcPPCresetchip_0   : out std_logic := '0';
    -- RstcPPCresetsys_0    : out std_logic := '0';
    -- RstcPPCresetcore_1   : out std_logic := '0';
    -- RstcPPCresetchip_1   : out std_logic := '0';
    -- RstcPPCresetsys_1    : out std_logic := '0';

    -- to Microblaze active high reset
    mb_reset             : out std_logic := '0';
    -- active high resets
    bus_struct_reset     : out std_logic_vector(0 to C_NUM_BUS_RST - 1)
                                                           := (others => '0');
    peripheral_reset     : out std_logic_vector(0 to C_NUM_PERP_RST - 1)
                                                           := (others => '0');
    -- active low resets
    interconnect_aresetn : out
                          std_logic_vector(0 to (C_NUM_INTERCONNECT_ARESETN-1))
                                                            := (others => '1');
    peripheral_aresetn   : out std_logic_vector(0 to (C_NUM_PERP_ARESETN-1))
                                                             := (others => '1')
   );

end entity proc_sys_reset;

-------------------------------------------------------------------------------
-- Architecture
-------------------------------------------------------------------------------
architecture imp of proc_sys_reset is

-------------------------------------------------------------------------------
-- Constant Declarations
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- Signal and Type Declarations
-- signal Core_Reset_Req_0_d1   : std_logic := '0';  -- delayed Core_Reset_Req
-- signal Core_Reset_Req_0_d2   : std_logic := '0';  -- delayed Core_Reset_Req
-- signal Core_Reset_Req_0_d3   : std_logic := '0';  -- delayed Core_Reset_Req
-- signal Core_Reset_Req_1_d1   : std_logic := '0';  -- delayed Core_Reset_Req
-- signal Core_Reset_Req_1_d2   : std_logic := '0';  -- delayed Core_Reset_Req
-- signal Core_Reset_Req_1_d3   : std_logic := '0';  -- delayed Core_Reset_Req

signal core_cnt_en_0         : std_logic := '0'; -- Core_Reset_Req_0 counter enable
signal core_cnt_en_1         : std_logic := '0'; -- Core_Reset_Req_1 counter enable

signal core_req_edge_0       : std_logic := '1'; -- Rising edge of Core_Reset_Req_0
signal core_req_edge_1       : std_logic := '1'; -- Rising edge of Core_Reset_Req_1

signal core_cnt_0            : std_logic_vector(3 downto 0); -- core counter output
signal core_cnt_1            : std_logic_vector(3 downto 0); -- core counter output

signal lpf_reset             : std_logic; -- Low pass filtered ext or aux

--signal Chip_Reset_Req        : std_logic := '0';
--signal System_Reset_Req      : std_logic := '0';

signal Bsr_out   : std_logic;
signal Pr_out    : std_logic;

-- signal Core_out  : std_logic;
-- signal Chip_out  : std_logic;
-- signal Sys_out   : std_logic;
signal MB_out    : std_logic;

-------------------------------------------------------------------------------
-- Attributes to synthesis
-------------------------------------------------------------------------------

attribute equivalent_register_removal: string;
attribute equivalent_register_removal of bus_struct_reset : signal is "no";
attribute equivalent_register_removal of peripheral_reset : signal is "no";

attribute equivalent_register_removal of interconnect_aresetn : signal is "no";
attribute equivalent_register_removal of peripheral_aresetn : signal is "no";

begin
-------------------------------------------------------------------------------

-- ---------------------
-- -- MB_RESET_HIGH_GEN: Generate active high reset for Micro-Blaze
-- ---------------------
-- MB_RESET_HIGH_GEN: if C_INT_RESET_HIGH = 1 generate
-- begin
  MB_Reset_PROCESS: process (slowest_sync_clk)
  begin
    if (slowest_sync_clk'event and slowest_sync_clk = '1') then
      mb_reset <= MB_out;
    end if;
  end process;
-- ----------------------------------------------------------------------------
-- -- This For-generate creates D-Flip Flops for the Bus_Struct_Reset output(s)
-- ----------------------------------------------------------------------------
  BSR_OUT_DFF: for i in 0 to (C_NUM_BUS_RST-1) generate
    BSR_DFF : process (slowest_sync_clk)
    begin
      if (slowest_sync_clk'event and slowest_sync_clk = '1') then
        bus_struct_reset(i) <= Bsr_out;
      end if;
    end process;
  end generate BSR_OUT_DFF;

-- ---------------------------------------------------------------------------
-- This For-generate creates D-Flip Flops for the Interconnect_aresetn op(s)
-- ---------------------------------------------------------------------------
  ACTIVE_LOW_BSR_OUT_DFF: for i in 0 to (C_NUM_INTERCONNECT_ARESETN-1) generate
    BSR_DFF : process (slowest_sync_clk)
    begin
      if (slowest_sync_clk'event and slowest_sync_clk = '1') then
        interconnect_aresetn(i) <= not (Bsr_out);
      end if;
    end process;
  end generate ACTIVE_LOW_BSR_OUT_DFF;
-------------------------------------------------------------------------------

-- ----------------------------------------------------------------------------
-- -- This For-generate creates D-Flip Flops for the Peripheral_Reset output(s)
-- ----------------------------------------------------------------------------
  PR_OUT_DFF: for i in 0 to (C_NUM_PERP_RST-1) generate
    PR_DFF : process (slowest_sync_clk)
    begin
      if (slowest_sync_clk'event and slowest_sync_clk = '1') then
        peripheral_reset(i) <= Pr_out;
      end if;
    end process;
  end generate PR_OUT_DFF;

-- ----------------------------------------------------------------------------
-- This For-generate creates D-Flip Flops for the Peripheral_aresetn op(s)
-- ----------------------------------------------------------------------------
  ACTIVE_LOW_PR_OUT_DFF: for i in 0 to (C_NUM_PERP_ARESETN-1) generate
    ACTIVE_LOW_PR_DFF : process (slowest_sync_clk)
    begin
      if (slowest_sync_clk'event and slowest_sync_clk = '1') then
        peripheral_aresetn(i) <= not(Pr_out);
      end if;
    end process;
  end generate ACTIVE_LOW_PR_OUT_DFF;
-------------------------------------------------------------------------------
-- This process defines the RstcPPCreset and MB_Reset outputs
-------------------------------------------------------------------------------
  -- Rstc_output_PROCESS_0: process (Slowest_sync_clk)
  -- begin
  --   if (Slowest_sync_clk'event and Slowest_sync_clk = '1') then
  --     RstcPPCresetcore_0  <= not (core_cnt_0(3) and core_cnt_0(2) and
  --                                 core_cnt_0(1) and core_cnt_0(0))
  --                            or Core_out;
  --     RstcPPCresetchip_0  <= Chip_out;
  --     RstcPPCresetsys_0   <= Sys_out;
  --   end if;
  -- end process;

  -- Rstc_output_PROCESS_1: process (Slowest_sync_clk)
  -- begin
  --   if (Slowest_sync_clk'event and Slowest_sync_clk = '1') then
  --     RstcPPCresetcore_1  <= not (core_cnt_1(3) and core_cnt_1(2) and
  --                                 core_cnt_1(1) and core_cnt_1(0))
  --                               or Core_out;
  --     RstcPPCresetchip_1  <= Chip_out;
  --     RstcPPCresetsys_1   <= Sys_out;
  --   end if;
  -- end process;

-------------------------------------------------------------------------------

---------------------------------------------------------------------------------
---- This process delays signals so the the edge can be detected and used
----  Double register to sync up with slowest_sync_clk
---------------------------------------------------------------------------------
--  DELAY_PROCESS_0: process (Slowest_sync_clk)
--  begin
--    if (Slowest_sync_clk'event and Slowest_sync_clk = '1') then
--      core_reset_req_0_d1   <= Core_Reset_Req_0;
--      core_reset_req_0_d2   <= core_reset_req_0_d1;
--      core_reset_req_0_d3   <= core_reset_req_0_d2;
--    end if;
--  end process;
--
--  DELAY_PROCESS_1: process (Slowest_sync_clk)
--  begin
--    if (Slowest_sync_clk'event and Slowest_sync_clk = '1') then
--      core_reset_req_1_d1   <= Core_Reset_Req_1;
--      core_reset_req_1_d2   <= core_reset_req_1_d1;
--      core_reset_req_1_d3   <= core_reset_req_1_d2;
--    end if;
--  end process;


-- ** -- -------------------------------------------------------------------------------
-- ** -- -- This instantiates a counter to ensure the Core_Reset_Req_* will genereate a
-- ** -- -- RstcPPCresetcore_* that is a mimimum of 15 clocks
-- ** -- -------------------------------------------------------------------------------
-- ** --   CORE_RESET_0 : entity proc_sys_reset_v5_0_10.UPCNT_N
-- ** --   generic map (C_SIZE => 4)
-- ** --   port map(
-- ** --     Data     => "0000",                    -- in  STD_LOGIC_VECTOR (C_SIZE-1 downto 0);
-- ** --     Cnt_en   => core_cnt_en_0,             -- in  STD_LOGIC;                           
-- ** --     Load     => '0',                       -- in  STD_LOGIC;                           
-- ** --     Clr      => core_req_edge_0,           -- in  STD_LOGIC;                           
-- ** --     Clk      => Slowest_sync_clk,          -- in  STD_LOGIC;                           
-- ** --     Qout     => core_cnt_0                 -- out STD_LOGIC_VECTOR (C_SIZE-1 downto 0) 
-- ** --   );
-- ** -- 
-- ** --   CORE_RESET_1 : entity proc_sys_reset_v5_0_10.UPCNT_N
-- ** --   generic map (C_SIZE => 4)
-- ** --   port map(
-- ** --     Data     => "0000",                    -- in  STD_LOGIC_VECTOR (C_SIZE-1 downto 0);
-- ** --     Cnt_en   => core_cnt_en_1,             -- in  STD_LOGIC;                           
-- ** --     Load     => '0',                       -- in  STD_LOGIC;                           
-- ** --     Clr      => core_req_edge_1,           -- in  STD_LOGIC;                           
-- ** --     Clk      => Slowest_sync_clk,          -- in  STD_LOGIC;                           
-- ** --     Qout     => core_cnt_1                 -- out STD_LOGIC_VECTOR (C_SIZE-1 downto 0) 
-- ** --   );
-- ** -- 
-- ** -- -------------------------------------------------------------------------------
-- ** -- -- CORE_RESET_PROCESS
-- ** -- -------------------------------------------------------------------------------
-- ** -- --  This generates the reset pulse and the count enable to core reset counter
-- ** -- --
-- ** --   CORE_RESET_PROCESS_0: process (Slowest_sync_clk)
-- ** --   begin
-- ** --      if (Slowest_sync_clk'event and Slowest_sync_clk = '1') then
-- ** --        core_cnt_en_0   <= not (core_cnt_0(3) and core_cnt_0(2) and core_cnt_0(1));
-- ** --                           --or not core_req_edge_0;
-- ** --        --core_req_edge_0 <= not(Core_Reset_Req_0_d2 and not Core_Reset_Req_0_d3);
-- ** --      end if;
-- ** --   end process;
-- ** -- 
-- ** --   CORE_RESET_PROCESS_1: process (Slowest_sync_clk)
-- ** --   begin
-- ** --     if (Slowest_sync_clk'event and Slowest_sync_clk = '1') then
-- ** --       core_cnt_en_1   <= not (core_cnt_1(3) and core_cnt_1(2) and core_cnt_1(1));
-- ** --                          --or not core_req_edge_1;
-- ** --       --core_req_edge_1 <= not(Core_Reset_Req_1_d2 and not Core_Reset_Req_1_d3);
-- ** --     end if;
-- ** --   end process;

-------------------------------------------------------------------------------
-- This instantiates a low pass filter to filter both External and Auxiliary
-- Reset Inputs.
-------------------------------------------------------------------------------
  EXT_LPF : entity proc_sys_reset_v5_0_10.LPF
  generic map (
    C_EXT_RST_WIDTH  => C_EXT_RST_WIDTH,
    C_AUX_RST_WIDTH  => C_AUX_RST_WIDTH,
    C_EXT_RESET_HIGH => C_EXT_RESET_HIGH,
    C_AUX_RESET_HIGH => C_AUX_RESET_HIGH
  )
  port map(
    MB_Debug_Sys_Rst       => mb_debug_sys_rst,        --  in  std_logic
    Dcm_locked             => dcm_locked,              --  in  std_logic
    External_System_Reset  => ext_reset_in,            --  in  std_logic
    Auxiliary_System_Reset => aux_reset_in,            --  in  std_logic
    Slowest_Sync_Clk       => slowest_sync_clk,        --  in  std_logic
    Lpf_reset              => lpf_reset                --  out std_logic
  );

-------------------------------------------------------------------------------
-- This instantiates the sequencer
--  This controls the time between resets becoming inactive
-------------------------------------------------------------------------------

  -- System_Reset_Req <= System_Reset_Req_0 or System_Reset_Req_1;

  -- Chip_Reset_Req   <= Chip_Reset_Req_0 or Chip_Reset_Req_1;

  SEQ : entity proc_sys_reset_v5_0_10.SEQUENCE_PSR
  --generic map (
  --  C_EXT_RESET_HIGH_1 => C_EXT_RESET_HIGH
  --)
  port map(
    Lpf_reset         => lpf_reset,                    -- in  std_logic
    --System_Reset_Req  => '0', -- System_Reset_Req,     -- in  std_logic
    --Chip_Reset_Req    => '0', -- Chip_Reset_Req,       -- in  std_logic
    Slowest_Sync_Clk  => slowest_sync_clk,             -- in  std_logic
    Bsr_out           => Bsr_out,                      -- out std_logic
    Pr_out            => Pr_out,                       -- out std_logic
    --Core_out          => open, -- Core_out,            -- out std_logic
    --Chip_out          => open, -- Chip_out,            -- out std_logic
    --Sys_out           => open, -- Sys_out,             -- out std_logic
    MB_out            => MB_out);                      -- out std_logic

end imp;

--END_SINGLE_FILE_TAG


