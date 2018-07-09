-------------------------------------------------------------------------------
-- lmb_bram_if_funcs.vhd - Entity and architecture
-------------------------------------------------------------------------------
--
-- (c) Copyright 2001-2015 Xilinx, Inc. All rights reserved.
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
-- Filename:        lmb_bram_if_funcs.vhd
--
-- Description:     Support functions for lmb_bram_if_cntlr
--
-- VHDL-Standard:   VHDL'93
-------------------------------------------------------------------------------
-- Structure:
--                  lmb_bram_if_funcs.vhd
--
-------------------------------------------------------------------------------
-- Author:          stefana
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

package lmb_bram_if_funcs is

  type TARGET_FAMILY_TYPE is (
                              -- pragma xilinx_rtl_off
                              VIRTEX7,
                              KINTEX7,
                              ARTIX7,
                              ZYNQ,
                              VIRTEXU,
                              KINTEXU,
                              ZYNQUPLUS,
                              VIRTEXUPLUS,
                              KINTEXUPLUS,
                              SPARTAN7,
                              -- pragma xilinx_rtl_on
                              RTL
                             );

  function String_To_Family (S : string; Select_RTL : boolean) return TARGET_FAMILY_TYPE;

  -- Get the maximum number of inputs to a LUT.
  function Family_To_LUT_Size(Family : TARGET_FAMILY_TYPE) return integer;

end package lmb_bram_if_funcs;

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

package body lmb_bram_if_funcs is

  function LowerCase_Char(char : character) return character is
  begin
    -- If char is not an upper case letter then return char
    if char < 'A' or char > 'Z' then
      return char;
    end if;
    -- Otherwise map char to its corresponding lower case character and
    -- return that
    case char is
      when 'A'    => return 'a'; when 'B' => return 'b'; when 'C' => return 'c'; when 'D' => return 'd';
      when 'E'    => return 'e'; when 'F' => return 'f'; when 'G' => return 'g'; when 'H' => return 'h';
      when 'I'    => return 'i'; when 'J' => return 'j'; when 'K' => return 'k'; when 'L' => return 'l';
      when 'M'    => return 'm'; when 'N' => return 'n'; when 'O' => return 'o'; when 'P' => return 'p';
      when 'Q'    => return 'q'; when 'R' => return 'r'; when 'S' => return 's'; when 'T' => return 't';
      when 'U'    => return 'u'; when 'V' => return 'v'; when 'W' => return 'w'; when 'X' => return 'x';
      when 'Y'    => return 'y'; when 'Z' => return 'z';
      when others => return char;
    end case;
  end LowerCase_Char;

  -- Returns true if case insensitive string comparison determines that
  -- str1 and str2 are equal
  function Equal_String( str1, str2 : STRING ) RETURN BOOLEAN IS
    CONSTANT len1 : INTEGER := str1'length;
    CONSTANT len2 : INTEGER := str2'length;
    VARIABLE equal : BOOLEAN := TRUE;
  BEGIN
    IF NOT (len1=len2) THEN
      equal := FALSE;
    ELSE
      FOR i IN str1'range LOOP
        IF NOT (LowerCase_Char(str1(i)) = LowerCase_Char(str2(i))) THEN
          equal := FALSE;
        END IF;
      END LOOP;
    END IF;

    RETURN equal;
  END Equal_String;

  function String_To_Family (S : string; Select_RTL : boolean) return TARGET_FAMILY_TYPE is
  begin  -- function String_To_Family
    if ((Select_RTL) or Equal_String(S, "rtl")) then
      return RTL;
    elsif Equal_String(S, "virtex7") or Equal_String(S, "qvirtex7") then
      return VIRTEX7;
    elsif Equal_String(S, "kintex7")  or Equal_String(S, "kintex7l")  or
          Equal_String(S, "qkintex7") or Equal_String(S, "qkintex7l") then
      return KINTEX7;
    elsif Equal_String(S, "artix7")  or Equal_String(S, "artix7l")  or Equal_String(S, "aartix7") or
          Equal_String(S, "qartix7") or Equal_String(S, "qartix7l") then
      return ARTIX7;
    elsif Equal_String(S, "zynq")  or Equal_String(S, "azynq") or Equal_String(S, "qzynq") then
      return ZYNQ;
    elsif Equal_String(S, "virtexu") or Equal_String(S, "qvirtexu") then
      return VIRTEXU;
    elsif Equal_String(S, "kintexu")  or Equal_String(S, "kintexul")  or
          Equal_String(S, "qkintexu") or Equal_String(S, "qkintexul") then
      return KINTEXU;
    elsif Equal_String(S, "zynquplus") or Equal_String(S, "zynquplusRFSOC") then
      return ZYNQUPLUS;
    elsif Equal_String(S, "virtexuplus") or Equal_String(S, "virtexuplusHBM") then
      return VIRTEXUPLUS;
    elsif Equal_String(S, "kintexuplus") then
      return KINTEXUPLUS;
    elsif Equal_String(S, "spartan7") then
      return SPARTAN7;
    else
      -- assert (false) report "No known target family" severity failure;
      return RTL;
    end if;
  end function String_To_Family;

  function Family_To_LUT_Size(Family : TARGET_FAMILY_TYPE) return integer is
  begin
    return 6;
  end function Family_To_LUT_Size;

end package body lmb_bram_if_funcs;


-------------------------------------------------------------------------------
-- primitives.vhd - Entity and architecture
-------------------------------------------------------------------------------
--
-- (c) Copyright 2015 Xilinx, Inc. All rights reserved.
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
-- Filename:        primitives.vhd
--
-- Description:     
--                  
-- VHDL-Standard:   VHDL'93
-------------------------------------------------------------------------------
-- Structure:   
--              lmb_bram_if_primitives.vhd
--
-------------------------------------------------------------------------------
-- Author:          rolandp
--
-- History:
--   rolandp  2015-01-22    First Version
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

----- entity LUT6 -----
library IEEE;
use IEEE.std_logic_1164.all;
use ieee.numeric_std.all;

library lmb_bram_if_cntlr_v4_0_14;
use lmb_bram_if_cntlr_v4_0_14.lmb_bram_if_funcs.all;

entity MB_LUT6 is
  generic (
    C_TARGET : TARGET_FAMILY_TYPE;
    INIT     : bit_vector := X"0000000000000000"
  );
  port (
    O  : out std_logic;
    I0 : in  std_logic;
    I1 : in  std_logic;
    I2 : in  std_logic;
    I3 : in  std_logic;
    I4 : in  std_logic;
    I5 : in  std_logic
  );
end entity MB_LUT6;

library Unisim;
use Unisim.vcomponents.all;

architecture IMP of MB_LUT6 is
begin
  
  Using_RTL: if ( C_TARGET = RTL ) generate 
    constant INIT_reg : std_logic_vector(63 downto 0) := To_StdLogicVector(INIT);
  begin
    process (I0, I1, I2, I3, I4, I5)
      variable I_reg    : std_logic_vector(5 downto 0);
      variable I0_v, I1_v, I2_v, I3_v, I4_v, I5_v : std_logic;
    begin
      -- Filter unknowns
      if I0 = '0' then I0_v := '0'; else I0_v := '1'; end if;
      if I1 = '0' then I1_v := '0'; else I1_v := '1'; end if;
      if I2 = '0' then I2_v := '0'; else I2_v := '1'; end if;
      if I3 = '0' then I3_v := '0'; else I3_v := '1'; end if;
      if I4 = '0' then I4_v := '0'; else I4_v := '1'; end if;
      if I5 = '0' then I5_v := '0'; else I5_v := '1'; end if;
      I_reg := TO_STDLOGICVECTOR(I5_v & I4_v & I3_v &  I2_v & I1_v & I0_v);
      O     <= INIT_reg(TO_INTEGER(unsigned(I_reg)));
    end process;
  end generate Using_RTL;
  
  Using_FPGA: if ( C_TARGET /= RTL ) generate 
  begin
    Native: LUT6
      generic map(
        INIT    => INIT
      )
      port map(
        O       => O,
        I0      => I0,
        I1      => I1,
        I2      => I2,
        I3      => I3,
        I4      => I4,
        I5      => I5
      );
  end generate Using_FPGA;
  
end architecture IMP;

----- entity MUXCY -----
library IEEE;
use IEEE.std_logic_1164.all;

library lmb_bram_if_cntlr_v4_0_14;
use lmb_bram_if_cntlr_v4_0_14.lmb_bram_if_funcs.all;

entity MB_MUXCY is
  generic (
    C_TARGET : TARGET_FAMILY_TYPE
  );
  port (
    LO : out std_logic;
    CI : in  std_logic;
    DI : in  std_logic;
    S  : in  std_logic
  );
end entity MB_MUXCY;

library Unisim;
use Unisim.vcomponents.all;

architecture IMP of MB_MUXCY is
begin
  
  Using_RTL: if ( C_TARGET = RTL ) generate 
  begin
    LO <= DI when S = '0' else CI;
  end generate Using_RTL;
  
  Using_FPGA: if ( C_TARGET /= RTL ) generate 
  begin
    Native: MUXCY_L
      port map(
        LO => LO,
        CI => CI,
        DI => DI,
        S  => S
      );
  end generate Using_FPGA;
  
end architecture IMP;

----- entity XORCY -----
library IEEE;
use IEEE.std_logic_1164.all;

library lmb_bram_if_cntlr_v4_0_14;
use lmb_bram_if_cntlr_v4_0_14.lmb_bram_if_funcs.all;

entity MB_XORCY is
  generic (
    C_TARGET : TARGET_FAMILY_TYPE
  );
  port (
    O  : out std_logic;
    CI : in  std_logic;
    LI : in  std_logic
  );
end entity MB_XORCY;

library Unisim;
use Unisim.vcomponents.all;

architecture IMP of MB_XORCY is
begin
  
  Using_RTL: if ( C_TARGET = RTL ) generate 
  begin
    O <= (CI xor LI);
  end generate Using_RTL;
  
  Using_FPGA: if ( C_TARGET /= RTL ) generate 
  begin
    Native: XORCY
      port map(
        O  => O,
        CI => CI,
        LI => LI
      );
  end generate Using_FPGA;
  
end architecture IMP;

----- entity MUXF7 -----
library IEEE;
use IEEE.std_logic_1164.all;

library lmb_bram_if_cntlr_v4_0_14;
use lmb_bram_if_cntlr_v4_0_14.lmb_bram_if_funcs.all;

entity MB_MUXF7 is
  generic (
    C_TARGET : TARGET_FAMILY_TYPE
  );
  port (
    O  : out std_logic;
    I0 : in  std_logic;
    I1 : in  std_logic;
    S  : in  std_logic
  );
end entity MB_MUXF7;

library Unisim;
use Unisim.vcomponents.all;

architecture IMP of MB_MUXF7 is
begin
  
  Using_RTL: if ( C_TARGET = RTL ) generate 
  begin
    O <= I0 when S = '0' else I1;
  end generate Using_RTL;
  
  Using_FPGA: if ( C_TARGET /= RTL ) generate 
  begin
    Native: MUXF7
      port map(
        O  => O,
        I0 => I0,
        I1 => I1,
        S  => S
      );
  end generate Using_FPGA;
  
end architecture IMP;

----- entity MUXF8 -----
library IEEE;
use IEEE.std_logic_1164.all;

library lmb_bram_if_cntlr_v4_0_14;
use lmb_bram_if_cntlr_v4_0_14.lmb_bram_if_funcs.all;

entity MB_MUXF8 is
  generic (
    C_TARGET : TARGET_FAMILY_TYPE
  );
  port (
    O  : out std_logic;
    I0 : in  std_logic;
    I1 : in  std_logic;
    S  : in  std_logic
  );
end entity MB_MUXF8;

library Unisim;
use Unisim.vcomponents.all;

architecture IMP of MB_MUXF8 is
begin
  
  Using_RTL: if ( C_TARGET = RTL ) generate 
  begin
    O <= I0 when S = '0' else I1;
  end generate Using_RTL;
  
  Using_FPGA: if ( C_TARGET /= RTL ) generate 
  begin
    Native: MUXF8
      port map(
        O  => O,
        I0 => I0,
        I1 => I1,
        S  => S
      );
  end generate Using_FPGA;
  
end architecture IMP;

----- entity FDRE -----
library IEEE;
use IEEE.std_logic_1164.all;

library lmb_bram_if_cntlr_v4_0_14;
use lmb_bram_if_cntlr_v4_0_14.lmb_bram_if_funcs.all;

entity MB_FDRE is
  generic (
    C_TARGET : TARGET_FAMILY_TYPE;
    INIT : bit := '0'
  );
  port(
    Q  : out std_logic;
    C  : in  std_logic;
    CE : in  std_logic;
    D  : in  std_logic;
    R  : in  std_logic
  );
end entity MB_FDRE;

library Unisim;
use Unisim.vcomponents.all;

architecture IMP of MB_FDRE is
begin
  
  Using_RTL: if ( C_TARGET = RTL ) generate 
    function To_StdLogic(A : in bit ) return std_logic is
    begin
      if( A = '1' ) then
        return '1';
      end if;
      return '0';
    end;

    signal q_o : std_logic := To_StdLogic(INIT);
  begin
    Q <=  q_o;
    process(C)
    begin
      if (rising_edge(C)) then
        if (R = '1') then
          q_o <= '0';
        elsif (CE = '1') then
          q_o <= D;
        end if;
      end if;
    end process;
  end generate Using_RTL;
  
  Using_FPGA: if ( C_TARGET /= RTL ) generate 
  begin
    Native: FDRE
      generic map(
        INIT => INIT
      )
      port map(
        Q   => Q,
        C   => C,
        CE  => CE,
        D   => D,
        R   => R
      );
  end generate Using_FPGA;
  
end architecture IMP;



-------------------------------------------------------------------------------
-- xor18.vhd - Entity and architecture
-------------------------------------------------------------------------------
--
-- (c) Copyright [2003] - [2015] Xilinx, Inc. All rights reserved.
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
-- PART OF THIS FILE AT ALL TIMES
--
------------------------------------------------------------------------------
-- Filename:        xor18.vhd
--
-- Description:
--
-- VHDL-Standard:   VHDL'93
-------------------------------------------------------------------------------
-- Structure:
--              xor18.vhd
--
-------------------------------------------------------------------------------
-- Author:          rolandp
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

library lmb_bram_if_cntlr_v4_0_14;
use lmb_bram_if_cntlr_v4_0_14.all;
use lmb_bram_if_cntlr_v4_0_14.lmb_bram_if_funcs.all;

entity XOR18 is 
  generic (
    C_TARGET   : TARGET_FAMILY_TYPE);
  port (
    InA : in  std_logic_vector(0 to 17);
    res : out std_logic);
end entity XOR18;

architecture IMP of XOR18 is

  component MB_LUT6 is
  generic (
    C_TARGET : TARGET_FAMILY_TYPE;
    INIT     : bit_vector := X"0000000000000000"
  );
  port (
    O  : out std_logic;
    I0 : in  std_logic;
    I1 : in  std_logic;
    I2 : in  std_logic;
    I3 : in  std_logic;
    I4 : in  std_logic;
    I5 : in  std_logic
  );
  end component MB_LUT6;

  component MB_MUXCY is
  generic (
    C_TARGET : TARGET_FAMILY_TYPE
  );
  port (
    LO : out std_logic;
    CI : in  std_logic;
    DI : in  std_logic;
    S  : in  std_logic
  );
  end component MB_MUXCY;

  component MB_XORCY is
  generic (
    C_TARGET : TARGET_FAMILY_TYPE
  );
  port (
    O  : out std_logic;
    CI : in  std_logic;
    LI : in  std_logic
  );
  end component MB_XORCY;

begin  -- architecture IMP

  Using_FPGA: if ( C_TARGET /= RTL ) generate 
    signal xor6_1   : std_logic;
    signal xor6_2   : std_logic;
    signal xor6_3   : std_logic;
    signal xor18_c1 : std_logic;
    signal xor18_c2 : std_logic;
  begin  -- generate Using_LUT6

    XOR6_1_LUT : MB_LUT6
      generic map(
        C_TARGET => C_TARGET,
        INIT => X"6996966996696996")
      port map(
        O    => xor6_1,
        I0   => InA(17),
        I1   => InA(16),
        I2   => InA(15),
        I3   => InA(14),
        I4   => InA(13),
        I5   => InA(12));

    XOR_1st_MUXCY : MB_MUXCY
      generic map(
        C_TARGET => C_TARGET)
      port map (
        DI => '1',
        CI => '0',
        S  => xor6_1,
        LO => xor18_c1);

    XOR6_2_LUT : MB_LUT6
      generic map(
        C_TARGET => C_TARGET,
        INIT => X"6996966996696996")
      port map(
        O    => xor6_2,
        I0   => InA(11),
        I1   => InA(10),
        I2   => InA(9),
        I3   => InA(8),
        I4   => InA(7),
        I5   => InA(6));

    XOR_2nd_MUXCY : MB_MUXCY
      generic map(
        C_TARGET => C_TARGET)
      port map (
        DI => xor6_1,
        CI => xor18_c1,
        S  => xor6_2,
        LO => xor18_c2);

    XOR6_3_LUT : MB_LUT6
      generic map(
        C_TARGET => C_TARGET,
        INIT => X"6996966996696996")
      port map(
        O    => xor6_3,
        I0   => InA(5),
        I1   => InA(4),
        I2   => InA(3),
        I3   => InA(2),
        I4   => InA(1),
        I5   => InA(0));

    XOR18_XORCY : MB_XORCY
      generic map(
        C_TARGET => C_TARGET)
      port map (
        LI => xor6_3,
        CI => xor18_c2,
        O  => res);
    
  end generate Using_FPGA;

  Using_RTL: if ( C_TARGET = RTL ) generate 
  begin 

    res <= InA(17) xor InA(16) xor InA(15) xor InA(14) xor InA(13) xor InA(12) xor
           InA(11) xor InA(10) xor InA(9) xor InA(8) xor InA(7) xor InA(6) xor
           InA(5) xor InA(4) xor InA(3) xor InA(2) xor InA(1) xor InA(0);    

  end generate Using_RTL;
end architecture IMP;


-------------------------------------------------------------------------------
-- parity.vhd - Entity and architecture
-------------------------------------------------------------------------------
--
-- (c) Copyright [2003] - [2015] Xilinx, Inc. All rights reserved.
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
-- PART OF THIS FILE AT ALL TIMES
--
------------------------------------------------------------------------------
-- Filename:        parity.vhd
--
-- Description:     Generate parity optimally for all target architectures
--
-- VHDL-Standard:   VHDL'93
-------------------------------------------------------------------------------
-- Structure:
--                  parity.vhd
--                    xor18.vhd
--                    parity_recursive_LUT6.vhd
--
-------------------------------------------------------------------------------
-- Author:          stefana
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

library lmb_bram_if_cntlr_v4_0_14;
use lmb_bram_if_cntlr_v4_0_14.lmb_bram_if_funcs.all;

entity Parity is
  generic (
    C_TARGET   : TARGET_FAMILY_TYPE;
    C_SIZE     : integer := 6
    );
  port (
    InA : in  std_logic_vector(0 to C_SIZE - 1);
    Res : out std_logic
    );
end entity Parity;

architecture IMP of Parity is

  component MB_LUT6 is
  generic (
    C_TARGET : TARGET_FAMILY_TYPE;
    INIT     : bit_vector := X"0000000000000000"
  );
  port (
    O  : out std_logic;
    I0 : in  std_logic;
    I1 : in  std_logic;
    I2 : in  std_logic;
    I3 : in  std_logic;
    I4 : in  std_logic;
    I5 : in  std_logic
  );
  end component MB_LUT6;

  component MB_MUXF7 is
  generic (
    C_TARGET : TARGET_FAMILY_TYPE
  );
  port (
    O  : out std_logic;
    I0 : in  std_logic;
    I1 : in  std_logic;
    S  : in  std_logic
  );
  end component MB_MUXF7;
  
  component MB_MUXF8 is
  generic (
    C_TARGET : TARGET_FAMILY_TYPE
  );
  port (
    O  : out std_logic;
    I0 : in  std_logic;
    I1 : in  std_logic;
    S  : in  std_logic
  );
  end component MB_MUXF8;

  -- Non-recursive loop implementation
  function ParityGen (InA : std_logic_vector) return std_logic is
    variable result : std_logic;
  begin
    result := '0';
    for I in InA'range loop
      result := result xor InA(I);
    end loop;
    return result;
  end function ParityGen;

begin  -- architecture IMP

  Using_FPGA : if (C_TARGET /= RTL) generate

    --------------------------------------------------------------------------------------------------
    -- Single LUT6
    --------------------------------------------------------------------------------------------------
    Single_LUT6 : if C_SIZE > 1 and C_SIZE <= 6 generate
      signal inA6 : std_logic_vector(0 to 5);
    begin

      Assign_InA : process (InA) is
      begin
        inA6                      <= (others => '0');
        inA6(0 to InA'length - 1) <= InA;
      end process Assign_InA;

      XOR6_LUT : MB_LUT6
        generic map(
          C_TARGET => C_TARGET,
          INIT => X"6996966996696996")
        port map(
          O  => Res,
          I0 => inA6(5),
          I1 => inA6(4),
          I2 => inA6(3),
          I3 => inA6(2),
          I4 => inA6(1),
          I5 => inA6(0));
    end generate Single_LUT6;

    --------------------------------------------------------------------------------------------------
    -- Two LUT6 and one MUXF7
    --------------------------------------------------------------------------------------------------
    Use_MUXF7 : if C_SIZE = 7 generate
      signal inA7     : std_logic_vector(0 to 6);
      signal result6  : std_logic;
      signal result6n : std_logic;
    begin

      Assign_InA : process (InA) is
      begin
        inA7                      <= (others => '0');
        inA7(0 to InA'length - 1) <= InA;
      end process Assign_InA;

      XOR6_LUT : MB_LUT6
        generic map(
          C_TARGET => C_TARGET,
          INIT => X"6996966996696996")
        port map(
          O  => result6,
          I0 => inA7(5),
          I1 => inA7(4),
          I2 => inA7(3),
          I3 => inA7(2),
          I4 => inA7(1),
          I5 => inA7(0));

      XOR6_LUT_N : MB_LUT6
        generic map(
          C_TARGET => C_TARGET,
          INIT => X"9669699669969669") 
        port map(
          O  => result6n,
          I0 => inA7(5),
          I1 => inA7(4),
          I2 => inA7(3),
          I3 => inA7(2),
          I4 => inA7(1),
          I5 => inA7(0));

      MUXF7_LUT : MB_MUXF7
        generic map(
          C_TARGET => C_TARGET)
        port map (
          O  => Res,
          I0 => result6,
          I1 => result6n,
          S  => inA7(6));
    end generate Use_MUXF7;

    --------------------------------------------------------------------------------------------------
    -- Four LUT6, two MUXF7 and one MUXF8
    --------------------------------------------------------------------------------------------------
    Use_MUXF8 : if C_SIZE = 8 generate
      signal inA8       : std_logic_vector(0 to 7);
      signal result6_1  : std_logic;
      signal result6_1n : std_logic;
      signal result6_2  : std_logic;
      signal result6_2n : std_logic;
      signal result7_1  : std_logic;
      signal result7_1n : std_logic;
    begin

      Assign_InA : process (InA) is
      begin
        inA8                      <= (others => '0');
        inA8(0 to InA'length - 1) <= InA;
      end process Assign_InA;

      XOR6_LUT1 : MB_LUT6
        generic map(
          C_TARGET => C_TARGET,
          INIT => X"6996966996696996")
        port map(
          O  => result6_1,
          I0 => inA8(5),
          I1 => inA8(4),
          I2 => inA8(3),
          I3 => inA8(2),
          I4 => inA8(1),
          I5 => inA8(0));

      XOR6_LUT2_N : MB_LUT6
        generic map(
          C_TARGET => C_TARGET,
          INIT => X"9669699669969669") 
        port map(
          O  => result6_1n,
          I0 => inA8(5),
          I1 => inA8(4),
          I2 => inA8(3),
          I3 => inA8(2),
          I4 => inA8(1),
          I5 => inA8(0));

      MUXF7_LUT1 : MB_MUXF7
        generic map(
          C_TARGET => C_TARGET)
        port map (
          O  => result7_1,
          I0 => result6_1,
          I1 => result6_1n,
          S  => inA8(6));

      XOR6_LUT3 : MB_LUT6
        generic map(
          C_TARGET => C_TARGET,
          INIT => X"6996966996696996")
        port map(
          O  => result6_2,
          I0 => inA8(5),
          I1 => inA8(4),
          I2 => inA8(3),
          I3 => inA8(2),
          I4 => inA8(1),
          I5 => inA8(0));

      XOR6_LUT4_N : MB_LUT6
        generic map(
          C_TARGET => C_TARGET,
          INIT => X"9669699669969669") 
        port map(
          O  => result6_2n,
          I0 => inA8(5),
          I1 => inA8(4),
          I2 => inA8(3),
          I3 => inA8(2),
          I4 => inA8(1),
          I5 => inA8(0));

      MUXF7_LUT2 : MB_MUXF7
        generic map(
          C_TARGET => C_TARGET)
        port map (
          O  => result7_1n,
          I0 => result6_2n,
          I1 => result6_2,
          S  => inA8(6));

      MUXF8_LUT : MB_MUXF8
        generic map(
          C_TARGET => C_TARGET)
        port map (
          O  => res,
          I0 => result7_1,
          I1 => result7_1n,
          S  => inA8(7));

    end generate Use_MUXF8;
  end generate Using_FPGA;

  Using_RTL: if ( C_TARGET = RTL ) generate 
  begin
    Res <= ParityGen(InA);
  end generate Using_RTL;

end architecture IMP;


-------------------------------------------------------------------------------
-- parityenable.vhd - Entity and architecture
-------------------------------------------------------------------------------
--
-- (c) Copyright [2003] - [2015] Xilinx, Inc. All rights reserved.
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
-- PART OF THIS FILE AT ALL TIMES
--
------------------------------------------------------------------------------
-- Filename:        parity.vhd
--
-- Description:     Generate parity optimally for all target architectures
--
-- VHDL-Standard:   VHDL'93
-------------------------------------------------------------------------------
-- Structure:
--                  parity.vhd
--                    xor18.vhd
--                    parity_recursive_LUT6.vhd
--
-------------------------------------------------------------------------------
-- Author:          stefana
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

library lmb_bram_if_cntlr_v4_0_14;
use lmb_bram_if_cntlr_v4_0_14.all;
use lmb_bram_if_cntlr_v4_0_14.lmb_bram_if_funcs.all;

entity ParityEnable is
  generic (
    C_TARGET   : TARGET_FAMILY_TYPE;
    C_SIZE     :     integer := 4
    );
  port (
    InA        : in  std_logic_vector(0 to C_SIZE - 1);
    Enable     : in  std_logic;
    Res        : out std_logic
    );
end entity ParityEnable;

architecture IMP of ParityEnable is

  -- Non-recursive loop implementation
  function ParityGen (InA : std_logic_vector) return std_logic is
    variable result : std_logic;
  begin
    result := '0';
    for I in InA'range loop
      result := result xor InA(I);
    end loop;
    return result;
  end function ParityGen;

  component MB_LUT6 is
  generic (
    C_TARGET : TARGET_FAMILY_TYPE;
    INIT     : bit_vector := X"0000000000000000"
  );
  port (
    O  : out std_logic;
    I0 : in  std_logic;
    I1 : in  std_logic;
    I2 : in  std_logic;
    I3 : in  std_logic;
    I4 : in  std_logic;
    I5 : in  std_logic
  );
  end component MB_LUT6;

begin  -- architecture IMP

  Using_FPGA: if ( C_TARGET /= RTL ) generate 

    --------------------------------------------------------------------------------------------------
    -- Single LUT6
    --------------------------------------------------------------------------------------------------
    Single_LUT6 : if C_SIZE > 1 and C_SIZE <= 5 generate
      signal inA5 : std_logic_vector(0 to 4);
    begin

      Assign_InA : process (InA) is
      begin
        inA5                      <= (others => '0');
        inA5(0 to InA'length - 1) <= InA;
      end process Assign_InA;

      XOR6_LUT : MB_LUT6
        generic map(
          C_TARGET => C_TARGET,
          INIT => X"9669699600000000")
        port map(
          O  => Res,
          I0 => InA5(4),
          I1 => inA5(3),
          I2 => inA5(2),
          I3 => inA5(1),
          I4 => inA5(0),
          I5 => Enable);
    end generate Single_LUT6;

  end generate Using_FPGA;

  Using_RTL: if ( C_TARGET = RTL ) generate 
  begin
    Res <= Enable and ParityGen(InA);
  end generate Using_RTL;

end architecture IMP;


-------------------------------------------------------------------------------
-- checkbit_handler.vhd - Entity and architecture
-------------------------------------------------------------------------------
--
-- (c) Copyright [2003] - [2015] Xilinx, Inc. All rights reserved.
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
-- PART OF THIS FILE AT ALL TIMES
--
-------------------------------------------------------------------------------
-- Filename:        gen_checkbits.vhd
--
-- Description:     
--                  
-- VHDL-Standard:   VHDL'93/02
-------------------------------------------------------------------------------
-- Structure:   
--              gen_checkbits.vhd
--
-------------------------------------------------------------------------------
-- Author:          goran
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

library lmb_bram_if_cntlr_v4_0_14;
use lmb_bram_if_cntlr_v4_0_14.all;
use lmb_bram_if_cntlr_v4_0_14.lmb_bram_if_funcs.all;

entity checkbit_handler is
  generic (
    C_TARGET   : TARGET_FAMILY_TYPE;
    C_ENCODE   : boolean := true);
  port (
    DataIn     : in  std_logic_vector(0 to 31);
    CheckIn    : in  std_logic_vector(0 to 6);
    CheckOut   : out std_logic_vector(0 to 6);
    Syndrome   : out std_logic_vector(0 to 6);
    Enable_ECC : in  std_logic;
    UE_Q       : in  std_logic;
    CE_Q       : in  std_logic;
    UE         : out std_logic;
    CE         : out std_logic
    );
end entity checkbit_handler;

architecture IMP of checkbit_handler is

  component XOR18 is
    generic (
      C_TARGET   : TARGET_FAMILY_TYPE);
    port (
      InA : in  std_logic_vector(0 to 17);
      res : out std_logic);
  end component XOR18;
  
  component Parity is
    generic (
      C_TARGET   : TARGET_FAMILY_TYPE;
      C_SIZE     : integer);
    port (
      InA : in  std_logic_vector(0 to C_SIZE - 1);
      Res : out std_logic);
  end component Parity;

  component ParityEnable
    generic (
      C_TARGET   : TARGET_FAMILY_TYPE;
      C_SIZE     : integer);
    port (
      InA    : in  std_logic_vector(0 to C_SIZE - 1);
      Enable : in  std_logic;
      Res    : out std_logic);
  end component ParityEnable;

  component MB_MUXF7 is
  generic (
    C_TARGET : TARGET_FAMILY_TYPE
  );
  port (
    O  : out std_logic;
    I0 : in  std_logic;
    I1 : in  std_logic;
    S  : in  std_logic
  );
  end component MB_MUXF7;
  
  signal data_chk0 : std_logic_vector(0 to 17);
  signal data_chk1 : std_logic_vector(0 to 17);
  signal data_chk2 : std_logic_vector(0 to 17);
  signal data_chk3 : std_logic_vector(0 to 14);
  signal data_chk4 : std_logic_vector(0 to 14);
  signal data_chk5 : std_logic_vector(0 to 5);
  
begin  -- architecture IMP
  data_chk0 <= DataIn(0) & DataIn(1) & DataIn(3) & DataIn(4) & DataIn(6) & DataIn(8) & DataIn(10) &
               DataIn(11) & DataIn(13) & DataIn(15) & DataIn(17) & DataIn(19) & DataIn(21) &
               DataIn(23) & DataIn(25) & DataIn(26) & DataIn(28) & DataIn(30);

  data_chk1 <= DataIn(0) & DataIn(2) & DataIn(3) & DataIn(5) & DataIn(6) & DataIn(9) & DataIn(10) &
               DataIn(12) & DataIn(13) & DataIn(16) & DataIn(17) & DataIn(20) & DataIn(21) &
               DataIn(24) & DataIn(25) & DataIn(27) & DataIn(28) & DataIn(31);

  data_chk2 <= DataIn(1) & DataIn(2) & DataIn(3) & DataIn(7) & DataIn(8) & DataIn(9) & DataIn(10) &
               DataIn(14) & DataIn(15) & DataIn(16) & DataIn(17) & DataIn(22) & DataIn(23) & DataIn(24) &
               DataIn(25) & DataIn(29) & DataIn(30) & DataIn(31);

  data_chk3 <= DataIn(4) & DataIn(5) & DataIn(6) & DataIn(7) & DataIn(8) & DataIn(9) & DataIn(10) &
               DataIn(18) & DataIn(19) & DataIn(20) & DataIn(21) & DataIn(22) & DataIn(23) & DataIn(24) &
               DataIn(25);

  data_chk4 <= DataIn(11) & DataIn(12) & DataIn(13) & DataIn(14) & DataIn(15) & DataIn(16) & DataIn(17) &
               DataIn(18) & DataIn(19) & DataIn(20) & DataIn(21) & DataIn(22) & DataIn(23) & DataIn(24) &
               DataIn(25);

  data_chk5 <= DataIn(26) & DataIn(27) & DataIn(28) & DataIn(29) & DataIn(30) & DataIn(31);

  -- Encode bits for writing data
  Encode_Bits : if (C_ENCODE) generate
    signal data_chk3_i : std_logic_vector(0 to 17);
    signal data_chk4_i : std_logic_vector(0 to 17);
    signal data_chk6   : std_logic_vector(0 to 17);
  begin
    ------------------------------------------------------------------------------------------------
    -- Checkbit 0 built up using XOR18
    ------------------------------------------------------------------------------------------------
    XOR18_I0 : XOR18
      generic map (
        C_TARGET => C_TARGET)
      port map (
        InA => data_chk0,               -- [in  std_logic_vector(0 to 17)]
        res => CheckOut(0));            -- [out std_logic]

    ------------------------------------------------------------------------------------------------
    -- Checkbit 1 built up using XOR18
    ------------------------------------------------------------------------------------------------
    XOR18_I1 : XOR18
      generic map (
        C_TARGET => C_TARGET)
      port map (
        InA => data_chk1,               -- [in  std_logic_vector(0 to 17)]
        res => CheckOut(1));            -- [out std_logic]

    ------------------------------------------------------------------------------------------------
    -- Checkbit 2 built up using XOR18
    ------------------------------------------------------------------------------------------------
    XOR18_I2 : XOR18
      generic map (
        C_TARGET => C_TARGET)
      port map (
        InA => data_chk2,               -- [in  std_logic_vector(0 to 17)]
        res => CheckOut(2));            -- [out std_logic]

    ------------------------------------------------------------------------------------------------
    -- Checkbit 3 built up using XOR18
    ------------------------------------------------------------------------------------------------
    data_chk3_i <= data_chk3 & "000";
    XOR18_I3 : XOR18
      generic map (
        C_TARGET => C_TARGET)
      port map (
        InA => data_chk3_i,             -- [in  std_logic_vector(0 to 17)]
        res => CheckOut(3));            -- [out std_logic]

    ------------------------------------------------------------------------------------------------
    -- Checkbit 4 built up using XOR18
    ------------------------------------------------------------------------------------------------
    data_chk4_i <= data_chk4 & "000";
    XOR18_I4 : XOR18
      generic map (
        C_TARGET => C_TARGET)
      port map (
        InA => data_chk4_i,             -- [in  std_logic_vector(0 to 17)]
        res => CheckOut(4));            -- [out std_logic]

    ------------------------------------------------------------------------------------------------
    -- Checkbit 5 built up from 1 LUT6
    ------------------------------------------------------------------------------------------------
    Parity_chk5_1 : Parity
      generic map (
        C_TARGET => C_TARGET, C_SIZE => 6)
      port map (
        InA => data_chk5,             -- [in  std_logic_vector(0 to C_SIZE - 1)]
        Res => CheckOut(5));          -- [out std_logic]
    
    ------------------------------------------------------------------------------------------------
    -- Checkbit 6 built up from 3 LUT7 and 4 LUT6
    ------------------------------------------------------------------------------------------------
    data_chk6 <= DataIn(0) & DataIn(1) & DataIn(2) & DataIn(4) & DataIn(5) & DataIn(7) & DataIn(10) &
                 DataIn(11) & DataIn(12) & DataIn(14) & DataIn(17) & DataIn(18) & DataIn(21) &
                 DataIn(23) & DataIn(24) & DataIn(26) & DataIn(27) & DataIn(29);
    XOR18_I6 : XOR18
      generic map (
        C_TARGET => C_TARGET)       -- [boolean]
      port map (
        InA => data_chk6,             -- [in  std_logic_vector(0 to 17)]
        res => CheckOut(6));            -- [out std_logic]

    -- Unused
    Syndrome <= (others => '0');
    UE       <= '0';
    CE       <= '0';
  end generate Encode_Bits;

  --------------------------------------------------------------------------------------------------
  -- Decode bits to get syndrome and UE/CE signals
  --------------------------------------------------------------------------------------------------
  Decode_Bits : if (not C_ENCODE) generate
    signal syndrome_i  : std_logic_vector(0 to 6);
    signal chk0_1 : std_logic_vector(0 to 3);
    signal chk1_1 : std_logic_vector(0 to 3);
    signal chk2_1 : std_logic_vector(0 to 3);
    signal data_chk3_i : std_logic_vector(0 to 15);
    signal chk3_1 : std_logic_vector(0 to 1);
    signal data_chk4_i : std_logic_vector(0 to 15);
    signal chk4_1 : std_logic_vector(0 to 1);
    signal data_chk5_i : std_logic_vector(0 to 6);
    signal data_chk6   : std_logic_vector(0 to 38);
    signal chk6_1 : std_logic_vector(0 to 5);

    signal syndrome_3_to_5       : std_logic_vector(3 to 5);
    signal syndrome_3_to_5_multi : std_logic;
    signal syndrome_3_to_5_zero  : std_logic;
    signal ue_i_0 : std_logic;
    signal ue_i_1 : std_logic;

  begin
    ------------------------------------------------------------------------------------------------
    -- Syndrome bit 0 built up from 3 LUT6 and 1 LUT4
    ------------------------------------------------------------------------------------------------
    chk0_1(3) <= CheckIn(0);
    Parity_chk0_1 : Parity
      generic map (C_TARGET => C_TARGET, C_SIZE => 6)
      port map (
        InA                   => data_chk0(0 to 5),  -- [in  std_logic_vector(0 to C_SIZE - 1)]
        Res                   => chk0_1(0));  -- [out std_logic]
    Parity_chk0_2 : Parity
      generic map (C_TARGET => C_TARGET, C_SIZE => 6)
      port map (
        InA                   => data_chk0(6 to 11),  -- [in  std_logic_vector(0 to C_SIZE - 1)]
        Res                   => chk0_1(1));  -- [out std_logic]
    Parity_chk0_3 : Parity
      generic map (C_TARGET => C_TARGET, C_SIZE => 6)
      port map (
        InA                   => data_chk0(12 to 17),  -- [in  std_logic_vector(0 to C_SIZE - 1)]
        Res                   => chk0_1(2));  -- [out std_logic]
    Parity_chk0_4 : ParityEnable
      generic map (C_TARGET => C_TARGET, C_SIZE => 4)
      port map (
        InA                   => chk0_1,  -- [in  std_logic_vector(0 to C_SIZE - 1)]
        Enable                => Enable_ECC,  -- [in  std_logic]
        Res                   => syndrome_i(0));  -- [out std_logic]

    ------------------------------------------------------------------------------------------------
    -- Syndrome bit 1 built up from 3 LUT6 and 1 LUT4
    ------------------------------------------------------------------------------------------------
    chk1_1(3) <= CheckIn(1);
    Parity_chk1_1 : Parity
      generic map (C_TARGET => C_TARGET, C_SIZE => 6)
      port map (
        InA => data_chk1(0 to 5),       -- [in  std_logic_vector(0 to C_SIZE - 1)]
        Res => chk1_1(0));              -- [out std_logic]
    Parity_chk1_2 : Parity
      generic map (C_TARGET => C_TARGET, C_SIZE => 6)
      port map (
        InA => data_chk1(6 to 11),      -- [in  std_logic_vector(0 to C_SIZE - 1)]
        Res => chk1_1(1));              -- [out std_logic]
    Parity_chk1_3 : Parity
      generic map (C_TARGET => C_TARGET, C_SIZE => 6)
      port map (
        InA => data_chk1(12 to 17),     -- [in  std_logic_vector(0 to C_SIZE - 1)]
        Res => chk1_1(2));              -- [out std_logic]
    Parity_chk1_4 : ParityEnable      
      generic map (C_TARGET => C_TARGET, C_SIZE => 4)
      port map (
        InA => chk1_1,             -- [in  std_logic_vector(0 to C_SIZE - 1)]
        Enable => Enable_ECC,  -- [in  std_logic]
        Res => syndrome_i(1));          -- [out std_logic]

    ------------------------------------------------------------------------------------------------
    -- Syndrome bit 2 built up from 3 LUT6 and 1 LUT4
    ------------------------------------------------------------------------------------------------
    chk2_1(3) <= CheckIn(2);
    Parity_chk2_1 : Parity
      generic map (C_TARGET => C_TARGET, C_SIZE => 6)
      port map (
        InA => data_chk2(0 to 5),       -- [in  std_logic_vector(0 to C_SIZE - 1)]
        Res => chk2_1(0));              -- [out std_logic]
    Parity_chk2_2 : Parity
      generic map (C_TARGET => C_TARGET, C_SIZE => 6)
      port map (
        InA => data_chk2(6 to 11),      -- [in  std_logic_vector(0 to C_SIZE - 1)]
        Res => chk2_1(1));              -- [out std_logic]
    Parity_chk2_3 : Parity
      generic map (C_TARGET => C_TARGET, C_SIZE => 6)
      port map (
        InA => data_chk2(12 to 17),     -- [in  std_logic_vector(0 to C_SIZE - 1)]
        Res => chk2_1(2));              -- [out std_logic]
    Parity_chk2_4 : ParityEnable
      generic map (C_TARGET => C_TARGET, C_SIZE => 4)
      port map (
        InA => chk2_1,             -- [in  std_logic_vector(0 to C_SIZE - 1)]
        Enable => Enable_ECC,  -- [in  std_logic]
        Res => syndrome_i(2));          -- [out std_logic]

    ------------------------------------------------------------------------------------------------
    -- Syndrome bit 3 built up from 2 LUT8 and 1 LUT2
    ------------------------------------------------------------------------------------------------
    data_chk3_i <= data_chk3 & CheckIn(3);
    Parity_chk3_1 : Parity
      generic map (C_TARGET => C_TARGET, C_SIZE => 8)
      port map (
        InA => data_chk3_i(0 to 7),       -- [in  std_logic_vector(0 to C_SIZE - 1)]
        Res => chk3_1(0));              -- [out std_logic]
    Parity_chk3_2 : Parity
      generic map (C_TARGET => C_TARGET, C_SIZE => 8)
      port map (
        InA => data_chk3_i(8 to 15),      -- [in  std_logic_vector(0 to C_SIZE - 1)]
        Res => chk3_1(1));              -- [out std_logic]
    Parity_chk3_3 : ParityEnable
      generic map (C_TARGET => C_TARGET, C_SIZE => 2)
      port map (
        InA => chk3_1,                  -- [in  std_logic_vector(0 to C_SIZE - 1)]
        Enable => Enable_ECC,  -- [in  std_logic]
        Res => syndrome_i(3));              -- [out std_logic]

    ------------------------------------------------------------------------------------------------
    -- Syndrome bit 4 built up from 2 LUT8 and 1 LUT2
    ------------------------------------------------------------------------------------------------
    data_chk4_i <= data_chk4 & CheckIn(4);
    Parity_chk4_1 : Parity
      generic map (C_TARGET => C_TARGET, C_SIZE => 8)
      port map (
        InA => data_chk4_i(0 to 7),       -- [in  std_logic_vector(0 to C_SIZE - 1)]
        Res => chk4_1(0));              -- [out std_logic]
    Parity_chk4_2 : Parity
      generic map (C_TARGET => C_TARGET, C_SIZE => 8)
      port map (
        InA => data_chk4_i(8 to 15),      -- [in  std_logic_vector(0 to C_SIZE - 1)]
        Res => chk4_1(1));              -- [out std_logic]
    Parity_chk4_3 : Parity
      generic map (C_TARGET => C_TARGET, C_SIZE => 2)
      port map (
        InA => chk4_1,                  -- [in  std_logic_vector(0 to C_SIZE - 1)]
        Res => syndrome_i(4));              -- [out std_logic]


    ------------------------------------------------------------------------------------------------
    -- Syndrome bit 5 built up from 1 LUT7
    ------------------------------------------------------------------------------------------------
    data_chk5_i <= data_chk5 & CheckIn(5);
    Parity_chk5_1 : Parity
      generic map (C_TARGET => C_TARGET, C_SIZE => 7)
      port map (
        InA => data_chk5_i,             -- [in  std_logic_vector(0 to C_SIZE - 1)]
        Res => syndrome_i(5));          -- [out std_logic]
    
    ------------------------------------------------------------------------------------------------
    -- Syndrome bit 6 built up from 3 LUT7 and 4 LUT6
    ------------------------------------------------------------------------------------------------
    data_chk6 <= DataIn(0) & DataIn(1) & DataIn(2) & DataIn(3) & DataIn(4) & DataIn(5) & DataIn(6) & DataIn(7) &
                 DataIn(8) & DataIn(9) & DataIn(10) & DataIn(11) & DataIn(12) & DataIn(13) & DataIn(14) &
                 DataIn(15) & DataIn(16) & DataIn(17) & DataIn(18) & DataIn(19) & DataIn(20) & DataIn(21) &
                 DataIn(22) & DataIn(23) & DataIn(24) & DataIn(25) & DataIn(26) & DataIn(27) & DataIn(28) &
                 DataIn(29) & DataIn(30) & DataIn(31) & CheckIn(5) & CheckIn(4) & CheckIn(3) & CheckIn(2) &
                 CheckIn(1) & CheckIn(0) & CheckIn(6);
    Parity_chk6_1 : Parity
      generic map (C_TARGET => C_TARGET, C_SIZE => 6)
      port map (
        InA => data_chk6(0 to 5),       -- [in  std_logic_vector(0 to C_SIZE - 1)]
        Res => chk6_1(0));              -- [out std_logic]
    Parity_chk6_2 : Parity
      generic map (C_TARGET => C_TARGET, C_SIZE => 6)
      port map (
        InA => data_chk6(6 to 11),      -- [in  std_logic_vector(0 to C_SIZE - 1)]
        Res => chk6_1(1));              -- [out std_logic]
    Parity_chk6_3 : Parity
      generic map (C_TARGET => C_TARGET, C_SIZE => 6)
      port map (
        InA => data_chk6(12 to 17),     -- [in  std_logic_vector(0 to C_SIZE - 1)]
        Res => chk6_1(2));              -- [out std_logic]
    Parity_chk6_4 : Parity
      generic map (C_TARGET => C_TARGET, C_SIZE => 7)
      port map (
        InA => data_chk6(18 to 24),     -- [in  std_logic_vector(0 to C_SIZE - 1)]
        Res => chk6_1(3));              -- [out std_logic]
    Parity_chk6_5 : Parity
      generic map (C_TARGET => C_TARGET, C_SIZE => 7)
      port map (
        InA => data_chk6(25 to 31),     -- [in  std_logic_vector(0 to C_SIZE - 1)]
        Res => chk6_1(4));              -- [out std_logic]
    Parity_chk6_6 : Parity
      generic map (C_TARGET => C_TARGET, C_SIZE => 7)
      port map (
        InA => data_chk6(32 to 38),     -- [in  std_logic_vector(0 to C_SIZE - 1)]
        Res => chk6_1(5));              -- [out std_logic]
    Parity_chk6_7 : Parity
      generic map (C_TARGET => C_TARGET, C_SIZE => 6)
      port map (
        InA => chk6_1,             -- [in  std_logic_vector(0 to C_SIZE - 1)]
        Res => syndrome_i(6));          -- [out std_logic]

    Syndrome <= syndrome_i;
    
    syndrome_3_to_5 <= (chk3_1(0) xor chk3_1(1)) & (chk4_1(0) xor chk4_1(1)) & syndrome_i(5);
    syndrome_3_to_5_zero <= '1' when syndrome_3_to_5 = "000" else '0';
    syndrome_3_to_5_multi <= '1' when (syndrome_3_to_5 = "111" or
                                       syndrome_3_to_5 = "011" or
                                       syndrome_3_to_5 = "101") else
                             '0';

    CE <= '0' when (Enable_ECC = '0') else
          (syndrome_i(6) or CE_Q) when (syndrome_3_to_5_multi = '0') else
          CE_Q;

    ue_i_0 <= '0' when (Enable_ECC = '0') else
              '1' when (syndrome_3_to_5_zero = '0') or (syndrome_i(0 to 2) /= "000") else
              UE_Q;
    ue_i_1 <= '0' when (Enable_ECC = '0') else
              (syndrome_3_to_5_multi or UE_Q);

    Use_FPGA: if (C_TARGET /= RTL) generate
      UE_MUXF7 : MB_MUXF7
        generic map (
          C_TARGET => C_TARGET)
        port map (
          I0 => ue_i_0,
          I1 => ue_i_1,
          S  => syndrome_i(6),
          O  => UE);      
    end generate Use_FPGA;

    Use_RTL: if (C_TARGET = RTL) generate
      UE <= ue_i_1 when syndrome_i(6) = '1' else ue_i_0;
    end generate Use_RTL;

    -- Unused
    CheckOut <= (others => '0');
  end generate Decode_Bits;

end architecture IMP;


-------------------------------------------------------------------------------
-- correct_one_bit.vhd - Entity and architecture
-------------------------------------------------------------------------------
--
-- (c) Copyright [2003] - [2015] Xilinx, Inc. All rights reserved.
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
-- PART OF THIS FILE AT ALL TIMES
--
------------------------------------------------------------------------------
-- Filename:        correct_one_bit.vhd
--
-- Description:
--
-- VHDL-Standard:   VHDL'93
-------------------------------------------------------------------------------
-- Structure:
--              correct_one_bit
-------------------------------------------------------------------------------
-- Author:          rolandp
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

library lmb_bram_if_cntlr_v4_0_14;
use lmb_bram_if_cntlr_v4_0_14.all;
use lmb_bram_if_cntlr_v4_0_14.lmb_bram_if_funcs.all;

entity Correct_One_Bit is
  generic (
    C_TARGET      : TARGET_FAMILY_TYPE;
    Correct_Value : std_logic_vector(0 to 6));
  port (
    DIn      : in  std_logic;
    Syndrome : in  std_logic_vector(0 to 6);
    DCorr    : out std_logic);
end entity Correct_One_Bit;

architecture IMP of Correct_One_Bit is

  component MB_MUXCY is
  generic (
    C_TARGET : TARGET_FAMILY_TYPE
  );
  port (
    LO : out std_logic;
    CI : in  std_logic;
    DI : in  std_logic;
    S  : in  std_logic
  );
  end component MB_MUXCY;

  component MB_XORCY is
  generic (
    C_TARGET : TARGET_FAMILY_TYPE
  );
  port (
    O  : out std_logic;
    CI : in  std_logic;
    LI : in  std_logic
  );
  end component MB_XORCY;

  -----------------------------------------------------------------------------
  -- Find which bit that has a '1'
  -- There is always one bit which has a '1'
  -----------------------------------------------------------------------------
  function find_one (Syn : std_logic_vector(0 to 6)) return natural is
  begin  -- function find_one
    for I in 0 to 6 loop
      if (Syn(I) = '1') then
        return I;
      end if;
    end loop;  -- I
    return 0;                           -- Should never reach this statement
  end function find_one;

  constant di_index : natural := find_one(Correct_Value);

  signal corr_sel : std_logic;
  signal corr_c   : std_logic;
  signal lut_compare  : std_logic_vector(0 to 5);
  signal lut_corr_val : std_logic_vector(0 to 5);
begin  -- architecture IMP

  Remove_DI_Index : process (Syndrome) is
  begin  -- process Remove_DI_Index
    if (di_index = 0) then
      lut_compare  <= Syndrome(1 to 6);
      lut_corr_val <= Correct_Value(1 to 6);
    elsif (di_index = 6) then
      lut_compare  <= Syndrome(0 to 5);
      lut_corr_val <= Correct_Value(0 to 5);
    else
      lut_compare  <= Syndrome(0 to di_index-1) & Syndrome(di_index+1 to 6);
      lut_corr_val <= Correct_Value(0 to di_index-1) & Correct_Value(di_index+1 to 6);
    end if;
  end process Remove_DI_Index;

  corr_sel <= '0' when lut_compare = lut_corr_val else '1';
  
  Corr_MUXCY : MB_MUXCY
    generic map(
      C_TARGET => C_TARGET)
    port map (
      DI => Syndrome(di_index),
      CI => '0',
      S  => corr_sel,
      LO => corr_c);

  Corr_XORCY : MB_XORCY
    generic map(
      C_TARGET => C_TARGET)
    port map (
      LI => DIn,
      CI => corr_c,
      O  => DCorr);

end architecture IMP;


-------------------------------------------------------------------------------
-- pselect_mask.vhd - Entity and architecture
-------------------------------------------------------------------------------
--
-- (c) Copyright [2003] - [2015] Xilinx, Inc. All rights reserved.
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
-- PART OF THIS FILE AT ALL TIMES
--
------------------------------------------------------------------------------
-- Filename:        pselect_mask.vhd
--
-- Description:     
--                  
-- VHDL-Standard:   VHDL'93
-------------------------------------------------------------------------------
-- Structure:   
--              pselect_mask.vhd
--
-------------------------------------------------------------------------------
-- Author:          goran
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
use IEEE.std_logic_unsigned.all;

entity pselect_mask is

  generic (
    C_AW   : integer                   := 32;
    C_BAR  : std_logic_vector(0 to 63) := X"0000000000020000";
    C_MASK : std_logic_vector(0 to 63) := X"000000000007C000"
    );
  port (
    A     : in  std_logic_vector(0 to C_AW-1);
    Valid : in  std_logic;
    CS    : out std_logic
    );

end entity pselect_mask;

architecture imp of pselect_mask is

  function Nr_Of_Ones (S : std_logic_vector) return natural is
    variable tmp : natural := 0;
  begin  -- function Nr_Of_Ones
    for I in S'range loop
      if (S(I) = '1') then
        tmp := tmp + 1;
      end if;
    end loop;  -- I
    return tmp;
  end function Nr_Of_Ones;

  function fix_AB (B : boolean; I : integer) return integer is
  begin  -- function fix_AB
    if (not B) then
      return I + 1;
    else
      return I;
    end if;
  end function fix_AB;

  constant Nr      : integer := Nr_Of_Ones(C_MASK(64 - C_AW to 63));
  constant Use_CIN : boolean := ((Nr mod 4) = 0);
  constant AB      : integer := fix_AB(Use_CIN, Nr);
  
  signal A_Bus : std_logic_vector(0 to AB);
  signal BAR   : std_logic_vector(0 to AB);

-------------------------------------------------------------------------------
-- Begin architecture section
-------------------------------------------------------------------------------
begin  -- VHDL_RTL

  Make_Busses : process (A,Valid) is
    variable tmp : natural;
  begin  -- process Make_Busses
    tmp   := 0;
    A_Bus <= (others => '0');
    BAR   <= (others => '0');
    for I in 0 to C_AW - 1 loop
      if (C_MASK(64 - C_AW + I) = '1') then
        A_Bus(tmp) <= A(I);
        BAR(tmp)   <= C_BAR(64 - C_AW + I);
        tmp        := tmp + 1;
      end if;
    end loop;  -- I
    if (not Use_CIN) then
      BAR(tmp) <= '1';
      A_Bus(tmp) <= Valid;
    end if;
  end process Make_Busses;

  CS <= Valid when A_Bus=BAR else '0';

end imp;


-------------------------------------------------------------------------------
-- axi_interface.vhd - Entity and architecture
-------------------------------------------------------------------------------
--
-- (c) Copyright 2003-2015 Xilinx, Inc. All rights reserved.
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
-- Filename:        axi_interface.vhd
--
-- Description:     
--                  
-- VHDL-Standard:   VHDL'93
-------------------------------------------------------------------------------
-- Structure:   
--              axi_interface.vhd
--
-------------------------------------------------------------------------------
-- Author:          rolandp
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

library lmb_bram_if_cntlr_v4_0_14;
use lmb_bram_if_cntlr_v4_0_14.all;
use lmb_bram_if_cntlr_v4_0_14.lmb_bram_if_funcs.all;

entity axi_interface is
  generic (
    C_TARGET                : TARGET_FAMILY_TYPE;
    -- AXI4-Lite slave generics
    C_S_AXI_BASEADDR        : std_logic_vector       := X"FFFF_FFFF";
    C_S_AXI_HIGHADDR        : std_logic_vector       := X"0000_0000";
    C_S_AXI_ADDR_WIDTH      : integer                := 32;
    C_S_AXI_DATA_WIDTH      : integer                := 32;
    C_REGADDR_WIDTH         : integer                := 5;    -- Address bits including register offset.
    C_DWIDTH                : integer                := 32);  -- Width of data bus.
  port (
    LMB_Clk : in std_logic;
    LMB_Rst : in std_logic;

    -- AXI4-Lite SLAVE SINGLE INTERFACE
    S_AXI_AWADDR  : in  std_logic_vector(C_S_AXI_ADDR_WIDTH-1 downto 0);
    S_AXI_AWVALID : in  std_logic;
    S_AXI_AWREADY : out std_logic;
    S_AXI_WDATA   : in  std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0);
    S_AXI_WSTRB   : in  std_logic_vector((C_S_AXI_DATA_WIDTH/8)-1 downto 0);
    S_AXI_WVALID  : in  std_logic;
    S_AXI_WREADY  : out std_logic;
    S_AXI_BRESP   : out std_logic_vector(1 downto 0);
    S_AXI_BVALID  : out std_logic;
    S_AXI_BREADY  : in  std_logic;
    S_AXI_ARADDR  : in  std_logic_vector(C_S_AXI_ADDR_WIDTH-1 downto 0);
    S_AXI_ARVALID : in  std_logic;
    S_AXI_ARREADY : out std_logic;
    S_AXI_RDATA   : out std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0);
    S_AXI_RRESP   : out std_logic_vector(1 downto 0);
    S_AXI_RVALID  : out std_logic;
    S_AXI_RREADY  : in  std_logic;
    
    -- lmb_bram_if_cntlr signals
    RegWr         : out std_logic;
    RegWrData     : out std_logic_vector(0 to C_DWIDTH - 1);
    RegAddr       : out std_logic_vector(0 to C_REGADDR_WIDTH-1);  
    RegRdData     : in  std_logic_vector(0 to C_DWIDTH - 1));
end entity axi_interface;

architecture IMP of axi_interface is

  component MB_FDRE is
  generic (
    C_TARGET : TARGET_FAMILY_TYPE;
    INIT : bit := '0'
  );
  port(
    Q  : out std_logic;
    C  : in  std_logic;
    CE : in  std_logic;
    D  : in  std_logic;
    R  : in  std_logic
  );
  end component MB_FDRE;
  
  -----------------------------------------------------------------------------
  -- Signal declaration
  -----------------------------------------------------------------------------
  signal new_write_access       : std_logic;
  signal new_read_access        : std_logic;
  signal ongoing_write          : std_logic;
  signal ongoing_read           : std_logic;

  signal S_AXI_RVALID_i         : std_logic;

  signal RegRdData_i            : std_logic_vector(C_DWIDTH - 1 downto 0);

begin  -- architecture IMP

  -----------------------------------------------------------------------------
  -- Handling the AXI4-Lite bus interface (AR/AW/W)
  -----------------------------------------------------------------------------
  
  -- Detect new transaction.
  -- Only allow one access at a time
  new_write_access  <= not (ongoing_read or ongoing_write) and S_AXI_AWVALID and S_AXI_WVALID;
  new_read_access   <= not (ongoing_read or ongoing_write) and S_AXI_ARVALID and not new_write_access;

  -- Acknowledge new transaction.
  S_AXI_AWREADY <= new_write_access;
  S_AXI_WREADY  <= new_write_access;
  S_AXI_ARREADY <= new_read_access;

  -- Store register address and write data 
  Reg: process (LMB_Clk) is
  begin
    if LMB_Clk'event and LMB_Clk = '1' then
      if LMB_Rst = '1' then
        RegAddr   <= (others => '0');
        RegWrData <= (others => '0');
      elsif new_write_access = '1' then
        RegAddr   <= S_AXI_AWADDR(C_REGADDR_WIDTH-1+2 downto 2);
        RegWrData <= S_AXI_WDATA(C_DWIDTH-1 downto 0);
      elsif new_read_access = '1' then
        RegAddr   <= S_AXI_ARADDR(C_REGADDR_WIDTH-1+2 downto 2);
      end if;
    end if;
  end process Reg;
  
  -- Handle write access.
  WriteAccess: process (LMB_Clk) is
  begin
    if LMB_Clk'event and LMB_Clk = '1' then
      if LMB_Rst = '1' then
        ongoing_write <= '0';
      elsif new_write_access = '1' then
        ongoing_write <= '1';
      elsif ongoing_write = '1' and S_AXI_BREADY = '1' then
        ongoing_write <= '0';
      end if;
      RegWr <= new_write_access;
    end if;
  end process WriteAccess;

  S_AXI_BVALID <= ongoing_write;
  S_AXI_BRESP  <= (others => '0');

  -- Handle read access
  ReadAccess: process (LMB_Clk) is
  begin
    if LMB_Clk'event and LMB_Clk = '1' then
      if LMB_Rst = '1' then
        ongoing_read   <= '0';
        S_AXI_RVALID_i <= '0';
      elsif new_read_access = '1' then
        ongoing_read   <= '1';
        S_AXI_RVALID_i <= '0';
      elsif ongoing_read = '1' then
        if S_AXI_RREADY = '1' and S_AXI_RVALID_i = '1' then
          ongoing_read   <= '0';
          S_AXI_RVALID_i <= '0';
        else
          S_AXI_RVALID_i <= '1'; -- Asserted one cycle after ongoing_read to match S_AXI_RDDATA
        end if;
      end if;
    end if;
  end process ReadAccess;

  S_AXI_RVALID <= S_AXI_RVALID_i;
  S_AXI_RRESP  <= (others => '0');
  
  Not_All_Bits_Are_Used: if (C_DWIDTH < C_S_AXI_DATA_WIDTH) generate
  begin
    S_AXI_RDATA(C_S_AXI_DATA_WIDTH-1 downto C_S_AXI_DATA_WIDTH - C_DWIDTH)  <= (others=>'0');
  end generate Not_All_Bits_Are_Used;

  RegRdData_i <= RegRdData;             -- Swap to - downto
  
  S_AXI_RDATA_DFF : for I in C_DWIDTH - 1 downto 0 generate
  begin
    S_AXI_RDATA_FDRE : MB_FDRE
      generic map (
        C_TARGET => C_TARGET)
      port map (
        Q  => S_AXI_RDATA(I),
        C  => LMB_Clk,
        CE => ongoing_read,
        D  => RegRdData_i(I),
        R  => LMB_Rst);
  end generate S_AXI_RDATA_DFF;
  
end architecture IMP;


-------------------------------------------------------------------------------
-- lmb_mux.vhd - Entity and architecture
-------------------------------------------------------------------------------
--
-- (c) Copyright [2003] - [2015] Xilinx, Inc. All rights reserved.
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
-- PART OF THIS FILE AT ALL TIMES
--
------------------------------------------------------------------------------
-- Filename:        lmb_mux.vhd
--
-- Description:     
--                  
-- VHDL-Standard:   VHDL'93
-------------------------------------------------------------------------------
-- Structure:   
--              lmb_mux.vhd
--                pselct_mask.vhd
--
-------------------------------------------------------------------------------
-- Author:          rolandp
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
use IEEE.std_logic_unsigned.all;

library lmb_bram_if_cntlr_v4_0_14;
use lmb_bram_if_cntlr_v4_0_14.all;
use lmb_bram_if_cntlr_v4_0_14.lmb_bram_if_funcs.all;

entity lmb_mux is
  generic (
    C_TARGET     : TARGET_FAMILY_TYPE;
    C_BASEADDR   : std_logic_vector(0 to 63) := X"FFFFFFFFFFFFFFFF";
    C_MASK       : std_logic_vector(0 to 63) := X"0000000000800000";
    C_MASK1      : std_logic_vector(0 to 63) := X"0000000000800000";
    C_MASK2      : std_logic_vector(0 to 63) := X"0000000000800000";
    C_MASK3      : std_logic_vector(0 to 63) := X"0000000000800000";
    C_LMB_AWIDTH : integer                   := 32;
    C_LMB_DWIDTH : integer                   := 32;
    C_ECC        : integer                   := 0;
    C_NUM_LMB    : integer                   := 1);
  port (
    LMB_Clk : in std_logic := '0';
    LMB_Rst : in std_logic := '0';

    -- LMB Bus 0
    LMB0_ABus        : in  std_logic_vector(0 to C_LMB_AWIDTH-1);
    LMB0_WriteDBus   : in  std_logic_vector(0 to C_LMB_DWIDTH-1);
    LMB0_AddrStrobe  : in  std_logic;
    LMB0_ReadStrobe  : in  std_logic;
    LMB0_WriteStrobe : in  std_logic;
    LMB0_BE          : in  std_logic_vector(0 to (C_LMB_DWIDTH/8 - 1));
    Sl0_DBus         : out std_logic_vector(0 to C_LMB_DWIDTH-1);
    Sl0_Ready        : out std_logic;
    Sl0_Wait         : out std_logic;
    Sl0_UE           : out std_logic;
    Sl0_CE           : out std_logic;

    -- LMB Bus 1
    LMB1_ABus        : in  std_logic_vector(0 to C_LMB_AWIDTH-1);
    LMB1_WriteDBus   : in  std_logic_vector(0 to C_LMB_DWIDTH-1);
    LMB1_AddrStrobe  : in  std_logic;
    LMB1_ReadStrobe  : in  std_logic;
    LMB1_WriteStrobe : in  std_logic;
    LMB1_BE          : in  std_logic_vector(0 to (C_LMB_DWIDTH/8 - 1));
    Sl1_DBus         : out std_logic_vector(0 to C_LMB_DWIDTH-1);
    Sl1_Ready        : out std_logic;
    Sl1_Wait         : out std_logic;
    Sl1_UE           : out std_logic;
    Sl1_CE           : out std_logic;

    -- LMB Bus 2
    LMB2_ABus        : in  std_logic_vector(0 to C_LMB_AWIDTH-1);
    LMB2_WriteDBus   : in  std_logic_vector(0 to C_LMB_DWIDTH-1);
    LMB2_AddrStrobe  : in  std_logic;
    LMB2_ReadStrobe  : in  std_logic;
    LMB2_WriteStrobe : in  std_logic;
    LMB2_BE          : in  std_logic_vector(0 to (C_LMB_DWIDTH/8 - 1));
    Sl2_DBus         : out std_logic_vector(0 to C_LMB_DWIDTH-1);
    Sl2_Ready        : out std_logic;
    Sl2_Wait         : out std_logic;
    Sl2_UE           : out std_logic;
    Sl2_CE           : out std_logic;

    -- LMB Bus 3
    LMB3_ABus        : in  std_logic_vector(0 to C_LMB_AWIDTH-1);
    LMB3_WriteDBus   : in  std_logic_vector(0 to C_LMB_DWIDTH-1);
    LMB3_AddrStrobe  : in  std_logic;
    LMB3_ReadStrobe  : in  std_logic;
    LMB3_WriteStrobe : in  std_logic;
    LMB3_BE          : in  std_logic_vector(0 to (C_LMB_DWIDTH/8 - 1));
    Sl3_DBus         : out std_logic_vector(0 to C_LMB_DWIDTH-1);
    Sl3_Ready        : out std_logic;
    Sl3_Wait         : out std_logic;
    Sl3_UE           : out std_logic;
    Sl3_CE           : out std_logic;
    
    -- Muxed LMB Bus
    LMB_ABus        : out std_logic_vector(0 to C_LMB_AWIDTH-1);
    LMB_WriteDBus   : out std_logic_vector(0 to C_LMB_DWIDTH-1);
    LMB_WriteECC    : out std_logic_vector(0 to 6);
    LMB_AddrStrobe  : out std_logic;
    LMB_ReadStrobe  : out std_logic;
    LMB_WriteStrobe : out std_logic;
    IsWordWrite     : out std_logic;
    LMB_BE          : out std_logic_vector(0 to (C_LMB_DWIDTH/8 - 1));
    Sl_DBus         : in  std_logic_vector(0 to C_LMB_DWIDTH-1);
    Sl_Ready        : in  std_logic;
    Sl_Wait         : in  std_logic;
    Sl_UE           : in  std_logic;
    Sl_CE           : in  std_logic;

    lmb_select      : out std_logic);
end entity lmb_mux;

architecture imp of lmb_mux is

  component pselect_mask
    generic (
      C_AW   : integer                   := 32;
      C_BAR  : std_logic_vector(0 to 63) := X"0000000000000000";
      C_MASK : std_logic_vector(0 to 63) := X"0000000000800000");
    port (
      A     : in  std_logic_vector(0 to C_AW - 1);
      CS    : out std_logic;
      Valid : in  std_logic);
  end component;

  component checkbit_handler is
    generic (
      C_TARGET   : TARGET_FAMILY_TYPE;
      C_ENCODE   : boolean);
    port (
      DataIn     : in  std_logic_vector(0 to 31);
      CheckIn    : in  std_logic_vector(0 to 6);
      CheckOut   : out std_logic_vector(0 to 6);
      Syndrome   : out std_logic_vector(0 to 6);
      Enable_ECC : in  std_logic;
      UE_Q       : in  std_logic;
      CE_Q       : in  std_logic;
      UE         : out std_logic;
      CE         : out std_logic);
  end component checkbit_handler;

  signal one : std_logic;

-------------------------------------------------------------------------------
-- Begin architecture section
-------------------------------------------------------------------------------
begin  -- VHDL_RTL

  LMB1_no: if (C_NUM_LMB < 2) generate
    Sl1_DBus               <= (others => '0');
    Sl1_Ready              <= '0';
    Sl1_Wait               <= '0';
    Sl1_UE                 <= '0';
    Sl1_CE                 <= '0';
  end generate LMB1_no;
  
  LMB2_no: if (C_NUM_LMB < 3) generate
    Sl2_DBus               <= (others => '0');
    Sl2_Ready              <= '0';
    Sl2_Wait               <= '0';
    Sl2_UE                 <= '0';
    Sl2_CE                 <= '0';
  end generate LMB2_no;

  LMB3_no: if (C_NUM_LMB < 4) generate
    Sl3_DBus               <= (others => '0');
    Sl3_Ready              <= '0';
    Sl3_Wait               <= '0';
    Sl3_UE                 <= '0';
    Sl3_CE                 <= '0';
  end generate LMB3_no;
    
  one <= '1';

  one_lmb: if (C_NUM_LMB = 1) generate
  begin
    
    -----------------------------------------------------------------------------
    -- Do the LMB address decoding
    -----------------------------------------------------------------------------
    pselect_mask_lmb : pselect_mask
      generic map (
        C_AW   => LMB_ABus'length,
        C_BAR  => C_BASEADDR,
        C_MASK => C_MASK)
      port map (
        A     => LMB0_ABus,
        CS    => lmb_select,
        Valid => one);

    LMB_ABus        <= LMB0_ABus;
    LMB_WriteDBus   <= LMB0_WriteDBus;
    LMB_WriteECC    <= (others => '0');
    LMB_AddrStrobe  <= LMB0_AddrStrobe;
    LMB_ReadStrobe  <= LMB0_ReadStrobe;
    LMB_WriteStrobe <= LMB0_WriteStrobe;
    IsWordWrite     <= LMB0_WriteStrobe when (LMB0_BE = "1111") else '0';
    LMB_BE          <= LMB0_BE;
    Sl0_DBus        <= Sl_DBus;
    Sl0_Ready       <= Sl_Ready;
    Sl0_Wait        <= Sl_Wait;
    Sl0_UE          <= Sl_UE;
    Sl0_CE          <= Sl_CE;

  end generate one_lmb;

  more_than_one_lmb: if (C_NUM_LMB > 1) generate

    type C_Mask_Vec_T is array (0 to 3) of std_logic_vector(0 to 63);
    constant C_Mask_Vec : C_MASK_Vec_T := (C_MASK, C_MASK1, C_MASK2, C_MASK3);

    type ABus_vec_T  is array (0 to C_NUM_LMB-1) of std_logic_vector(0 to C_LMB_AWIDTH - 1); 
    type DBus_vec_T  is array (0 to C_NUM_LMB-1) of std_logic_vector(0 to C_LMB_DWIDTH - 1); 
    type ECC_vec_T   is array (0 to C_NUM_LMB-1) of std_logic_vector(0 to 6); 
    type BE_vec_T    is array (0 to C_NUM_LMB-1) of std_logic_vector(0 to C_LMB_DWIDTH/8 - 1);
  
    signal LMB_ABus_vec          : ABus_vec_T;
    signal LMB_ABus_vec_i        : ABus_vec_T;
    signal LMB_ABus_vec_Q        : ABus_vec_T;
    signal LMB_WriteDBus_vec     : DBus_vec_T;
    signal LMB_WriteDBus_vec_i   : DBus_vec_T;
    signal LMB_WriteDBus_vec_Q   : DBus_vec_T;
    signal LMB_WriteECC_vec      : ECC_vec_T;
    signal LMB_WriteECC_vec_i    : ECC_vec_T;
    signal LMB_WriteECC_vec_Q    : ECC_vec_T;
    signal LMB_AddrStrobe_vec    : std_logic_vector(0 to C_NUM_LMB-1);
    signal LMB_AddrStrobe_vec_i  : std_logic_vector(0 to C_NUM_LMB-1);
    signal LMB_AddrStrobe_vec_Q  : std_logic_vector(0 to C_NUM_LMB-1);
    signal LMB_ReadStrobe_vec    : std_logic_vector(0 to C_NUM_LMB-1);
    signal LMB_ReadStrobe_vec_i  : std_logic_vector(0 to C_NUM_LMB-1);
    signal LMB_ReadStrobe_vec_Q  : std_logic_vector(0 to C_NUM_LMB-1);
    signal LMB_WriteStrobe_vec   : std_logic_vector(0 to C_NUM_LMB-1);
    signal LMB_WriteStrobe_vec_i : std_logic_vector(0 to C_NUM_LMB-1);
    signal LMB_WriteStrobe_vec_Q : std_logic_vector(0 to C_NUM_LMB-1);
    signal IsWordWrite_vec       : std_logic_vector(0 to C_NUM_LMB-1);
    signal IsWordWrite_vec_i     : std_logic_vector(0 to C_NUM_LMB-1);
    signal IsWordWrite_vec_Q     : std_logic_vector(0 to C_NUM_LMB-1);
    signal LMB_BE_vec            : BE_vec_T;
    signal LMB_BE_vec_i          : BE_vec_T;
    signal LMB_BE_vec_Q          : BE_vec_T;
    signal Sl_DBus_vec           : DBus_vec_T;
    signal Sl_Ready_vec          : std_logic_vector(0 to C_NUM_LMB-1);
    signal Sl_Wait_vec           : std_logic_vector(0 to C_NUM_LMB-1);
    signal Sl_UE_vec             : std_logic_vector(0 to C_NUM_LMB-1);
    signal Sl_CE_vec             : std_logic_vector(0 to C_NUM_LMB-1);

    signal wait_vec              : std_logic_vector(0 to C_NUM_LMB-1);
    signal lmb_select_vec        : std_logic_vector(0 to C_NUM_LMB-1);
    signal as_and_lmb_select_vec : std_logic_vector(0 to C_NUM_LMB-1);

    signal ongoing     : natural range 0 to C_NUM_LMB-1;
    signal ongoing_new : natural range 0 to C_NUM_LMB-1;
    signal ongoing_Q   : natural range 0 to C_NUM_LMB-1;

  begin

    LMB_ABus_vec(0)        <= LMB0_ABus;
    LMB_WriteDBus_vec(0)   <= LMB0_WriteDBus;
    LMB_AddrStrobe_vec(0)  <= LMB0_AddrStrobe;
    LMB_ReadStrobe_vec(0)  <= LMB0_ReadStrobe;
    LMB_WriteStrobe_vec(0) <= LMB0_WriteStrobe;
    IsWordWrite_vec(0)     <= LMB0_WriteStrobe when (LMB0_BE = "1111") else '0';
    LMB_BE_vec(0)          <= LMB0_BE;
    Sl0_DBus               <= Sl_DBus_vec(0);
    Sl0_Ready              <= Sl_Ready_vec(0);
    Sl0_Wait               <= Sl_Wait_vec(0);
    Sl0_UE                 <= Sl_UE_vec(0);
    Sl0_CE                 <= Sl_CE_vec(0);

    ECC_lmb0_yes: if (C_ECC = 1) generate
      checkbit_handler_LMB0 : checkbit_handler
        generic map (
          C_TARGET   => C_TARGET,
          C_ENCODE   => true)
        port map (
          DataIn     => LMB_WriteDBus_vec(0),
          CheckIn    => (others => '0'),
          CheckOut   => LMB_WriteECC_vec(0),
          Syndrome   => open,
          Enable_ECC => '1',
          UE_Q       => '0',
          CE_Q       => '0',
          UE         => open,
          CE         => open);
    end generate ECC_lmb0_yes;

    ECC_lmb0_no: if (C_ECC = 0) generate
      LMB_WriteECC_vec(0) <= (others => '0');
    end generate ECC_lmb0_no;

    LMB_ABus_vec(1)        <= LMB1_ABus;
    LMB_WriteDBus_vec(1)   <= LMB1_WriteDBus;
    LMB_AddrStrobe_vec(1)  <= LMB1_AddrStrobe;
    LMB_ReadStrobe_vec(1)  <= LMB1_ReadStrobe;
    LMB_WriteStrobe_vec(1) <= LMB1_WriteStrobe;
    IsWordWrite_vec(1)     <= LMB1_WriteStrobe when (LMB1_BE = "1111") else '0';
    LMB_BE_vec(1)          <= LMB1_BE;
    Sl1_DBus               <= Sl_DBus_vec(1);
    Sl1_Ready              <= Sl_Ready_vec(1);
    Sl1_Wait               <= Sl_Wait_vec(1);
    Sl1_UE                 <= Sl_UE_vec(1);
    Sl1_CE                 <= Sl_CE_vec(1);

    ECC_lmb1_yes: if (C_ECC = 1) generate
      checkbit_handler_LMB1 : checkbit_handler
        generic map (
          C_TARGET   => C_TARGET,
          C_ENCODE   => true)
        port map (
          DataIn     => LMB_WriteDBus_vec(1),
          CheckIn    => (others => '0'),
          CheckOut   => LMB_WriteECC_vec(1),
          Syndrome   => open,
          Enable_ECC => '1',
          UE_Q       => '0',
          CE_Q       => '0',
          UE         => open,
          CE         => open);
    end generate ECC_lmb1_yes;

    ECC_lmb1_no: if (C_ECC = 0) generate
      LMB_WriteECC_vec(1) <= (others => '0');
    end generate ECC_lmb1_no;

    LMB2_yes: if (C_NUM_LMB > 2) generate
      LMB_ABus_vec(2)        <= LMB2_ABus;
      LMB_WriteDBus_vec(2)   <= LMB2_WriteDBus;
      LMB_AddrStrobe_vec(2)  <= LMB2_AddrStrobe;
      LMB_ReadStrobe_vec(2)  <= LMB2_ReadStrobe;
      LMB_WriteStrobe_vec(2) <= LMB2_WriteStrobe;
      IsWordWrite_vec(2)     <= LMB2_WriteStrobe when (LMB2_BE = "1111") else '0';
      LMB_BE_vec(2)          <= LMB2_BE;
      Sl2_DBus               <= Sl_DBus_vec(2);
      Sl2_Ready              <= Sl_Ready_vec(2);
      Sl2_Wait               <= Sl_Wait_vec(2);
      Sl2_UE                 <= Sl_UE_vec(2);
      Sl2_CE                 <= Sl_CE_vec(2);

      ECC_lmb2_yes: if (C_ECC = 1) generate
        checkbit_handler_LMB2 : checkbit_handler
          generic map (
            C_TARGET   => C_TARGET,
            C_ENCODE   => true)
          port map (
            DataIn     => LMB_WriteDBus_vec(2),
            CheckIn    => (others => '0'),
            CheckOut   => LMB_WriteECC_vec(2),
            Syndrome   => open,
            Enable_ECC => '1',
            UE_Q       => '0',
            CE_Q       => '0',
            UE         => open,
            CE         => open); 
      end generate ECC_lmb2_yes;

      ECC_lmb2_no: if (C_ECC = 0) generate
        LMB_WriteECC_vec(2) <= (others => '0');
      end generate ECC_lmb2_no;
     
    end generate LMB2_yes;

    LMB3_yes: if (C_NUM_LMB > 3) generate
      LMB_ABus_vec(3)        <= LMB3_ABus;
      LMB_WriteDBus_vec(3)   <= LMB3_WriteDBus;
      LMB_AddrStrobe_vec(3)  <= LMB3_AddrStrobe;
      LMB_ReadStrobe_vec(3)  <= LMB3_ReadStrobe;
      LMB_WriteStrobe_vec(3) <= LMB3_WriteStrobe;
      IsWordWrite_vec(3)     <= LMB3_WriteStrobe when (LMB3_BE = "1111") else '0';
      LMB_BE_vec(3)          <= LMB3_BE;
      Sl3_DBus               <= Sl_DBus_vec(3);
      Sl3_Ready              <= Sl_Ready_vec(3);
      Sl3_Wait               <= Sl_Wait_vec(3);
      Sl3_UE                 <= Sl_UE_vec(3);
      Sl3_CE                 <= Sl_CE_vec(3);

      ECC_lmb3_yes: if (C_ECC = 1) generate
        checkbit_handler_LMB3 : checkbit_handler
          generic map (
            C_TARGET   => C_TARGET,
            C_ENCODE   => true)
          port map (
            DataIn     => LMB_WriteDBus_vec(3),
            CheckIn    => (others => '0'),
            CheckOut   => LMB_WriteECC_vec(3),
            Syndrome   => open,
            Enable_ECC => '1',
            UE_Q       => '0',
            CE_Q       => '0',
            UE         => open,
            CE         => open);
      end generate ECC_lmb3_yes;

      ECC_lmb3_no: if (C_ECC = 0) generate
        LMB_WriteECC_vec(3) <= (others => '0');
      end generate ECC_lmb3_no;

    end generate LMB3_yes;

    lmb_mux_generate: for I in 0 to C_NUM_LMB-1 generate
    begin

      -----------------------------------------------------------------------------
      -- Do the LMB address decoding
      -----------------------------------------------------------------------------
      pselect_mask_lmb : pselect_mask
        generic map (
          C_AW   => LMB_ABus'length,
          C_BAR  => C_BASEADDR,
          C_MASK => C_Mask_Vec(I))
        port map (
          A     => LMB_ABus_vec(I),
          CS    => lmb_select_vec(I),
          Valid => one);

      as_and_lmb_select_vec(I) <= lmb_select_vec(I) and LMB_AddrStrobe_vec(I);

      remember_access : process (LMB_Clk) is
      begin
        if (LMB_Clk'event and LMB_Clk = '1') then
          if (LMB_Rst = '1') then
            LMB_ABus_vec_Q(I)        <= (others => '0');
            LMB_WriteDBus_vec_Q(I)   <= (others => '0');
            LMB_WriteECC_vec_Q(I)    <= (others => '0');
            LMB_AddrStrobe_vec_Q(I)  <= '0';
            LMB_ReadStrobe_vec_Q(I)  <= '0';
            LMB_WriteStrobe_vec_Q(I) <= '0';
            IsWordWrite_vec_Q(I)     <= '0';
            LMB_BE_vec_Q(I)          <= (others => '0');
          elsif (as_and_lmb_select_vec(I) = '1' and ongoing /= I) then
            LMB_ABus_vec_Q(I)        <= LMB_ABus_vec(I);
            LMB_WriteDBus_vec_Q(I)   <= LMB_WriteDBus_vec(I);
            LMB_WriteECC_vec_Q(I)    <= LMB_WriteECC_vec(I);
            LMB_AddrStrobe_vec_Q(I)  <= LMB_AddrStrobe_vec(I);
            LMB_ReadStrobe_vec_Q(I)  <= LMB_ReadStrobe_vec(I);
            LMB_WriteStrobe_vec_Q(I) <= LMB_WriteStrobe_vec(I);
            IsWordWrite_vec_Q(I)     <= IsWordWrite_vec(I);
            LMB_BE_vec_Q(I)          <= LMB_BE_vec(I);
          end if;
        end if;
      end process remember_access;

      wait_proc : process (LMB_Clk) is
      begin
        if (LMB_Clk'event and LMB_Clk = '1') then
          if (LMB_Rst = '1') then
            wait_vec(I) <= '0';
          elsif (as_and_lmb_select_vec(I) = '1' and ongoing /= I) then
            wait_vec(I) <= '1';
          elsif (wait_vec(I) = '1' and ongoing = I) then
            wait_vec(I) <= '0';
          end if;
        end if;
      end process wait_proc;

      LMB_ABus_vec_i(I)        <= LMB_ABus_vec_Q(I) when wait_vec(I) = '1' else
                                  LMB_ABus_vec(I);
      LMB_WriteDBus_vec_i(I)   <= LMB_WriteDBus_vec_Q(I) when wait_vec(I) = '1' else
                                  LMB_WriteDBus_vec(I);
      LMB_WriteECC_vec_i(I)    <= LMB_WriteECC_vec_Q(I) when wait_vec(I) = '1' else
                                  LMB_WriteECC_vec(I);
      LMB_AddrStrobe_vec_i(I)  <= LMB_AddrStrobe_vec_Q(I) when wait_vec(I) = '1' else
                                  LMB_AddrStrobe_vec(I);
      LMB_ReadStrobe_vec_i(I)  <= LMB_ReadStrobe_vec_Q(I) when wait_vec(I) = '1' else
                                  LMB_ReadStrobe_vec(I);
      LMB_WriteStrobe_vec_i(I) <= LMB_WriteStrobe_vec_Q(I) when wait_vec(I) = '1' else
                                  LMB_WriteStrobe_vec(I);
      IsWordWrite_vec_i(I)     <= IsWordWrite_vec_Q(I) when wait_vec(I) = '1' else
                                  IsWordWrite_vec(I);
      LMB_BE_vec_i(I)          <= LMB_BE_vec_Q(I) when wait_vec(I) = '1' else
                                  LMB_BE_vec(I);

      -- Assign selected LMB from internal signals
      Sl_DBus_vec(I)  <= Sl_DBus;
      Sl_Ready_vec(I) <= Sl_Ready when ongoing_Q = I else
                        '0';
      Sl_Wait_vec(I)  <= Sl_Wait when ongoing_Q = I else
                         wait_vec(I);
      Sl_UE_vec(I)    <= Sl_UE when ongoing_Q = I else
                        '0';
      Sl_CE_vec(I)    <= Sl_CE when ongoing_Q = I else
                        '0';
    end generate lmb_mux_generate;

    OnGoing_Reg : process (LMB_Clk) is
    begin 
      if (LMB_Clk'event and LMB_Clk = '1') then
        if (LMB_Rst = '1') then
          ongoing_Q <= 0;
        else
          ongoing_Q <= ongoing;
        end if;
      end if;
    end process OnGoing_Reg;

    Arbit : process (as_and_lmb_select_vec, wait_vec) is
      variable N : natural range 0 to C_NUM_LMB-1;
    begin 
      ongoing_new <= 0;
      for N in 0 to C_NUM_LMB - 1 loop
        if as_and_lmb_select_vec(N) = '1' or wait_vec(N) = '1' then
          ongoing_new <= N;
          exit;
        end if;
      end loop;
    end process Arbit;
  
    ongoing <= ongoing_Q when Sl_Wait = '1' and Sl_Ready = '0' else
               ongoing_new;

    -- Assign selected LMB
    LMB_ABus        <= LMB_ABus_vec_i(ongoing);
    LMB_WriteDBus   <= LMB_WriteDBus_vec_i(ongoing);
    LMB_WriteECC    <= LMB_WriteECC_vec_i(ongoing);
    LMB_AddrStrobe  <= LMB_AddrStrobe_vec_i(ongoing);
    LMB_ReadStrobe  <= LMB_ReadStrobe_vec_i(ongoing);
    LMB_WriteStrobe <= LMB_WriteStrobe_vec_i(ongoing);
    IsWordWrite     <= IsWordWrite_vec_i(ongoing);
    LMB_BE          <= LMB_BE_vec_i(ongoing);

    lmb_select      <= lmb_select_vec(ongoing) or wait_vec(ongoing);
    
  end generate more_than_one_lmb;

end imp;


-------------------------------------------------------------------------------
-- lmb_bram_if_cntlr.vhd - Entity and architecture
-------------------------------------------------------------------------------
--
-- (c) Copyright [2003] - [2017] Xilinx, Inc. All rights reserved.
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
-- PART OF THIS FILE AT ALL TIMES
--
------------------------------------------------------------------------------
-- Filename:        lmb_bram_if_cntlr.vhd
--
-- Description:
--
-- VHDL-Standard:   VHDL'93
-------------------------------------------------------------------------------
-- Structure:
--              lmb_bram_if_cntlr
--                lmb_mux
--                correct_one_bit
--                xor18.vhd
--                axi_interface
-------------------------------------------------------------------------------
-- Author:          rolandp
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

library lmb_bram_if_cntlr_v4_0_14;
use lmb_bram_if_cntlr_v4_0_14.all;

entity lmb_bram_if_cntlr is
  generic (
    C_FAMILY                   : string                    := "Virtex7";
    C_HIGHADDR                 : std_logic_vector(0 to 63) := X"0000000000000000";
    C_BASEADDR                 : std_logic_vector(0 to 63) := X"FFFFFFFFFFFFFFFF";
    C_MASK                     : std_logic_vector(0 to 63) := X"0000000000800000";
    C_MASK1                    : std_logic_vector(0 to 63) := X"0000000000800000";
    C_MASK2                    : std_logic_vector(0 to 63) := X"0000000000800000";
    C_MASK3                    : std_logic_vector(0 to 63) := X"0000000000800000";
    C_LMB_AWIDTH               : integer                   := 32;
    C_LMB_DWIDTH               : integer                   := 32;
    C_ECC                      : integer                   := 0;
    C_INTERCONNECT             : integer                   := 1;
    C_FAULT_INJECT             : integer                   := 0;
    C_CE_FAILING_REGISTERS     : integer                   := 0;
    C_UE_FAILING_REGISTERS     : integer                   := 0;
    C_ECC_STATUS_REGISTERS     : integer                   := 0;
    C_ECC_ONOFF_REGISTER       : integer                   := 0;
    C_ECC_ONOFF_RESET_VALUE    : integer                   := 1;
    C_CE_COUNTER_WIDTH         : integer                   := 0;
    C_WRITE_ACCESS             : integer                   := 2;
    C_NUM_LMB                  : integer                   := 1;
    -- BRAM generic
    C_BRAM_AWIDTH              : integer                   := 32;
    -- AXI generics
    C_S_AXI_CTRL_BASEADDR      : std_logic_vector          := X"FFFF_FFFF";
    C_S_AXI_CTRL_HIGHADDR      : std_logic_vector          := X"0000_0000";
    C_S_AXI_CTRL_ADDR_WIDTH    : integer                   := 32;
    C_S_AXI_CTRL_DATA_WIDTH    : integer                   := 32);
  port (
    LMB_Clk : in std_logic := '0';
    LMB_Rst : in std_logic := '0';

    -- LMB Bus
    LMB_ABus        : in  std_logic_vector(0 to C_LMB_AWIDTH-1);
    LMB_WriteDBus   : in  std_logic_vector(0 to C_LMB_DWIDTH-1);
    LMB_AddrStrobe  : in  std_logic;
    LMB_ReadStrobe  : in  std_logic;
    LMB_WriteStrobe : in  std_logic;
    LMB_BE          : in  std_logic_vector(0 to (C_LMB_DWIDTH/8 - 1));
    Sl_DBus         : out std_logic_vector(0 to C_LMB_DWIDTH-1);
    Sl_Ready        : out std_logic;
    Sl_Wait         : out std_logic;
    Sl_UE           : out std_logic;
    Sl_CE           : out std_logic;

    -- Supplementary LMB Bus 1
    LMB1_ABus        : in  std_logic_vector(0 to C_LMB_AWIDTH-1);
    LMB1_WriteDBus   : in  std_logic_vector(0 to C_LMB_DWIDTH-1);
    LMB1_AddrStrobe  : in  std_logic;
    LMB1_ReadStrobe  : in  std_logic;
    LMB1_WriteStrobe : in  std_logic;
    LMB1_BE          : in  std_logic_vector(0 to (C_LMB_DWIDTH/8 - 1));
    Sl1_DBus         : out std_logic_vector(0 to C_LMB_DWIDTH-1);
    Sl1_Ready        : out std_logic;
    Sl1_Wait         : out std_logic;
    Sl1_UE           : out std_logic;
    Sl1_CE           : out std_logic;

    -- Supplementary LMB Bus 2
    LMB2_ABus        : in  std_logic_vector(0 to C_LMB_AWIDTH-1);
    LMB2_WriteDBus   : in  std_logic_vector(0 to C_LMB_DWIDTH-1);
    LMB2_AddrStrobe  : in  std_logic;
    LMB2_ReadStrobe  : in  std_logic;
    LMB2_WriteStrobe : in  std_logic;
    LMB2_BE          : in  std_logic_vector(0 to (C_LMB_DWIDTH/8 - 1));
    Sl2_DBus         : out std_logic_vector(0 to C_LMB_DWIDTH-1);
    Sl2_Ready        : out std_logic;
    Sl2_Wait         : out std_logic;
    Sl2_UE           : out std_logic;
    Sl2_CE           : out std_logic;

    -- Supplementary LMB Bus 3
    LMB3_ABus        : in  std_logic_vector(0 to C_LMB_AWIDTH-1);
    LMB3_WriteDBus   : in  std_logic_vector(0 to C_LMB_DWIDTH-1);
    LMB3_AddrStrobe  : in  std_logic;
    LMB3_ReadStrobe  : in  std_logic;
    LMB3_WriteStrobe : in  std_logic;
    LMB3_BE          : in  std_logic_vector(0 to (C_LMB_DWIDTH/8 - 1));
    Sl3_DBus         : out std_logic_vector(0 to C_LMB_DWIDTH-1);
    Sl3_Ready        : out std_logic;
    Sl3_Wait         : out std_logic;
    Sl3_UE           : out std_logic;
    Sl3_CE           : out std_logic;

    -- ports to data memory block
    BRAM_Rst_A  : out std_logic;
    BRAM_Clk_A  : out std_logic;
    BRAM_Addr_A : out std_logic_vector(0 to C_BRAM_AWIDTH-1);
    BRAM_EN_A   : out std_logic;
    BRAM_WEN_A  : out std_logic_vector(0 to (C_LMB_DWIDTH+8*C_ECC)/8-1);
    BRAM_Dout_A : out std_logic_vector(0 to C_LMB_DWIDTH+8*C_ECC-1);
    BRAM_Din_A  : in  std_logic_vector(0 to C_LMB_DWIDTH+8*C_ECC-1);

    -- AXI Interface
    S_AXI_CTRL_ACLK    : in  std_logic;
    S_AXI_CTRL_ARESETN : in  std_logic;
    S_AXI_CTRL_AWADDR  : in  std_logic_vector(C_S_AXI_CTRL_ADDR_WIDTH-1 downto 0);
    S_AXI_CTRL_AWVALID : in  std_logic;
    S_AXI_CTRL_AWREADY : out std_logic;
    S_AXI_CTRL_WDATA   : in  std_logic_vector(C_S_AXI_CTRL_DATA_WIDTH-1 downto 0);
    S_AXI_CTRL_WSTRB   : in  std_logic_vector((C_S_AXI_CTRL_DATA_WIDTH/8)-1 downto 0);
    S_AXI_CTRL_WVALID  : in  std_logic;
    S_AXI_CTRL_WREADY  : out std_logic;
    S_AXI_CTRL_BRESP   : out std_logic_vector(1 downto 0);
    S_AXI_CTRL_BVALID  : out std_logic;
    S_AXI_CTRL_BREADY  : in  std_logic;
    S_AXI_CTRL_ARADDR  : in  std_logic_vector(C_S_AXI_CTRL_ADDR_WIDTH-1 downto 0);
    S_AXI_CTRL_ARVALID : in  std_logic;
    S_AXI_CTRL_ARREADY : out std_logic;
    S_AXI_CTRL_RDATA   : out std_logic_vector(C_S_AXI_CTRL_DATA_WIDTH-1 downto 0);
    S_AXI_CTRL_RRESP   : out std_logic_vector(1 downto 0);
    S_AXI_CTRL_RVALID  : out std_logic;
    S_AXI_CTRL_RREADY  : in  std_logic;

    -- Interrupt and error signals
    UE        : out std_logic;
    CE        : out std_logic;
    Interrupt : out std_logic);
end lmb_bram_if_cntlr;

library lmb_bram_if_cntlr_v4_0_14;
use lmb_bram_if_cntlr_v4_0_14.lmb_bram_if_funcs.all;

architecture imp of lmb_bram_if_cntlr is

------------------------------------------------------------------------------
-- component declarations
------------------------------------------------------------------------------

  component lmb_mux is
  generic (
    C_TARGET     : TARGET_FAMILY_TYPE;
    C_BASEADDR   : std_logic_vector(0 to 63) := X"FFFFFFFFFFFFFFFF";
    C_MASK       : std_logic_vector(0 to 63) := X"0000000000800000";
    C_MASK1      : std_logic_vector(0 to 63) := X"0000000000800000";
    C_MASK2      : std_logic_vector(0 to 63) := X"0000000000800000";
    C_MASK3      : std_logic_vector(0 to 63) := X"0000000000800000";
    C_LMB_AWIDTH : integer                   := 32;
    C_LMB_DWIDTH : integer                   := 32;
    C_ECC        : integer                   := 0;
    C_NUM_LMB    : integer                   := 1);
  port (
    LMB_Clk : in std_logic := '0';
    LMB_Rst : in std_logic := '0';

    -- LMB Bus 0
    LMB0_ABus        : in  std_logic_vector(0 to C_LMB_AWIDTH-1);
    LMB0_WriteDBus   : in  std_logic_vector(0 to C_LMB_DWIDTH-1);
    LMB0_AddrStrobe  : in  std_logic;
    LMB0_ReadStrobe  : in  std_logic;
    LMB0_WriteStrobe : in  std_logic;
    LMB0_BE          : in  std_logic_vector(0 to (C_LMB_DWIDTH/8 - 1));
    Sl0_DBus         : out std_logic_vector(0 to C_LMB_DWIDTH-1);
    Sl0_Ready        : out std_logic;
    Sl0_Wait         : out std_logic;
    Sl0_UE           : out std_logic;
    Sl0_CE           : out std_logic;

    -- LMB Bus 1
    LMB1_ABus        : in  std_logic_vector(0 to C_LMB_AWIDTH-1);
    LMB1_WriteDBus   : in  std_logic_vector(0 to C_LMB_DWIDTH-1);
    LMB1_AddrStrobe  : in  std_logic;
    LMB1_ReadStrobe  : in  std_logic;
    LMB1_WriteStrobe : in  std_logic;
    LMB1_BE          : in  std_logic_vector(0 to (C_LMB_DWIDTH/8 - 1));
    Sl1_DBus         : out std_logic_vector(0 to C_LMB_DWIDTH-1);
    Sl1_Ready        : out std_logic;
    Sl1_Wait         : out std_logic;
    Sl1_UE           : out std_logic;
    Sl1_CE           : out std_logic;

    -- LMB Bus 2
    LMB2_ABus        : in  std_logic_vector(0 to C_LMB_AWIDTH-1);
    LMB2_WriteDBus   : in  std_logic_vector(0 to C_LMB_DWIDTH-1);
    LMB2_AddrStrobe  : in  std_logic;
    LMB2_ReadStrobe  : in  std_logic;
    LMB2_WriteStrobe : in  std_logic;
    LMB2_BE          : in  std_logic_vector(0 to (C_LMB_DWIDTH/8 - 1));
    Sl2_DBus         : out std_logic_vector(0 to C_LMB_DWIDTH-1);
    Sl2_Ready        : out std_logic;
    Sl2_Wait         : out std_logic;
    Sl2_UE           : out std_logic;
    Sl2_CE           : out std_logic;

    -- LMB Bus 3
    LMB3_ABus        : in  std_logic_vector(0 to C_LMB_AWIDTH-1);
    LMB3_WriteDBus   : in  std_logic_vector(0 to C_LMB_DWIDTH-1);
    LMB3_AddrStrobe  : in  std_logic;
    LMB3_ReadStrobe  : in  std_logic;
    LMB3_WriteStrobe : in  std_logic;
    LMB3_BE          : in  std_logic_vector(0 to (C_LMB_DWIDTH/8 - 1));
    Sl3_DBus         : out std_logic_vector(0 to C_LMB_DWIDTH-1);
    Sl3_Ready        : out std_logic;
    Sl3_Wait         : out std_logic;
    Sl3_UE           : out std_logic;
    Sl3_CE           : out std_logic;

    -- Muxed LMB Bus
    LMB_ABus        : out std_logic_vector(0 to C_LMB_AWIDTH-1);
    LMB_WriteDBus   : out std_logic_vector(0 to C_LMB_DWIDTH-1);
    LMB_WriteECC    : out std_logic_vector(0 to 6);
    LMB_AddrStrobe  : out std_logic;
    LMB_ReadStrobe  : out std_logic;
    LMB_WriteStrobe : out std_logic;
    IsWordWrite     : out std_logic;
    LMB_BE          : out std_logic_vector(0 to (C_LMB_DWIDTH/8 - 1));
    Sl_DBus         : in  std_logic_vector(0 to C_LMB_DWIDTH-1);
    Sl_Ready        : in  std_logic;
    Sl_Wait         : in  std_logic;
    Sl_UE           : in  std_logic;
    Sl_CE           : in  std_logic;

    lmb_select       : out std_logic);
  end component lmb_mux;

  component axi_interface
  generic (
    C_TARGET           : TARGET_FAMILY_TYPE;
    C_S_AXI_BASEADDR   : std_logic_vector := X"FFFF_FFFF";
    C_S_AXI_HIGHADDR   : std_logic_vector := X"0000_0000";
    C_S_AXI_ADDR_WIDTH : integer          := 32;
    C_S_AXI_DATA_WIDTH : integer          := 32;
    C_REGADDR_WIDTH    : integer          := 5;    -- Address bits including register offset.
    C_DWIDTH           : integer          := 32);  -- Width of data bus.
  port (
    LMB_Clk       : in std_logic;
    LMB_Rst       : in std_logic;
    S_AXI_AWADDR  : in  std_logic_vector(C_S_AXI_ADDR_WIDTH-1 downto 0);
    S_AXI_AWVALID : in  std_logic;
    S_AXI_AWREADY : out std_logic;
    S_AXI_WDATA   : in  std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0);
    S_AXI_WSTRB   : in  std_logic_vector((C_S_AXI_DATA_WIDTH/8)-1 downto 0);
    S_AXI_WVALID  : in  std_logic;
    S_AXI_WREADY  : out std_logic;
    S_AXI_BRESP   : out std_logic_vector(1 downto 0);
    S_AXI_BVALID  : out std_logic;
    S_AXI_BREADY  : in  std_logic;
    S_AXI_ARADDR  : in  std_logic_vector(C_S_AXI_ADDR_WIDTH-1 downto 0);
    S_AXI_ARVALID : in  std_logic;
    S_AXI_ARREADY : out std_logic;
    S_AXI_RDATA   : out std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0);
    S_AXI_RRESP   : out std_logic_vector(1 downto 0);
    S_AXI_RVALID  : out std_logic;
    S_AXI_RREADY  : in  std_logic;
    RegWr         : out std_logic;
    RegWrData     : out std_logic_vector(0 to C_DWIDTH - 1);
    RegAddr       : out std_logic_vector(0 to C_REGADDR_WIDTH-1);
    RegRdData     : in  std_logic_vector(0 to C_DWIDTH - 1));
  end component;

  component checkbit_handler is
    generic (
      C_TARGET   : TARGET_FAMILY_TYPE;
      C_ENCODE   : boolean);
    port (
      DataIn     : in  std_logic_vector(0 to 31);
      CheckIn    : in  std_logic_vector(0 to 6);
      CheckOut   : out std_logic_vector(0 to 6);
      Syndrome   : out std_logic_vector(0 to 6);
      Enable_ECC : in  std_logic;
      UE_Q       : in  std_logic;
      CE_Q       : in  std_logic;
      UE         : out std_logic;
      CE         : out std_logic);
  end component checkbit_handler;

  component Correct_One_Bit
    generic (
      C_TARGET      : TARGET_FAMILY_TYPE;
      Correct_Value : std_logic_vector(0 to 6));
    port (
      DIn      : in  std_logic;
      Syndrome : in  std_logic_vector(0 to 6);
      DCorr    : out std_logic);
  end component Correct_One_Bit;

  constant C_TARGET   : TARGET_FAMILY_TYPE := String_To_Family(C_FAMILY, false);

  constant C_HAS_FAULT_INJECT         : boolean := C_FAULT_INJECT = 1;
  constant C_HAS_CE_FAILING_REGISTERS : boolean := C_CE_FAILING_REGISTERS = 1;
  constant C_HAS_UE_FAILING_REGISTERS : boolean := C_UE_FAILING_REGISTERS = 1;
  constant C_HAS_ECC_STATUS_REGISTERS : boolean := C_ECC_STATUS_REGISTERS = 1;
  constant C_HAS_ECC_ONOFF_REGISTER   : boolean := C_ECC_ONOFF_REGISTER = 1;
  constant C_HAS_CE_COUNTER           : boolean := C_CE_COUNTER_WIDTH /= 0;

  constant C_BUS_NEEDED : boolean := C_HAS_FAULT_INJECT  or
                                     C_HAS_CE_FAILING_REGISTERS or
                                     C_HAS_UE_FAILING_REGISTERS or
                                     C_HAS_ECC_STATUS_REGISTERS or
                                     C_HAS_ECC_ONOFF_REGISTER or
                                     C_HAS_CE_COUNTER;

  constant C_AXI : integer := 2;

  constant C_HAS_AXI : boolean := C_ECC = 1 and C_INTERCONNECT = C_AXI and C_BUS_NEEDED;

  constant C_ECC_WIDTH : integer := 7;

  -- Intermediate signals to handle multiple LMB ports
  signal LMB_ABus_i        : std_logic_vector(0 to C_LMB_AWIDTH-1);
  signal LMB_WriteDBus_i   : std_logic_vector(0 to C_LMB_DWIDTH-1);
  signal LMB_WriteECC      : std_logic_vector(0 to 6);
  signal LMB_AddrStrobe_i  : std_logic;
  signal LMB_ReadStrobe_i  : std_logic;
  signal LMB_WriteStrobe_i : std_logic;
  signal LMB_BE_i          : std_logic_vector(0 to (C_LMB_DWIDTH/8 - 1));
  signal Sl_DBus_i         : std_logic_vector(0 to C_LMB_DWIDTH-1);
  signal Sl_Ready_i        : std_logic;
  signal Sl_Wait_i         : std_logic;
  signal Sl_UE_i           : std_logic;
  signal Sl_CE_i           : std_logic;

  signal lmb_select       : std_logic;
  signal lmb_as           : std_logic;

  signal lmb_we : std_logic_vector(0 to 3);

  signal Sl_Rdy : std_logic;

  signal LMB_WrECC   : std_logic_vector(0 to C_ECC_WIDTH-1);
  signal IsWordWrite : std_logic;

  signal bram_din_a_i  : std_logic_vector(0 to C_LMB_DWIDTH+8*C_ECC-1);

begin

  assert C_LMB_AWIDTH >= C_BRAM_AWIDTH
    report "C_LMB_AWIDTH must be greater than or equal to C_BRAM_AWIDTH"
    severity failure;

  -----------------------------------------------------------------------------
  -- Cleaning incoming data from BRAM from 'U' for simulation purpose
  -- This is added since simulation model for BRAM will not initialize
  -- undefined memory locations with zero.
  -- Added as a work-around until this is fixed in the simulation model.
  -----------------------------------------------------------------------------
  Cleaning_machine: process (BRAM_Din_A) is
  begin  -- process Cleaning_machine
    -- Default assignments
    bram_din_a_i <= BRAM_Din_A;
    -- pragma translate_off
    bram_din_a_i <= To_StdLogicVector(To_bitvector(BRAM_Din_A));
    -- pragma translate_on

  end process Cleaning_machine;

  lmb_mux_I : lmb_mux
    generic map (
      C_TARGET     => C_TARGET,
      C_BASEADDR   => C_BASEADDR,
      C_MASK       => C_MASK,
      C_MASK1      => C_MASK1,
      C_MASK2      => C_MASK2,
      C_MASK3      => C_MASK3,
      C_LMB_AWIDTH => C_LMB_AWIDTH,
      C_LMB_DWIDTH => C_LMB_DWIDTH,
      C_ECC        => C_ECC,
      C_NUM_LMB    => C_NUM_LMB)
    port map (
      LMB_Clk          => LMB_Clk,
      LMB_Rst          => LMB_Rst,
      LMB0_ABus        => LMB_ABus,
      LMB0_WriteDBus   => LMB_WriteDBus,
      LMB0_AddrStrobe  => LMB_AddrStrobe,
      LMB0_ReadStrobe  => LMB_ReadStrobe,
      LMB0_WriteStrobe => LMB_WriteStrobe,
      LMB0_BE          => LMB_BE,
      Sl0_DBus         => Sl_DBus,
      Sl0_Ready        => Sl_Ready,
      Sl0_Wait         => Sl_Wait,
      Sl0_UE           => Sl_UE,
      Sl0_CE           => Sl_CE,
      LMB1_ABus        => LMB1_ABus,
      LMB1_WriteDBus   => LMB1_WriteDBus,
      LMB1_AddrStrobe  => LMB1_AddrStrobe,
      LMB1_ReadStrobe  => LMB1_ReadStrobe,
      LMB1_WriteStrobe => LMB1_WriteStrobe,
      LMB1_BE          => LMB1_BE,
      Sl1_DBus         => Sl1_DBus,
      Sl1_Ready        => Sl1_Ready,
      Sl1_Wait         => Sl1_Wait,
      Sl1_UE           => Sl1_UE,
      Sl1_CE           => Sl1_CE,
      LMB2_ABus        => LMB2_ABus,
      LMB2_WriteDBus   => LMB2_WriteDBus,
      LMB2_AddrStrobe  => LMB2_AddrStrobe,
      LMB2_ReadStrobe  => LMB2_ReadStrobe,
      LMB2_WriteStrobe => LMB2_WriteStrobe,
      LMB2_BE          => LMB2_BE,
      Sl2_DBus         => Sl2_DBus,
      Sl2_Ready        => Sl2_Ready,
      Sl2_Wait         => Sl2_Wait,
      Sl2_UE           => Sl2_UE,
      Sl2_CE           => Sl2_CE,
      LMB3_ABus        => LMB3_ABus,
      LMB3_WriteDBus   => LMB3_WriteDBus,
      LMB3_AddrStrobe  => LMB3_AddrStrobe,
      LMB3_ReadStrobe  => LMB3_ReadStrobe,
      LMB3_WriteStrobe => LMB3_WriteStrobe,
      LMB3_BE          => LMB3_BE,
      Sl3_DBus         => Sl3_DBus,
      Sl3_Ready        => Sl3_Ready,
      Sl3_Wait         => Sl3_Wait,
      Sl3_UE           => Sl3_UE,
      Sl3_CE           => Sl3_CE,
      LMB_ABus         => LMB_ABus_i,
      LMB_WriteDBus    => LMB_WriteDBus_i,
      LMB_WriteECC     => LMB_WriteECC,
      LMB_AddrStrobe   => LMB_AddrStrobe_i,
      LMB_ReadStrobe   => LMB_ReadStrobe_i,
      LMB_WriteStrobe  => LMB_WriteStrobe_i,
      IsWordWrite      => IsWordWrite,
      LMB_BE           => LMB_BE_i,
      Sl_DBus          => Sl_DBus_i,
      Sl_Ready         => Sl_Ready_i,
      Sl_Wait          => Sl_Wait_i,
      Sl_UE            => Sl_UE_i,
      Sl_CE            => Sl_CE_i,
      lmb_select       => lmb_select);

  BRAM_Rst_A  <= '0';
  BRAM_Clk_A  <= LMB_Clk;

  lmb_we(0) <= LMB_BE_i(0) and LMB_WriteStrobe_i and lmb_select;
  lmb_we(1) <= LMB_BE_i(1) and LMB_WriteStrobe_i and lmb_select;
  lmb_we(2) <= LMB_BE_i(2) and LMB_WriteStrobe_i and lmb_select;
  lmb_we(3) <= LMB_BE_i(3) and LMB_WriteStrobe_i and lmb_select;


  No_ECC : if (C_ECC = 0) generate

  begin

    BRAM_EN_A   <= LMB_AddrStrobe_i;
    BRAM_WEN_A  <= lmb_we;
    BRAM_Dout_A <= LMB_WriteDBus_i;
    Sl_DBus_i   <= bram_din_a_i;
    BRAM_Addr_A <= LMB_ABus_i(C_LMB_AWIDTH - C_BRAM_AWIDTH to C_LMB_AWIDTH - 1);

    -- only used wen ECC enabled, tie to constant inactive
    Sl_Wait_i   <= '0';
    Sl_UE_i     <= '0';
    Sl_CE_i     <= '0';
    UE          <= '0';
    CE          <= '0';
    Interrupt   <= '0';

    -----------------------------------------------------------------------------
    -- Writes are pipelined in MB with 5 stage pipeline
    -----------------------------------------------------------------------------
    Ready_Handling : process (LMB_Clk) is
    begin
      if (LMB_Clk'event and LMB_Clk = '1') then
        if (LMB_Rst = '1') then
          Sl_Rdy <= '0';
          lmb_as <= '0';
        else
          Sl_Rdy <= lmb_select;
          lmb_as <= LMB_AddrStrobe_i;
        end if;
      end if;
    end process Ready_Handling;

    Sl_Ready_i <= Sl_Rdy and lmb_as;

  end generate No_ECC;

  ECC : if (C_ECC = 1) generate

    constant NO_WRITES  : integer := 0;
    constant ONLY_WORD  : integer := 1;
    constant ALL_WRITES : integer := 2;

    signal enable_ecc : std_logic;

    -- On/Off Register
    constant C_ECC_ONOFF         : natural := 31;
    constant C_ECC_ONOFF_WIDTH   : natural := 1;
    signal ECC_EnableCheckingReg : std_logic_vector(32-C_ECC_ONOFF_WIDTH to 31);

    -- Fault Inject Registers
    signal FaultInjectData   : std_logic_vector(0 to C_LMB_DWIDTH-1);
    signal FaultInjectECC    : std_logic_vector(32-C_ECC_WIDTH to 31);

    -- Signals for read modify write operation when byte/half-word write
    signal write_access           : std_logic;
    signal full_word_write_access : std_logic;
    signal RdModifyWr_Read        : std_logic;  -- Read cycle in read modify write sequence
    signal RdModifyWr_Modify      : std_logic;  -- Modify cycle in read modify write sequence
    signal RdModifyWr_Modify_i    : std_logic;  -- Modify cycle in read modify write sequence
    signal RdModifyWr_Write       : std_logic;  -- Write cycle in read modify write sequence
    signal LMB_ABus_Q             : std_logic_vector(0 to C_LMB_AWIDTH-1);

    -- Read ECC
    signal Syndrome          : std_logic_vector(0 to C_ECC_WIDTH-1);
    signal CorrectedRdData   : std_logic_vector(0 to C_LMB_DWIDTH-1);
    signal CorrectedRdData_Q : std_logic_vector(0 to C_LMB_DWIDTH-1);
    signal CE_Q              : std_logic;
    signal UE_Q              : std_logic;

    -- Enable and address same for both data and ECC BRAM
    signal bram_en   : std_logic;
    signal bram_addr : std_logic_vector(0 to C_LMB_AWIDTH-1);

    subtype syndrome_bits is std_logic_vector(0 to 6);
    type correct_data_table_type is array(natural range 0 to 31) of syndrome_bits;
    constant correct_data_table : correct_data_table_type := (
      0 => "1100001",  1 => "1010001",  2 => "0110001",  3 => "1110001",
      4 => "1001001",  5 => "0101001",  6 => "1101001",  7 => "0011001",
      8 => "1011001",  9 => "0111001",  10 => "1111001",  11 => "1000101",
      12 => "0100101",  13 => "1100101",  14 => "0010101",  15 => "1010101",
      16 => "0110101",  17 => "1110101",  18 => "0001101",  19 => "1001101",
      20 => "0101101",  21 => "1101101",  22 => "0011101",  23 => "1011101",
      24 => "0111101",  25 => "1111101",  26 => "1000011",  27 => "0100011",
      28 => "1100011",  29 => "0010011",  30 => "1010011",  31 => "0110011"
      );

    type bool_array is array (natural range 0 to 6) of boolean;
    constant inverted_bit : bool_array := (false,false,true,false,true,false,false);
  begin

    assert C_LMB_DWIDTH = 32 report "C_LMB_DWIDTH must be 32 when C_ECC = 1" severity failure;

    -- Enable BRAMs when access on LMB and in the second cycle in a read/modify write
    bram_en <= '1' when LMB_AddrStrobe_i = '1' or RdModifyWr_Write = '1' else
               '0';

    BRAM_EN_A <= bram_en;

    -- ECC checking enable during access and when checking is turned on
    enable_ecc <= ECC_EnableCheckingReg(C_ECC_ONOFF) and Sl_Wait_i and not(full_word_write_access);

    -----------------------------------------------------------------------------
    -- Writes are pipelined in MB with 5 stage pipeline
    -----------------------------------------------------------------------------
    Ready_Handling : process (LMB_Clk) is
    begin
      if (LMB_Clk'event and LMB_Clk = '1') then
        if (LMB_Rst = '1') then
          Sl_Rdy <= '0';
          lmb_as <= '0';

        else
          -- Directly drive ready on valid read access or on valid word write access
          -- otherwise drive ready when we have written the new data on a
          -- readmodifywrite sequence
          Sl_Rdy <= ((LMB_AddrStrobe_i and lmb_select) and (LMB_ReadStrobe_i or IsWordWrite))
                        or RdModifyWr_Write;
          lmb_as <= LMB_AddrStrobe_i;
        end if;
      end if;
    end process Ready_Handling;

    Sl_Ready_i <= Sl_Rdy;

    Wait_Handling: process (LMB_Clk) is
    begin  -- process Wait_Handling
      if (LMB_Clk'event and LMB_Clk = '1') then  -- rising clock edge
        if (LMB_Rst = '1') then
          Sl_Wait_i <= '0';
        elsif (LMB_AddrStrobe_i = '1') then
          Sl_Wait_i <= lmb_select;
        elsif (Sl_Rdy = '1') then
          Sl_Wait_i <= '0';
        end if;
      end if;
    end process Wait_Handling;

    -- Generate ECC bits for checking data read from BRAM
    checkbit_handler_I1 : checkbit_handler
      generic map (
        C_TARGET   => C_TARGET,
        C_ENCODE   => false)                 -- [boolean]
      port map (
        DataIn     => bram_din_a_i(0 to 31),   -- [in  std_logic_vector(0 to 31)]
        CheckIn    => bram_din_a_i(33 to 39),  -- [in  std_logic_vector(0 to 6)]
        CheckOut   => open,                    -- [out std_logic_vector(0 to 6)]
        Syndrome   => Syndrome,                -- [out std_logic_vector(0 to 6)]
        Enable_ECC => enable_ecc,              -- [in  std_logic]
        UE_Q       => UE_Q,                    -- [in  std_logic]
        CE_Q       => CE_Q,                    -- [in  std_logic]
        UE         => Sl_UE_i,                 -- [out std_logic]
        CE         => Sl_CE_i);                -- [out std_logic]

    -- Discrete error signals
    UE <= Sl_UE_i and Sl_Ready_i;
    CE <= Sl_CE_i and Sl_Ready_i;

    -- Correct Data
    Gen_Correct_Data: for I in 0 to 31 generate
      Correct_One_Bit_I : Correct_One_Bit
        generic map (
          C_TARGET      => C_TARGET,
          Correct_Value => correct_data_table(I))
        port map (
          DIn           => bram_din_a_i(I),
          Syndrome      => Syndrome,
          DCorr         => CorrectedRdData(I));
    end generate Gen_Correct_Data;

    -- Drive corrected read data on LMB
    Sl_DBus_i <= CorrectedRdData;

    -- Remember address and writestrobe
    AddressReg : process(LMB_Clk) is
    begin
      if (LMB_Clk'event and LMB_Clk = '1') then
        if LMB_Rst = '1' then
          LMB_ABus_Q             <= (others => '0');
          write_access           <= '0';
          full_word_write_access <= '0';
        elsif LMB_AddrStrobe_i = '1' then
          LMB_ABus_Q             <= LMB_ABus_i;
          write_access           <= LMB_WriteStrobe_i;
          full_word_write_access <= LMB_BE_i(0) and LMB_BE_i(1) and LMB_BE_i(2) and LMB_BE_i(3) and LMB_WriteStrobe_i;
        end if;
      end if;
    end process AddressReg;

    bram_addr <= LMB_ABus_Q when RdModifyWr_Write = '1' else
                 LMB_ABus_i;

    BRAM_Addr_A <= bram_addr(C_LMB_AWIDTH - C_BRAM_AWIDTH to C_LMB_AWIDTH - 1);

    Do_Writes : if (C_WRITE_ACCESS /= NO_WRITES) generate
      signal WrData  : std_logic_vector(0 to C_LMB_DWIDTH-1);
      signal WrECC   : std_logic_vector(0 to C_ECC_WIDTH-1);
    begin

      DO_BYTE_HALFWORD_WRITES : if (C_WRITE_ACCESS = ALL_WRITES) generate
        signal wrdata_i    : std_logic_vector(0 to C_LMB_DWIDTH-1);
        signal writeDBus_Q : std_logic_vector(0 to C_LMB_DWIDTH-1);
        signal lmb_be_q    : std_logic_vector(0 to (C_LMB_DWIDTH/8 - 1));
      begin

        -- Remember correctable/uncorrectable error from read in read modify write
        CorrReg : process(LMB_Clk) is
        begin
          if (LMB_Clk'event and LMB_Clk = '1') then
            if RdModifyWr_Modify = '1' then   -- Remember error signals
              CE_Q <= Sl_CE_i;
              UE_Q <= Sl_UE_i;
            elsif RdModifyWr_Write = '1' then   -- Keep the signals one more cycle
              CE_Q <= CE_Q;
              UE_Q <= UE_Q;
            else
              CE_Q <= '0';
              UE_Q <= '0';
            end if;
          end if;
        end process CorrReg;

        -- Remember byte write enables one clock cycle to properly mux bytes to write,
        -- with read data in read/modify write operation
        -- Write in Read/Write always 1 cycle after Read
        StoreLMB_WE : process(LMB_Clk) is
        begin
          if (LMB_Clk'event and LMB_Clk = '1') then
            RdModifyWr_Modify_i <= RdModifyWr_Read;
            RdModifyWr_Write    <= RdModifyWr_Modify;
            CorrectedRdData_Q   <= CorrectedRdData;
          end if;
        end process StoreLMB_WE;

        RdModifyWr_Modify <= RdModifyWr_Modify_i and lmb_as;

        RdModifyWr_Read  <= '1' when lmb_we /= "1111" and lmb_we /= "0000" and (C_WRITE_ACCESS = ALL_WRITES) else
                            '0';

        -- Remember write data one cycle to be available after read has been completed in a
        -- read/modify write operation
        StoreWriteDBus : process(LMB_Clk) is
        begin
          if (LMB_Clk'event and LMB_Clk = '1') then
            if (LMB_Rst = '1') then
              WriteDBus_Q <= (others => '0');
              lmb_be_q    <= (others => '0');
            elsif (LMB_AddrStrobe_i = '1') then
              WriteDBus_Q <= LMB_WriteDBus_i;
              lmb_be_q    <= LMB_BE_i;
            end if;
          end if;
        end process StoreWriteDBus;

        wrdata_i <= WriteDBus_Q when RdModifyWr_Write = '1' else LMB_WriteDBus_i;

        -- Select BRAM data to write from LMB on 32-bit word access or a mix of
        -- read data and LMB write data for read/modify write operations
        WrData(0 to 7)   <= wrdata_i(0 to 7) when ((RdModifyWr_Write = '0' and LMB_BE_i(0) = '1') or
                                                   (RdModifyWr_Write = '1' and lmb_be_q(0) = '1')) else
                            CorrectedRdData_Q(0 to 7);
        WrData(8 to 15)  <= wrdata_i(8 to 15) when ((RdModifyWr_Write = '0' and LMB_BE_i(1) = '1') or
                                                    (RdModifyWr_Write = '1' and lmb_be_q(1) = '1')) else
                            CorrectedRdData_Q(8 to 15);
        WrData(16 to 23) <= wrdata_i(16 to 23) when ((RdModifyWr_Write = '0' and LMB_BE_i(2) = '1') or
                                                     (RdModifyWr_Write = '1' and lmb_be_q(2) = '1')) else
                            CorrectedRdData_Q(16 to 23);
        WrData(24 to 31) <= wrdata_i(24 to 31) when ((RdModifyWr_Write = '0' and LMB_BE_i(3) = '1') or
                                                     (RdModifyWr_Write = '1' and lmb_be_q(3) = '1')) else
                            CorrectedRdData_Q(24 to 31);

        One_LMB: if (C_NUM_LMB = 1) generate
        begin
 
          -- Generate ECC bits for writing into BRAM
          checkbit_handler_I2 : checkbit_handler
            generic map (
              C_TARGET   => C_TARGET,
              C_ENCODE   => true)           -- [boolean]
            port map (
              DataIn     => WrData,         -- [in  std_logic_vector(0 to 31)]
              CheckIn    => (others => '0'),-- [in  std_logic_vector(0 to 6)]
              CheckOut   => WrECC,          -- [out std_logic_vector(0 to 6)]
              Syndrome   => open,           -- [out std_logic_vector(0 to 6)]
              Enable_ECC => '1',            -- [in  std_logic]
              UE_Q       => '0',            -- [in  std_logic]
              CE_Q       => '0',            -- [in  std_logic]
              UE         => open,           -- [out std_logic]
              CE         => open);          -- [out std_logic]

        end generate One_LMB;

        -- Timing QoR to move ECC generation before LMB source selection for
        -- one cycle word write
        Many_LMB: if (C_NUM_LMB > 1) generate
          signal WrECC_i        : std_logic_vector(0 to C_ECC_WIDTH-1);
          signal RdModifyWrData : std_logic_vector(0 to C_LMB_DWIDTH-1);
        begin
          -- Only used for generating ECC for Read-Modify-Write
          RdModifyWrData(0 to 7)   <= WriteDBus_Q(0 to 7) when lmb_be_q(0) = '1' else
                                      CorrectedRdData_Q(0 to 7);
          RdModifyWrData(8 to 15)  <= WriteDBus_Q(8 to 15) when lmb_be_q(1) = '1' else
                                      CorrectedRdData_Q(8 to 15);
          RdModifyWrData(16 to 23) <= WriteDBus_Q(16 to 23) when lmb_be_q(2) = '1' else
                                      CorrectedRdData_Q(16 to 23);
          RdModifyWrData(24 to 31) <= WriteDBus_Q(24 to 31) when lmb_be_q(3) = '1' else
                                      CorrectedRdData_Q(24 to 31);
          -- Generate ECC bits for writing into BRAM
          checkbit_handler_I2 : checkbit_handler
            generic map (
              C_TARGET   => C_TARGET,
              C_ENCODE   => true)           -- [boolean]
            port map (
              DataIn     => RdModifyWrData, -- [in  std_logic_vector(0 to 31)]
              CheckIn    => (others => '0'),-- [in  std_logic_vector(0 to 6)]
              CheckOut   => WrECC_i,        -- [out std_logic_vector(0 to 6)]
              Syndrome   => open,           -- [out std_logic_vector(0 to 6)]
              Enable_ECC => '1',            -- [in  std_logic]
              UE_Q       => '0',            -- [in  std_logic]
              CE_Q       => '0',            -- [in  std_logic]
              UE         => open,           -- [out std_logic]
              CE         => open);          -- [out std_logic]
          
          WrECC <= WrECC_i when RdModifyWr_Write = '1' else  -- from Read-Modify-Write above
                   LMB_WriteECC;                             -- directly from lmb_mux pre generated ECC
        end generate Many_LMB;

      end generate DO_BYTE_HALFWORD_WRITES;

      DO_Only_Word_Writes : if (C_WRITE_ACCESS = ONLY_WORD) generate
        RdModifyWr_Write  <= '0';
        RdModifyWr_Read   <= '0';
        RdModifyWr_Modify <= '0';
        CorrectedRdData_Q <= (others => '0');
        WrData            <= LMB_WriteDBus_i;
        CE_Q              <= '0';
        UE_Q              <= '0';
      end generate DO_Only_Word_Writes;

      -- Generate BRAM WEN, which will always be all 1's due to read modify write
      -- for non 32-bit word access
      WrDataSel : process(IsWordWrite, lmb_select, RdModifyWr_Modify, RdModifyWr_Write, UE_Q)
      begin
        if (RdModifyWr_Modify = '1') then
          BRAM_WEN_A <= (others => '0');
        elsif (RdModifyWr_Write = '1') then
          if (UE_Q = '0') then
            BRAM_WEN_A <= (others => '1');  -- byte or half word write, and not UE
          else
            BRAM_WEN_A <= (others => '0');
          end if;
        elsif (IsWordWrite = '1') then           -- word write
          BRAM_WEN_A <= (others => lmb_select);
        else
          BRAM_WEN_A <= (others => '0');
        end if;
      end process WrDataSel;
  
      -- Drive BRAM write data and inject fault if applicable
      BRAM_Dout_A(0 to 31)  <= WrData xor FaultInjectData;
      BRAM_Dout_A(32 to 39) <= ('0' & WrECC) xor ('0' & FaultInjectECC);

    end generate Do_Writes;

    No_Write_Accesses : if (C_WRITE_ACCESS = NO_WRITES) generate
      RdModifyWr_Write  <= '0';
      RdModifyWr_Read   <= '0';
      RdModifyWr_Modify <= '0';
      CorrectedRdData_Q <= (others => '0');
      FaultInjectData   <= (others => '0');
      FaultInjectECC    <= (others => '0');
      CE_Q              <= '0';
      UE_Q              <= '0';
      BRAM_WEN_A        <= (others => '0');
      BRAM_Dout_A       <= (others => '0');
    end generate No_Write_Accesses;

    Has_AXI : if C_HAS_AXI generate

      -- Register accesses
      -- Register addresses use word address, i.e 2 LSB don't care
      -- Don't decode MSB, i.e. mirroring of registers in address space of module
      -- Don't decode unmapped addresses
      -- Data registers occupy 32 words to accommodate up to 1024-bit words in other IPs
      -- ECC registers occupy 16 words to accomodate up to 512-bit ECC in other IPs
      -- Address registers occupy 2 words to accommodate 64-bit address
      constant C_REGADDR_WIDTH     : integer          := 8;
      constant C_ECC_StatusReg     : std_logic_vector := "00000000";  -- 0x000 ECC_STATUS
      constant C_ECC_EnableIRQReg  : std_logic_vector := "00000001";  -- 0x004 ECC_EN_IRQ
      constant C_ECC_OnOffReg      : std_logic_vector := "00000010";  -- 0x008 ECC_ONOFF
      constant C_CE_CounterReg     : std_logic_vector := "00000011";  -- 0x00C CE_CNT
      constant C_CE_FailingData    : std_logic_vector := "01000000";  -- 0x100 CE_FFD[31:0]
      constant C_CE_FailingECC     : std_logic_vector := "01100000";  -- 0x180 CE_FFE
      constant C_CE_FailingAddrLSH : std_logic_vector := "01110000";  -- 0x1C0 CE_FFA[31:0]
      constant C_CE_FailingAddrMSH : std_logic_vector := "01110001";  -- 0x1C4 CE_FFA[C_LMB_AWIDTH-1:32]
      constant C_UE_FailingData    : std_logic_vector := "10000000";  -- 0x200 UE_FFD[31:0]
      constant C_UE_FailingECC     : std_logic_vector := "10100000";  -- 0x280 UE_FFE
      constant C_UE_FailingAddrLSH : std_logic_vector := "10110000";  -- 0x2C0 UE_FFA[31:0]
      constant C_UE_FailingAddrMSH : std_logic_vector := "10110001";  -- 0x2C4 UE_FFA[C_LMB_AWIDTH-1:32]
      constant C_FaultInjectData   : std_logic_vector := "11000000";  -- 0x300 FI_D[31:0]
      constant C_FaultInjectECC    : std_logic_vector := "11100000";  -- 0x380 FI_ECC

      -- ECC Status register bit positions
      constant C_ECC_STATUS_CE        : natural := 30;
      constant C_ECC_STATUS_UE        : natural := 31;
      constant C_ECC_STATUS_WIDTH     : natural := 2;
      constant C_ECC_ENABLE_IRQ_CE    : natural := 30;
      constant C_ECC_ENABLE_IRQ_UE    : natural := 31;
      constant C_ECC_ENABLE_IRQ_WIDTH : natural := 2;

      -- Read and write data to internal registers
      constant C_DWIDTH : integer := 32;
      signal RegWrData  : std_logic_vector(0 to C_DWIDTH-1);
      signal RegRdData  : std_logic_vector(0 to C_DWIDTH-1);
      signal RegAddr    : std_logic_vector(0 to C_REGADDR_WIDTH-1);
      signal RegWr      : std_logic;

      -- Correctable Error First Failing Register
      signal CE_FailingAddress : std_logic_vector(0 to C_LMB_AWIDTH-1);
      signal CE_FailingAddrLSH : std_logic_vector(0 to 31);
      signal CE_FailingAddrMSH : std_logic_vector(0 to 31);
      signal CE_FailingData    : std_logic_vector(0 to C_LMB_DWIDTH-1);
      signal CE_FailingECC     : std_logic_vector(32-C_ECC_WIDTH to 31);
      -- Uncorrectable Error First Failing Register
      signal UE_FailingAddress : std_logic_vector(0 to C_LMB_AWIDTH-1);
      signal UE_FailingAddrLSH : std_logic_vector(0 to 31);
      signal UE_FailingAddrMSH : std_logic_vector(0 to 31);
      signal UE_FailingData    : std_logic_vector(0 to C_LMB_DWIDTH-1);
      signal UE_FailingECC     : std_logic_vector(32-C_ECC_WIDTH to 31);
      -- ECC Status and Control register
      signal ECC_StatusReg     : std_logic_vector(32-C_ECC_STATUS_WIDTH to 31);
      signal ECC_EnableIRQReg  : std_logic_vector(32-C_ECC_ENABLE_IRQ_WIDTH to 31);

      -- Correctable Error Counter
      signal CE_CounterReg     : std_logic_vector(32-C_CE_COUNTER_WIDTH to 31);

      signal sample_registers : std_logic;

    begin

      sample_registers <= lmb_as and not full_word_write_access;

      -- Implement fault injection registers
      Fault_Inject : if C_HAS_FAULT_INJECT and (C_WRITE_ACCESS /= NO_WRITES) generate
      begin
        FaultInjectDataReg : process(LMB_Clk) is
        begin
          if LMB_Clk'event and LMB_Clk = '1' then
            if LMB_Rst = '1' then
              FaultInjectData <= (others => '0');
              FaultInjectECC  <= (others => '0');
            elsif RegWr = '1' and RegAddr = C_FaultInjectData then
              FaultInjectData <= RegWrData;
            elsif RegWr = '1' and RegAddr = C_FaultInjectECC then
              FaultInjectECC  <= RegWrData(FaultInjectECC'range);
            elsif (Sl_Rdy = '1') and (write_access = '1') then  -- One shoot, clear after first LMB write
              FaultInjectData <= (others => '0');
              FaultInjectECC  <= (others => '0');
            end if;
          end if;
        end process FaultInjectDataReg;
      end generate Fault_Inject;

      No_Fault_Inject : if not C_HAS_FAULT_INJECT or (C_WRITE_ACCESS = NO_WRITES) generate
      begin
        FaultInjectData <= (others => '0');
        FaultInjectECC  <= (others => '0');
      end generate No_Fault_Inject;

      -- Implement Correctable Error First Failing Register
      CE_Failing_Registers : if C_HAS_CE_FAILING_REGISTERS generate
      begin
        CE_FailingReg : process(LMB_Clk) is
        begin
          if LMB_Clk'event and LMB_Clk = '1' then
            if LMB_Rst = '1' then
              CE_FailingAddress <= (others => '0');
              CE_FailingData    <= (others => '0');
              CE_FailingECC     <= (others => '0');
            elsif Sl_CE_i = '1' and sample_registers = '1' and ECC_StatusReg(C_ECC_STATUS_CE) = '0' then
              CE_FailingAddress <= LMB_ABus_Q;
              CE_FailingData    <= bram_din_a_i(CE_FailingData'range);
              CE_FailingECC     <= bram_din_a_i(33 to 33+C_ECC_WIDTH-1);
            end if;
          end if;
        end process CE_FailingReg;

        CE_FailingAddrLSH <= CE_FailingAddress(C_LMB_AWIDTH-32 to C_LMB_AWIDTH-1);

        Use_Extended_Address: if C_LMB_AWIDTH > 32 generate
        begin
          Assign_FailingAddress: process (CE_FailingAddress) is
          begin
            CE_FailingAddrMSH <= (others => '0');
            for I in 0 to C_LMB_AWIDTH - 32 - 1 loop
              CE_FailingAddrMSH(64 - C_LMB_AWIDTH + I) <= CE_FailingAddress(I);
            end loop;
          end process Assign_FailingAddress;
        end generate Use_Extended_Address;

        No_Extended_Address: if C_LMB_AWIDTH <= 32 generate
        begin
          CE_FailingAddrMSH <= (others => '0');
        end generate No_Extended_Address;

      end generate CE_Failing_Registers;

      No_CE_Failing_Registers : if not C_HAS_CE_FAILING_REGISTERS generate
      begin
        CE_FailingAddress <= (others => '0');
        CE_FailingAddrLSH <= (others => '0');
        CE_FailingAddrMSH <= (others => '0');
        CE_FailingData    <= (others => '0');
        CE_FailingECC     <= (others => '0');
      end generate No_CE_Failing_Registers;

      -- Implement Unorrectable Error First Failing Register
      UE_Failing_Registers : if C_HAS_UE_FAILING_REGISTERS generate
      begin
        UE_FailingReg : process(LMB_Clk) is
        begin
          if LMB_Clk'event and LMB_Clk = '1' then
            if LMB_Rst = '1' then
              UE_FailingAddress <= (others => '0');
              UE_FailingData    <= (others => '0');
              UE_FailingECC     <= (others => '0');
            elsif Sl_UE_i = '1' and sample_registers = '1' and ECC_StatusReg(C_ECC_STATUS_UE) = '0' then
              UE_FailingAddress <= LMB_ABus_Q;
              UE_FailingData    <= bram_din_a_i(UE_FailingData'range);
              UE_FailingECC     <= bram_din_a_i(33 to 33+C_ECC_WIDTH-1);
            end if;
          end if;
        end process UE_FailingReg;

        UE_FailingAddrLSH <= UE_FailingAddress(C_LMB_AWIDTH-32 to C_LMB_AWIDTH-1);

        Use_Extended_Address: if C_LMB_AWIDTH > 32 generate
        begin
          Assign_FailingAddress: process (UE_FailingAddress) is
          begin
            UE_FailingAddrMSH <= (others => '0');
            for I in 0 to C_LMB_AWIDTH - 32 - 1 loop
              UE_FailingAddrMSH(64 - C_LMB_AWIDTH + I) <= UE_FailingAddress(I);
            end loop;
          end process Assign_FailingAddress;
        end generate Use_Extended_Address;

        No_Extended_Address: if C_LMB_AWIDTH <= 32 generate
        begin
          UE_FailingAddrMSH <= (others => '0');
        end generate No_Extended_Address;

      end generate UE_Failing_Registers;

      No_UE_Failing_Registers : if not C_HAS_UE_FAILING_REGISTERS generate
      begin
        UE_FailingAddress <= (others => '0');
        UE_FailingAddrLSH <= (others => '0');
        UE_FailingAddrMSH <= (others => '0');
        UE_FailingData    <= (others => '0');
        UE_FailingECC     <= (others => '0');
      end generate No_UE_Failing_Registers;

      ECC_Status_Registers : if C_HAS_ECC_STATUS_REGISTERS generate
      begin

        StatusReg : process(LMB_Clk) is
        begin
          if LMB_Clk'event and LMB_Clk = '1' then
            if LMB_Rst = '1' then
              ECC_StatusReg <= (others => '0');
            elsif RegWr = '1' and RegAddr = C_ECC_StatusReg then
              -- CE Interrupt status bit
              if RegWrData(C_ECC_STATUS_CE) = '1' then
                ECC_StatusReg(C_ECC_STATUS_CE) <= '0';  -- Clear when write '1'
              end if;
              -- UE Interrupt status bit
              if RegWrData(C_ECC_STATUS_UE) = '1' then
                ECC_StatusReg(C_ECC_STATUS_UE) <= '0';  -- Clear when write '1'
              end if;
            else
              if Sl_CE_i = '1' and sample_registers = '1' then
                ECC_StatusReg(C_ECC_STATUS_CE) <= '1';  -- Set when CE occurs
              end if;
              if Sl_UE_i = '1' and sample_registers = '1' then
                ECC_StatusReg(C_ECC_STATUS_UE) <= '1';  -- Set when UE occurs
              end if;
            end if;
          end if;
        end process StatusReg;

        EnableIRQReg : process(LMB_Clk) is
        begin
          if LMB_Clk'event and LMB_Clk = '1' then
            if LMB_Rst = '1' then
              ECC_EnableIRQReg <= (others => '0');
            elsif RegWr = '1' and RegAddr = C_ECC_EnableIRQReg then
              -- CE Interrupt enable bit
              ECC_EnableIRQReg(C_ECC_ENABLE_IRQ_CE) <= RegWrData(C_ECC_ENABLE_IRQ_CE);
              -- UE Interrupt enable bit
              ECC_EnableIRQReg(C_ECC_ENABLE_IRQ_UE) <= RegWrData(C_ECC_ENABLE_IRQ_UE);
            end if;
          end if;
        end process EnableIRQReg;

        Interrupt <= (ECC_StatusReg(C_ECC_STATUS_CE) and ECC_EnableIRQReg(C_ECC_ENABLE_IRQ_CE)) or
                     (ECC_StatusReg(C_ECC_STATUS_UE) and ECC_EnableIRQReg(C_ECC_ENABLE_IRQ_UE));

      end generate ECC_Status_Registers;

      No_ECC_Status_Registers : if not C_HAS_ECC_STATUS_REGISTERS generate
      begin
        ECC_EnableIRQReg <= (others => '0');
        ECC_StatusReg    <= (others => '0');
        Interrupt        <= '0';
      end generate No_ECC_Status_Registers;

      ECC_OnOff_Register : if C_HAS_ECC_ONOFF_REGISTER generate
      begin

        OnOffReg : process(LMB_Clk) is
        begin
          if LMB_Clk'event and LMB_Clk = '1' then
            if LMB_Rst = '1' then
              if C_ECC_ONOFF_RESET_VALUE = 0 then
                 ECC_EnableCheckingReg(C_ECC_ONOFF) <= '0';
              else
                 ECC_EnableCheckingReg(C_ECC_ONOFF) <= '1';
              end if;
            elsif RegWr = '1' and RegAddr = C_ECC_OnOffReg then
              ECC_EnableCheckingReg(C_ECC_ONOFF) <= RegWrData(C_ECC_ONOFF);
            end if;
          end if;
        end process OnOffReg;

      end generate ECC_OnOff_Register;

      No_ECC_OnOff_Register : if not C_HAS_ECC_ONOFF_REGISTER generate
      begin
        ECC_EnableCheckingReg(C_ECC_ONOFF) <= '1';
      end generate No_ECC_OnOff_Register;

      CE_Counter : if C_HAS_CE_COUNTER generate
        -- One extra bit compare to CE_CounterReg to handle carry bit
        signal CE_CounterReg_plus_1 : std_logic_vector(31-C_CE_COUNTER_WIDTH to 31);
      begin

        CountReg : process(LMB_Clk) is
        begin
          if (LMB_Clk'event and LMB_Clk = '1') then
            if (LMB_Rst = '1') then
              CE_CounterReg <= (others => '0');
            elsif RegWr = '1' and RegAddr = C_CE_CounterReg then
              CE_CounterReg <= RegWrData(CE_CounterReg'range);
            elsif Sl_CE_i = '1' and
                  sample_registers = '1' and
                  CE_CounterReg_plus_1(CE_CounterReg_plus_1'left) = '0' then
              CE_CounterReg <= CE_CounterReg_plus_1(32-C_CE_COUNTER_WIDTH to 31);
            end if;
          end if;
        end process CountReg;

        CE_CounterReg_plus_1 <= std_logic_vector(unsigned(('0' & CE_CounterReg)) + 1);

      end generate CE_Counter;

      No_CE_Counter : if not C_HAS_CE_COUNTER generate
      begin
        CE_CounterReg <= (others => '0');
      end generate No_CE_Counter;

      SelRegRdData : process (RegAddr,
                              ECC_StatusReg, ECC_EnableIRQReg, ECC_EnableCheckingReg, CE_CounterReg,
                              CE_FailingAddrLSH, CE_FailingAddrMSH, CE_FailingData, CE_FailingECC,
                              UE_FailingAddrLSH, UE_FailingAddrMSH, UE_FailingData, UE_FailingECC)
      begin
        RegRdData <= (others => '0');

        case RegAddr is
          when C_ECC_StatusReg     => RegRdData(ECC_StatusReg'range)          <= ECC_StatusReg;
          when C_ECC_EnableIRQReg  => RegRdData(ECC_EnableIRQReg'range)       <= ECC_EnableIRQReg;
          when C_ECC_OnOffReg      => RegRdData(ECC_EnableCheckingReg'range)  <= ECC_EnableCheckingReg;
          when C_CE_CounterReg     => RegRdData(CE_CounterReg'range)          <= CE_CounterReg;
          when C_CE_FailingAddrLSH => RegRdData                               <= CE_FailingAddrLSH;
          when C_CE_FailingAddrMSH => RegRdData                               <= CE_FailingAddrMSH;
          when C_CE_FailingData    => RegRdData(CE_FailingData'range)         <= CE_FailingData;
          when C_CE_FailingECC     => RegRdData(CE_FailingECC'range)          <= CE_FailingECC;
          when C_UE_FailingAddrLSH => RegRdData                               <= UE_FailingAddrLSH;
          when C_UE_FailingAddrMSH => RegRdData                               <= UE_FailingAddrMSH;
          when C_UE_FailingData    => RegRdData(UE_FailingData'range)         <= UE_FailingData;
          when C_UE_FailingECC     => RegRdData(UE_FailingECC'range)          <= UE_FailingECC;
          when others              => RegRdData                               <= (others => '0');
        end case;
      end process SelRegRdData;

      AXI : if C_HAS_AXI generate
      begin
        axi_I : axi_interface
        generic map(
          C_TARGET           => C_TARGET,
          C_S_AXI_BASEADDR   => C_S_AXI_CTRL_BASEADDR,
          C_S_AXI_HIGHADDR   => C_S_AXI_CTRL_HIGHADDR,
          C_S_AXI_ADDR_WIDTH => C_S_AXI_CTRL_ADDR_WIDTH,
          C_S_AXI_DATA_WIDTH => C_S_AXI_CTRL_DATA_WIDTH,
          C_REGADDR_WIDTH    => C_REGADDR_WIDTH,
          C_DWIDTH           => C_DWIDTH)
        port map (
          LMB_Clk       => LMB_Clk,
          LMB_Rst       => LMB_Rst,
          S_AXI_AWADDR  => S_AXI_CTRL_AWADDR,
          S_AXI_AWVALID => S_AXI_CTRL_AWVALID,
          S_AXI_AWREADY => S_AXI_CTRL_AWREADY,
          S_AXI_WDATA   => S_AXI_CTRL_WDATA,
          S_AXI_WSTRB   => S_AXI_CTRL_WSTRB,
          S_AXI_WVALID  => S_AXI_CTRL_WVALID,
          S_AXI_WREADY  => S_AXI_CTRL_WREADY,
          S_AXI_BRESP   => S_AXI_CTRL_BRESP,
          S_AXI_BVALID  => S_AXI_CTRL_BVALID,
          S_AXI_BREADY  => S_AXI_CTRL_BREADY,
          S_AXI_ARADDR  => S_AXI_CTRL_ARADDR,
          S_AXI_ARVALID => S_AXI_CTRL_ARVALID,
          S_AXI_ARREADY => S_AXI_CTRL_ARREADY,
          S_AXI_RDATA   => S_AXI_CTRL_RDATA,
          S_AXI_RRESP   => S_AXI_CTRL_RRESP,
          S_AXI_RVALID  => S_AXI_CTRL_RVALID,
          S_AXI_RREADY  => S_AXI_CTRL_RREADY,
          RegWr         => RegWr,
          RegWrData     => RegWrData,
          RegAddr       => RegAddr,
          RegRdData     => RegRdData);
      end generate AXI;

    end generate Has_AXI;

    No_AXI : if not C_HAS_AXI generate
    begin
      FaultInjectData <= (others => '0');
      FaultInjectECC  <= (others => '0');
      Interrupt       <= '0';

      ECC_EnableCheckingReg(C_ECC_ONOFF) <= '1';
    end generate No_AXI;

  end generate ECC;

  No_AXI_ECC : if not C_HAS_AXI generate
  begin
    S_AXI_CTRL_AWREADY <= '0';
    S_AXI_CTRL_WREADY  <= '0';
    S_AXI_CTRL_BRESP   <= (others => '0');
    S_AXI_CTRL_BVALID  <= '0';
    S_AXI_CTRL_ARREADY <= '0';
    S_AXI_CTRL_RDATA   <= (others => '0');
    S_AXI_CTRL_RRESP   <= (others => '0');
    S_AXI_CTRL_RVALID  <= '0';
  end generate No_AXI_ECC;

end architecture imp;


