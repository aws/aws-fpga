-------------------------------------------------------------------------------
-- Processor Common Library Package
-------------------------------------------------------------------------------
--
-- *************************************************************************
-- ** (c) Copyright 2017-2018, 2023 Advanced Micro Devices, Inc. All rights reserved **                                                                   **
-- **                                                                                **
-- ** This file contains confidential and proprietary information                    **
-- ** of AMD and is protected under U.S. and international copyright                 **
-- ** and other intellectual property laws.                                          **
-- **                                                                                **
-- ** DISCLAIMER                                                                     **
-- ** This disclaimer is not a license and does not grant any                        **
-- ** rights to the materials distributed herewith. Except as                        **
-- ** otherwise provided in a valid license issued to you by                         **
-- ** AMD, and to the maximum extent permitted by applicable                         **
-- ** law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND                        **
-- ** WITH ALL FAULTS, AND AMD HEREBY DISCLAIMS ALL WARRANTIES                       **
-- ** AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING                      **
-- ** BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-                         **
-- ** INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and                       **
-- ** (2) AMD shall not be liable (whether in contract or tort,                      **
-- ** including negligence, or under any other theory of                             **
-- ** liability) for any loss or damage of any kind or nature                        **
-- ** related to, arising under or in connection with these                          **
-- ** materials, including for any direct, or any indirect,                          **
-- ** special, incidental, or consequential loss or damage                           **
-- ** (including loss of data, profits, goodwill, or any type of                     **
-- ** loss or damage suffered as a result of any action brought                      **
-- ** by a third party) even if such damage or loss was                              **
-- ** reasonably foreseeable or AMD had been advised of the                          **
-- ** possibility of the same.                                                       **
-- **                                                                                **
-- ** CRITICAL APPLICATIONS                                                          **
-- ** AMD products are not designed or intended to be fail-                          **
-- ** safe, or for use in any application requiring fail-safe                        **
-- ** performance, such as life-support or safety devices or                         **
-- ** systems, Class III medical devices, nuclear facilities,                        **
-- ** applications related to the deployment of airbags, or any                      **
-- ** other applications that could lead to death, personal                          **
-- ** injury, or severe property or environmental damage                             **
-- ** (individually and collectively, "Critical                                      **
-- ** Applications"). Customer assumes the sole risk and                             **
-- ** liability of any use of AMD products in Critical                               **
-- ** Applications, subject only to applicable laws and                              **
-- ** regulations governing limitations on product liability.                        **
-- **                                                                                **
-- ** THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS                       **
-- ** PART OF THIS FILE AT ALL TIMES.                                                **
-- **          **
-- **          **
-- **          **
-- **          **
-- **                                                                                **
-- *************************************************************************
--

-------------------------------------------------------------------------------
-- Filename:        clk_mmcm_hbm_proc_common_pkg.vhd
-- Version:         v1.21b
-- Description:     This file contains the constants and functions used in the 
--                  processor common library components.
--
-------------------------------------------------------------------------------
-- Structure:       
--
-------------------------------------------------------------------------------
-- Author:      ALS
-- History:
--  ALS         09/12/01      -- Created from opb_arb_pkg.vhd
--
--  ALS         09/21/01        
-- ^^^^^^
--  Added pwr function. Replaced log2 function with one that works for XST.
-- ~~~~~~
--
--  ALS         12/07/01
-- ^^^^^^
--  Added Addr_bits function.
-- ~~~~~~
--  ALS         01/31/02
-- ^^^^^^
--  Added max2 function.
-- ~~~~~~
--  FLO         02/22/02
-- ^^^^^^
--  Extended input argument range of log2 function to 2^30. Also, added
--  a check that the argument does not exceed this value; a failure
--  assertion violation is generated if it does not.
-- ~~~~~~
--  FLO         08/31/06
-- ^^^^^^
--  Removed type TARGET_FAMILY_TYPE and functions Get_Reg_File_Area and
--  Get_RLOC_Name. These objects are not used. Further, the functions
--  produced misleading warnings (CR419886, CR419898).
-- ~~~~~~
--  FLO         05/25/07
-- ^^^^^^
--  -Reimplemented function pad_power2 to correct error when the input
--  argument is 1. (fixes CR 303469)
--  -Added function clog2(x), which returns the integer ceiling of the
--  base 2 logarithm of x. This function can be used in place of log2
--  when wishing to avoid the XST warning, "VHDL Assertion Statement
--  with non constant condition is ignored".
-- ~~~~~~
--
--     DET     1/17/2008     v3_00_a
-- ~~~~~~
--     - Incorporated new disclaimer header
-- ^^^^^^
--
--     DET     5/8/2009     v3_00_a for EDK L.SP2
-- ~~~~~~
--   - Per CR520627
--     - Added synthesis translate_off/on constructs to the log2 function
--       around the assertion statement. This removes a repetative XST Warning
--       in SRP files about a non-constant assertion check.
-- ^^^^^^
--  FL0         20/27/2010
-- ^^^^^^
--  Removed 42 TBD comment, again. (CR 568493)
-- ~~~~~~
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
-- need conversion function to convert reals/integers to std logic vectors
use ieee.std_logic_arith.conv_std_logic_vector;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;


package clk_mmcm_hbm_proc_common_pkg is

-------------------------------------------------------------------------------
-- Type Declarations
-------------------------------------------------------------------------------
type CHAR_TO_INT_TYPE is array (character) of integer;
-- type INTEGER_ARRAY_TYPE is array (natural range <>) of integer;
-- Type SLV64_ARRAY_TYPE is array (natural range <>) of std_logic_vector(0 to 63);

-------------------------------------------------------------------------------
-- Function and Procedure Declarations
-------------------------------------------------------------------------------
function max2 (num1, num2 : integer) return integer;
function min2 (num1, num2 : integer) return integer;
function Addr_Bits(x,y : std_logic_vector) return integer;
function clog2(x : positive) return natural;
function pad_power2 ( in_num : integer )  return integer;
function pad_4 ( in_num : integer )  return integer;
function log2(x : natural) return integer;
function pwr(x: integer; y: integer) return integer;
function String_To_Int(S : string) return integer;
function itoa (int : integer) return string;
-------------------------------------------------------------------------------
-- Constant Declarations
-------------------------------------------------------------------------------
-- the RESET_ACTIVE constant should denote the logic level of an active reset
constant RESET_ACTIVE       : std_logic         := '1'; 

-- table containing strings representing hex characters for conversion to
-- integers
constant STRHEX_TO_INT_TABLE : CHAR_TO_INT_TYPE :=
    ('0'     => 0,
     '1'     => 1,
     '2'     => 2,
     '3'     => 3,
     '4'     => 4,
     '5'     => 5,
     '6'     => 6,
     '7'     => 7,
     '8'     => 8,
     '9'     => 9,
     'A'|'a' => 10,
     'B'|'b' => 11,
     'C'|'c' => 12,
     'D'|'d' => 13,
     'E'|'e' => 14,
     'F'|'f' => 15,
     others  => -1);

 
end clk_mmcm_hbm_proc_common_pkg;

package body clk_mmcm_hbm_proc_common_pkg is
-------------------------------------------------------------------------------
-- Function Definitions
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-- Function max2
--
-- This function returns the greater of two numbers.
-------------------------------------------------------------------------------
function max2 (num1, num2 : integer) return integer is
begin
    if num1 >= num2 then
        return num1;
    else
        return num2;
    end if;
end function max2;


-------------------------------------------------------------------------------
-- Function min2
--
-- This function returns the lesser of two numbers.
-------------------------------------------------------------------------------
function min2 (num1, num2 : integer) return integer is
begin
    if num1 <= num2 then
        return num1;
    else
        return num2;
    end if;
end function min2;


-------------------------------------------------------------------------------
-- Function Addr_bits
--
-- function to convert an address range (base address and an upper address)
-- into the number of upper address bits needed for decoding a device
-- select signal.  will handle slices and big or little endian
-------------------------------------------------------------------------------
function Addr_Bits(x,y : std_logic_vector) return integer is
  variable addr_xor : std_logic_vector(x'range);
  variable count    : integer := 0;
begin
  assert x'length = y'length and (x'ascending xnor y'ascending)
    report "Addr_Bits: arguments are not the same type"
    severity ERROR;
  addr_xor := x xor y;
  for i in x'range
  loop
    if addr_xor(i) = '1' then return count;
    end if;
    count := count + 1;
  end loop;
  return x'length;
end Addr_Bits;


--------------------------------------------------------------------------------
-- Function clog2 - returns the integer ceiling of the base 2 logarithm of x,
--                  i.e., the least integer greater than or equal to log2(x).
--------------------------------------------------------------------------------
function clog2(x : positive) return natural is
  variable r  : natural := 0;
  variable rp : natural := 1; -- rp tracks the value 2**r
begin 
  while rp < x loop -- Termination condition T: x <= 2**r
    -- Loop invariant L: 2**(r-1) < x
    r := r + 1;
    if rp > integer'high - rp then exit; end if;  -- If doubling rp overflows
      -- the integer range, the doubled value would exceed x, so safe to exit.
    rp := rp + rp;
  end loop;
  -- L and T  <->  2**(r-1) < x <= 2**r  <->  (r-1) < log2(x) <= r
  return r; --
end clog2;

-------------------------------------------------------------------------------
-- Function pad_power2
--
-- This function returns the next power of 2 from the input number. If the 
-- input number is a power of 2, this function returns the input number.
--
-- This function is used to round up the number of masters to the next power
-- of 2 if the number of masters is not already a power of 2.
--
-- Input argument 0, which is not a power of two, is accepted and returns 0.
-- Input arguments less than 0 are not allowed.
-------------------------------------------------------------------------------
-- 
function pad_power2 (in_num : integer  ) return integer is
begin         
    if in_num = 0 then
        return 0;
    else
        return 2**(clog2(in_num));
    end if;
end pad_power2;




-------------------------------------------------------------------------------
-- Function pad_4
--
-- This function returns the next multiple of 4 from the input number. If the 
-- input number is a multiple of 4, this function returns the input number.
--
-------------------------------------------------------------------------------
-- 
function pad_4 (in_num : integer  ) return integer is

variable out_num     : integer;

begin
    out_num := (((in_num-1)/4) + 1)*4;
    return out_num;
    
end pad_4;

-------------------------------------------------------------------------------
-- Function log2 -- returns number of bits needed to encode x choices
--   x = 0  returns 0
--   x = 1  returns 0
--   x = 2  returns 1
--   x = 4  returns 2, etc.
-------------------------------------------------------------------------------
--
function log2(x : natural) return integer is
  variable i  : integer := 0; 
  variable val: integer := 1;
begin 
  if x = 0 then return 0;
  else
    for j in 0 to 29 loop -- for loop for XST 
      if val >= x then null; 
      else
        i := i+1;
        val := val*2;
      end if;
    end loop;
  -- Fix per CR520627  XST was ignoring this anyway and printing a  
  -- Warning in SRP file. This will get rid of the warning and not
  -- impact simulation.  
  -- synthesis translate_off
    assert val >= x
      report "Function log2 received argument larger" &
             " than its capability of 2^30. "
      severity failure;
  -- synthesis translate_on
    return i;
  end if;  
end function log2; 


-------------------------------------------------------------------------------
-- Function pwr -- x**y
-- negative numbers not allowed for y
-------------------------------------------------------------------------------

function pwr(x: integer; y: integer) return integer is
  variable z : integer := 1;
begin
  if y = 0 then return 1; 
  else
    for i in 1 to y loop
      z := z * x;
    end loop;
    return z;
  end if;
end function pwr;

-------------------------------------------------------------------------------
-- Function itoa
-- 
-- The itoa function converts an integer to a text string.
-- This function is required since `image doesn't work in Synplicity
-- Valid input range is -9999 to 9999
-------------------------------------------------------------------------------
--  
  function itoa (int : integer) return string is
    type table is array (0 to 9) of string (1 to 1);
    constant LUT     : table :=
      ("0", "1", "2", "3", "4", "5", "6", "7", "8", "9");
    variable str1            : string(1 to 1);
    variable str2            : string(1 to 2);
    variable str3            : string(1 to 3);
    variable str4            : string(1 to 4);
    variable str5            : string(1 to 5);
    variable abs_int         : natural;
    
    variable thousands_place : natural;
    variable hundreds_place  : natural;
    variable tens_place      : natural;
    variable ones_place      : natural;
    variable sign            : integer;
    
  begin
    abs_int := abs(int);
    if abs_int > int then sign := -1;
    else sign := 1;
    end if;
    thousands_place :=  abs_int/1000;
    hundreds_place :=  (abs_int-thousands_place*1000)/100;
    tens_place :=      (abs_int-thousands_place*1000-hundreds_place*100)/10;
    ones_place :=      
      (abs_int-thousands_place*1000-hundreds_place*100-tens_place*10);
    
    if sign>0 then
      if thousands_place>0 then
        str4 := LUT(thousands_place) & LUT(hundreds_place) & LUT(tens_place) &
                LUT(ones_place);
        return str4;
      elsif hundreds_place>0 then 
        str3 := LUT(hundreds_place) & LUT(tens_place) & LUT(ones_place);
        return str3;
      elsif tens_place>0 then
        str2 := LUT(tens_place) & LUT(ones_place);
        return str2;
      else
        str1 := LUT(ones_place);
        return str1;
      end if;
    else
      if thousands_place>0 then
        str5 := "-" & LUT(thousands_place) & LUT(hundreds_place) & 
          LUT(tens_place) & LUT(ones_place);
        return str5;
      elsif hundreds_place>0 then 
        str4 := "-" & LUT(hundreds_place) & LUT(tens_place) & LUT(ones_place);
        return str4;
      elsif tens_place>0 then
        str3 := "-" & LUT(tens_place) & LUT(ones_place);
        return str3;
      else
        str2 := "-" & LUT(ones_place);
        return str2;
      end if;
    end if;  
  end itoa; 
  
  

-----------------------------------------------------------------------------
-- Function String_To_Int
--
-- Converts a string of hex character to an integer
-- accept negative numbers
-----------------------------------------------------------------------------
  function String_To_Int(S : String) return Integer is
    variable Result : integer := 0;
    variable Temp   : integer := S'Left;
    variable Negative : integer := 1;
  begin
    for I in S'Left to S'Right loop
      if (S(I) = '-') then
        Temp     := 0;
        Negative := -1;
      else
        Temp := STRHEX_TO_INT_TABLE(S(I));
        if (Temp = -1) then
          assert false
            report "Wrong value in String_To_Int conversion " & S(I)
            severity error;
        end if;
      end if;
      Result := Result * 16 + Temp;
    end loop;
    return (Negative * Result);
  end String_To_Int;

end package body clk_mmcm_hbm_proc_common_pkg;
