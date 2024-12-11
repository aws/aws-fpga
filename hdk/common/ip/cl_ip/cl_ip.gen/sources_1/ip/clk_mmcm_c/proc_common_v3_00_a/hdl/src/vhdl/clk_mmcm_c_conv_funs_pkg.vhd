----------------------------------------------------------------------------
-- conv_funs_pkg.vhd
-------------------------------------------------------------------------------
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
----------------------------------------------------------------------------
-- Filename:        conv_funs_pkg.vhd
--
-- Description:     
-- Various string conversion functions.                
--                  
--                  
--                  
-- VHDL-Standard:   VHDL'93
-------------------------------------------------------------------------------
-- Structure:   
--              conv_funs_pkg.vhd
--
-------------------------------------------------------------------------------
-- Revision History:
--
--
-- Author:          unknown
-- Revision:        $Revision: 1.1.4.1 $
-- Date:            $1/1/2002$
--
-- History:
--   XXX   1/1/2002       Initial Version
--  
--     DET     1/17/2008     v3_00_a
-- ~~~~~~
--     - Incorporated new disclaimer header
-- ^^^^^^
--
-------------------------------------------------------------------------------
library IEEE;
use IEEE.std_logic_1164.all;

package clk_mmcm_c_conv_funs_pkg is

  -- hex string to std_logic_vector
  function hex_string_to_slv (instring      : STRING;
                              return_length : POSITIVE range 1 to 64 := 32)
    return STD_LOGIC_VECTOR;

  -- octal string to std_logic_vector
  function oct_string_to_slv (instring      : STRING;
                              return_length : POSITIVE range 1 to 64 := 32)
    return STD_LOGIC_VECTOR;

  -- binary string to std_logic_vector
  function bin_string_to_slv (instring      : STRING;
                              return_length : POSITIVE range 1 to 64 := 32)
    return STD_LOGIC_VECTOR;

  --  string to std_logic_vector
  function string_to_std_logic_vector (instring      : STRING;
                                       return_length : POSITIVE range 1 to 64 := 32)
    return STD_LOGIC_VECTOR;

end clk_mmcm_c_conv_funs_pkg;

-- 
--------------------------------------------------------------------------------
-- 

package body clk_mmcm_c_conv_funs_pkg is

  type basetype is (binary, octal, decimal, hex);

  function max(x, y : INTEGER) return INTEGER is
  begin
    if x > y then return x; else return y; end if;
  end max;

  function MIN(x, y : INTEGER) return INTEGER is
  begin
    if x < y then return x; else return y; end if;
  end MIN;


  function hex_string_to_slv (instring      : STRING;
                              return_length : POSITIVE range 1 to 64 := 32) 
    return STD_LOGIC_VECTOR is
    -- if return_length is < than instring'length*4, result will be truncated on the left
    -- if instring is other than characters 0 to 9 or a,A to f,F or 
    -- x,X,z,Z,u,U,-,w,W, 
    --   those result bits will be set to 0
    variable temp_string   : STRING(1 to instring'LENGTH)                                 := instring;
    variable vector_size   : POSITIVE                                                     := max(instring'LENGTH*4, return_length);
    variable char_ptr      : INTEGER range -3 to max(instring'LENGTH*4, return_length)    := max(instring'LENGTH*4, return_length);
    variable return_vector : STD_LOGIC_VECTOR(1 to max(instring'LENGTH*4, return_length)) := (others => '0');
  begin
    for i in temp_string'REVERSE_RANGE loop
      case temp_string(i) is
        when '0'     => return_vector(char_ptr-3 to char_ptr) := "0000";
        when '1'     => return_vector(char_ptr-3 to char_ptr) := "0001";
        when '2'     => return_vector(char_ptr-3 to char_ptr) := "0010";
        when '3'     => return_vector(char_ptr-3 to char_ptr) := "0011";
        when '4'     => return_vector(char_ptr-3 to char_ptr) := "0100";
        when '5'     => return_vector(char_ptr-3 to char_ptr) := "0101";
        when '6'     => return_vector(char_ptr-3 to char_ptr) := "0110";
        when '7'     => return_vector(char_ptr-3 to char_ptr) := "0111";
        when '8'     => return_vector(char_ptr-3 to char_ptr) := "1000";
        when '9'     => return_vector(char_ptr-3 to char_ptr) := "1001";
        when 'a'|'A' => return_vector(char_ptr-3 to char_ptr) := "1010";
        when 'b'|'B' => return_vector(char_ptr-3 to char_ptr) := "1011";
        when 'c'|'C' => return_vector(char_ptr-3 to char_ptr) := "1100";
        when 'd'|'D' => return_vector(char_ptr-3 to char_ptr) := "1101";
        when 'e'|'E' => return_vector(char_ptr-3 to char_ptr) := "1110";
        when 'f'|'F' => return_vector(char_ptr-3 to char_ptr) := "1111";
-- xst doesn't handle these
--        when 'U'     => return_vector(char_ptr-3 to char_ptr) := "UUUU";
--        when 'X'     => return_vector(char_ptr-3 to char_ptr) := "XXXX";
--        when 'Z'     => return_vector(char_ptr-3 to char_ptr) := "ZZZZ";
--        when 'W'     => return_vector(char_ptr-3 to char_ptr) := "WWWW";
--        when 'H'     => return_vector(char_ptr-3 to char_ptr) := "HHHH";
--        when 'L'     => return_vector(char_ptr-3 to char_ptr) := "LLLL";
--        when '-'     => return_vector(char_ptr-3 to char_ptr) := "----";
-- but synplicity does
        when '_'     => char_ptr                              := char_ptr + 4;
        when others  =>
          assert FALSE
            report lf &
            "hex_string_to_slv conversion found illegal input character: " & 
            temp_string(i) & lf & "converting character to '----'"
            severity WARNING;
          return_vector(char_ptr-3 to char_ptr) := "----";
      end case;
      char_ptr := char_ptr - 4;
    end loop;
    return return_vector(vector_size-return_length+1 to vector_size);
  end hex_string_to_slv;

  function oct_string_to_slv (instring      : STRING;
                              return_length : POSITIVE range 1 to 64 := 32)
    return STD_LOGIC_VECTOR is
    -- if return_length is < than instring'length*3, result will be truncated on the left
    -- if instring is other than characters 0 to 7 or or x,X,z,Z,u,U,-,w,W,
    --   those result bits will be set to 0
    variable temp_string   : STRING(1 to instring'LENGTH)                                 := instring;
    variable vector_size   : POSITIVE                                                     := max(instring'LENGTH*3, return_length);
    variable char_ptr      : INTEGER range -2 to max(instring'LENGTH*3, return_length)    := max(instring'LENGTH*3, return_length);
    variable return_vector : STD_LOGIC_VECTOR(1 to max(instring'LENGTH*3, return_length)) := (others => '0');
  begin
    for i in temp_string'REVERSE_RANGE loop
      case temp_string(i) is
        when '0'    => return_vector(char_ptr-2 to char_ptr) := "000";
        when '1'    => return_vector(char_ptr-2 to char_ptr) := "001";
        when '2'    => return_vector(char_ptr-2 to char_ptr) := "010";
        when '3'    => return_vector(char_ptr-2 to char_ptr) := "011";
        when '4'    => return_vector(char_ptr-2 to char_ptr) := "100";
        when '5'    => return_vector(char_ptr-2 to char_ptr) := "101";
        when '6'    => return_vector(char_ptr-2 to char_ptr) := "110";
        when '7'    => return_vector(char_ptr-2 to char_ptr) := "111";
-- xst doesn't handle these
--        when 'U'    => return_vector(char_ptr-2 to char_ptr) := "UUU";
--        when 'X'    => return_vector(char_ptr-2 to char_ptr) := "XXX";
--        when 'Z'    => return_vector(char_ptr-2 to char_ptr) := "ZZZ";
--        when 'W'    => return_vector(char_ptr-2 to char_ptr) := "WWW";
--        when 'H'    => return_vector(char_ptr-2 to char_ptr) := "HHH";
--        when 'L'    => return_vector(char_ptr-2 to char_ptr) := "LLL";
--        when '-'    => return_vector(char_ptr-2 to char_ptr) := "---";
-- but synplicity does
        when '_'    => char_ptr                              := char_ptr + 3;
        when others =>
          assert FALSE
            report lf &
            "oct_string_to_slv conversion found illegal input character: " & 
            temp_string(i) & lf & "converting character to '---'"
            severity WARNING;
          return_vector(char_ptr-2 to char_ptr) := "---";
      end case;
      char_ptr := char_ptr - 3;
    end loop;
    return return_vector(vector_size-return_length+1 to vector_size);
  end oct_string_to_slv;

  function bin_string_to_slv (instring      : STRING;
                              return_length : POSITIVE range 1 to 64 := 32)
    return STD_LOGIC_VECTOR is
    -- if return_length is < than instring'length, result will be truncated on the left
    -- if instring is other than characters 0 to 1 or x,X,z,Z,u,U,-,w,W, 
    --   those result bits will be set to 0
    variable temp_string   : STRING(1 to instring'LENGTH)                               := instring;
    variable vector_size   : POSITIVE                                                   := max(instring'LENGTH, return_length);
    variable char_ptr      : INTEGER range 0 to max(instring'LENGTH, return_length)+1   := max(instring'LENGTH, return_length);
    variable return_vector : STD_LOGIC_VECTOR(1 to max(instring'LENGTH, return_length)) := (others => '0');
  begin
    for i in temp_string'REVERSE_RANGE loop
      case temp_string(i) is
        when '0'    => return_vector(char_ptr) := '0';
        when '1'    => return_vector(char_ptr) := '1';
-- xst doesn't handle these
--        when 'U'    => return_vector(char_ptr) := 'U';
--        when 'X'    => return_vector(char_ptr) := 'X';
--        when 'Z'    => return_vector(char_ptr) := 'Z';
--        when 'W'    => return_vector(char_ptr) := 'W';
--        when 'H'    => return_vector(char_ptr) := 'H';
--        when 'L'    => return_vector(char_ptr) := 'L';
--        when '-'    => return_vector(char_ptr) := '-';
-- but synplicity does
        when '_'    => char_ptr                := char_ptr + 1;
        when others =>
          assert FALSE
            report lf &
            "bin_string_to_slv conversion found illegal input character: " & 
            temp_string(i) & lf & "converting character to '-'"
            severity WARNING;
          return_vector(char_ptr) := '-';
      end case;
      char_ptr := char_ptr - 1;
    end loop;
    return return_vector(vector_size-return_length+1 to vector_size);
  end bin_string_to_slv;

  function string_to_std_logic_vector (instring      : STRING;
                                       return_length : POSITIVE range 1 to 64 := 32)
    return STD_LOGIC_VECTOR is
    variable instring_length : POSITIVE := instring'LENGTH;
    variable temp_string     : STRING(1 to instring'LENGTH-2);
  begin  -- function string_to_std_logic_vector
    if instring(1) = '0' and (instring(2) = 'x' or instring(2) = 'X') then
      temp_string := instring(3 to instring_length);
      return hex_string_to_slv(temp_string, return_length);
    elsif instring(1) = '0' and (instring(2) = 'o' or instring(2) = 'O') then
      temp_string := instring(3 to instring_length);
      return oct_string_to_slv(temp_string, return_length);
    elsif instring(1) = '0' and (instring(2) = 'b' or instring(2) = 'B') then
      temp_string := instring(3 to instring_length);
      return bin_string_to_slv(temp_string, return_length);
    else
      return bin_string_to_slv(instring, return_length);
    end if;
    
  end function string_to_std_logic_vector;
  
end clk_mmcm_c_conv_funs_pkg;
