-------------------------------------------------------------------------------
-- clk_mmcm_a_family.vhd
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
-- Filename:        clk_mmcm_a_family.vhd
--
-- Description:     
-- This HDL file provides various functions for determining features (such
-- as BRAM types) in the various device families in Xilinx products.                
--                  
--                  
--                  
-- VHDL-Standard:   VHDL'93
-------------------------------------------------------------------------------
-- Structure:   
--              clk_mmcm_a_family.vhd
--
-------------------------------------------------------------------------------
--  Revision history
--
-- ???  ??????????   Initial version
-- jam  03/31/2003   added spartan3 to constants and derived function. Added
--                   comments to try and explain how the function is used
-- jam  04/01/2003   removed VIRTEX from the derived list for BYZANTIUM,
--                   VIRTEX2P, and SPARTAN3.  This changes VIRTEX2 to be a
--                   base family type, similar to X4K and VIRTEX
-- jam  04/02/2003   add VIRTEX back into the hierarchy of VIRTEX2P, BYZANTIUM
--                   and SPARTAN3; add additional comments showing use in
--                   VHDL
-- lss  03/24/2004   Added QVIRTEX2, QRVIRTEX2, VIRTEX4
-- flo  03/22/2005   Added SPARTAN3E
-- als  02/23/2006   Added VIRTEX5
-- flo  09/13/2006   Added SPARTAN3A and SPARTAN3A. This may allow
--                   legacy designs to support spartan3a and spartan3an in
--                   terms of BRAMs. For new work (and maintenence where
--                   possible) this package, family, should be dropped in favor
--                   of the package, family_support.
--
--     DET     1/17/2008     v3_00_a
-- ~~~~~~
--     - Changed proc_common library version to v3_00_a
--     - Incorporated new disclaimer header
-- ^^^^^^
--
--------------------------------------------------------------------------------
-- @BEGIN_CHANGELOG EDK_H_SP1
-- Added spartan3e
-- @END_CHANGELOG
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

package clk_mmcm_a_family is

   -- constant declarations

  constant ANY       : string := "any";
  constant X4K       : string := "x4k";
  constant X4KE      : string := "x4ke";
  constant X4KL      : string := "x4kl";
  constant X4KEX     : string := "x4kex";
  constant X4KXL     : string := "x4kxl";
  constant X4KXV     : string := "x4kxv";
  constant X4KXLA    : string := "x4kxla";
  constant SPARTAN   : string := "spartan";
  constant SPARTANXL : string := "spartanxl";
  constant SPARTAN2  : string := "spartan2";
  constant SPARTAN2E : string := "spartan2e";
  constant VIRTEX    : string := "virtex";
  constant VIRTEXE   : string := "virtexe";
  constant VIRTEX2   : string := "virtex2";
  constant VIRTEX2P  : string := "virtex2p";
  constant BYZANTIUM : string := "byzantium";
  constant SPARTAN3  : string := "spartan3";
  constant QRVIRTEX2 : string := "qrvirtex2";
  constant QVIRTEX2  : string := "qvirtex2";
  constant VIRTEX4  : string := "virtex4";
  constant VIRTEX5  : string := "virtex5";
  constant SPARTAN3E : string := "spartan3e";
  constant SPARTAN3A : string := "spartan3a";
  constant SPARTAN3AN: string := "spartan3an";


-- function declarations

-- derived - provides a means to determine if a family specified in child is
--           the same as, or is a super set of, the family specified in
--           ancestor.
--
--           Typically, child is set to the generic specifying the family type
--           the user wishes to implement the design into (C_FAMILY), and the
--           designer hard codes ancestor to the family type supported by the
--           design.  If the design supports multiple family types, then each
--           of those family types would need to be tested against C_FAMILY
--           using this function. An example for the VIRTEX2P hierarchy
--           is shown below:
--
--              VIRTEX2P_SPECIFIC_LOGIC_GEN:
--              if derived(C_FAMILY,VIRTEX2P)
--              generate
--                   -- logic specific to Virtex2P family
--              end generate VIRTEX2P_SPECIFIC_LOGIC_GEN;
--
--              NON_VIRTEX2P_SPECIFIC_LOGIC_GEN:
--              if not derived(C_FAMILY,VIRTEX2P)
--              generate
--
--                 VIRTEX2_SPECIFIC_LOGIC_GEN:
--                 if derived(C_FAMILY,VIRTEX2)
--                 generate
--                      -- logic specific to Virtex2 family
--                 end generate VIRTEX2_SPECIFIC_LOGIC_GEN;
--
--                 NON_VIRTEX2_SPECIFIC_LOGIC_GEN
--                 if not derived(C_FAMILY,VIRTEX2)
--                 generate
--
--                   VIRTEX_SPECIFIC_LOGIC_GEN:
--                   if derived(C_FAMILY,VIRTEX)
--                   generate
--                        -- logic specific to Virtex family
--                   end generate VIRTEX_SPECIFIC_LOGIC_GEN;
--
--                   NON_VIRTEX_SPECIFIC_LOGIC_GEN;
--                   if not derived(C_FAMILY,VIRTEX)
--                   generate
--
--                     ANY_FAMILY_TYPE_LOGIC_GEN:
--                     if derived(C_FAMILY,ANY)
--                     generate
--                          -- logic not specific to any family
--                     end generate ANY_FAMILY_TYPE_LOGIC_GEN;
--
--                   end generate NON_VIRTEX_SPECIFIC_LOGIC_GEN;
--
--                 end generate NON_VIRTEX2_SPECIFIC_LOGIC_GEN;
--
--              end generate NON_VIRTEX2P_SPECIFIC_LOGIC_GEN;
--
--           This function will return TRUE if the family type specified in
--           child is equal to, or a super set of, the family type specified in
--           ancestor, otherwise it returns FALSE.
--
--           The current super sets are defined by the following list, where
--           all family types listed to the right of an item are contained in
--           the super set of that item, for all lines containing that item.
--
--             ANY, X4K, SPARTAN, SPARTANXL
--             ANY, X4K, X4KE, X4KL
--             ANY, X4K, X4KEX, X4KXL, X4KXV, X4KXLA
--             ANY, VIRTEX, SPARTAN2, SPARTAN2E
--             ANY, VIRTEX, VIRTEXE
--             ANY, VIRTEX, VIRTEX2, BYZANTIUM
--             ANY, VIRTEX, VIRTEX2, VIRTEX2P
--             ANY, VIRTEX, VIRTEX2, SPARTAN3
--
--           For exampel, all other family types are contained in the super set
--           for ANY.  Stated another way, if the designer specifies ANY
--           for the family type the design supports, then the function will
--           return TRUE for any family type the user wishes to implement the
--           design into.
--
--              if derived(C_FAMILY,ANY) generate ... end generate;
--
--           If the designer specifies VIRTEX2 as the family type supported by
--           the design, then the function will only return TRUE if the user
--           intends to implement the design in VIRTEX2, VIRTEX2P, BYZANTIUM,
--           or SPARTAN3.
--
--              if derived(C_FAMILY,VIRTEX2) generate
--                  -- logic that uses VIRTEX2 BRAMs
--              end generate;
--
--              if not derived(C_FAMILY,VIRTEX2) generate
--                  -- logic that uses non VIRTEX2 BRAMs
--              end generate;
--
--           Note:
--           The last three lines of the list above were modified from the
--           original to remove VIRTEX from those lines because, from our point
--           of view, VIRTEX2 is different enough from VIRTEX to conclude that
--           it should be its own base family type.
--
--  **************************************************************************
--                              WARNING
--  **************************************************************************
--    DO NOT RELY ON THE DERIVED FUNCTION TO PROVIDE DIFFERENTIATION BETWEEN
--    FAMILY TYPES FOR ANYTHING OTHER THAN BRAMS
--
--    Use of the derived function assumes that the designer is not using
--    RLOCs (RLOC'd FIFO's from Coregen, etc.) and that the BRAMs in the
--    derived families are similar.  If the designer is using specific
--    elements of a family type, they are responsible for ensuring that
--    those same elements are available in all family types supported by
--    their design, and that the elements function exactly the same in all
--    "similar" families.
--
--  **************************************************************************
--
  function derived ( child, ancestor : string ) return boolean;



-- equalIgnoreCase - Returns TRUE if case insensitive string comparison
--                   determines that str1 and str2 are equal, otherwise FALSE
  function equalIgnoreCase( str1, str2 : string ) return boolean;



-- toLowerCaseChar - Returns the lower case form of char if char is an upper
--                   case letter.  Otherwise char is returned.
  function toLowerCaseChar( char : character ) return character;
      
end clk_mmcm_a_family;



package body clk_mmcm_a_family is

      -- True if architecture "child" is derived from, or equal to,
      -- the architecture "ancestor".
      -- ANY, X4K, SPARTAN, SPARTANXL
      -- ANY, X4K, X4KE, X4KL
      -- ANY, X4K, X4KEX, X4KXL, X4KXV, X4KXLA
      -- ANY, VIRTEX, SPARTAN2, SPARTAN2E
      -- ANY, VIRTEX, VIRTEXE
      -- ANY, VIRTEX, VIRTEX2, BYZANTIUM
      -- ANY, VIRTEX, VIRTEX2, VIRTEX2P
      -- ANY, VIRTEX, VIRTEX2, SPARTAN3

  function derived ( child, ancestor : string ) return boolean is
    variable is_derived : boolean := FALSE;
  begin
    if equalIgnoreCase( child, VIRTEX ) then        -- base family type
      if ( equalIgnoreCase(ancestor,VIRTEX) OR
           equalIgnoreCase(ancestor,ANY)
         ) then is_derived := TRUE;
      end if;
    elsif equalIgnoreCase( child, VIRTEX2 ) then
      if ( equalIgnoreCase(ancestor,VIRTEX2) OR
           equalIgnoreCase(ancestor,VIRTEX) OR
           equalIgnoreCase(ancestor,ANY)
         ) then is_derived := TRUE;
      end if;
    elsif equalIgnoreCase( child, QRVIRTEX2 ) then
      if ( equalIgnoreCase(ancestor,QRVIRTEX2) OR
           equalIgnoreCase(ancestor,VIRTEX2) OR
           equalIgnoreCase(ancestor,VIRTEX) OR
           equalIgnoreCase(ancestor,ANY)
         ) then is_derived := TRUE;
      end if;
    elsif equalIgnoreCase( child, QVIRTEX2 ) then
      if ( equalIgnoreCase(ancestor,QVIRTEX2) OR
           equalIgnoreCase(ancestor,VIRTEX2) OR
           equalIgnoreCase(ancestor,VIRTEX) OR
           equalIgnoreCase(ancestor,ANY)
         ) then is_derived := TRUE;
      end if;
    elsif equalIgnoreCase( child, VIRTEX5 ) then
      if ( equalIgnoreCase(ancestor,VIRTEX5) OR
           equalIgnoreCase(ancestor,VIRTEX4) OR
           equalIgnoreCase(ancestor,VIRTEX2P) OR
           equalIgnoreCase(ancestor,VIRTEX2)  OR
           equalIgnoreCase(ancestor,VIRTEX) OR
           equalIgnoreCase(ancestor,ANY)
         ) then is_derived := TRUE;
      end if;
    elsif equalIgnoreCase( child, VIRTEX4 ) then
      if ( equalIgnoreCase(ancestor,VIRTEX4) OR
           equalIgnoreCase(ancestor,VIRTEX2P) OR
           equalIgnoreCase(ancestor,VIRTEX2)  OR
           equalIgnoreCase(ancestor,VIRTEX) OR
           equalIgnoreCase(ancestor,ANY)
         ) then is_derived := TRUE;
      end if;
    elsif equalIgnoreCase( child, VIRTEX2P ) then
      if ( equalIgnoreCase(ancestor,VIRTEX2P) OR
           equalIgnoreCase(ancestor,VIRTEX2)  OR
           equalIgnoreCase(ancestor,VIRTEX) OR
           equalIgnoreCase(ancestor,ANY)
         ) then is_derived := TRUE;
      end if;
    elsif equalIgnoreCase( child, BYZANTIUM ) then
      if ( equalIgnoreCase(ancestor,BYZANTIUM) OR
           equalIgnoreCase(ancestor,VIRTEX2)   OR
           equalIgnoreCase(ancestor,VIRTEX) OR
           equalIgnoreCase(ancestor,ANY)
         ) then is_derived := TRUE;
      end if;
    elsif equalIgnoreCase( child, VIRTEXE ) then
      if ( equalIgnoreCase(ancestor,VIRTEXE) OR
           equalIgnoreCase(ancestor,VIRTEX)  OR
           equalIgnoreCase(ancestor,ANY)
         ) then is_derived := TRUE;
      end if;
    elsif equalIgnoreCase( child, SPARTAN2 ) then
      if ( equalIgnoreCase(ancestor,SPARTAN2) OR
           equalIgnoreCase(ancestor,VIRTEX)   OR
           equalIgnoreCase(ancestor,ANY)
         ) then is_derived := TRUE;
      end if;
    elsif equalIgnoreCase( child, SPARTAN2E ) then
      if ( equalIgnoreCase(ancestor,SPARTAN2E) OR
           equalIgnoreCase(ancestor,SPARTAN2)  OR
           equalIgnoreCase(ancestor,VIRTEX)    OR
           equalIgnoreCase(ancestor,ANY)
         ) then is_derived := TRUE;
      end if;
    elsif equalIgnoreCase( child, SPARTAN3 ) then
      if ( equalIgnoreCase(ancestor,SPARTAN3) OR
           equalIgnoreCase(ancestor,VIRTEX2)  OR
           equalIgnoreCase(ancestor,VIRTEX) OR
           equalIgnoreCase(ancestor,ANY)
         ) then is_derived := TRUE;
      end if;
    elsif equalIgnoreCase( child, SPARTAN3E ) then
      if ( equalIgnoreCase(ancestor,SPARTAN3E) OR
           equalIgnoreCase(ancestor,SPARTAN3) OR
           equalIgnoreCase(ancestor,VIRTEX2)  OR
           equalIgnoreCase(ancestor,VIRTEX) OR
           equalIgnoreCase(ancestor,ANY)
         ) then is_derived := TRUE;
      end if;
    elsif equalIgnoreCase( child, SPARTAN3A ) then
      if ( equalIgnoreCase(ancestor,SPARTAN3A) OR
           equalIgnoreCase(ancestor,SPARTAN3E) OR
           equalIgnoreCase(ancestor,SPARTAN3) OR
           equalIgnoreCase(ancestor,VIRTEX2)  OR
           equalIgnoreCase(ancestor,VIRTEX) OR
           equalIgnoreCase(ancestor,ANY)
         ) then is_derived := TRUE;
      end if;
    elsif equalIgnoreCase( child, SPARTAN3AN ) then
      if ( equalIgnoreCase(ancestor,SPARTAN3AN) OR
           equalIgnoreCase(ancestor,SPARTAN3E) OR
           equalIgnoreCase(ancestor,SPARTAN3) OR
           equalIgnoreCase(ancestor,VIRTEX2)  OR
           equalIgnoreCase(ancestor,VIRTEX) OR
           equalIgnoreCase(ancestor,ANY)
         ) then is_derived := TRUE;
      end if;
    elsif equalIgnoreCase( child, X4K ) then        -- base family type
      if ( equalIgnoreCase(ancestor,X4K) OR
           equalIgnoreCase(ancestor,ANY)
         ) then is_derived := TRUE;
      end if;
    elsif equalIgnoreCase( child, X4KEX ) then
      if ( equalIgnoreCase(ancestor,X4KEX) OR
           equalIgnoreCase(ancestor,X4K)   OR
           equalIgnoreCase(ancestor,ANY)
         ) then is_derived := TRUE;
      end if;
    elsif equalIgnoreCase( child, X4KXL ) then
      if ( equalIgnoreCase(ancestor,X4KXL) OR
           equalIgnoreCase(ancestor,X4KEX) OR
           equalIgnoreCase(ancestor,X4K)   OR
           equalIgnoreCase(ancestor,ANY)
         ) then is_derived := TRUE;
      end if;
    elsif equalIgnoreCase( child, X4KXV ) then
      if ( equalIgnoreCase(ancestor,X4KXV) OR
           equalIgnoreCase(ancestor,X4KXL) OR
           equalIgnoreCase(ancestor,X4KEX) OR
           equalIgnoreCase(ancestor,X4K)   OR
           equalIgnoreCase(ancestor,ANY)
         ) then is_derived := TRUE;
      end if;
    elsif equalIgnoreCase( child, X4KXLA ) then
      if ( equalIgnoreCase(ancestor,X4KXLA) OR
           equalIgnoreCase(ancestor,X4KXV)  OR
           equalIgnoreCase(ancestor,X4KXL)  OR
           equalIgnoreCase(ancestor,X4KEX)  OR
           equalIgnoreCase(ancestor,X4K)    OR
           equalIgnoreCase(ancestor,ANY)
         ) then is_derived := TRUE;
      end if;
    elsif equalIgnoreCase( child, X4KE ) then
      if ( equalIgnoreCase(ancestor,X4KE) OR
           equalIgnoreCase(ancestor,X4K)  OR
           equalIgnoreCase(ancestor,ANY)
         ) then is_derived := TRUE;
      end if;
    elsif equalIgnoreCase( child, X4KL ) then
      if ( equalIgnoreCase(ancestor,X4KL) OR
           equalIgnoreCase(ancestor,X4KE) OR
           equalIgnoreCase(ancestor,X4K)  OR
           equalIgnoreCase(ancestor,ANY)
         ) then is_derived := TRUE;
      end if;
    elsif equalIgnoreCase( child, SPARTAN ) then
      if ( equalIgnoreCase(ancestor,SPARTAN) OR
           equalIgnoreCase(ancestor,X4K)     OR
           equalIgnoreCase(ancestor,ANY)
         ) then is_derived := TRUE;
      end if;
    elsif equalIgnoreCase( child, SPARTANXL ) then
      if ( equalIgnoreCase(ancestor,SPARTANXL) OR
           equalIgnoreCase(ancestor,SPARTAN)   OR
           equalIgnoreCase(ancestor,X4K)       OR
           equalIgnoreCase(ancestor,ANY)
         ) then is_derived := TRUE;
      end if;
    elsif equalIgnoreCase( child, ANY ) then
      if equalIgnoreCase( ancestor, any ) then is_derived := TRUE;
      end if;
    end if;

         return is_derived;
     end derived;


     -- Returns the lower case form of char if char is an upper case letter.
     -- Otherwise char is returned.
     function toLowerCaseChar( char : character ) return character is
     begin
        -- If char is not an upper case letter then return char
        if char < 'A' OR char > 'Z' then
          return char;
        end if;
        -- Otherwise map char to its corresponding lower case character and
        -- return that
        case char is
          when 'A' => return 'a';
          when 'B' => return 'b';
          when 'C' => return 'c';
          when 'D' => return 'd';
          when 'E' => return 'e';
          when 'F' => return 'f';
          when 'G' => return 'g';
          when 'H' => return 'h';
          when 'I' => return 'i';
          when 'J' => return 'j';
          when 'K' => return 'k';
          when 'L' => return 'l';
          when 'M' => return 'm';
          when 'N' => return 'n';
          when 'O' => return 'o';
          when 'P' => return 'p';
          when 'Q' => return 'q';
          when 'R' => return 'r';
          when 'S' => return 's';
          when 'T' => return 't';
          when 'U' => return 'u';
          when 'V' => return 'v';
          when 'W' => return 'w';
          when 'X' => return 'x';
          when 'Y' => return 'y';
          when 'Z' => return 'z';
          when others => return char;
        end case;
     end toLowerCaseChar;
      

     -- Returns true if case insensitive string comparison determines that
     -- str1 and str2 are equal
     function equalIgnoreCase( str1, str2 : string ) return boolean is
       constant LEN1 : integer := str1'length;
       constant LEN2 : integer := str2'length;
       variable equal : boolean := TRUE;
     begin
        if not (LEN1 = LEN2) then
          equal := FALSE;
        else
          for i in str1'range loop
            if not (toLowerCaseChar(str1(i)) = toLowerCaseChar(str2(i))) then
              equal := FALSE;
            end if;
          end loop;
        end if;

        return equal;
     end equalIgnoreCase;
      
 end clk_mmcm_a_family;

