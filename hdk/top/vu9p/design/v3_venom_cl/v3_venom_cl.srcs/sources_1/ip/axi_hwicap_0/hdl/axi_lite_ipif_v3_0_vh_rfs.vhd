-- IPIF Common Library Package  
-------------------------------------------------------------------------------
--
-- *************************************************************************
-- **                                                                     **
-- ** DISCLAIMER OF LIABILITY                                             **
-- **                                                                     **
-- ** This text/file contains proprietary, confidential                   **
-- ** information of Xilinx, Inc., is distributed under                   **
-- ** license from Xilinx, Inc., and may be used, copied                  **
-- ** and/or disclosed only pursuant to the terms of a valid              **
-- ** license agreement with Xilinx, Inc. Xilinx hereby                   **
-- ** grants you a license to use this text/file solely for               **
-- ** design, simulation, implementation and creation of                  **
-- ** design files limited to Xilinx devices or technologies.             **
-- ** Use with non-Xilinx devices or technologies is expressly            **
-- ** prohibited and immediately terminates your license unless           **
-- ** covered by a separate agreement.                                    **
-- **                                                                     **
-- ** Xilinx is providing this design, code, or information               **
-- ** "as-is" solely for use in developing programs and                   **
-- ** solutions for Xilinx devices, with no obligation on the             **
-- ** part of Xilinx to provide support. By providing this design,        **
-- ** code, or information as one possible implementation of              **
-- ** this feature, application or standard, Xilinx is making no          **
-- ** representation that this implementation is free from any            **
-- ** claims of infringement. You are responsible for obtaining           **
-- ** any rights you may require for your implementation.                 **
-- ** Xilinx expressly disclaims any warranty whatsoever with             **
-- ** respect to the adequacy of the implementation, including            **
-- ** but not limited to any warranties or representations that this      **
-- ** implementation is free from claims of infringement, implied         **
-- ** warranties of merchantability or fitness for a particular           **
-- ** purpose.                                                            **
-- **                                                                     **
-- ** Xilinx products are not intended for use in life support            **
-- ** appliances, devices, or systems. Use in such applications is        **
-- ** expressly prohibited.                                               **
-- **                                                                     **
-- ** Any modifications that are made to the Source Code are              **
-- ** done at the user’s sole risk and will be unsupported.               **
-- ** The Xilinx Support Hotline does not have access to source           **
-- ** code and therefore cannot answer specific questions related         **
-- ** to source HDL. The Xilinx Hotline support of original source        **
-- ** code IP shall only address issues and questions related             **
-- ** to the standard Netlist version of the core (and thus               **
-- ** indirectly, the original core source).                              **
-- **                                                                     **
-- ** Copyright (c) 2002-2010 Xilinx, Inc. All rights reserved.           **
-- **                                                                     **
-- ** This copyright and support notice must be retained as part          **
-- ** of this text at all times.                                          **
-- **                                                                     **
-- *************************************************************************
--

-------------------------------------------------------------------------------
-- Filename:        ipif_pkg.vhd
-- Version:         Intital
-- Description:     This file contains the constants and functions used in the 
--                  ipif common library components.
--
-------------------------------------------------------------------------------
-- Structure:       
--
-------------------------------------------------------------------------------
-- Author:      DET
-- History:
--  DET         02/21/02      -- Created from proc_common_pkg.vhd
--
--  DET         03/13/02      -- PLB IPIF development updates
-- ^^^^^^
--              - Commented out string types and string functions due to an XST
--                problem with string arrays and functions. THe string array
--                processing functions were replaced with comperable functions
--                operating on integer arrays.
-- ~~~~~~
--
--
--     DET     4/30/2002     Initial
-- ~~~~~~
--     - Added three functions: rebuild_slv32_array, rebuild_slv64_array, and
--       rebuild_int_array to support removal of unused elements from the 
--       ARD arrays.
-- ^^^^^^ --
--
--     FLO     8/12/2002
-- ~~~~~~
--     - Added three functions: bits_needed_for_vac, bits_needed_for_occ,
--       and get_id_index_iboe.
--       (Removed provisional functions bits_needed_for_vacancy,
--        bits needed_for_occupancy, and bits_needed_for.)
-- ^^^^^^
--
--     FLO     3/24/2003
-- ~~~~~~
--     - Added dependent property paramters for channelized DMA.
--     - Added common property parameter array type.
--     - Definded the KEYHOLD_BURST common-property parameter.
-- ^^^^^^
--
--     FLO     10/22/2003
-- ~~~~~~
--     - Some adjustment to CHDMA parameterization.
--     - Cleanup of obsolete code and comments. (The former "XST workaround"
--       has become the officially deployed method.)
-- ^^^^^^
--
--     LSS     03/24/2004
-- ~~~~~~
--     - Added 5 functions
-- ^^^^^^
--
--      ALS     09/03/04
-- ^^^^^^
--      -- Added constants to describe the channel protocols used in MCH_OPB_IPIF
-- ~~~~~~
--
--     DET     1/17/2008     v4_0
-- ~~~~~~
--     - Changed proc_common library version to v4_0
--     - Incorporated new disclaimer header
-- ^^^^^^
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
use ieee.std_logic_arith.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;


package ipif_pkg is


-------------------------------------------------------------------------------
-- Type Declarations
-------------------------------------------------------------------------------
type    SLV32_ARRAY_TYPE is array (natural range <>) of std_logic_vector(0 to 31);
subtype SLV64_TYPE is std_logic_vector(0 to 63);
type    SLV64_ARRAY_TYPE is array (natural range <>) of SLV64_TYPE;
type    INTEGER_ARRAY_TYPE is array (natural range <>) of integer;

-------------------------------------------------------------------------------
-- Function and Procedure Declarations
-------------------------------------------------------------------------------
function "=" (s1: in string; s2: in string) return boolean;

function equaluseCase( str1, str2 : STRING ) RETURN BOOLEAN;

function calc_num_ce (ce_num_array : INTEGER_ARRAY_TYPE) return integer;

function calc_start_ce_index (ce_num_array : INTEGER_ARRAY_TYPE;
                              index        : integer) return integer;
                              
function get_min_dwidth (dwidth_array: INTEGER_ARRAY_TYPE) return integer;

function get_max_dwidth (dwidth_array: INTEGER_ARRAY_TYPE) return integer;

function S32 (in_string : string) return string;


--------------------------------------------------------------------------------
-- ARD support functions.
-- These function can be useful when operating with the ARD parameterization.
--------------------------------------------------------------------------------

function get_id_index (id_array :INTEGER_ARRAY_TYPE; 
                       id       : integer)
                       return integer;

function get_id_index_iboe (id_array :INTEGER_ARRAY_TYPE; 
                       id       : integer)
                       return integer;


function find_ard_id (id_array : INTEGER_ARRAY_TYPE;
                      id       : integer) return boolean;


function find_id_dwidth (id_array    : INTEGER_ARRAY_TYPE; 
                         dwidth_array: INTEGER_ARRAY_TYPE;
                         id          : integer;
                         default_i   : integer) 
                         return integer;


function cnt_ipif_id_blks (id_array : INTEGER_ARRAY_TYPE) return integer;

function get_ipif_id_dbus_index (id_array : INTEGER_ARRAY_TYPE;
                                 id          : integer)
                                 return integer ;


function rebuild_slv32_array (slv32_array     : SLV32_ARRAY_TYPE;
                              num_valid_pairs : integer)
                              return SLV32_ARRAY_TYPE;

function rebuild_slv64_array (slv64_array     : SLV64_ARRAY_TYPE;
                              num_valid_pairs : integer)
                              return SLV64_ARRAY_TYPE;


function rebuild_int_array (int_array       : INTEGER_ARRAY_TYPE;
                            num_valid_entry : integer)
                            return INTEGER_ARRAY_TYPE;

-- 5 Functions Added 3/24/04

function populate_intr_mode_array (num_user_intr        : integer;
                                   intr_capture_mode    : integer)
                                  return INTEGER_ARRAY_TYPE ;

function add_intr_ard_id_array(include_intr    : boolean;
                              ard_id_array     : INTEGER_ARRAY_TYPE)
                              return INTEGER_ARRAY_TYPE; 

function add_intr_ard_addr_range_array(include_intr    : boolean;
                              ZERO_ADDR_PAD        : std_logic_vector;
                              intr_baseaddr            : std_logic_vector;
                              intr_highaddr            : std_logic_vector;
                              ard_id_array             : INTEGER_ARRAY_TYPE;
                              ard_addr_range_array     : SLV64_ARRAY_TYPE)
                              return SLV64_ARRAY_TYPE; 

function add_intr_ard_num_ce_array(include_intr     : boolean;
                              ard_id_array          : INTEGER_ARRAY_TYPE;
                              ard_num_ce_array      : INTEGER_ARRAY_TYPE)
                              return INTEGER_ARRAY_TYPE; 

function add_intr_ard_dwidth_array(include_intr    : boolean;
                              intr_dwidth           : integer;
                              ard_id_array          : INTEGER_ARRAY_TYPE;
                              ard_dwidth_array      : INTEGER_ARRAY_TYPE)
                              return INTEGER_ARRAY_TYPE; 

function log2(x : natural) return integer;
function clog2(x : positive) return natural;


-------------------------------------------------------------------------------
-- Constant Declarations
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-- Channel Protocols
--  The constant declarations below give symbolic-name aliases for values that 
--  can be used in the C_MCH_PROTOCOL_ARRAY generic of the MCH_OPB_IPIF.
-------------------------------------------------------------------------------
constant XCL                    : integer := 0;
constant DAG                    : integer := 1;

--------------------------------------------------------------------------------
-- Address range types.
-- The constant declarations, below, give symbolic-name aliases for values
-- that can be used in the C_ARD_ID_ARRAY generic of IPIFs. The first set
-- gives aliases that are used to include IPIF services.
--------------------------------------------------------------------------------
-- IPIF module aliases
Constant IPIF_INTR              : integer := 1;
Constant IPIF_RST               : integer := 2;
Constant IPIF_SESR_SEAR         : integer := 3;
Constant IPIF_DMA_SG            : integer := 4;
Constant IPIF_WRFIFO_REG        : integer := 5;
Constant IPIF_WRFIFO_DATA       : integer := 6;
Constant IPIF_RDFIFO_REG        : integer := 7;
Constant IPIF_RDFIFO_DATA       : integer := 8;
Constant IPIF_CHDMA_CHANNELS    : integer := 9;
Constant IPIF_CHDMA_GLOBAL_REGS : integer := 10;
Constant CHDMA_STATUS_FIFO      : integer := 90;

-- Some predefined user module aliases
Constant USER_00                : integer := 100;
Constant USER_01                : integer := 101;
Constant USER_02                : integer := 102;
Constant USER_03                : integer := 103;
Constant USER_04                : integer := 104;
Constant USER_05                : integer := 105;
Constant USER_06                : integer := 106;
Constant USER_07                : integer := 107;
Constant USER_08                : integer := 108;
Constant USER_09                : integer := 109;
Constant USER_10                : integer := 110;
Constant USER_11                : integer := 111;
Constant USER_12                : integer := 112;
Constant USER_13                : integer := 113;
Constant USER_14                : integer := 114;
Constant USER_15                : integer := 115;
Constant USER_16                : integer := 116;
        
                                          
                                          
---( Start  of Dependent Properties declarations
--------------------------------------------------------------------------------
-- Declarations for Dependent Properties (properties that depend on the type of
-- the address range, or in other words, address-range-specific parameters).
-- There is one property, i.e. one parameter, encoded as an integer at
-- each index of the properties array. There is one properties array for
-- each address range.
-- 
-- The C_ARD_DEPENDENT_PROPS_ARRAY generic parameter in (most) IPIFs is such
-- a properties array and it is usually giving its (static) value using a
-- VHDL aggregate construct.  (--ToDo, give an example of this.)
--
-- The the "assigned" default value of a dependent property is zero. This value
-- is usually specified the aggregate by leaving its (index) name out so that
-- it is covered by an "others => 0" choice in the aggregate. Some parameters,
-- as noted in the definitions, below, have an "effective" default value that is
-- different from the assigned default value of zero. In such cases, the
-- function, eff_dp, given below, can be used to get the effective value of
-- the dependent property.
--------------------------------------------------------------------------------

constant DEPENDENT_PROPS_SIZE : integer := 32;

subtype DEPENDENT_PROPS_TYPE
         is INTEGER_ARRAY_TYPE(0 to DEPENDENT_PROPS_SIZE-1);

type DEPENDENT_PROPS_ARRAY_TYPE
         is array (natural range <>) of DEPENDENT_PROPS_TYPE;


--------------------------------------------------------------------------------
-- Below are the indices of dependent properties for the different types of
-- address ranges.
--
-- Example: Let C_ARD_DEPENDENT_PROPS_ARRAY hold the dependent properites
-- for a set of address ranges. Then, e.g.,
--
--   C_ARD_DEPENDENT_PROPS_ARRAY(i)(FIFO_CAPACITY_BITS)
--
-- gives the fifo capacity in bits, provided that the i'th address range
-- is of type IPIF_WRFIFO_DATA or IPIF_RDFIFO_DATA.
--
-- These indices should be referenced only by the names below and never
-- by numerical literals. (The right to change numerical index assignments
-- is reserved; applications using the names will not be affected by such
-- reassignments.)
--------------------------------------------------------------------------------
--
--ToDo, if the interrupt controller parameterization is ever moved to
--      C_ARD_DEPENDENT_PROPS_ARRAY, then the following declarations
--      could be uncommented and used.
---- IPIF_INTR                                                               IDX
---------------------------------------------------------------------------- ---
constant EXCLUDE_DEV_ISC                                       : integer := 0;
      -- 1 specifies that only the global interrupt
      -- enable is present in the device interrupt source
      -- controller and that the only source of interrupts
      -- in the device is the IP interrupt source controller.
      -- 0 specifies that the full device interrupt
      -- source controller structure will be included.
constant INCLUDE_DEV_PENCODER                                  : integer := 1;
      -- 1 will include the Device IID in the device interrupt
      -- source controller, 0 will exclude it.


--
-- IPIF_WRFIFO_DATA or IPIF_RDFIFO_DATA                                      IDX
---------------------------------------------------------------------------- ---
constant FIFO_CAPACITY_BITS                                      : integer := 0;
constant WR_WIDTH_BITS                                           : integer := 1;
constant RD_WIDTH_BITS                                           : integer := 2;
constant EXCLUDE_PACKET_MODE                                     : integer := 3;
      -- 1  Don't include packet mode features
      -- 0  Include packet mode features
constant EXCLUDE_VACANCY                                         : integer := 4;
      -- 1  Don't include vacancy calculation
      -- 0  Include vacancy calculation
      --    See also the functions
      --    bits_needed_for_vac  and
      --    bits_needed_for_occ  that are declared below.
constant INCLUDE_DRE                                             : integer := 5;
constant INCLUDE_AUTOPUSH_POP                                    : integer := 6;
constant AUTOPUSH_POP_CE                                         : integer := 7;
constant INCLUDE_CSUM                                            : integer := 8;
--------------------------------------------------------------------------------

--
-- DMA_SG                                                                    IDX
---------------------------------------------------------------------------- ---
--------------------------------------------------------------------------------

-- IPIF_CHDMA_CHANNELS                                                       IDX
---------------------------------------------------------------------------- ---
constant NUM_SUBS_FOR_PHYS_0                                     : integer :=0;
constant NUM_SUBS_FOR_PHYS_1                                     : integer :=1;
constant NUM_SUBS_FOR_PHYS_2                                     : integer :=2;
constant NUM_SUBS_FOR_PHYS_3                                     : integer :=3;
constant NUM_SUBS_FOR_PHYS_4                                     : integer :=4;
constant NUM_SUBS_FOR_PHYS_5                                     : integer :=5;
constant NUM_SUBS_FOR_PHYS_6                                     : integer :=6;
constant NUM_SUBS_FOR_PHYS_7                                     : integer :=7;
constant NUM_SUBS_FOR_PHYS_8                                     : integer :=8;
constant NUM_SUBS_FOR_PHYS_9                                     : integer :=9;
constant NUM_SUBS_FOR_PHYS_10                                    : integer :=10;
constant NUM_SUBS_FOR_PHYS_11                                    : integer :=11;
constant NUM_SUBS_FOR_PHYS_12                                    : integer :=12;
constant NUM_SUBS_FOR_PHYS_13                                    : integer :=13;
constant NUM_SUBS_FOR_PHYS_14                                    : integer :=14;
constant NUM_SUBS_FOR_PHYS_15                                    : integer :=15;
      -- Gives the number of sub-channels for physical channel i.
      --
      -- These constants, which will be MAX_NUM_PHYS_CHANNELS in number (see
      -- below), have consecutive values starting with 0 for
      -- NUM_SUBS_FOR_PHYS_0. (The constants serve the purpose of giving symbolic
      -- names for use in the dependent-properties aggregates that parameterize
      -- an IPIF_CHDMA_CHANNELS address range.)
      --  
      -- [Users can ignore this note for developers
      --   If the number of physical channels changes, both the
      --   IPIF_CHDMA_CHANNELS constants and MAX_NUM_PHYS_CHANNELS,
      --   below, must be adjusted.
      --   (Use of an array constant or a function of the form
      --    NUM_SUBS_FOR_PHYS(i) to define the indices
      --    runs afoul of LRM restrictions on non-locally static aggregate
      --    choices. (Further, the LRM imposes perhaps unnecessarily
      --    strict limits on what qualifies as a locally static primary.)
      --    Note: This information is supplied for the benefit of anyone seeking
      --    to improve the way that these NUM_SUBS_FOR_PHYS parameter
      --    indices are defined.)
      -- End of note for developers ]
      --
      -- The value associated with any index NUM_SUBS_FOR_PHYS_i in the
      -- dependent-properties array must be even since TX and RX channels
      -- come in pairs with the TX followed immediately by
      -- the corresponding RX.
      --
constant NUM_SIMPLE_DMA_CHANS                                  : integer :=16;
      -- The number of simple DMA channels.
constant NUM_SIMPLE_SG_CHANS                                   : integer :=17;
      -- The number of simple SG channels.
constant INTR_COALESCE                                         : integer :=18;
      -- 0 Interrupt coalescing is disabled
      -- 1 Interrupt coalescing is enabled
constant CLK_PERIOD_PS                                         : integer :=19;
      -- The period of the OPB Bus clock in ps.
      -- The default value of 0 is a special value that
      -- is synonymous with 10000 ps (10 ns).
      -- The value for CLK_PERIOD_PS is relevant only if (INTR_COALESCE = 1).
constant PACKET_WAIT_UNIT_NS                                   : integer :=20;  
      -- Gives the unit for used for timing of pack-wait bounds.
      -- The default value of 0 is a special value that
      -- is synonymous with 1,000,000 ns (1 ms) and a non-default
      -- value is typically only used for testing.
      -- Relevant only if (INTR_COALESCE = 1).
constant BURST_SIZE                                            : integer :=21;
      -- 1, 2, 4, 8 or 16 
      -- The default value of 0 is a special value that
      -- is synonymous with a burst size of 16.
      -- Setting the BURST_SIZE to 1 effectively disables
      -- bursts.
constant REMAINDER_AS_SINGLES                                  : integer :=22;
      -- 0 Remainder handled as a short burst
      -- 1 Remainder handled as a series of singles

      --------------------------------------------------------------------------------
      -- The constant below is not the index of a dependent-properties
      -- parameter (and, as such, would never appear as a choice in a
      -- dependent-properties aggregate). Rather, it is fixed to the maximum
      -- number of physical channels that an Address Range of type
      -- IPIF_CHDMA_CHANNELS supports. It must be maintained in conjuction with
      -- the constants named, e.g., NUM_SUBS_FOR_PHYS_15, above.
      --------------------------------------------------------------------------------
      constant MAX_NUM_PHYS_CHANNELS : natural := 16;


      --------------------------------------------------------------------------
      -- EXAMPLE: Here is an example dependent-properties aggregate for an 
      -- address range of type IPIF_CHDMA_CHANNELS. 
      -- To have a compact list of all of the CHDMA parameters, all are
      -- shown, however three are commented out and the unneeded
      -- MUM_SUBS_FOR_PHYS_x are excluded. The "OTHERS => 0" association
      -- gives these parameters their default values, such that, for the example
      --
      --     - All physical channels above 2 have zero subchannels (effectively,
      --       these physical channels are not used)
      --     - There are no simple SG channels
      --     - The packet-wait time unit is 1 ms
      --     - Burst size is 16
      --------------------------------------------------------------------------
      --    (
      --     NUM_SUBS_FOR_PHYS_0                        =>     8,
      --     NUM_SUBS_FOR_PHYS_1                        =>     4,
      --     NUM_SUBS_FOR_PHYS_2                        =>    14,
      --     NUM_SIMPLE_DMA_CHANS                       =>     1,
      --   --NUM_SIMPLE_SG_CHANS                        =>     5,
      --     INTR_COALESCE                              =>     1,
      --     CLK_PERIOD_PS                              => 20000,
      --   --PACKET_WAIT_UNIT_NS                        => 50000,
      --   --BURST_SIZE                                 =>     1,
      --     REMAINDER_AS_SINGLES                       =>     1,
      --     OTHERS                                     =>     0
      --    )
      --
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Calculates the number of bits needed to convey the vacancy (emptiness) of
-- the fifo described by dependent_props, if fifo_present. If not fifo_present,
-- returns 0 (or the smallest value allowed by tool limitations on null arrays)
-- without making reference to dependent_props.
--------------------------------------------------------------------------------
function  bits_needed_for_vac(
              fifo_present: boolean;
              dependent_props : DEPENDENT_PROPS_TYPE
          ) return integer;

--------------------------------------------------------------------------------
-- Calculates the number of bits needed to convey the occupancy (fullness) of
-- the fifo described by dependent_props, if fifo_present. If not fifo_present,
-- returns 0 (or the smallest value allowed by tool limitations on null arrays)
-- without making reference to dependent_props.
--------------------------------------------------------------------------------
function  bits_needed_for_occ(
              fifo_present: boolean;
              dependent_props : DEPENDENT_PROPS_TYPE
          ) return integer;

--------------------------------------------------------------------------------
-- Function eff_dp.
--
-- For some of the dependent properties, the default value of zero is meant
-- to imply an effective default value of other than zero (see e.g.
-- PKT_WAIT_UNIT_NS for the IPIF_CHDMA_CHANNELS address-range type). The
-- following function is used to get the (possibly default-adjusted)
-- value for a dependent property.
--
-- Example call:
--
--    eff_value_of_param :=
--        eff_dp(
--            C_IPIF_CHDMA_CHANNELS,
--            PACKET_WAIT_UNIT_NS,
--            C_ARD_DEPENDENT_PROPS_ARRAY(i)(PACKET_WAIT_UNIT_NS)
--        );
--
--    where C_ARD_DEPENDENT_PROPS_ARRAY(i) is an object of type
--    DEPENDENT_PROPS_ARRAY_TYPE, that was parameterized for an address range of
--    type C_IPIF_CHDMA_CHANNELS.
--------------------------------------------------------------------------------
function eff_dp(id       : integer;  -- The type of address range.
                dep_prop : integer;  -- The index of the dependent prop.
                value    : integer   -- The value at that index.
               ) return    integer;  -- The effective value, possibly adjusted
                                     -- if value has the default value of 0.

---) End  of Dependent Properties declarations


--------------------------------------------------------------------------------
-- Declarations for Common Properties (properties that apply regardless of the
-- type of the address range). Structurally, these work the same as
-- the dependent properties.
--------------------------------------------------------------------------------

constant COMMON_PROPS_SIZE : integer := 2;

subtype COMMON_PROPS_TYPE
         is INTEGER_ARRAY_TYPE(0 to COMMON_PROPS_SIZE-1);

type COMMON_PROPS_ARRAY_TYPE
         is array (natural range <>) of COMMON_PROPS_TYPE;

--------------------------------------------------------------------------------
-- Below are the indices of the common properties.
--
-- These indices should be referenced only by the names below and never
-- by numerical literals.
--                                                                           IDX
---------------------------------------------------------------------------- ---
constant KEYHOLE_BURST                                           : integer := 0;
      -- 1 All addresses of a burst are forced to the initial
      --   address of the burst.
      -- 0 Burst addresses follow the bus protocol.




-- IP interrupt mode array constants
Constant INTR_PASS_THRU         : integer := 1;
Constant INTR_PASS_THRU_INV     : integer := 2;
Constant INTR_REG_EVENT         : integer := 3;
Constant INTR_REG_EVENT_INV     : integer := 4;
Constant INTR_POS_EDGE_DETECT   : integer := 5;
Constant INTR_NEG_EDGE_DETECT   : integer := 6;




 
end ipif_pkg;




package body ipif_pkg is

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
-- Function Definitions
-------------------------------------------------------------------------------


-----------------------------------------------------------------------------
-- Function "="
--
-- This function can be used to overload the "=" operator when comparing
-- strings.
-----------------------------------------------------------------------------
  function "=" (s1: in string; s2: in string) return boolean is
      constant tc: character := ' ';  -- string termination character
      variable i: integer := 1;
      variable v1 : string(1 to s1'length) := s1;
      variable v2 : string(1 to s2'length) := s2;
  begin
      while (i <= v1'length) and (v1(i) /= tc) and
            (i <= v2'length) and (v2(i) /= tc) and
            (v1(i) = v2(i))
      loop
          i := i+1;
      end loop;
      return ((i > v1'length) or (v1(i) = tc)) and
             ((i > v2'length) or (v2(i) = tc));
  end;




----------------------------------------------------------------------------
-- Function equaluseCase
--
-- This function returns true if case sensitive string comparison determines
-- that str1 and str2 are the same.
-----------------------------------------------------------------------------
   FUNCTION equaluseCase( str1, str2 : STRING ) RETURN BOOLEAN IS
     CONSTANT len1 : INTEGER := str1'length;
     CONSTANT len2 : INTEGER := str2'length;
     VARIABLE equal : BOOLEAN := TRUE;
   BEGIN
      IF NOT (len1=len2) THEN
        equal := FALSE;
      ELSE
        FOR i IN str1'range LOOP
          IF NOT (str1(i) = str2(i)) THEN
            equal := FALSE;
          END IF;
        END LOOP;
      END IF;

      RETURN equal;
   END equaluseCase;
 

-----------------------------------------------------------------------------
-- Function calc_num_ce
--
-- This function is used to process the array specifying the number of Chip
-- Enables required for a Base Address specification. The array is input to
-- the function and an integer is returned reflecting the total number of 
-- Chip Enables required for the CE, RdCE, and WrCE Buses
-----------------------------------------------------------------------------
  function calc_num_ce (ce_num_array : INTEGER_ARRAY_TYPE) return integer is

     Variable ce_num_sum : integer := 0;

  begin
    
    for i in 0 to (ce_num_array'length)-1 loop
        ce_num_sum := ce_num_sum + ce_num_array(i);
    End loop;
     
    return(ce_num_sum);
       
  end function calc_num_ce;


-----------------------------------------------------------------------------
-- Function calc_start_ce_index
--
-- This function is used to process the array specifying the number of Chip
-- Enables required for a Base Address specification. The CE Size array is 
-- input to the function and an integer index representing the index of the 
-- target module in the ce_num_array. An integer is returned reflecting the 
-- starting index of the assigned Chip Enables within the CE, RdCE, and 
-- WrCE Buses.
-----------------------------------------------------------------------------
 function calc_start_ce_index (ce_num_array : INTEGER_ARRAY_TYPE;
                               index        : integer) return integer is

    Variable ce_num_sum : integer := 0;

 begin
   If (index = 0) Then
     ce_num_sum := 0;
   else
      for i in 0 to index-1 loop
          ce_num_sum := ce_num_sum + ce_num_array(i);
      End loop;
   End if;
    
   return(ce_num_sum);
      
 end function calc_start_ce_index;
 
 
-----------------------------------------------------------------------------
-- Function get_min_dwidth
--
-- This function is used to process the array specifying the data bus width
-- for each of the target modules. The dwidth_array is input to the function
-- and an integer is returned that is the smallest value found of all the 
-- entries in the array.
-----------------------------------------------------------------------------
 function get_min_dwidth (dwidth_array: INTEGER_ARRAY_TYPE) return integer is

    Variable temp_min : Integer := 1024;
    
 begin

    for i in 0 to dwidth_array'length-1 loop
        
       If (dwidth_array(i) < temp_min) Then
          temp_min := dwidth_array(i);
       else
           null;
       End if;
        
    End loop;
    
    return(temp_min);
                  
 end function get_min_dwidth;

 
 
-----------------------------------------------------------------------------
-- Function get_max_dwidth
--
-- This function is used to process the array specifying the data bus width
-- for each of the target modules. The dwidth_array is input to the function
-- and an integer is returned that is the largest value found of all the 
-- entries in the array.
-----------------------------------------------------------------------------
 function get_max_dwidth (dwidth_array: INTEGER_ARRAY_TYPE) return integer is

    Variable temp_max : Integer := 0;
    
 begin

    for i in 0 to dwidth_array'length-1 loop
        
       If (dwidth_array(i) > temp_max) Then
          temp_max := dwidth_array(i);
       else
           null;
       End if;
        
    End loop;
    
    return(temp_max);
                  
 end function get_max_dwidth;

 

-----------------------------------------------------------------------------
-- Function S32
--
-- This function is used to expand an input string to 32 characters by
-- padding with spaces. If the input string is larger than 32 characters,
-- it will truncate to 32 characters.
-----------------------------------------------------------------------------
 function S32 (in_string : string) return string is

   constant OUTPUT_STRING_LENGTH : integer := 32;
   Constant space : character := ' ';
   
   variable new_string    : string(1 to 32);
   Variable start_index   : Integer :=  in_string'length+1;
   
 begin

   If (in_string'length < OUTPUT_STRING_LENGTH) Then
    
      for i in 1 to in_string'length loop
          new_string(i) :=  in_string(i);
      End loop; 
   
      for j in start_index to OUTPUT_STRING_LENGTH loop
          new_string(j) :=  space;
      End loop; 
   
   
   else  -- use first 32 chars of in_string (truncate the rest)

      for k in 1 to OUTPUT_STRING_LENGTH loop
          new_string(k) :=  in_string(k);
      End loop; 
   
   End if;
  
   return(new_string);
  
 end function S32;
 

-----------------------------------------------------------------------------
-- Function get_id_index
--
-- This function is used to process the array specifying the target function
-- assigned to a Base Address pair address range. The id_array and a 
-- id number is input to the function. A integer is returned reflecting the
-- array index of the id matching the id input number. This function
-- should only be called if the id number is known to exist in the 
-- name_array input. This can be detirmined by using the  find_ard_id
-- function.
-----------------------------------------------------------------------------
 function get_id_index (id_array :INTEGER_ARRAY_TYPE;      
                        id       : integer) return integer is
 
    Variable match       : Boolean := false;
    Variable match_index : Integer := 10000; -- a really big number!
    
    
 begin
 
    for array_index in 0 to id_array'length-1 loop
        
               
        If (match = true) Then  -- match already found so do nothing
            
            null; 
            
        else  -- compare the numbers one by one
          
           match       := (id_array(array_index) = id);
           
           If (match) Then
              match_index := array_index;
           else
               null;
           End if;
          
        End if;
        
    End loop;
   
    return(match_index);
    
 end function get_id_index;
 

--------------------------------------------------------------------------------
-- get_id_index but return a value in bounds on error (iboe).
--
-- This function is the same as get_id_index, except that when id does
-- not exist in id_array, the value returned is any index that is
-- within the index range of id_array.
--
-- This function would normally only be used where function find_ard_id
-- is used to establish the existence of id but, even when non-existent,
-- an element of one of the ARD arrays will be computed from the
-- returned get_id_index_iboe value. See, e.g., function bits_needed_for_vac
-- and the example call, below
--
--      bits_needed_for_vac(
--        find_ard_id(C_ARD_ID_ARRAY, IPIF_RDFIFO_DATA),
--        C_ARD_DEPENDENT_PROPS_ARRAY(get_id_index_iboe(C_ARD_ID_ARRAY,
--                                                      IPIF_RDFIFO_DATA))
--      )
--------------------------------------------------------------------------------
 function get_id_index_iboe (id_array :INTEGER_ARRAY_TYPE;      
                             id       : integer) return integer is
 
    Variable match       : Boolean := false;
    Variable match_index : Integer := id_array'left; -- any valid array index
    
 begin
    for array_index in 0 to id_array'length-1 loop
        If (match = true) Then  -- match already found so do nothing
            null; 
        else  -- compare the numbers one by one
           match       := (id_array(array_index) = id);
           If (match) Then match_index := array_index;
           else null;
           End if;
        End if;
    End loop;
    return(match_index);
 end function get_id_index_iboe;
 

-----------------------------------------------------------------------------
-- Function find_ard_id
--
-- This function is used to process the array specifying the target function
-- assigned to a Base Address pair address range. The id_array and a 
-- integer id is input to the function. A boolean is returned reflecting the
-- presence (or not) of a number in the array matching the id input number.
-----------------------------------------------------------------------------
function find_ard_id (id_array : INTEGER_ARRAY_TYPE;
                      id       : integer) return boolean is
 
    Variable match       : Boolean := false;
    
 begin
 
    for array_index in 0 to id_array'length-1 loop
        
        
        If (match = true) Then  -- match already found so do nothing
            
            null; 
            
        else  -- compare the numbers one by one

           match       := (id_array(array_index) = id);
          
        End if;
        
    End loop;
   
    return(match);
    
 end function find_ard_id;
 
 
-----------------------------------------------------------------------------
-- Function find_id_dwidth
--
-- This function is used to find the data width of a target module. If the
-- target module exists, the data width is extracted from the input dwidth 
-- array. If the module is not in the ID array, the default input is 
-- returned. This function is needed to assign data port size constraints on
-- unconstrained port widths.
-----------------------------------------------------------------------------
function find_id_dwidth (id_array    : INTEGER_ARRAY_TYPE; 
                        dwidth_array: INTEGER_ARRAY_TYPE;
                        id          : integer;
                        default_i   : integer) return integer is


     Variable id_present   : Boolean := false;
     Variable array_index  : Integer := 0;
     Variable dwidth       : Integer := default_i;

 begin

    id_present := find_ard_id(id_array, id);
   
    If (id_present) Then
      array_index :=  get_id_index (id_array, id);
      dwidth      :=  dwidth_array(array_index);
    else
       null; -- use default input 
    End if;
   
   
   Return (dwidth);
   
 end function find_id_dwidth;

 
 
 

-----------------------------------------------------------------------------
-- Function cnt_ipif_id_blks
--
-- This function is used to detirmine the number of IPIF components specified
-- in the ARD ID Array. An integer is returned representing the number
-- of elements counted. User IDs are ignored in the counting process.
-----------------------------------------------------------------------------
function cnt_ipif_id_blks (id_array : INTEGER_ARRAY_TYPE) 
                           return integer is

    Variable blk_count   : integer := 0;
    Variable temp_id     : integer;
    
 begin
 
    for array_index in 0 to id_array'length-1 loop
        
        temp_id :=  id_array(array_index);
        
        If (temp_id = IPIF_WRFIFO_DATA or
            temp_id = IPIF_RDFIFO_DATA or
            temp_id = IPIF_RST or
            temp_id = IPIF_INTR or
            temp_id = IPIF_DMA_SG or
            temp_id = IPIF_SESR_SEAR
           ) Then  -- IPIF block found
            
            blk_count := blk_count+1; 
            
        else  -- go to next loop iteration
          
            null;
          
        End if;
        
    End loop;
   
    return(blk_count);
    
end function cnt_ipif_id_blks;



-----------------------------------------------------------------------------
-- Function get_ipif_id_dbus_index
--
-- This function is used to detirmine the IPIF relative index of a given
-- ID value. User IDs are ignored in the index detirmination.
-----------------------------------------------------------------------------
function get_ipif_id_dbus_index (id_array : INTEGER_ARRAY_TYPE;
                                 id       : integer)
                                 return integer is
    
    Variable blk_index   : integer := 0;
    Variable temp_id     : integer;
    Variable id_found    : Boolean := false;
    
begin

    for array_index in 0 to id_array'length-1 loop
        
        temp_id :=  id_array(array_index);
        
        If (id_found) then

           null;
            
        elsif (temp_id = id) then
        
          id_found := true;
        
        elsif (temp_id = IPIF_WRFIFO_DATA or 
               temp_id = IPIF_RDFIFO_DATA or 
               temp_id = IPIF_RST or         
               temp_id = IPIF_INTR or        
               temp_id = IPIF_DMA_SG or      
               temp_id = IPIF_SESR_SEAR      
              ) Then  -- IPIF block found
            
            blk_index := blk_index+1; 
            
        else  -- user block so do nothing
          
            null;
          
        End if;
        
    End loop;
   
    return(blk_index);
    
   
end function get_ipif_id_dbus_index;



 ------------------------------------------------------------------------------ 
 -- Function: rebuild_slv32_array
 --
 -- Description:
 -- This function takes an input slv32 array and rebuilds an output slv32
 -- array composed of the first "num_valid_entry" elements from the input 
 -- array.
 ------------------------------------------------------------------------------ 
 function rebuild_slv32_array (slv32_array  : SLV32_ARRAY_TYPE;
                               num_valid_pairs : integer)
                               return SLV32_ARRAY_TYPE is
 
      --Constants
      constant num_elements          : Integer := num_valid_pairs * 2;
      
      -- Variables
      variable temp_baseaddr32_array :  SLV32_ARRAY_TYPE( 0 to num_elements-1);
 
 begin
 
     for array_index in 0 to num_elements-1 loop
     
        temp_baseaddr32_array(array_index) := slv32_array(array_index);
     
     end loop;
   
   
     return(temp_baseaddr32_array);
   
 end function rebuild_slv32_array;
 


  
 ------------------------------------------------------------------------------ 
 -- Function: rebuild_slv64_array
 --
 -- Description:
 -- This function takes an input slv64 array and rebuilds an output slv64
 -- array composed of the first "num_valid_entry" elements from the input 
 -- array.
 ------------------------------------------------------------------------------ 
 function rebuild_slv64_array (slv64_array  : SLV64_ARRAY_TYPE;
                               num_valid_pairs : integer)
                               return SLV64_ARRAY_TYPE is
 
      --Constants
      constant num_elements          : Integer := num_valid_pairs * 2;
      
      -- Variables
      variable temp_baseaddr64_array :  SLV64_ARRAY_TYPE( 0 to num_elements-1);
 
 begin
 
     for array_index in 0 to num_elements-1 loop
     
        temp_baseaddr64_array(array_index) := slv64_array(array_index);
     
     end loop;
   
   
     return(temp_baseaddr64_array);
   
 end function rebuild_slv64_array;
 


 ------------------------------------------------------------------------------ 
 -- Function: rebuild_int_array
 --
 -- Description:
 -- This function takes an input integer array and rebuilds an output integer
 -- array composed of the first "num_valid_entry" elements from the input 
 -- array.
 ------------------------------------------------------------------------------ 
 function rebuild_int_array (int_array       : INTEGER_ARRAY_TYPE;
                             num_valid_entry : integer)
                             return INTEGER_ARRAY_TYPE is
 
      -- Variables
      variable temp_int_array   : INTEGER_ARRAY_TYPE( 0 to num_valid_entry-1);
 
 begin
 
     for array_index in 0 to num_valid_entry-1 loop
     
        temp_int_array(array_index) := int_array(array_index);
     
     end loop;
   
   
     return(temp_int_array);
   
 end function rebuild_int_array;
 

 
    function  bits_needed_for_vac(
                  fifo_present: boolean;
                  dependent_props : DEPENDENT_PROPS_TYPE
              ) return integer is
    begin
        if not fifo_present then
            return 1; -- Zero would be better but leads to "0 to -1" null
                      -- ranges that are not handled by XST Flint or earlier
                      -- because of the negative index.
        else
            return
            log2(1 + dependent_props(FIFO_CAPACITY_BITS) /
                     dependent_props(RD_WIDTH_BITS)
            );
        end if;
    end function bits_needed_for_vac;


    function  bits_needed_for_occ(
                  fifo_present: boolean;
                  dependent_props : DEPENDENT_PROPS_TYPE
              ) return integer is
    begin
        if not fifo_present then
            return 1; -- Zero would be better but leads to "0 to -1" null
                      -- ranges that are not handled by XST Flint or earlier
                      -- because of the negative index.
        else
            return
            log2(1 + dependent_props(FIFO_CAPACITY_BITS) /
                     dependent_props(WR_WIDTH_BITS)
            );
        end if;
    end function bits_needed_for_occ;


    function eff_dp(id       : integer;
                    dep_prop : integer;
                    value    : integer) return integer is
        variable dp : integer := dep_prop;
        type     bo2na_type is array (boolean) of natural;
        constant bo2na : bo2na_type := (0, 1);
    begin
        if value /= 0 then return value; end if; -- Not default
        case id is
            when IPIF_CHDMA_CHANNELS =>
                 -------------------
                 return(   bo2na(dp =  CLK_PERIOD_PS          ) * 10000
                         + bo2na(dp =  PACKET_WAIT_UNIT_NS    ) * 1000000
                         + bo2na(dp =  BURST_SIZE             ) * 16
                       );
            when others => return 0;
        end case;
    end eff_dp;


function populate_intr_mode_array (num_user_intr        : integer;
                                   intr_capture_mode    : integer)
                                   return INTEGER_ARRAY_TYPE is
    variable intr_mode_array    : INTEGER_ARRAY_TYPE(0 to num_user_intr-1);
begin
    for i in 0 to num_user_intr-1 loop
        intr_mode_array(i) := intr_capture_mode;
    end loop;
    
    return intr_mode_array;
end function populate_intr_mode_array;


function add_intr_ard_id_array(include_intr    : boolean;
                              ard_id_array     : INTEGER_ARRAY_TYPE)
                              return INTEGER_ARRAY_TYPE is
    variable intr_ard_id_array   : INTEGER_ARRAY_TYPE(0 to ard_id_array'length);
begin
    intr_ard_id_array(0 to ard_id_array'length-1) := ard_id_array;
    if include_intr then
       intr_ard_id_array(ard_id_array'length) := IPIF_INTR;
       return intr_ard_id_array;
    else
        return ard_id_array;
    end if;
end function add_intr_ard_id_array;


function add_intr_ard_addr_range_array(include_intr    : boolean;
                              ZERO_ADDR_PAD        : std_logic_vector;
                              intr_baseaddr            : std_logic_vector;
                              intr_highaddr            : std_logic_vector;
                              ard_id_array             : INTEGER_ARRAY_TYPE;
                              ard_addr_range_array     : SLV64_ARRAY_TYPE)
                              return SLV64_ARRAY_TYPE is
    variable intr_ard_addr_range_array   : SLV64_ARRAY_TYPE(0 to ard_addr_range_array'length+1);
begin
    intr_ard_addr_range_array(0 to ard_addr_range_array'length-1) := ard_addr_range_array;
    if include_intr  then
       intr_ard_addr_range_array(2*get_id_index(ard_id_array,IPIF_INTR)) 
                        := ZERO_ADDR_PAD & intr_baseaddr;
       intr_ard_addr_range_array(2*get_id_index(ard_id_array,IPIF_INTR)+1) 
                        := ZERO_ADDR_PAD & intr_highaddr;
       return intr_ard_addr_range_array;
    else
        return ard_addr_range_array;
    end if;
end function add_intr_ard_addr_range_array;

function add_intr_ard_dwidth_array(include_intr    : boolean;
                              intr_dwidth           : integer;
                              ard_id_array          : INTEGER_ARRAY_TYPE;
                              ard_dwidth_array      : INTEGER_ARRAY_TYPE)
                              return INTEGER_ARRAY_TYPE is
    variable intr_ard_dwidth_array   : INTEGER_ARRAY_TYPE(0 to ard_dwidth_array'length);
begin
    intr_ard_dwidth_array(0 to ard_dwidth_array'length-1) := ard_dwidth_array;
    if include_intr  then
       intr_ard_dwidth_array(get_id_index(ard_id_array, IPIF_INTR)) := intr_dwidth;
       return intr_ard_dwidth_array;
    else
        return ard_dwidth_array;
    end if;
end function add_intr_ard_dwidth_array;

function add_intr_ard_num_ce_array(include_intr     : boolean;
                              ard_id_array          : INTEGER_ARRAY_TYPE;
                              ard_num_ce_array      : INTEGER_ARRAY_TYPE)
                              return INTEGER_ARRAY_TYPE is
    variable intr_ard_num_ce_array   : INTEGER_ARRAY_TYPE(0 to ard_num_ce_array'length);
begin
    intr_ard_num_ce_array(0 to ard_num_ce_array'length-1) := ard_num_ce_array;
    if include_intr  then
       intr_ard_num_ce_array(get_id_index(ard_id_array, IPIF_INTR)) := 16;
       return intr_ard_num_ce_array;
    else
        return ard_num_ce_array;
    end if;
end function add_intr_ard_num_ce_array;


end package body ipif_pkg;


-- pselect_f.vhd - entity/architecture pair
-------------------------------------------------------------------------------
--
-- *************************************************************************
-- **                                                                     **
-- ** DISCLAIMER OF LIABILITY                                             **
-- **                                                                     **
-- ** This text/file contains proprietary, confidential                   **
-- ** information of Xilinx, Inc., is distributed under                   **
-- ** license from Xilinx, Inc., and may be used, copied                  **
-- ** and/or disclosed only pursuant to the terms of a valid              **
-- ** license agreement with Xilinx, Inc. Xilinx hereby                   **
-- ** grants you a license to use this text/file solely for               **
-- ** design, simulation, implementation and creation of                  **
-- ** design files limited to Xilinx devices or technologies.             **
-- ** Use with non-Xilinx devices or technologies is expressly            **
-- ** prohibited and immediately terminates your license unless           **
-- ** covered by a separate agreement.                                    **
-- **                                                                     **
-- ** Xilinx is providing this design, code, or information               **
-- ** "as-is" solely for use in developing programs and                   **
-- ** solutions for Xilinx devices, with no obligation on the             **
-- ** part of Xilinx to provide support. By providing this design,        **
-- ** code, or information as one possible implementation of              **
-- ** this feature, application or standard, Xilinx is making no          **
-- ** representation that this implementation is free from any            **
-- ** claims of infringement. You are responsible for obtaining           **
-- ** any rights you may require for your implementation.                 **
-- ** Xilinx expressly disclaims any warranty whatsoever with             **
-- ** respect to the adequacy of the implementation, including            **
-- ** but not limited to any warranties or representations that this      **
-- ** implementation is free from claims of infringement, implied         **
-- ** warranties of merchantability or fitness for a particular           **
-- ** purpose.                                                            **
-- **                                                                     **
-- ** Xilinx products are not intended for use in life support            **
-- ** appliances, devices, or systems. Use in such applications is        **
-- ** expressly prohibited.                                               **
-- **                                                                     **
-- ** Any modifications that are made to the Source Code are              **
-- ** done at the user’s sole risk and will be unsupported.               **
-- ** The Xilinx Support Hotline does not have access to source           **
-- ** code and therefore cannot answer specific questions related         **
-- ** to source HDL. The Xilinx Hotline support of original source        **
-- ** code IP shall only address issues and questions related             **
-- ** to the standard Netlist version of the core (and thus               **
-- ** indirectly, the original core source).                              **
-- **                                                                     **
-- ** Copyright (c) 2008-2010 Xilinx, Inc. All rights reserved.           **
-- **                                                                     **
-- ** This copyright and support notice must be retained as part          **
-- ** of this text at all times.                                          **
-- **                                                                     **
-- *************************************************************************
--
-------------------------------------------------------------------------------
-- Filename:        pselect_f.vhd
--
-- Description:
--                  (Note: At least as early as I.31, XST implements a carry-
--                   chain structure for most decoders when these are coded in
--                   inferrable VHLD. An example of such code can be seen
--                   below in the "INFERRED_GEN" Generate Statement.
--
--                   ->  New code should not need to instantiate pselect-type
--                       components.
--
--                   ->  Existing code can be ported to Virtex5 and later by
--                       replacing pselect instances by pselect_f instances.
--                       As long as the C_FAMILY parameter is not included
--                       in the Generic Map, an inferred implementation
--                       will result.
--
--                   ->  If the designer wishes to force an explicit carry-
--                       chain implementation, pselect_f can be used with
--                       the C_FAMILY parameter set to the target
--                       Xilinx FPGA family.
--                  )
--
--                  Parameterizeable peripheral select (address decode).
--                  AValid qualifier comes in on Carry In at bottom
--                  of carry chain.
--
--
-- VHDL-Standard:   VHDL'93
-------------------------------------------------------------------------------
-- Structure:       pselect_f.vhd
--                    family_support.vhd
--
-------------------------------------------------------------------------------
-- History:
-- Vaibhav & FLO   05/26/06    First Version
--
--     DET     1/17/2008     v4_0
-- ~~~~~~
--     - Changed proc_common library version to v4_0
--     - Incorporated new disclaimer header
-- ^^^^^^
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


-----------------------------------------------------------------------------
-- Entity section
-----------------------------------------------------------------------------
-------------------------------------------------------------------------------
-- Definition of Generics:
--          C_AB            -- number of address bits to decode
--          C_AW            -- width of address bus
--          C_BAR           -- base address of peripheral (peripheral select
--                             is asserted when the C_AB most significant
--                             address bits match the C_AB most significant
--                             C_BAR bits
-- Definition of Ports:
--          A               -- address input
--          AValid          -- address qualifier
--          CS              -- peripheral select
-------------------------------------------------------------------------------

entity pselect_f is

  generic (
    C_AB     : integer := 9;
    C_AW     : integer := 32;
    C_BAR    : std_logic_vector;
    C_FAMILY : string := "nofamily"
    );
  port (
    A        : in   std_logic_vector(0 to C_AW-1);
    AValid   : in   std_logic;
    CS       : out  std_logic
    );

end entity pselect_f;

-----------------------------------------------------------------------------
-- Architecture section
-----------------------------------------------------------------------------

architecture imp of pselect_f is



  -----------------------------------------------------------------------------
  -- C_BAR may not be indexed from 0 and may not be ascending;
  -- BAR recasts C_BAR to have these properties.
  -----------------------------------------------------------------------------
  constant BAR          : std_logic_vector(0 to C_BAR'length-1) := C_BAR;

 -- type bo2sl_type is array (boolean) of std_logic;
 -- constant bo2sl  : bo2sl_type := (false => '0', true => '1');
 
  function min(i, j: integer) return integer is
  begin
      if i<j then return i; else return j; end if;
  end;

begin

  ------------------------------------------------------------------------------
  -- Check that the generics are valid.
  ------------------------------------------------------------------------------
  -- synthesis translate_off
     assert (C_AB <= C_BAR'length) and (C_AB <= C_AW)
     report "pselect_f generic error: " &
            "(C_AB <= C_BAR'length) and (C_AB <= C_AW)" &
            " does not hold."
     severity failure;
  -- synthesis translate_on


  ------------------------------------------------------------------------------
  -- Build a behavioral decoder
  ------------------------------------------------------------------------------
  
    XST_WA:if C_AB > 0 generate
      CS  <= AValid when A(0 to C_AB-1) = BAR (0 to C_AB-1) else
             '0' ;
    end generate XST_WA;
    
    PASS_ON_GEN:if C_AB = 0 generate
      CS  <= AValid ;
    end generate PASS_ON_GEN;
    



end imp;



-------------------------------------------------------------------
-- (c) Copyright 1984 - 2012 Xilinx, Inc. All rights reserved.
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
-------------------------------------------------------------------
-- ************************************************************************
--
-------------------------------------------------------------------------------
-- Filename:        address_decoder.vhd
-- Version:         v2.0
-- Description:     Address decoder utilizing unconstrained arrays for Base
--                  Address specification and ce number.
-------------------------------------------------------------------------------
-- Structure:   This section shows the hierarchical structure of axi_lite_ipif.
--
--              --axi_lite_ipif.vhd
--                    --slave_attachment.vhd
--                       --address_decoder.vhd
-------------------------------------------------------------------------------
-- Author:      BSB
--
-- History:
--
--  BSB      05/20/10      -- First version
-- ~~~~~~
--  - Created the first version v1.00.a
-- ^^^^^^
-- ~~~~~~
--  SK       08/09/2010    --
--  - updated the core with optimziation. Closed CR 574507
--  - combined the CE generation logic to further optimize the code.
-- ^^^^^^
-- ~~~~~~
--  SK       12/16/12      -- v2.0
--  1. up reved to major version for 2013.1 Vivado release. No logic updates.
--  2. Updated the version of AXI LITE IPIF to v2.0 in X.Y format
--  3. updated the proc common version to proc_common_base_v5_0
--  4. No Logic Updates
-- ^^^^^^
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

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.numeric_std.all;

--library proc_common_base_v5_0;
--use proc_common_base_v5_0.proc_common_pkg.clog2;
--use proc_common_base_v5_0.pselect_f;
--use proc_common_base_v5_0.ipif_pkg.all;

library axi_lite_ipif_v3_0_4;
use axi_lite_ipif_v3_0_4.ipif_pkg.all;

-------------------------------------------------------------------------------
--                     Definition of Generics
-------------------------------------------------------------------------------
-- C_BUS_AWIDTH          -- Address bus width
-- C_S_AXI_MIN_SIZE      -- Minimum address range of the IP
-- C_ARD_ADDR_RANGE_ARRAY-- Base /High Address Pair for each Address Range
-- C_ARD_NUM_CE_ARRAY    -- Desired number of chip enables for an address range
-- C_FAMILY              -- Target FPGA family
-------------------------------------------------------------------------------
--                  Definition of Ports
-------------------------------------------------------------------------------
-- Bus_clk               -- Clock
-- Bus_rst               -- Reset
-- Address_In_Erly       -- Adddress in
-- Address_Valid_Erly    -- Address is valid
-- Bus_RNW               -- Read or write registered
-- Bus_RNW_Erly          -- Read or Write
-- CS_CE_ld_enable       -- chip select and chip enable registered
-- Clear_CS_CE_Reg       -- Clear_CS_CE_Reg clear
-- RW_CE_ld_enable       -- Read or Write Chip Enable
-- CS_for_gaps           -- CS generation for the gaps between address ranges
-- CS_Out                -- Chip select
-- RdCE_Out              -- Read Chip enable
-- WrCE_Out              -- Write chip enable
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-- Entity Declaration
-------------------------------------------------------------------------------

entity address_decoder is
    generic (
        C_BUS_AWIDTH          : integer := 32;
        C_S_AXI_MIN_SIZE      : std_logic_vector(0 to 31) := X"000001FF";
        C_ARD_ADDR_RANGE_ARRAY: SLV64_ARRAY_TYPE :=
            (
             X"0000_0000_1000_0000", --  IP user0 base address
             X"0000_0000_1000_01FF", --  IP user0 high address
             X"0000_0000_1000_0200", --  IP user1 base address
             X"0000_0000_1000_02FF"  --  IP user1 high address
            );
        C_ARD_NUM_CE_ARRAY  : INTEGER_ARRAY_TYPE :=
            (
             8,     -- User0 CE Number
             1      -- User1 CE Number
            );
        C_FAMILY            : string  := "virtex6"
    );
  port (
        Bus_clk             : in  std_logic;
        Bus_rst             : in  std_logic;

        -- PLB Interface signals
        Address_In_Erly     : in  std_logic_vector(0 to C_BUS_AWIDTH-1);
        Address_Valid_Erly  : in  std_logic;
        Bus_RNW             : in  std_logic;
        Bus_RNW_Erly        : in  std_logic;

        -- Registering control signals
        CS_CE_ld_enable     : in  std_logic;
        Clear_CS_CE_Reg     : in  std_logic;
        RW_CE_ld_enable     : in  std_logic;
        CS_for_gaps         : out std_logic;
        -- Decode output signals
        CS_Out              : out std_logic_vector
                                (0 to ((C_ARD_ADDR_RANGE_ARRAY'LENGTH)/2)-1);
        RdCE_Out            : out std_logic_vector
                                (0 to calc_num_ce(C_ARD_NUM_CE_ARRAY)-1);
        WrCE_Out            : out std_logic_vector
                                (0 to calc_num_ce(C_ARD_NUM_CE_ARRAY)-1)
    );
end entity address_decoder;

-------------------------------------------------------------------------------
-- Architecture section
-------------------------------------------------------------------------------

architecture IMP of address_decoder is
----------------------------------------------------------------------------------
-- below attributes are added to reduce the synth warnings in Vivado tool
attribute DowngradeIPIdentifiedWarnings: string;
attribute DowngradeIPIdentifiedWarnings of imp : architecture is "yes";
----------------------------------------------------------------------------------

-- local type declarations ----------------------------------------------------
type decode_bit_array_type is Array(natural range 0 to (
                           (C_ARD_ADDR_RANGE_ARRAY'LENGTH)/2)-1) of
                           integer;

type short_addr_array_type is Array(natural range 0 to
                           C_ARD_ADDR_RANGE_ARRAY'LENGTH-1) of
                           std_logic_vector(0 to C_BUS_AWIDTH-1);
-------------------------------------------------------------------------------
-- Function Declarations
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- This function converts a 64 bit address range array to a AWIDTH bit
-- address range array.
-------------------------------------------------------------------------------
function slv64_2_slv_awidth(slv64_addr_array   : SLV64_ARRAY_TYPE;
                            awidth             : integer)
                        return short_addr_array_type is

    variable temp_addr   : std_logic_vector(0 to 63);
    variable slv_array   : short_addr_array_type;
    begin
        for array_index in 0 to slv64_addr_array'length-1 loop
            temp_addr := slv64_addr_array(array_index);
            slv_array(array_index) := temp_addr((64-awidth) to 63);
        end loop;
        return(slv_array);
    end function slv64_2_slv_awidth;

-------------------------------------------------------------------------------
--Function Addr_bits
--function to convert an address range (base address and an upper address)
--into the number of upper address bits needed for decoding a device
--select signal.  will handle slices and big or little endian
-------------------------------------------------------------------------------
function Addr_Bits (x,y : std_logic_vector(0 to C_BUS_AWIDTH-1))
                    return integer is
    variable addr_nor : std_logic_vector(0 to C_BUS_AWIDTH-1);
    begin
        addr_nor := x xor y;
        for i in 0 to C_BUS_AWIDTH-1 loop
            if addr_nor(i)='1' then
                return i;
            end if;
        end loop;
--coverage off
        return(C_BUS_AWIDTH);
--coverage on
    end function Addr_Bits;


-------------------------------------------------------------------------------
--Function Get_Addr_Bits
--function calculates the array which has the decode bits for the each address
--range.
-------------------------------------------------------------------------------
function Get_Addr_Bits (baseaddrs : short_addr_array_type)
                        return decode_bit_array_type is

    variable num_bits : decode_bit_array_type;
    begin
        for i in 0 to ((baseaddrs'length)/2)-1 loop

            num_bits(i) :=  Addr_Bits (baseaddrs(i*2),
                                       baseaddrs(i*2+1));
        end loop;
        return(num_bits);
    end function Get_Addr_Bits;


-------------------------------------------------------------------------------
-- NEEDED_ADDR_BITS
--
-- Function Description:
--  This function calculates the number of address bits required
-- to support the CE generation logic. This is determined by
-- multiplying the number of CEs for an address space by the
-- data width of the address space (in bytes). Each address
-- space entry is processed and the biggest of the spaces is
-- used to set the number of address bits required to be latched
-- and used for CE decoding. A minimum value of 1 is returned by
-- this function.
--
-------------------------------------------------------------------------------
function needed_addr_bits (ce_array   : INTEGER_ARRAY_TYPE)
                            return integer is

    constant NUM_CE_ENTRIES     : integer := CE_ARRAY'length;
    variable biggest            : integer := 2;
    variable req_ce_addr_size   : integer := 0;
    variable num_addr_bits      : integer := 0;
    begin

        for i in 0 to NUM_CE_ENTRIES-1 loop
            req_ce_addr_size := ce_array(i) * 4;
            if (req_ce_addr_size > biggest) Then
                biggest := req_ce_addr_size;
            end if;
        end loop;
        num_addr_bits := clog2(biggest);
        return(num_addr_bits);
    end function NEEDED_ADDR_BITS;

-----------------------------------------------------------------------------
-- Function calc_high_address
--
-- This function is used to calculate the high address of the each address
-- range
-----------------------------------------------------------------------------
 function calc_high_address (high_address : short_addr_array_type;
                index      : integer) return std_logic_vector is

    variable calc_high_addr : std_logic_vector(0 to C_BUS_AWIDTH-1);

 begin
   If (index = (C_ARD_ADDR_RANGE_ARRAY'length/2-1)) Then
     calc_high_addr := C_S_AXI_MIN_SIZE(32-C_BUS_AWIDTH to 31);
   else
     calc_high_addr := high_address(index*2+2);
   end if;
   return(calc_high_addr);
 end function calc_high_address;

----------------------------------------------------------------------------
-- Constant Declarations
-------------------------------------------------------------------------------
constant ARD_ADDR_RANGE_ARRAY   : short_addr_array_type :=
                                    slv64_2_slv_awidth(C_ARD_ADDR_RANGE_ARRAY,
                                                       C_BUS_AWIDTH);

constant NUM_BASE_ADDRS         : integer := (C_ARD_ADDR_RANGE_ARRAY'length)/2;

constant DECODE_BITS            : decode_bit_array_type :=
                                    Get_Addr_Bits(ARD_ADDR_RANGE_ARRAY);

constant NUM_CE_SIGNALS         : integer :=
                                    calc_num_ce(C_ARD_NUM_CE_ARRAY);

constant NUM_S_H_ADDR_BITS      : integer :=
                                    needed_addr_bits(C_ARD_NUM_CE_ARRAY);
-------------------------------------------------------------------------------
-- Signal Declarations
-------------------------------------------------------------------------------
signal pselect_hit_i    : std_logic_vector
                            (0 to ((C_ARD_ADDR_RANGE_ARRAY'LENGTH)/2)-1);
signal cs_out_i         : std_logic_vector
                            (0 to ((C_ARD_ADDR_RANGE_ARRAY'LENGTH)/2)-1);
signal ce_expnd_i       : std_logic_vector(0 to NUM_CE_SIGNALS-1);
signal rdce_out_i       : std_logic_vector(0 to NUM_CE_SIGNALS-1);
signal wrce_out_i       : std_logic_vector(0 to NUM_CE_SIGNALS-1);

signal ce_out_i	        : std_logic_vector(0 to NUM_CE_SIGNALS-1); --

signal cs_ce_clr        : std_logic;
signal addr_out_s_h     : std_logic_vector(0 to NUM_S_H_ADDR_BITS-1);

signal Bus_RNW_reg      : std_logic;
-------------------------------------------------------------------------------
-- Begin architecture
-------------------------------------------------------------------------------
begin -- architecture IMP


-- Register clears
cs_ce_clr       <= not Bus_rst or Clear_CS_CE_Reg;

addr_out_s_h    <= Address_In_Erly(C_BUS_AWIDTH-NUM_S_H_ADDR_BITS
                                   to C_BUS_AWIDTH-1);
-------------------------------------------------------------------------------
-- MEM_DECODE_GEN: Universal Address Decode Block
-------------------------------------------------------------------------------
MEM_DECODE_GEN: for bar_index in 0 to NUM_BASE_ADDRS-1 generate
---------------
constant CE_INDEX_START : integer
                        := calc_start_ce_index(C_ARD_NUM_CE_ARRAY,bar_index);
constant CE_ADDR_SIZE   : Integer range 0 to 15
                        := clog2(C_ARD_NUM_CE_ARRAY(bar_index));
constant OFFSET         : integer := 2;

constant BASE_ADDR_x    : std_logic_vector(0 to C_BUS_AWIDTH-1)
                        := ARD_ADDR_RANGE_ARRAY(bar_index*2+1);

constant HIGH_ADDR_X    : std_logic_vector(0 to C_BUS_AWIDTH-1)
                        := calc_high_address(ARD_ADDR_RANGE_ARRAY,bar_index);
--constant DECODE_BITS_0  : integer:= DECODE_BITS(0);
---------
begin
---------

    -- GEN_FOR_MULTI_CS: Below logic generates the CS for decoded address
    -- -----------------
    GEN_FOR_MULTI_CS : if C_ARD_ADDR_RANGE_ARRAY'length > 2 generate
            -- Instantiate the basic Base Address Decoders
            MEM_SELECT_I: entity axi_lite_ipif_v3_0_4.pselect_f
                generic map
                (
                    C_AB     => DECODE_BITS(bar_index),
                    C_AW     => C_BUS_AWIDTH,
                    C_BAR    => ARD_ADDR_RANGE_ARRAY(bar_index*2),
                    C_FAMILY => C_FAMILY
                )
                port map
                (
                    A        => Address_In_Erly,            -- [in]
                    AValid   => Address_Valid_Erly,         -- [in]
                    CS       => pselect_hit_i(bar_index)    -- [out]
                );
    end generate GEN_FOR_MULTI_CS;

    -- GEN_FOR_ONE_CS: below logic decodes the CS for single address range
    -- ---------------
    GEN_FOR_ONE_CS : if C_ARD_ADDR_RANGE_ARRAY'length = 2 generate
            pselect_hit_i(bar_index) <= Address_Valid_Erly;
    end generate GEN_FOR_ONE_CS;


    -- Instantate backend registers for the Chip Selects
    BKEND_CS_REG : process(Bus_Clk)
            begin
                if(Bus_Clk'EVENT and Bus_Clk = '1')then
                  if(Bus_Rst='0' or Clear_CS_CE_Reg = '1')then
                    cs_out_i(bar_index) <= '0';
                  elsif(CS_CE_ld_enable='1')then
                    cs_out_i(bar_index) <= pselect_hit_i(bar_index);
                  end if;
                end if;
    end process BKEND_CS_REG;

    -------------------------------------------------------------------------
    -- PER_CE_GEN: Now expand the individual CEs for each base address.
    -------------------------------------------------------------------------
    PER_CE_GEN: for j in natural range 0 to C_ARD_NUM_CE_ARRAY(bar_index) - 1 generate
    -----------
    begin
    -----------
        ----------------------------------------------------------------------
        -- CE decoders for multiple CE's
        ----------------------------------------------------------------------
        MULTIPLE_CES_THIS_CS_GEN : if CE_ADDR_SIZE > 0 generate
        constant BAR    : std_logic_vector(0 to CE_ADDR_SIZE-1) :=
                            std_logic_vector(to_unsigned(j,CE_ADDR_SIZE));
        begin
            CE_I : entity axi_lite_ipif_v3_0_4.pselect_f
                generic map (
                    C_AB        => CE_ADDR_SIZE                             ,
                    C_AW        => CE_ADDR_SIZE                             ,
                    C_BAR       => BAR                                      ,
                    C_FAMILY    => C_FAMILY
                )
                port map (
                    A           => addr_out_s_h
                                    (NUM_S_H_ADDR_BITS-OFFSET-CE_ADDR_SIZE
                                    to NUM_S_H_ADDR_BITS - OFFSET - 1)      ,
                    AValid      => pselect_hit_i(bar_index)                 ,
                    CS          => ce_expnd_i(CE_INDEX_START+j)
                );
            end generate MULTIPLE_CES_THIS_CS_GEN;
	    --------------------------------------
        ----------------------------------------------------------------------
        -- SINGLE_CE_THIS_CS_GEN: CE decoders for single CE
        ----------------------------------------------------------------------
        SINGLE_CE_THIS_CS_GEN : if CE_ADDR_SIZE = 0 generate
            ce_expnd_i(CE_INDEX_START+j) <= pselect_hit_i(bar_index);
        end generate;
	-------------
    end generate PER_CE_GEN;
    ------------------------
end generate MEM_DECODE_GEN;

    -- RNW_REG_P: Register the incoming RNW signal at the time of registering the
    --            address. This is  need to generate the CE's separately.

    RNW_REG_P:process(Bus_Clk)
    begin
    if(Bus_Clk'EVENT and Bus_Clk = '1')then
       if(RW_CE_ld_enable='1')then
	Bus_RNW_reg <= Bus_RNW_Erly;
       end if;
    end if;
    end process RNW_REG_P;

    ---------------------------------------------------------------------------
    -- GEN_BKEND_CE_REGISTERS
    -- This ForGen implements the backend registering for
    -- the CE, RdCE, and WrCE output buses.
    ---------------------------------------------------------------------------
GEN_BKEND_CE_REGISTERS : for ce_index in 0 to NUM_CE_SIGNALS-1 generate
signal rdce_expnd_i : std_logic_vector(0 to NUM_CE_SIGNALS-1);
signal wrce_expnd_i : std_logic_vector(0 to NUM_CE_SIGNALS-1);
------
begin
------


    BKEND_RDCE_REG : process(Bus_Clk)
        begin
            if(Bus_Clk'EVENT and Bus_Clk = '1')then
              if(cs_ce_clr='1')then
                ce_out_i(ce_index) <= '0';
              elsif(RW_CE_ld_enable='1')then
                ce_out_i(ce_index) <= ce_expnd_i(ce_index);
              end if;
            end if;
    end process BKEND_RDCE_REG;
    rdce_out_i(ce_index)   <= ce_out_i(ce_index) and Bus_RNW_reg;
    wrce_out_i(ce_index)   <= ce_out_i(ce_index) and not Bus_RNW_reg;

-------------------------------
end generate GEN_BKEND_CE_REGISTERS;
-------------------------------------------------------------------------------

CS_for_gaps <= '0'; -- Removed the GAP adecoder logic
---------------------------------
CS_Out       <= cs_out_i   ;
RdCE_Out     <= rdce_out_i ;
WrCE_Out     <= wrce_out_i ;

end architecture IMP;


-------------------------------------------------------------------
-- (c) Copyright 1984 - 2012 Xilinx, Inc. All rights reserved.
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
-------------------------------------------------------------------
-- ************************************************************************
--
-------------------------------------------------------------------------------
-- Filename:        slave_attachment.vhd
-- Version:         v2.0
-- Description:     AXI slave attachment supporting single transfers
-------------------------------------------------------------------------------
-- Structure:   This section shows the hierarchical structure of axi_lite_ipif.
--
--              --axi_lite_ipif.vhd
--                    --slave_attachment.vhd
--                       --address_decoder.vhd
-------------------------------------------------------------------------------
-- Author:      BSB
--
-- History:
--
--  BSB      05/20/10      -- First version
-- ~~~~~~
--  - Created the first version v1.00.a
-- ^^^^^^
-- ~~~~~~
--  SK       06/09/10      -- updated to reduce the utilization
--  1. State machine is re-designed
--  2. R and B channels are registered and AW, AR, W channels are non-registered
--  3. Address decoding is done only for the required address bits and not complete
--     32 bits
--  4. combined the response signals like ip2bus_error in optimzed code to remove the mux
--  5. Added local function "clog2" with "integer" as input in place of proc_common_pkg
--     function.
-- ^^^^^^
-- ~~~~~~
--  SK       12/16/12      -- v2.0
--  1. up reved to major version for 2013.1 Vivado release. No logic updates.
--  2. Updated the version of AXI LITE IPIF to v2.0 in X.Y format
--  3. updated the proc common version to proc_common_base_v5_0
--  4. No Logic Updates
-- ^^^^^^
-------------------------------------------------------------------------------
-- Naming Conventions:
--      active low signals:                     "*_n"
--      clock signals:                          "clk", "clk_div#", "clk_#x"
--      reset signals:                          "rst", "rst_n"
--      generics:                               "C_*"
--      user defined types:                     "*_TYPE"
--      access_cs machine next state:               "*_ns"
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
use ieee.numeric_std.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_misc.all;

--library proc_common_base_v5_0;
--use proc_common_base_v5_0.proc_common_pkg.clog2;
--use proc_common_base_v5_0.ipif_pkg.all;

library axi_lite_ipif_v3_0_4;
use axi_lite_ipif_v3_0_4.ipif_pkg.all;

-------------------------------------------------------------------------------
--                     Definition of Generics
-------------------------------------------------------------------------------
-- C_IPIF_ABUS_WIDTH     -- IPIF Address bus width
-- C_IPIF_DBUS_WIDTH     -- IPIF Data Bus width
-- C_S_AXI_MIN_SIZE      -- Minimum address range of the IP
-- C_USE_WSTRB           -- Use write strobs or not
-- C_DPHASE_TIMEOUT      -- Data phase time out counter
-- C_ARD_ADDR_RANGE_ARRAY-- Base /High Address Pair for each Address Range
-- C_ARD_NUM_CE_ARRAY    -- Desired number of chip enables for an address range
-- C_FAMILY              -- Target FPGA family
-------------------------------------------------------------------------------
--                  Definition of Ports
-------------------------------------------------------------------------------
-- S_AXI_ACLK            -- AXI Clock
-- S_AXI_ARESET          -- AXI Reset
-- S_AXI_AWADDR          -- AXI Write address
-- S_AXI_AWVALID         -- Write address valid
-- S_AXI_AWREADY         -- Write address ready
-- S_AXI_WDATA           -- Write data
-- S_AXI_WSTRB           -- Write strobes
-- S_AXI_WVALID          -- Write valid
-- S_AXI_WREADY          -- Write ready
-- S_AXI_BRESP           -- Write response
-- S_AXI_BVALID          -- Write response valid
-- S_AXI_BREADY          -- Response ready
-- S_AXI_ARADDR          -- Read address
-- S_AXI_ARVALID         -- Read address valid
-- S_AXI_ARREADY         -- Read address ready
-- S_AXI_RDATA           -- Read data
-- S_AXI_RRESP           -- Read response
-- S_AXI_RVALID          -- Read valid
-- S_AXI_RREADY          -- Read ready
-- Bus2IP_Clk            -- Synchronization clock provided to User IP
-- Bus2IP_Reset          -- Active high reset for use by the User IP
-- Bus2IP_Addr           -- Desired address of read or write operation
-- Bus2IP_RNW            -- Read or write indicator for the transaction
-- Bus2IP_BE             -- Byte enables for the data bus
-- Bus2IP_CS             -- Chip select for the transcations
-- Bus2IP_RdCE           -- Chip enables for the read
-- Bus2IP_WrCE           -- Chip enables for the write
-- Bus2IP_Data           -- Write data bus to the User IP
-- IP2Bus_Data           -- Input Read Data bus from the User IP
-- IP2Bus_WrAck          -- Active high Write Data qualifier from the IP
-- IP2Bus_RdAck          -- Active high Read Data qualifier from the IP
-- IP2Bus_Error          -- Error signal from the IP
-------------------------------------------------------------------------------

entity slave_attachment is
  generic (

    C_ARD_ADDR_RANGE_ARRAY: SLV64_ARRAY_TYPE :=
       (
        X"0000_0000_7000_0000", -- IP user0 base address
        X"0000_0000_7000_00FF", -- IP user0 high address
        X"0000_0000_7000_0100", -- IP user1 base address
        X"0000_0000_7000_01FF"  -- IP user1 high address
       );
    C_ARD_NUM_CE_ARRAY  : INTEGER_ARRAY_TYPE :=
       (
        1,         -- User0 CE Number
        8          -- User1 CE Number
       );
    C_IPIF_ABUS_WIDTH   : integer := 32;
    C_IPIF_DBUS_WIDTH   : integer := 32;
    C_S_AXI_MIN_SIZE    : std_logic_vector(31 downto 0):= X"000001FF";
    C_USE_WSTRB         : integer := 0;
    C_DPHASE_TIMEOUT    : integer range 0 to 512 := 16;
    C_FAMILY            : string  := "virtex6"
        );
  port(
        -- AXI signals
    S_AXI_ACLK          : in  std_logic;
    S_AXI_ARESETN       : in  std_logic;
    S_AXI_AWADDR        : in  std_logic_vector
                          (C_IPIF_ABUS_WIDTH-1 downto 0);
    S_AXI_AWVALID       : in  std_logic;
    S_AXI_AWREADY       : out std_logic;
    S_AXI_WDATA         : in  std_logic_vector
                          (C_IPIF_DBUS_WIDTH-1 downto 0);
    S_AXI_WSTRB         : in  std_logic_vector
                          ((C_IPIF_DBUS_WIDTH/8)-1 downto 0);
    S_AXI_WVALID        : in  std_logic;
    S_AXI_WREADY        : out std_logic;
    S_AXI_BRESP         : out std_logic_vector(1 downto 0);
    S_AXI_BVALID        : out std_logic;
    S_AXI_BREADY        : in  std_logic;
    S_AXI_ARADDR        : in  std_logic_vector
                          (C_IPIF_ABUS_WIDTH-1 downto 0);
    S_AXI_ARVALID       : in  std_logic;
    S_AXI_ARREADY       : out std_logic;
    S_AXI_RDATA         : out std_logic_vector
                          (C_IPIF_DBUS_WIDTH-1 downto 0);
    S_AXI_RRESP         : out std_logic_vector(1 downto 0);
    S_AXI_RVALID        : out std_logic;
    S_AXI_RREADY        : in  std_logic;
    -- Controls to the IP/IPIF modules
    Bus2IP_Clk          : out std_logic;
    Bus2IP_Resetn       : out std_logic;
    Bus2IP_Addr         : out std_logic_vector
                          (C_IPIF_ABUS_WIDTH-1 downto 0);
    Bus2IP_RNW          : out std_logic;
    Bus2IP_BE           : out std_logic_vector
                          (((C_IPIF_DBUS_WIDTH/8) - 1) downto 0);
    Bus2IP_CS           : out std_logic_vector
                          (((C_ARD_ADDR_RANGE_ARRAY'LENGTH)/2 - 1) downto 0);
    Bus2IP_RdCE         : out std_logic_vector
                          ((calc_num_ce(C_ARD_NUM_CE_ARRAY) - 1) downto 0);
    Bus2IP_WrCE         : out std_logic_vector
                          ((calc_num_ce(C_ARD_NUM_CE_ARRAY) - 1) downto 0);
    Bus2IP_Data         : out std_logic_vector
                          ((C_IPIF_DBUS_WIDTH-1) downto 0);
    IP2Bus_Data         : in  std_logic_vector
                          ((C_IPIF_DBUS_WIDTH-1) downto 0);
    IP2Bus_WrAck        : in  std_logic;
    IP2Bus_RdAck        : in  std_logic;
    IP2Bus_Error        : in  std_logic
    );
end entity slave_attachment;

-------------------------------------------------------------------------------
architecture imp of slave_attachment is
----------------------------------------------------------------------------------
-- below attributes are added to reduce the synth warnings in Vivado tool
attribute DowngradeIPIdentifiedWarnings: string;
attribute DowngradeIPIdentifiedWarnings of imp : architecture is "yes";
----------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- Get_Addr_Bits: Function Declarations
-------------------------------------------------------------------------------
function Get_Addr_Bits (y : std_logic_vector(31 downto 0)) return integer is
variable i : integer := 0;
    begin
        for i in 31 downto 0 loop
            if y(i)='1' then
               return (i);
            end if;
        end loop;
        return -1;
end function Get_Addr_Bits;

-------------------------------------------------------------------------------
-- Constant Declarations
-------------------------------------------------------------------------------
constant CS_BUS_SIZE          : integer := C_ARD_ADDR_RANGE_ARRAY'length/2;
constant CE_BUS_SIZE          : integer := calc_num_ce(C_ARD_NUM_CE_ARRAY);

constant C_ADDR_DECODE_BITS   : integer := Get_Addr_Bits(C_S_AXI_MIN_SIZE);
constant C_NUM_DECODE_BITS    : integer := C_ADDR_DECODE_BITS +1;
constant ZEROS                : std_logic_vector((C_IPIF_ABUS_WIDTH-1) downto
                               (C_ADDR_DECODE_BITS+1)) := (others=>'0');
-------------------------------------------------------------------------------
-- Signal and Type Declarations
-------------------------------------------------------------------------------
signal s_axi_bvalid_i         : std_logic:= '0';
signal s_axi_arready_i        : std_logic;
signal s_axi_rvalid_i         : std_logic:= '0';
signal start                  : std_logic;
signal start2                  : std_logic;
-- Intermediate IPIC signals
signal bus2ip_addr_i          : std_logic_vector
                                ((C_IPIF_ABUS_WIDTH-1) downto 0);
signal timeout                : std_logic;

signal rd_done,wr_done        : std_logic;
signal rd_done1,wr_done1        : std_logic;
--signal rd_done2,wr_done2        : std_logic;
signal wrack_1,rdack_1        : std_logic;
--signal wrack_2,rdack_2        : std_logic;
signal rst                    : std_logic;
signal temp_i                 : std_logic;

  type BUS_ACCESS_STATES is (
    SM_IDLE,
    SM_READ,
    SM_WRITE,
    SM_RESP
  );
signal state : BUS_ACCESS_STATES;

signal cs_for_gaps_i : std_logic;
signal bus2ip_rnw_i  : std_logic;
signal s_axi_bresp_i : std_logic_vector(1 downto 0):=(others => '0');
signal s_axi_rresp_i : std_logic_vector(1 downto 0):=(others => '0');
signal s_axi_rdata_i : std_logic_vector
                     (C_IPIF_DBUS_WIDTH-1 downto 0):=(others => '0');
signal is_read, is_write : std_logic;
-------------------------------------------------------------------------------
-- begin the architecture logic
-------------------------------------------------------------------------------
begin

-------------------------------------------------------------------------------
-- Address registered
-------------------------------------------------------------------------------
Bus2IP_Clk     <= S_AXI_ACLK;
Bus2IP_Resetn  <= S_AXI_ARESETN;
--bus2ip_rnw_i     <= '1' when S_AXI_ARVALID='1'
--                  else
--                  '0';
BUS2IP_RNW     <= bus2ip_rnw_i;
Bus2IP_BE      <= S_AXI_WSTRB when ((C_USE_WSTRB = 1) and (bus2ip_rnw_i = '0'))
                  else
                  (others => '1');
Bus2IP_Data    <= S_AXI_WDATA;
Bus2IP_Addr    <= bus2ip_addr_i;

-- For AXI Lite interface, interconnect will duplicate the addresses on both the
-- read and write channel. so onlyone address is used for decoding as well as
-- passing it to IP.
--bus2ip_addr_i  <= ZEROS & S_AXI_ARADDR(C_ADDR_DECODE_BITS downto 0)
--                  when (S_AXI_ARVALID='1')
--		  else
--                ZEROS & S_AXI_AWADDR(C_ADDR_DECODE_BITS downto 0);

--------------------------------------------------------------------------------
-- start signal will be used to latch the incoming address

--start<= (S_AXI_ARVALID or (S_AXI_AWVALID and S_AXI_WVALID))
--        when (state = SM_IDLE)
--        else
--        '0';

-- x_done signals are used to release the hold from AXI, it will generate "ready"
-- signal on the read and write address channels.

rd_done <= IP2Bus_RdAck or (timeout and is_read);
wr_done <= IP2Bus_WrAck or (timeout and is_write);

--wr_done1 <= (not (wrack_1) and IP2Bus_WrAck) or timeout;
--rd_done1 <= (not (rdack_1) and IP2Bus_RdAck) or timeout;

temp_i  <= rd_done or wr_done;
-------------------------------------------------------------------------------
-- Address Decoder Component Instance
--
-- This component decodes the specified base address pairs and outputs the
-- specified number of chip enables and the target bus size.
-------------------------------------------------------------------------------
I_DECODER : entity axi_lite_ipif_v3_0_4.address_decoder
    generic map
    (
     C_BUS_AWIDTH          => C_NUM_DECODE_BITS,
     C_S_AXI_MIN_SIZE      => C_S_AXI_MIN_SIZE,
     C_ARD_ADDR_RANGE_ARRAY=> C_ARD_ADDR_RANGE_ARRAY,
     C_ARD_NUM_CE_ARRAY    => C_ARD_NUM_CE_ARRAY,
     C_FAMILY              => "nofamily"
    )
    port map
    (
     Bus_clk               =>  S_AXI_ACLK,
     Bus_rst               =>  S_AXI_ARESETN,
     Address_In_Erly       =>  bus2ip_addr_i(C_ADDR_DECODE_BITS downto 0),
     Address_Valid_Erly    =>  start2,
     Bus_RNW               =>  bus2ip_rnw_i, --S_AXI_ARVALID,
     Bus_RNW_Erly          =>  bus2ip_rnw_i, --S_AXI_ARVALID,
     CS_CE_ld_enable       =>  start2,
     Clear_CS_CE_Reg       =>  temp_i,
     RW_CE_ld_enable       =>  start2,
     CS_for_gaps           =>  open,
      -- Decode output signals
     CS_Out                =>  Bus2IP_CS,
     RdCE_Out              =>  Bus2IP_RdCE,
     WrCE_Out              =>  Bus2IP_WrCE
      );


 -- REGISTERING_RESET_P: Invert the reset coming from AXI
 -----------------------
 REGISTERING_RESET_P : process (S_AXI_ACLK) is
  begin
    if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
     rst <=  not S_AXI_ARESETN;
    end if;
  end process REGISTERING_RESET_P;


 REGISTERING_RESET_P2 : process (S_AXI_ACLK) is
  begin
    if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
     if (rst = '1') then
    --   wrack_1 <= '0';
    --   rdack_1 <= '0';
    --   wrack_2 <= '0';
    --   rdack_2 <= '0';
    --   wr_done2 <= '0';
    --   rd_done2 <= '0';
       bus2ip_rnw_i     <= '0';
       bus2ip_addr_i <= (others => '0');
       start2 <= '0';
     else
    --   wrack_1 <= IP2Bus_WrAck;
    --   rdack_1 <= IP2Bus_RdAck;
    --   wrack_2 <= wrack_1;
    --   rdack_2 <= rdack_1;
    --   wr_done2 <= wr_done1;
    --   rd_done2 <= rd_done1;

       if (state = SM_IDLE and S_AXI_ARVALID='1') then
          bus2ip_addr_i  <= ZEROS & S_AXI_ARADDR(C_ADDR_DECODE_BITS downto 0);
          bus2ip_rnw_i     <= '1';
          start2 <= '1';
       elsif (state = SM_IDLE and (S_AXI_AWVALID = '1' and S_AXI_WVALID = '1')) then
          bus2ip_addr_i  <= ZEROS & S_AXI_AWADDR(C_ADDR_DECODE_BITS downto 0);
          bus2ip_rnw_i     <= '0';
          start2 <= '1';
       else
          bus2ip_rnw_i     <= bus2ip_rnw_i;
          bus2ip_addr_i <= bus2ip_addr_i;
          start2 <= '0';
       end if;
     end if;
    end if;
  end process REGISTERING_RESET_P2;


-------------------------------------------------------------------------------
-- AXI Transaction Controller
-------------------------------------------------------------------------------
-- Access_Control: As per suggestion to optimize the core, the below state machine
--                 is re-coded. Latches are removed from original suggestions
Access_Control : process (S_AXI_ACLK) is
    begin
    if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
    if rst = '1' then
      state <= SM_IDLE;
      is_read <= '0';
      is_write <= '0';
    else
        case state is
          when SM_IDLE => if (S_AXI_ARVALID = '1') then  -- Read precedence over write
				state <= SM_READ;
                                is_read <='1';
                                is_write <= '0';
			  elsif (S_AXI_AWVALID = '1' and S_AXI_WVALID = '1') then
				state <= SM_WRITE;
                                is_read <='0';
                                is_write <= '1';
			  else
			        state <= SM_IDLE;
                                is_read <='0';
                                is_write <= '0';
			  end if;

          when SM_READ => if rd_done = '1' then
				state <= SM_RESP;
		          else
				state <= SM_READ;
			  end if;

          when SM_WRITE=> if (wr_done = '1') then
		                state <= SM_RESP;
		          else
				state <= SM_WRITE;
			  end if;

          when SM_RESP => if ((s_axi_bvalid_i and S_AXI_BREADY) or
			      (s_axi_rvalid_i and S_AXI_RREADY)) = '1' then
				state <= SM_IDLE;
                                is_read <='0';
                                is_write <= '0';
			  else
				state <= SM_RESP;
			  end if;
	  -- coverage off
	  when others =>  state <= SM_IDLE;
	  -- coverage on
        end case;
    end if;
   end if;
  end process Access_Control;

-------------------------------------------------------------------------------
  -- AXI Transaction Controller signals registered
-------------------------------------------------------------------------------
-- S_AXI_RDATA_RESP_P : BElow process generates the RRESP and RDATA on AXI
-----------------------
S_AXI_RDATA_RESP_P : process (S_AXI_ACLK) is
  begin
    if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
      if (rst = '1') then
      	 s_axi_rresp_i <= (others => '0');
	 s_axi_rdata_i <= (others => '0');
      elsif state = SM_READ then
	s_axi_rresp_i <= (IP2Bus_Error) & '0';
        s_axi_rdata_i <=  IP2Bus_Data;
      end if;
    end if;
end process S_AXI_RDATA_RESP_P;

S_AXI_RRESP <= s_axi_rresp_i;
S_AXI_RDATA <= s_axi_rdata_i;
-----------------------------

-- S_AXI_RVALID_I_P : below process generates the RVALID response on read channel
----------------------
S_AXI_RVALID_I_P : process (S_AXI_ACLK) is
  begin
    if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
      if (rst = '1') then
         s_axi_rvalid_i <= '0';
      elsif ((state = SM_READ) and rd_done = '1') then
         s_axi_rvalid_i <= '1';
      elsif (S_AXI_RREADY = '1') then
         s_axi_rvalid_i <= '0';
      end if;
    end if;
end process S_AXI_RVALID_I_P;

-- -- S_AXI_BRESP_P: Below process provides logic for write response
-- -----------------
S_AXI_BRESP_P : process (S_AXI_ACLK) is
  begin
    if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
      if (rst = '1') then
      	 s_axi_bresp_i <= (others => '0');
      elsif (state = SM_WRITE) then
	 s_axi_bresp_i <= (IP2Bus_Error) & '0';
      end if;
    end if;
end process S_AXI_BRESP_P;

S_AXI_BRESP <= s_axi_bresp_i;
--S_AXI_BVALID_I_P: below process provides logic for valid write response signal
-------------------
S_AXI_BVALID_I_P : process (S_AXI_ACLK) is
  begin
    if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
      if rst = '1' then
         s_axi_bvalid_i <= '0';
      elsif ((state = SM_WRITE) and wr_done = '1') then
         s_axi_bvalid_i <= '1';
      elsif (S_AXI_BREADY = '1') then
         s_axi_bvalid_i <= '0';
      end if;
    end if;
end process S_AXI_BVALID_I_P;
-----------------------------------------------------------------------------

-- INCLUDE_DPHASE_TIMER: Data timeout counter included only when its value is non-zero.
--------------
INCLUDE_DPHASE_TIMER: if C_DPHASE_TIMEOUT /= 0 generate

  constant COUNTER_WIDTH        : integer := clog2((C_DPHASE_TIMEOUT));
  signal dpto_cnt               : std_logic_vector (COUNTER_WIDTH downto 0);
    -- dpto_cnt is one bit wider then COUNTER_WIDTH, which allows the timeout
    -- condition to be captured as a carry into this "extra" bit.
begin

  DPTO_CNT_P : process (S_AXI_ACLK) is
    begin
      if (S_AXI_ACLK'event and S_AXI_ACLK = '1') then
        if ((state = SM_IDLE) or (state = SM_RESP)) then
           dpto_cnt <= (others=>'0');
        else
           dpto_cnt <= dpto_cnt + 1;
        end if;
      end if;
  end process DPTO_CNT_P;

  timeout <= '1' when (dpto_cnt = C_DPHASE_TIMEOUT) else '0';

end generate INCLUDE_DPHASE_TIMER;

EXCLUDE_DPHASE_TIMER: if C_DPHASE_TIMEOUT = 0 generate
  timeout <= '0';
end generate EXCLUDE_DPHASE_TIMER;

-----------------------------------------------------------------------------
S_AXI_BVALID <= s_axi_bvalid_i;
S_AXI_RVALID <= s_axi_rvalid_i;
-----------------------------------------------------------------------------
S_AXI_ARREADY <= rd_done;
S_AXI_AWREADY <= wr_done;
S_AXI_WREADY  <= wr_done;
-------------------------------------------------------------------------------
end imp;


-------------------------------------------------------------------
-- (c) Copyright 1984 - 2012 Xilinx, Inc. All rights reserved.
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
-------------------------------------------------------------------
-- ************************************************************************
--
-------------------------------------------------------------------------------
-- Filename:        axi_lite_ipif.vhd
-- Version:         v2.0
-- Description:     This is the top level design file for the axi_lite_ipif
--                  function. It provides a standardized slave interface
--                  between the IP and the AXI. This version supports
--                  single read/write transfers only.  It does not provide
--                  address pipelining or simultaneous read and write
--                  operations.
-------------------------------------------------------------------------------
-- Structure:   This section shows the hierarchical structure of axi_lite_ipif.
--
--              --axi_lite_ipif.vhd
--                    --slave_attachment.vhd
--                       --address_decoder.vhd
-------------------------------------------------------------------------------
-- Author:      BSB
--
-- History:
--
--  BSB      05/20/10      -- First version
-- ~~~~~~
--  - Created the first version v1.00.a
-- ^^^^^^
-- ~~~~~~
--  SK       06/09/10      -- v1.01.a
--  1. updated to reduce the utilization
--     Closed CR #574507
--  2. Optimized the state machine code
--  3. Optimized the address decoder logic to generate the CE's with common logic
--  4. Address GAP decoding logic is removed and timeout counter is made active
--     for all transactions.
-- ^^^^^^
-- ~~~~~~
--  SK       12/16/12      -- v2.0
--  1. up reved to major version for 2013.1 Vivado release. No logic updates.
--  2. Updated the version of AXI LITE IPIF to v2.0 in X.Y format
--  3. updated the proc common version to proc_common_base_v5_0
--  4. No Logic Updates
-- ^^^^^^
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
use ieee.std_logic_unsigned.all;
use ieee.numeric_std.all;
use ieee.std_logic_misc.all;

--library proc_common_base_v5_0;
--use proc_common_base_v5_0.ipif_pkg.all;

library axi_lite_ipif_v3_0_4;
    use axi_lite_ipif_v3_0_4.ipif_pkg.all;

-------------------------------------------------------------------------------
--                     Definition of Generics
-------------------------------------------------------------------------------
-- C_S_AXI_DATA_WIDTH    -- AXI data bus width
-- C_S_AXI_ADDR_WIDTH    -- AXI address bus width
-- C_S_AXI_MIN_SIZE      -- Minimum address range of the IP
-- C_USE_WSTRB           -- Use write strobs or not
-- C_DPHASE_TIMEOUT      -- Data phase time out counter
-- C_ARD_ADDR_RANGE_ARRAY-- Base /High Address Pair for each Address Range
-- C_ARD_NUM_CE_ARRAY    -- Desired number of chip enables for an address range
-- C_FAMILY              -- Target FPGA family
-------------------------------------------------------------------------------
--                  Definition of Ports
-------------------------------------------------------------------------------
-- S_AXI_ACLK            -- AXI Clock
-- S_AXI_ARESETN         -- AXI Reset
-- S_AXI_AWADDR          -- AXI Write address
-- S_AXI_AWVALID         -- Write address valid
-- S_AXI_AWREADY         -- Write address ready
-- S_AXI_WDATA           -- Write data
-- S_AXI_WSTRB           -- Write strobes
-- S_AXI_WVALID          -- Write valid
-- S_AXI_WREADY          -- Write ready
-- S_AXI_BRESP           -- Write response
-- S_AXI_BVALID          -- Write response valid
-- S_AXI_BREADY          -- Response ready
-- S_AXI_ARADDR          -- Read address
-- S_AXI_ARVALID         -- Read address valid
-- S_AXI_ARREADY         -- Read address ready
-- S_AXI_RDATA           -- Read data
-- S_AXI_RRESP           -- Read response
-- S_AXI_RVALID          -- Read valid
-- S_AXI_RREADY          -- Read ready
-- Bus2IP_Clk            -- Synchronization clock provided to User IP
-- Bus2IP_Reset          -- Active high reset for use by the User IP
-- Bus2IP_Addr           -- Desired address of read or write operation
-- Bus2IP_RNW            -- Read or write indicator for the transaction
-- Bus2IP_BE             -- Byte enables for the data bus
-- Bus2IP_CS             -- Chip select for the transcations
-- Bus2IP_RdCE           -- Chip enables for the read
-- Bus2IP_WrCE           -- Chip enables for the write
-- Bus2IP_Data           -- Write data bus to the User IP
-- IP2Bus_Data           -- Input Read Data bus from the User IP
-- IP2Bus_WrAck          -- Active high Write Data qualifier from the IP
-- IP2Bus_RdAck          -- Active high Read Data qualifier from the IP
-- IP2Bus_Error          -- Error signal from the IP
-------------------------------------------------------------------------------

entity axi_lite_ipif is
    generic (

      C_S_AXI_DATA_WIDTH    : integer  range 32 to 32   := 32;
      C_S_AXI_ADDR_WIDTH    : integer                   := 32;
      C_S_AXI_MIN_SIZE      : std_logic_vector(31 downto 0):= X"000001FF";
      C_USE_WSTRB           : integer := 0;
      C_DPHASE_TIMEOUT      : integer range 0 to 512 := 8;
      C_ARD_ADDR_RANGE_ARRAY: SLV64_ARRAY_TYPE :=  -- not used
         (
           X"0000_0000_7000_0000", -- IP user0 base address
           X"0000_0000_7000_00FF", -- IP user0 high address
           X"0000_0000_7000_0100", -- IP user1 base address
           X"0000_0000_7000_01FF"  -- IP user1 high address
         );

      C_ARD_NUM_CE_ARRAY    : INTEGER_ARRAY_TYPE := -- not used
         (
           4,         -- User0 CE Number
           12         -- User1 CE Number
         );
      C_FAMILY              : string  := "virtex6"
           );
    port (

        --System signals
      S_AXI_ACLK            : in  std_logic;
      S_AXI_ARESETN         : in  std_logic;
      S_AXI_AWADDR          : in  std_logic_vector
                              (C_S_AXI_ADDR_WIDTH-1 downto 0);
      S_AXI_AWVALID         : in  std_logic;
      S_AXI_AWREADY         : out std_logic;
      S_AXI_WDATA           : in  std_logic_vector
                              (C_S_AXI_DATA_WIDTH-1 downto 0);
      S_AXI_WSTRB           : in  std_logic_vector
                              ((C_S_AXI_DATA_WIDTH/8)-1 downto 0);
      S_AXI_WVALID          : in  std_logic;
      S_AXI_WREADY          : out std_logic;
      S_AXI_BRESP           : out std_logic_vector(1 downto 0);
      S_AXI_BVALID          : out std_logic;
      S_AXI_BREADY          : in  std_logic;
      S_AXI_ARADDR          : in  std_logic_vector
                              (C_S_AXI_ADDR_WIDTH-1 downto 0);
      S_AXI_ARVALID         : in  std_logic;
      S_AXI_ARREADY         : out std_logic;
      S_AXI_RDATA           : out std_logic_vector
                              (C_S_AXI_DATA_WIDTH-1 downto 0);
      S_AXI_RRESP           : out std_logic_vector(1 downto 0);
      S_AXI_RVALID          : out std_logic;
      S_AXI_RREADY          : in  std_logic;
      -- Controls to the IP/IPIF modules
      Bus2IP_Clk            : out std_logic;
      Bus2IP_Resetn         : out std_logic;
      Bus2IP_Addr           : out std_logic_vector
                              ((C_S_AXI_ADDR_WIDTH-1) downto 0);
      Bus2IP_RNW            : out std_logic;
      Bus2IP_BE             : out std_logic_vector
                              (((C_S_AXI_DATA_WIDTH/8)-1) downto 0);
      Bus2IP_CS             : out std_logic_vector
                              (((C_ARD_ADDR_RANGE_ARRAY'LENGTH)/2-1) downto 0);
      Bus2IP_RdCE           : out std_logic_vector
                              ((calc_num_ce(C_ARD_NUM_CE_ARRAY)-1) downto 0);
      Bus2IP_WrCE           : out std_logic_vector
                              ((calc_num_ce(C_ARD_NUM_CE_ARRAY)-1) downto 0);
      Bus2IP_Data           : out std_logic_vector
                              ((C_S_AXI_DATA_WIDTH-1) downto 0);
      IP2Bus_Data           : in  std_logic_vector
                              ((C_S_AXI_DATA_WIDTH-1) downto 0);
      IP2Bus_WrAck          : in  std_logic;
      IP2Bus_RdAck          : in  std_logic;
      IP2Bus_Error          : in  std_logic

       );

end axi_lite_ipif;

-------------------------------------------------------------------------------
-- Architecture
-------------------------------------------------------------------------------

architecture imp of axi_lite_ipif is
----------------------------------------------------------------------------------
-- below attributes are added to reduce the synth warnings in Vivado tool
attribute DowngradeIPIdentifiedWarnings: string;
attribute DowngradeIPIdentifiedWarnings of imp : architecture is "yes";
----------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- Begin architecture logic
-------------------------------------------------------------------------------
begin

-------------------------------------------------------------------------------
-- Slave Attachment
-------------------------------------------------------------------------------

I_SLAVE_ATTACHMENT:  entity axi_lite_ipif_v3_0_4.slave_attachment
    generic map(
        C_ARD_ADDR_RANGE_ARRAY    => C_ARD_ADDR_RANGE_ARRAY,
        C_ARD_NUM_CE_ARRAY        => C_ARD_NUM_CE_ARRAY,
        C_IPIF_ABUS_WIDTH         => C_S_AXI_ADDR_WIDTH,
        C_IPIF_DBUS_WIDTH         => C_S_AXI_DATA_WIDTH,
        C_USE_WSTRB               => C_USE_WSTRB,
        C_DPHASE_TIMEOUT          => C_DPHASE_TIMEOUT,
        C_S_AXI_MIN_SIZE          => C_S_AXI_MIN_SIZE,
        C_FAMILY                  => C_FAMILY
    )
    port map(
        -- AXI signals
        S_AXI_ACLK          =>  S_AXI_ACLK,
        S_AXI_ARESETN       =>  S_AXI_ARESETN,
        S_AXI_AWADDR        =>  S_AXI_AWADDR,
        S_AXI_AWVALID       =>  S_AXI_AWVALID,
        S_AXI_AWREADY       =>  S_AXI_AWREADY,
        S_AXI_WDATA         =>  S_AXI_WDATA,
        S_AXI_WSTRB         =>  S_AXI_WSTRB,
        S_AXI_WVALID        =>  S_AXI_WVALID,
        S_AXI_WREADY        =>  S_AXI_WREADY,
        S_AXI_BRESP         =>  S_AXI_BRESP,
        S_AXI_BVALID        =>  S_AXI_BVALID,
        S_AXI_BREADY        =>  S_AXI_BREADY,
        S_AXI_ARADDR        =>  S_AXI_ARADDR,
        S_AXI_ARVALID       =>  S_AXI_ARVALID,
        S_AXI_ARREADY       =>  S_AXI_ARREADY,
        S_AXI_RDATA         =>  S_AXI_RDATA,
        S_AXI_RRESP         =>  S_AXI_RRESP,
        S_AXI_RVALID        =>  S_AXI_RVALID,
        S_AXI_RREADY        =>  S_AXI_RREADY,
        -- IPIC signals
        Bus2IP_Clk          =>  Bus2IP_Clk,
        Bus2IP_Resetn       =>  Bus2IP_Resetn,
        Bus2IP_Addr         =>  Bus2IP_Addr,
        Bus2IP_RNW          =>  Bus2IP_RNW,
        Bus2IP_BE           =>  Bus2IP_BE,
        Bus2IP_CS           =>  Bus2IP_CS,
        Bus2IP_RdCE         =>  Bus2IP_RdCE,
        Bus2IP_WrCE         =>  Bus2IP_WrCE,
        Bus2IP_Data         =>  Bus2IP_Data,
        IP2Bus_Data         =>  IP2Bus_Data,
        IP2Bus_WrAck        =>  IP2Bus_WrAck,
        IP2Bus_RdAck        =>  IP2Bus_RdAck,
        IP2Bus_Error        =>  IP2Bus_Error
    );

end imp;


