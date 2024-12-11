-------------------------------------------------------------------------------
-- clk_mmcm_a_pselect_f.vhd - entity/architecture pair
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
-- Filename:        clk_mmcm_a_pselect_f.vhd
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
-- Structure:       clk_mmcm_a_pselect_f.vhd
--                    clk_mmcm_a_family_support.vhd
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

entity clk_mmcm_a_pselect_f is

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

end entity clk_mmcm_a_pselect_f;

-----------------------------------------------------------------------------
-- Architecture section
-----------------------------------------------------------------------------

architecture imp of clk_mmcm_a_pselect_f is



  -----------------------------------------------------------------------------
  -- C_BAR may not be indexed from 0 and may not be ascending;
  -- BAR recasts C_BAR to have these properties.
  -----------------------------------------------------------------------------
  constant BAR          : std_logic_vector(0 to C_BAR'length-1) := C_BAR;

  type bo2sl_type is array (boolean) of std_logic;
  constant bo2sl  : bo2sl_type := (false => '0', true => '1');
 
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
     report "clk_mmcm_a_pselect_f generic error: " &
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

