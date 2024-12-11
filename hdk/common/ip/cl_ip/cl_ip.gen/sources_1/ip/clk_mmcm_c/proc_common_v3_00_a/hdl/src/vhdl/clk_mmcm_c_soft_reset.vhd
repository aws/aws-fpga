-------------------------------------------------------------------------------
--soft_reset.vhd   v1.01a
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
-- Filename:        soft_reset.vhd
-- Version:         v1_00_a
-- Description:     This VHDL design file is the Soft Reset Service
--
-------------------------------------------------------------------------------
-- Structure:   
--
--              soft_reset.vhd
--                  
--
-------------------------------------------------------------------------------
-- Author:      Gary Burch
--
-- History:
--     GAB     Aug 2, 2006  v1.00a (initial release)
--
--
--     DET     1/17/2008     v3_00_a
-- ~~~~~~
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
-- Library definitions

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

library unisim;
use unisim.vcomponents.all;

-------------------------------------------------------------------------------

entity clk_mmcm_c_soft_reset is
    generic (
        C_SIPIF_DWIDTH          : integer := 32;
            -- Width of the write data bus

        C_RESET_WIDTH           : integer := 4     
            -- Width of triggered reset in Bus Clocks
    ); 
    port (
  
        -- Inputs From the IPIF Bus 
        Bus2IP_Reset        : in  std_logic;
        Bus2IP_Clk          : in  std_logic;
        Bus2IP_WrCE         : in  std_logic;
        Bus2IP_Data         : in  std_logic_vector(0 to C_SIPIF_DWIDTH-1);
        Bus2IP_BE           : in  std_logic_vector(0 to (C_SIPIF_DWIDTH/8)-1);

        -- Final Device Reset Output
        Reset2IP_Reset      : out std_logic; 

        -- Status Reply Outputs to the Bus 
        Reset2Bus_WrAck     : out std_logic;
        Reset2Bus_Error     : out std_logic;
        Reset2Bus_ToutSup   : out std_logic
    
    );
  end clk_mmcm_c_soft_reset ;
  
  

-------------------------------------------------------------------------------

architecture implementation of clk_mmcm_c_soft_reset is

-------------------------------------------------------------------------------
-- Function Declarations 
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- Type Declarations
-------------------------------------------------------------------------------
    
-------------------------------------------------------------------------------
-- Constant Declarations
-------------------------------------------------------------------------------

-- Module Software Reset screen value for write data
-- This requires a Hex 'A' to be written to ativate the S/W reset port
constant RESET_MATCH    : std_logic_vector(0 to 3) := "1010"; 
                                                           
-- Required BE index to be active during Reset activation
constant BE_MATCH       : integer := 3; 
                                                            
-------------------------------------------------------------------------------
-- Signal Declarations
-------------------------------------------------------------------------------

signal sm_reset         : std_logic;
signal error_reply      : std_logic;
signal reset_wrack      : std_logic;
signal reset_error      : std_logic;
signal reset_trig       : std_logic;
signal wrack            : std_logic;
signal wrack_ff_chain   : std_logic;
signal flop_q_chain     : std_logic_vector(0 to C_RESET_WIDTH);
--signal bus2ip_wrce_d1   : std_logic;

signal data_is_non_reset_match  : std_logic;
signal sw_rst_cond              : std_logic;
signal sw_rst_cond_d1           : std_logic;

-------------------------------------------------------------------------------
-- Architecture
-------------------------------------------------------------------------------
  
begin
           
-- Misc assignments         
Reset2Bus_WrAck     <= reset_wrack;
Reset2Bus_Error     <= reset_error;
Reset2Bus_ToutSup   <= sm_reset; -- Suppress a data phase timeout when
                                 -- a commanded reset is active.

reset_wrack         <=  (reset_error or wrack);-- and Bus2IP_WrCE;
reset_error         <=  data_is_non_reset_match and Bus2IP_WrCE;
Reset2IP_Reset      <=  Bus2IP_Reset or sm_reset;
      
---------------------------------------------------------------------------------
---- Register WRCE for use in creating a strobe pulse
---------------------------------------------------------------------------------
--REG_WRCE : process(Bus2IP_Clk)
--    begin
--        if(Bus2IP_Clk'EVENT and Bus2IP_Clk = '1')then
--            if(Bus2IP_Reset = '1')then
--                bus2ip_wrce_d1 <= '0';
--            else
--                bus2ip_wrce_d1 <= Bus2IP_WrCE;
--            end if;
--        end if;
--    end process REG_WRCE;
--
-------------------------------------------------------------------------------
-- Start the S/W reset state machine as a result of an IPIF Bus write to
-- the Reset port and the data on the DBus inputs matching the Reset 
-- match value. If the value on the data bus input does not match the 
-- designated reset key, an error acknowledge is generated.
-------------------------------------------------------------------------------
--DETECT_SW_RESET : process (Bus2IP_Clk)
--    begin
--        if(Bus2IP_Clk'EVENT and Bus2IP_Clk = '1') then
--            if (Bus2IP_Reset = '1') then
--                error_reply       <= '0';
--                reset_trig        <= '0';
--            elsif (Bus2IP_WrCE = '1' 
--            and Bus2IP_BE(BE_MATCH) = '1'
--            and Bus2IP_Data(28 to 31) = RESET_MATCH) then
--                error_reply       <= '0';
--                reset_trig        <= Bus2IP_WrCE and not bus2ip_wrce_d1;
--            elsif (Bus2IP_WrCE = '1') then 
--                error_reply       <= '1';
--                reset_trig        <= '0';
--            else
--                error_reply       <= '0';
--                reset_trig        <= '0';
--            end if;
--        end if;
--    end process DETECT_SW_RESET;


    data_is_non_reset_match <=
        '0' when (Bus2IP_Data(C_SIPIF_DWIDTH-4 to C_SIPIF_DWIDTH-1) = RESET_MATCH
             and Bus2IP_BE(BE_MATCH) = '1')
        else '1';

--------------------------------------------------------------------------------
-- SW Reset
--------------------------------------------------------------------------------
    ----------------------------------------------------------------------------
    sw_rst_cond <= Bus2IP_WrCE and not data_is_non_reset_match;
    --
    RST_PULSE_PROC : process (Bus2IP_Clk)
    Begin
       if (Bus2IP_Clk'EVENT and Bus2IP_Clk = '1') Then
           if (Bus2IP_Reset = '1') Then
              sw_rst_cond_d1    <= '0';
              reset_trig        <= '0';
           else
              sw_rst_cond_d1    <= sw_rst_cond;
              reset_trig        <= sw_rst_cond and not sw_rst_cond_d1;
           end if;
       end if;
    End process;

        
-------------------------------------------------------------------------------
-- RESET_FLOPS:
-- This FORGEN implements the register chain used to create 
-- the parameterizable reset pulse width.
-------------------------------------------------------------------------------
RESET_FLOPS : for index in 0 to C_RESET_WIDTH-1 generate

    flop_q_chain(0) <= '0';

    RST_FLOPS : FDRSE
        port map(
            Q   =>  flop_q_chain(index+1), -- :    out std_logic;
            C   =>  Bus2IP_Clk,            -- :    in  std_logic;
            CE  =>  '1',                   -- :    in  std_logic;
            D   =>  flop_q_chain(index),   -- :    in  std_logic;    
            R   =>  Bus2IP_Reset,          -- :    in  std_logic;
            S   =>  reset_trig             -- :    in  std_logic
        );

end generate RESET_FLOPS;

    
-- Use the last flop output for the commanded reset pulse 
sm_reset        <= flop_q_chain(C_RESET_WIDTH);

wrack_ff_chain  <= flop_q_chain(C_RESET_WIDTH) and 
                    not(flop_q_chain(C_RESET_WIDTH-1));


-- Register the Write Acknowledge for the Reset write
-- This is generated at the end of the reset pulse. This
-- keeps the Slave busy until the commanded reset completes.
FF_WRACK : FDRSE
    port map(
        Q   =>  wrack,            -- :  out std_logic;
        C   =>  Bus2IP_Clk,       -- :  in  std_logic;
        CE  =>  '1',              -- :  in  std_logic;
        D   =>  wrack_ff_chain,   -- :  in  std_logic;    
        R   =>  Bus2IP_Reset,     -- :  in  std_logic;
        S   =>  '0'               -- :  in  std_logic
    );


end implementation;


 






