-------------------------------------------------------------------------------
-- iomodule_vote_pkg.vhd - Package specification
-------------------------------------------------------------------------------
--
-- (c) Copyright 2015-2016 Xilinx, Inc. All rights reserved.
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
-- Filename:        iomodule_vote_pkg.vhd
--
-- Description:
--
-- VHDL-Standard:   VHDL'93/02
-------------------------------------------------------------------------------
-- Structure:
--              iomodule_vote_pkg
--
-------------------------------------------------------------------------------
-- Author:          rolandp
--
-- History:
--   rolandp 2015-09-14    First Version
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

package IOModule_Vote_Pkg is

  function vote (vote1, vote2, vote3 : std_logic_vector; tmr_disable : boolean) return std_logic_vector;
  function vote (vote1, vote2, vote3 : std_logic_vector; tmr_disable : boolean; tmr : integer) return std_logic_vector;

  function vote (vote1, vote2, vote3 : std_logic; tmr_disable : boolean) return std_logic;
  function vote (vote1, vote2, vote3 : std_logic; tmr_disable : boolean; tmr : integer) return std_logic;

  function vote (vote1 : boolean; vote2, vote3 : std_logic; tmr_disable : boolean) return boolean;
  function vote (vote1 : boolean; vote2, vote3 : std_logic; tmr_disable : boolean; tmr : integer) return boolean;

  constant C_MAX_FIT_SIZE       : natural := 32;
  constant C_MAX_PIT_SIZE       : natural := 32;
  constant C_MAX_GPO_SIZE       : natural := 32;
  constant C_UART_PROG_CNT_SIZE : natural := 20;

  -- FIT
  subtype  FIT_COUNT_Pos    is natural range C_MAX_FIT_SIZE - 1 downto 0;
  constant FIT_INTERRUPT_Pos : natural :=    FIT_COUNT_Pos'high + 1;
  constant FIT_TOGGLE_Pos    : natural :=    FIT_INTERRUPT_Pos + 1;

  constant C_FIT_VOTE_SIZE   : natural := FIT_TOGGLE_Pos  + 1;
  subtype  FIT1_Pos         is natural range C_FIT_VOTE_SIZE - 1 downto 0;
  subtype  FIT2_Pos         is natural range FIT1_Pos'high + C_FIT_VOTE_SIZE downto FIT1_Pos'high + 1;
  subtype  FIT3_Pos         is natural range FIT2_Pos'high + C_FIT_VOTE_SIZE downto FIT2_Pos'high + 1;
  subtype  FIT4_Pos         is natural range FIT3_Pos'high + C_FIT_VOTE_SIZE downto FIT3_Pos'high + 1;

  -- UART Baudrate Counter
  subtype  UART_BAUD_FIT_Pos  is natural range C_MAX_FIT_SIZE + 2 downto 0;
  subtype  UART_BAUD_REG_Pos  is natural range UART_BAUD_FIT_Pos'high + C_UART_PROG_CNT_SIZE downto
                                               UART_BAUD_FIT_Pos'high + 1;
  subtype  UART_BAUD_CNT_Pos  is natural range UART_BAUD_REG_Pos'high + C_UART_PROG_CNT_SIZE downto
                                               UART_BAUD_REG_Pos'high + 1;
  constant UART_BAUD_EN16_Pos  : natural :=    UART_BAUD_CNT_Pos'high + 1;

  -- UART Control
  constant PARITY_ERROR_Pos    : natural :=    0;
  constant FRAME_ERROR_Pos     : natural :=    PARITY_ERROR_Pos + 1;
  constant OVERRUN_ERROR_Pos   : natural :=    FRAME_ERROR_Pos + 1;
  constant ERROR_INTERRUPT_Pos : natural :=    OVERRUN_ERROR_Pos + 1;

  subtype  UART_CONTROL_Pos   is natural range UART_BAUD_EN16_Pos + 1 + ERROR_INTERRUPT_Pos downto
                                               UART_BAUD_EN16_Pos + 1;

  -- UART Transmit
  constant UART_TX_DIV16_Pos         : natural :=    0;
  constant UART_TX_DATA_ENABLE_Pos   : natural :=    UART_TX_DIV16_Pos + 1;
  constant UART_TX_START_Pos         : natural :=    UART_TX_DATA_ENABLE_Pos + 1;
  constant UART_TX_DATABITS_Pos      : natural :=    UART_TX_START_Pos + 1;
  subtype  UART_TX_MUX_SEL_Pos      is natural range UART_TX_DATABITS_Pos + 3 downto UART_TX_DATABITS_Pos + 1;
  constant UART_TX_DATA_IS_SENT_Pos  : natural :=    UART_TX_MUX_SEL_Pos'high + 1;
  constant UART_TX_SERIAL_DATA_Pos   : natural :=    UART_TX_DATA_IS_SENT_Pos + 1;
  constant UART_TX_Pos               : natural :=    UART_TX_SERIAL_DATA_Pos + 1;
  constant UART_TX_CALC_PARITY_Pos   : natural :=    UART_TX_Pos + 1;
  constant UART_TX_RUN_Pos           : natural :=    UART_TX_CALC_PARITY_Pos + 1;
  constant UART_TX_SEL_PARITY_Pos    : natural :=    UART_TX_RUN_Pos + 1;
  subtype  UART_TX_FIFO_DOUT_Pos    is natural range UART_TX_SEL_PARITY_Pos + 8 downto UART_TX_SEL_PARITY_Pos + 1;
  constant UART_TX_BUFFER_EMPTY_Pos  : natural :=    UART_TX_FIFO_DOUT_Pos'high + 1;

  subtype  UART_TRANSMIT_Pos        is natural range UART_CONTROL_Pos'high + 1 + UART_TX_BUFFER_EMPTY_Pos downto
                                                     UART_CONTROL_Pos'high + 1;

  -- UART Receive
  constant UART_RX_PREVIOUS_RX_Pos         : natural :=    0;
  constant UART_RX_START_EDGE_DETECTED_Pos : natural :=    UART_RX_PREVIOUS_RX_Pos + 1;
  constant UART_RX_RUNNING_Pos             : natural :=    UART_RX_START_EDGE_DETECTED_Pos + 1;
  constant UART_RX_RECYCLE_Pos             : natural :=    UART_RX_RUNNING_Pos + 1;
  constant UART_RX_STOP_BIT_POSITION_Pos   : natural :=    UART_RX_RECYCLE_Pos + 1;
  constant UART_RX_CALC_PARITY_Pos         : natural :=    UART_RX_STOP_BIT_POSITION_Pos + 1;
  constant UART_RX_MID_START_BIT_Pos       : natural :=    UART_RX_CALC_PARITY_Pos + 1;
  subtype  UART_RX_SERIAL_TO_PARALLEL_Pos is natural range UART_RX_MID_START_BIT_Pos + 9 downto
                                                           UART_RX_MID_START_BIT_Pos + 1;
  constant UART_RX_NEW_RX_DATA_WRITE_Pos   : natural :=    UART_RX_SERIAL_TO_PARALLEL_Pos'high + 1;
  constant UART_RX_DATA_EXISTS_Pos         : natural :=    UART_RX_NEW_RX_DATA_WRITE_Pos + 1;
  subtype  UART_RX_DATA_I_Pos             is natural range UART_RX_DATA_EXISTS_Pos + 8 downto
                                                           UART_RX_DATA_EXISTS_Pos + 1;
  subtype  UART_RX_DATA_Pos               is natural range UART_RX_DATA_I_Pos'high + 8 downto
                                                           UART_RX_DATA_I_Pos'high + 1;

  subtype  UART_RECEIVE_Pos               is natural range UART_TRANSMIT_Pos'high + 1 + UART_RX_DATA_Pos'high downto
                                                           UART_TRANSMIT_Pos'high + 1;
  -- UART Core at UART level 
  constant UART_CORE_low   : natural := 0;
  constant UART_CORE_high  : natural := UART_RECEIVE_Pos'high;
  subtype UART_CORE_Pos   is natural range UART_CORE_high downto UART_CORE_low;

  -- Pulse Sync
  constant PULSE_SYNC           : natural := 2;
  constant PULSE_SYNC_KEEP_Pos  : natural := 0;
  constant PULSE_SYNC_PULSE_Pos : natural := 1;
  subtype PULSE_SYNC_Pos       is natural range PULSE_SYNC_PULSE_Pos downto PULSE_SYNC_KEEP_Pos;

  -- UART Async fields
  constant TMR_DISABLE_UART_CLK_Pos   : natural := UART_CORE_high+1;
  subtype  WRITE_TX_DATA_Pos         is natural range TMR_DISABLE_UART_CLK_Pos+PULSE_SYNC downto TMR_DISABLE_UART_CLK_Pos+1;
  subtype  WRITE_DATA_Pos            is natural range WRITE_TX_DATA_Pos'high+8 downto WRITE_TX_DATA_Pos'high+1;
  subtype  WRITE_BAUD_Pos            is natural range WRITE_DATA_Pos'high+PULSE_SYNC downto WRITE_DATA_Pos'high+1;
  subtype  BAUD_DATA_Pos             is natural range WRITE_BAUD_Pos'high+C_UART_PROG_CNT_SIZE downto WRITE_BAUD_Pos'high+1;
  subtype  RX_DATA_RECEIVED_Pos      is natural range BAUD_DATA_Pos'high+PULSE_SYNC downto BAUD_DATA_Pos'high+1;
  subtype  RX_DATA_Pos               is natural range RX_DATA_RECEIVED_Pos'high+8 downto RX_DATA_RECEIVED_Pos'high+1;
  subtype  READ_RX_DATA_Pos          is natural range RX_DATA_Pos'high+PULSE_SYNC downto RX_DATA_Pos'high+1;
  constant READ_RX_PULSE_Pos          : natural := READ_RX_DATA_Pos'high+1;
  subtype  UART_STATUS_READ_Pos      is natural range READ_RX_PULSE_Pos+PULSE_SYNC downto READ_RX_PULSE_Pos+1;
  subtype  UART_STATUS_Pos           is natural range UART_STATUS_READ_Pos'high+8 downto UART_STATUS_READ_Pos'high+1;
  constant UART_STATUS_READ_PULSE_Pos : natural := UART_STATUS_Pos'high+1;
  subtype  UART_RX_INTERRUPT_Pos     is natural range UART_STATUS_READ_PULSE_Pos+PULSE_SYNC downto UART_STATUS_READ_PULSE_Pos+1;
  subtype  UART_TX_INTERRUPT_Pos     is natural range UART_RX_INTERRUPT_Pos'high+PULSE_SYNC downto UART_RX_INTERRUPT_Pos'high+1;
  subtype  UART_ERROR_INTERRUPT_Pos  is natural range UART_TX_INTERRUPT_Pos'high+PULSE_SYNC downto UART_TX_INTERRUPT_Pos'high+1;

  -- Async UART at UART level
  constant UART_ASYNC_low   : natural := UART_CORE_high+1;
  constant UART_ASYNC_high  : natural := UART_ERROR_INTERRUPT_Pos'high;
  subtype  UART_ASYNC_Pos   is natural range UART_ASYNC_high downto UART_ASYNC_low;
                                                
  -- All UART fields at iomodule level
  constant UART_low   : natural := FIT4_Pos'high + 1;
  constant UART_high  : natural := UART_ASYNC_high + FIT4_Pos'high + 1;
  subtype UART_Pos   is natural range UART_high downto UART_low;
  
  -- GPO
  subtype  GPO1_Pos                       is natural range UART_high+ C_MAX_GPO_SIZE downto
                                                           UART_high + 1;
  subtype  GPO2_Pos                       is natural range GPO1_Pos'high + C_MAX_GPO_SIZE downto GPO1_Pos'high + 1;
  subtype  GPO3_Pos                       is natural range GPO2_Pos'high + C_MAX_GPO_SIZE downto GPO2_Pos'high + 1;
  subtype  GPO4_Pos                       is natural range GPO3_Pos'high + C_MAX_GPO_SIZE downto GPO3_Pos'high + 1;

  -- PIT
  subtype  PIT_PRELOAD_VALUE_Pos          is natural range C_MAX_PIT_SIZE-1 downto 0;
  constant PIT_RELOAD_Pos                  : natural :=    PIT_PRELOAD_VALUE_Pos'high + 1;
  constant PIT_COUNT_EN_Pos                : natural :=    PIT_RELOAD_Pos + 1;
  constant PIT_COUNT_LOAD_N_Pos            : natural :=    PIT_COUNT_EN_Pos + 1;
  constant PIT_PRELOAD_WRITTEN_Pos         : natural :=    PIT_COUNT_LOAD_N_Pos + 1;
  subtype  PIT_COUNT_Pos                  is natural range PIT_PRELOAD_WRITTEN_Pos + C_MAX_PIT_SIZE downto
                                                           PIT_PRELOAD_WRITTEN_Pos + 1;
  constant PIT_INTERRUPT_I_Pos             : natural :=    PIT_COUNT_Pos'high + 1;
  constant PIT_TOGGLE_I_Pos                : natural :=    PIT_INTERRUPT_I_Pos + 1;
  constant PIT_VOTE_SIZE                   : natural :=    PIT_TOGGLE_I_Pos + 1;

  subtype  PIT1_Pos                       is natural range GPO4_Pos'high + PIT_VOTE_SIZE downto GPO4_Pos'high + 1;
  subtype  PIT2_Pos                       is natural range PIT1_Pos'high + PIT_VOTE_SIZE downto PIT1_Pos'high + 1;
  subtype  PIT3_Pos                       is natural range PIT2_Pos'high + PIT_VOTE_SIZE downto PIT2_Pos'high + 1;
  subtype  PIT4_Pos                       is natural range PIT3_Pos'high + PIT_VOTE_SIZE downto PIT3_Pos'high + 1;

  -- Interrupt
  subtype  IRQ_INTERRUPT_Pos              is natural range 31 downto 0;
  subtype  IRQ_INTR_PRESENT_Pos           is natural range IRQ_INTERRUPT_Pos'high + 32 downto
                                                           IRQ_INTERRUPT_Pos'high + 1;
  subtype  IRQ_CISR_Pos                   is natural range IRQ_INTR_PRESENT_Pos'high + 32 downto
                                                           IRQ_INTR_PRESENT_Pos'high + 1;
  subtype  IRQ_CIER_Pos                   is natural range IRQ_CISR_Pos'high + 32 downto IRQ_CISR_Pos'high + 1;
  subtype  IRQ_CIMR_Pos                   is natural range IRQ_CIER_Pos'high + 32 downto IRQ_CIER_Pos'high + 1;
  subtype  IRQ_CIVR_Pos                   is natural range IRQ_CIMR_Pos'high + 5 downto IRQ_CIMR_Pos'high + 1;
  subtype  IRQ_FAST_STATE_Pos             is natural range IRQ_CIVR_Pos'high + 2 downto IRQ_CIVR_Pos'high + 1;
  constant IRQ_INTC_IRQ_Pos                : natural :=    IRQ_FAST_STATE_Pos'high + 1;
  constant IRQ_DO_FAST_ACK_Pos             : natural :=    IRQ_INTC_IRQ_Pos + 1;
  constant IRQ_RST_CIPR_RD_Pos             : natural :=    IRQ_DO_FAST_ACK_Pos + 1;
  constant IRQ_VOTE_SIZE                   : natural :=    IRQ_RST_CIPR_RD_Pos + 1;


  subtype  IRQ_Pos                        is natural range PIT4_Pos'high + IRQ_VOTE_SIZE downto PIT4_Pos'high + 1;

  constant VOTE_SIZE : natural := IRQ_Pos'high + 1;

end package IOModule_Vote_Pkg;


-------------------------------------------------------------------------------
-- iomodule_vote_pkg_body.vhd - Package body
-------------------------------------------------------------------------------
--
-- (c) Copyright 2015-2016 Xilinx, Inc. All rights reserved.
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
-- Filename:        iomodule_vote_pkg_body.vhd
--
-- Description:
--
-- VHDL-Standard:   VHDL'93/02
-------------------------------------------------------------------------------
-- Structure:
--              iomodule_vote_pkg
--
-------------------------------------------------------------------------------
-- Author:          rolandp
--
-- History:
--   rolandp 2015-09-14    First Version
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

package body IOModule_Vote_Pkg is

  function vote(vote1, vote2, vote3 : std_logic_vector) return std_logic_vector is
    variable I     : integer := 0;
    variable voted : std_logic_vector(1023 downto 0);
    variable vote1_l, vote2_l, vote3_l : std_logic_vector(1023 downto 0);
  begin
    vote1_l(vote1'length - 1 downto 0) := vote1;
    vote2_l(vote2'length - 1 downto 0) := vote2;
    vote3_l(vote3'length - 1 downto 0) := vote3;
    for I in vote1_l'range loop
      voted(I) := (vote1_l(I) and vote2_l(I)) or
                  (vote1_l(I) and vote3_l(I)) or
                  (vote2_l(I) and vote3_l(I));
    end loop;
    return voted(vote1'length - 1 downto 0);
  end function vote;

  function vote(vote1, vote2, vote3 : std_logic_vector; tmr_disable : boolean) return std_logic_vector is
  begin
    if tmr_disable then
      return vote1;
    else
      return vote(vote1, vote2, vote3);
    end if;
  end function vote;

  function vote(vote1, vote2, vote3 : std_logic_vector;
                tmr_disable         : boolean;
                tmr                 : integer) return std_logic_vector is
  begin
    if (tmr = 0 or tmr_disable) then
      return vote1;
    else
      return vote(vote1, vote2, vote3);
    end if;
  end function vote;

  function vote(vote1, vote2, vote3 : std_logic) return std_logic is
    variable voted : std_logic;
  begin
    voted := (vote1 and vote2) or
             (vote1 and vote3) or
             (vote2 and vote3);
    return voted;
  end function vote;

  function vote(vote1, vote2, vote3 : std_logic; tmr_disable : boolean) return std_logic is
  begin
    if tmr_disable then
      return vote1;
    else
      return vote(vote1, vote2, vote3);
    end if;
  end function vote;

  function vote (vote1, vote2, vote3 : std_logic; tmr_disable : boolean; tmr : integer) return std_logic is
  begin
    if (tmr = 0 or tmr_disable) then
       return vote1;
    else
      return vote(vote1, vote2, vote3);
    end if;
  end function vote;

  function vote(vote1 : boolean; vote2, vote3 : std_logic) return boolean is
    variable voted, vote2_b, vote3_b : boolean;
  begin
    if (vote2 = '1') then
      vote2_b := true;
    else
      vote2_b := false;
    end if;
    if (vote3 = '1') then
      vote3_b := true;
    else
      vote3_b := false;
    end if;
    voted := (vote1   and vote2_b) or
             (vote1   and vote3_b) or
             (vote2_b and vote3_b);
    return voted;
  end function vote;

  function vote(vote1 : boolean; vote2, vote3 : std_logic; tmr_disable : boolean) return boolean is
  begin
    if tmr_disable then
      return vote1;
    else
      return vote(vote1, vote2, vote3);
    end if;
  end function vote;

  function vote(vote1 : boolean; vote2, vote3 : std_logic; tmr_disable : boolean; tmr : integer) return boolean is
  begin
    if (tmr = 0 or tmr_disable) then
      return vote1;
    else
      return vote(vote1, vote2, vote3);
    end if;
  end function vote;

end package body IOModule_Vote_Pkg;


-------------------------------------------------------------------------------
-- iomodule_funcs.vhd - Entity and architecture
-------------------------------------------------------------------------------
--
-- (c) Copyright 2001-2016 Xilinx, Inc. All rights reserved.
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
-- Filename:        iomodule_funcs.vhd
--
-- Description:     Support functions for iomodule
--
-- VHDL-Standard:   VHDL'93
-------------------------------------------------------------------------------
-- Structure:
--                  iomodule_funcs.vhd
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

package iomodule_funcs is

  type TARGET_FAMILY_TYPE is (
                              -- pragma xilinx_rtl_off
                              non_RTL,
                              -- pragma xilinx_rtl_on
                              RTL
                             );

  function String_To_Family (S : string; Select_RTL : boolean) return TARGET_FAMILY_TYPE;

end package iomodule_funcs;

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

package body iomodule_funcs is

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

  function LowerCase_String (s : string) return string is
    variable res : string(s'range);
  begin  -- function LoweerCase_String
    for I in s'range loop
      res(I) := LowerCase_Char(s(I));
    end loop;  -- I
    return res;
  end function LowerCase_String;

  -- Returns true if case insensitive string comparison determines that
  -- str1 and str2 are equal
  function Equal_String( str1, str2 : string ) return boolean is
    constant len1 : integer := str1'length;
    constant len2 : integer := str2'length;
    variable equal : boolean := true;
  begin
    if not (len1=len2) then
      equal := false;
    else
      for i in str1'range loop
        if not (LowerCase_Char(str1(i)) = LowerCase_Char(str2(i))) then
          equal := false;
        end if;
      end loop;
    end if;

    return equal;
  end Equal_String;

  function String_To_Family (S : string; Select_RTL : boolean) return TARGET_FAMILY_TYPE is
  begin  -- function String_To_Family
    if ((Select_RTL) or Equal_String(S, "rtl")) then
      return RTL;
    else
      return non_RTL;
    end if;
  end function String_To_Family;

end package body iomodule_funcs;


-------------------------------------------------------------------------------
-- xilinx_primitives.vhd - Entity and architecture
-------------------------------------------------------------------------------
--
-- (c) Copyright 2016 Xilinx, Inc. All rights reserved.
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
-- Filename:        xilinx_primitives.vhd
--
-- Description:     
--                  
-- VHDL-Standard:   VHDL'93
-------------------------------------------------------------------------------
-- Structure:   
--                  xilinx_primitives.vhd
--
-------------------------------------------------------------------------------
-- Author:          rolandp
--
-- History:
--   rolandp 2016-05-21    First Version
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

-- XIL_Scan_Reset_Control
library IEEE;
use IEEE.std_logic_1164.all;

entity xil_scan_reset_control is
  port (
    Scan_En          : in  std_logic;
    Scan_Reset_Sel   : in  std_logic;
    Scan_Reset       : in  std_logic;
    Functional_Reset : in  std_logic;
    Reset            : out std_logic);
end entity xil_scan_reset_control;

architecture IMP of xil_scan_reset_control is

begin
  Reset <= '0'               when Scan_En = '1' else
            Functional_Reset when Scan_Reset_Sel = '0' else
            Scan_Reset;
end architecture IMP;

----- entity XIL_SRL16E -----
library IEEE;
use IEEE.std_logic_1164.all;
library iomodule_v3_1_6;
use iomodule_v3_1_6.iomodule_funcs.all;

entity XIL_SRL16E is
  generic(
    C_TARGET    : TARGET_FAMILY_TYPE;
    C_USE_SRL16 : string;
    C_STATIC    : boolean    := false;
    INIT        : bit_vector := X"0000");
  port(
    Config_Reset : in  std_logic;
    Q            : out std_logic;
    A0           : in  std_logic;
    A1           : in  std_logic;
    A2           : in  std_logic;
    A3           : in  std_logic;
    CE           : in  std_logic;
    CLK          : in  std_logic;
    D            : in  std_logic);
end entity XIL_SRL16E;

library unisim;
use unisim.vcomponents.all;

library ieee;
use ieee.numeric_std.all;

architecture IMP of XIL_SRL16E is

begin  -- architecture IMP

  Use_unisim: if (C_USE_SRL16 /= "no" and C_TARGET /= RTL) generate
    XIL_SRL16E_I1: SRL16E
      generic map (
        INIT  => INIT)  -- [bit_vector]
      port map (
        Q   => Q,       -- [out std_logic]
        A0  => A0,      -- [in  std_logic]
        A1  => A1,      -- [in  std_logic]
        A2  => A2,      -- [in  std_logic]
        A3  => A3,      -- [in  std_logic]
        CE  => CE,      -- [in  std_logic]
        CLK => CLK,     -- [in  std_logic]
        D   => D);      -- [in std_logic]
  end generate Use_unisim;

  Use_RTL : if (C_USE_SRL16 = "no" or C_TARGET = RTL) generate
    signal shift_reg         : std_logic_vector(15 downto 0) := to_stdLogicVector(INIT);
    constant shift_reg_const : std_logic_vector(15 downto 0) := to_stdLogicVector(INIT);
    attribute shreg_extract : string;
    attribute shreg_extract of SHIFT_REG : signal is C_USE_SRL16;
  begin

    Static_Values: if (C_STATIC) generate
    begin
      Q <= shift_reg_const(to_integer(unsigned(to_stdLogicVector(A3 & A2 & A1 & A0))));
    end generate Static_Values;

    Dynamic_Values: if (not C_STATIC) generate
    begin
      Q <= shift_reg(to_integer(unsigned(to_stdLogicVector(A3 & A2 & A1 & A0))));

      process(CLK)
      begin
        if (rising_edge(CLK)) then
          if (Config_Reset = '1') then
            shift_reg <= shift_reg_const;
          else
            if CE = '1' then
              shift_reg <= shift_reg(14 downto 0) & D;
            end if;
          end if;
        end if;
      end process;
      
    end generate Dynamic_Values;

  end generate Use_RTL;

end architecture IMP;

----- entity XIL_SRLC16E -----
library IEEE;
use IEEE.std_logic_1164.all;
library iomodule_v3_1_6;
use iomodule_v3_1_6.iomodule_funcs.all;

entity XIL_SRLC16E is
  generic(
    C_TARGET    : TARGET_FAMILY_TYPE;
    C_USE_SRL16 : string;
    INIT        : bit_vector := X"0000");
  port(
    Config_Reset : in  std_logic;
    Q            : out std_logic;
    Q15          : out std_logic;
    A0           : in  std_logic;
    A1           : in  std_logic;
    A2           : in  std_logic;
    A3           : in  std_logic;
    CE           : in  std_logic;
    CLK          : in  std_logic;
    D            : in  std_logic);
end entity XIL_SRLC16E;

library unisim;
use unisim.vcomponents.all;

library ieee;
use ieee.numeric_std.all;

architecture IMP of XIL_SRLC16E is

begin  -- architecture IMP

  Use_unisim: if (C_USE_SRL16 /= "no" and C_TARGET /= RTL) generate
    XIL_SRL16CE_I1: SRLC16E
      generic map (
        INIT  => INIT)  -- [bit_vector]
      port map (
        Q15 => Q15,       -- [out std_logic]
        Q   => Q,       -- [out std_logic]
        A0  => A0,      -- [in  std_logic]
        A1  => A1,      -- [in  std_logic]
        A2  => A2,      -- [in  std_logic]
        A3  => A3,      -- [in  std_logic]
        CE  => CE,      -- [in  std_logic]
        CLK => CLK,     -- [in  std_logic]
        D   => D);      -- [in std_logic]
  end generate Use_unisim;

  Use_RTL : if (C_USE_SRL16 = "no" or C_TARGET = RTL) generate
    signal shift_reg        : std_logic_vector(15 downto 0) := to_stdLogicVector(INIT);
    attribute shreg_extract : string;
    attribute shreg_extract of SHIFT_REG : signal is C_USE_SRL16;
  begin

    Q   <= shift_reg(to_integer(unsigned(to_stdLogicVector(A3 & A2 & A1 & A0))));
    Q15 <= shift_reg(15);

    process(CLK)
    begin
      if (rising_edge(CLK)) then
        if (Config_Reset = '1') then
          shift_reg <= (others => '0');
        else
          if CE = '1' then
            shift_reg <= shift_reg(14 downto 0) & D;
          end if;
        end if;
      end if;
    end process;

  end generate Use_RTL;

end architecture IMP;

----- entity MUXCY -----
library IEEE;
use IEEE.std_logic_1164.all;
library iomodule_v3_1_6;
use iomodule_v3_1_6.iomodule_funcs.all;

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
library iomodule_v3_1_6;
use iomodule_v3_1_6.iomodule_funcs.all;

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

----- entity MUXCY with XORCY -----
library IEEE;
use IEEE.std_logic_1164.all;
library iomodule_v3_1_6;
use iomodule_v3_1_6.iomodule_funcs.all;

entity MB_MUXCY_XORCY is
  generic (
    C_TARGET : TARGET_FAMILY_TYPE
  );
  port (
    O  : out std_logic;
    LO : out std_logic;
    CI : in  std_logic;
    DI : in  std_logic;
    S  : in  std_logic
  );
end entity MB_MUXCY_XORCY;

library Unisim;
use Unisim.vcomponents.all;

architecture IMP of MB_MUXCY_XORCY is
begin
  
  Using_RTL: if ( C_TARGET = RTL ) generate 
  begin
    O <= (CI xor S);
    LO <= DI when S = '0' else CI;
  end generate Using_RTL;
  
  Using_FPGA: if ( C_TARGET /= RTL ) generate 
  begin
    Native_I1: MUXCY_L
      port map(
        LO => LO,
        CI => CI,
        DI => DI,
        S  => S
      );
    Native_I2: XORCY
      port map(
        O  => O,
        CI => CI,
        LI => S
      );
  end generate Using_FPGA;
  
end architecture IMP;

----- entity FDR -----
library IEEE;
use IEEE.std_logic_1164.all;
library iomodule_v3_1_6;
use iomodule_v3_1_6.iomodule_funcs.all;

entity MB_FDR is
  generic (
    C_TARGET : TARGET_FAMILY_TYPE;
    INIT : bit := '0'
  );
  port(
    Q  : out std_logic;
    C  : in  std_logic;
    D  : in  std_logic;
    R  : in  std_logic
  );
end entity MB_FDR;

library Unisim;
use Unisim.vcomponents.all;

architecture IMP of MB_FDR is
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
        else
          q_o <= D;
        end if;
      end if;
    end process;
  end generate Using_RTL;
  
  Using_FPGA: if ( C_TARGET /= RTL ) generate 
  begin
    Native: FDR
      generic map(
        INIT => INIT
      )
      port map(
        Q   => Q,
        C   => C,
        D   => D,
        R   => R
      );
  end generate Using_FPGA;
  
end architecture IMP;

----- entity FDRE -----
library IEEE;
use IEEE.std_logic_1164.all;
library iomodule_v3_1_6;
use iomodule_v3_1_6.iomodule_funcs.all;

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

----- entity FDSE -----
library IEEE;
use IEEE.std_logic_1164.all;
library iomodule_v3_1_6;
use iomodule_v3_1_6.iomodule_funcs.all;

entity MB_FDSE is
  generic (
    C_TARGET : TARGET_FAMILY_TYPE;
    INIT : bit := '1'
  );
  port(
    Q  : out std_logic;
    C  : in  std_logic;
    CE : in  std_logic;
    D  : in  std_logic;
    S  : in  std_logic
  );
end entity MB_FDSE;

library Unisim;
use Unisim.vcomponents.all;

architecture IMP of MB_FDSE is
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
        if (S = '1') then
          q_o <= '1';
        elsif (CE = '1') then
          q_o <= D;
        end if;
      end if;
    end process;
  end generate Using_RTL;
  
  Using_FPGA: if ( C_TARGET /= RTL ) generate 
  begin
    Native: FDSE
      generic map(
        INIT => INIT
      )
      port map(
        Q   => Q,
        C   => C,
        CE  => CE,
        D   => D,
        S   => S
      );
  end generate Using_FPGA;
  
end architecture IMP;

----- entity MULT_AND -----
library IEEE;
use IEEE.std_logic_1164.all;
library iomodule_v3_1_6;
use iomodule_v3_1_6.iomodule_funcs.all;

entity MB_MULT_AND is
  generic (
    C_TARGET : TARGET_FAMILY_TYPE;
    INIT : bit := '0'
  );
  port(
    LO : out std_logic;
    I0 : in  std_logic;
    I1 : in  std_logic
  );
end entity MB_MULT_AND;

library Unisim;
use Unisim.vcomponents.all;

architecture IMP of MB_MULT_AND is
begin
  
  Using_RTL: if ( C_TARGET = RTL ) generate 
  begin
    LO <= I0 and I1;
  end generate Using_RTL;
  
  Using_FPGA: if ( C_TARGET /= RTL ) generate 
  begin
    Native: MULT_AND
      port map(
        LO => LO,
        I0 => I0,
        I1 => I1
      );
  end generate Using_FPGA;
  
end architecture IMP;

----- entity LUT3 -----
library IEEE;
use IEEE.std_logic_1164.all;
use ieee.numeric_std.all;
library iomodule_v3_1_6;
use iomodule_v3_1_6.iomodule_funcs.all;

entity MB_LUT3 is
  generic (
    C_TARGET : TARGET_FAMILY_TYPE;
    INIT     : bit_vector := X"00"
  );
  port (
    O  : out std_logic;
    I0 : in  std_logic;
    I1 : in  std_logic;
    I2 : in  std_logic
  );
end entity MB_LUT3;

library Unisim;
use Unisim.vcomponents.all;

architecture IMP of MB_LUT3 is
begin
  
  Using_RTL: if ( C_TARGET = RTL ) generate 
    constant INIT_reg : std_logic_vector(7 downto 0) := To_StdLogicVector(INIT);
  begin
    process (I0, I1, I2)
      variable I_reg    : std_logic_vector(2 downto 0);
      variable I0_v, I1_v, I2_v : std_logic;
    begin
      -- Filter unknowns
      if I0 = '0' then I0_v := '0'; else I0_v := '1'; end if;
      if I1 = '0' then I1_v := '0'; else I1_v := '1'; end if;
      if I2 = '0' then I2_v := '0'; else I2_v := '1'; end if;
      I_reg := TO_STDLOGICVECTOR( I2_v & I1_v & I0_v);
      O     <= INIT_reg(TO_INTEGER(unsigned(I_reg)));
    end process;
  end generate Using_RTL;
  
  Using_FPGA: if ( C_TARGET /= RTL ) generate 
  begin
    Native: LUT3
      generic map(
        INIT    => INIT
      )
      port map(
        O       => O,
        I0      => I0,
        I1      => I1,
        I2      => I2
      );
  end generate Using_FPGA;
  
end architecture IMP;

----- entity MUXF5 -----
library IEEE;
use IEEE.std_logic_1164.all;
library iomodule_v3_1_6;
use iomodule_v3_1_6.iomodule_funcs.all;

entity MB_MUXF5 is
  generic (
    C_TARGET : TARGET_FAMILY_TYPE
  );
  port (
    O  : out std_logic;
    I0 : in  std_logic;
    I1 : in  std_logic;
    S  : in  std_logic
  );
end entity MB_MUXF5;

library Unisim;
use Unisim.vcomponents.all;

architecture IMP of MB_MUXF5 is
begin
  
  Using_RTL: if ( C_TARGET = RTL ) generate 
  begin
    O <= I0 when S = '0' else I1;
  end generate Using_RTL;
  
  Using_FPGA: if ( C_TARGET /= RTL ) generate 
  begin
    Native: MUXF5
      port map(
        O  => O,
        I0 => I0,
        I1 => I1,
        S  => S
      );
  end generate Using_FPGA;
  
end architecture IMP;

----- entity MUXF6 -----
library IEEE;
use IEEE.std_logic_1164.all;
library iomodule_v3_1_6;
use iomodule_v3_1_6.iomodule_funcs.all;

entity MB_MUXF6 is
  generic (
    C_TARGET : TARGET_FAMILY_TYPE
  );
  port (
    O  : out std_logic;
    I0 : in  std_logic;
    I1 : in  std_logic;
    S  : in  std_logic
  );
end entity MB_MUXF6;

library Unisim;
use Unisim.vcomponents.all;

architecture IMP of MB_MUXF6 is
begin
  
  Using_RTL: if ( C_TARGET = RTL ) generate 
  begin
    O <= I0 when S = '0' else I1;
  end generate Using_RTL;
  
  Using_FPGA: if ( C_TARGET /= RTL ) generate 
  begin
    Native: MUXF6
      port map(
        O  => O,
        I0 => I0,
        I1 => I1,
        S  => S
      );
  end generate Using_FPGA;
  
end architecture IMP;




------------------------------------------------------------------------------
-- synchronizers.vhd - Entity and architecture
-------------------------------------------------------------------------------
--
-- (c) Copyright 2014,2017 Xilinx, Inc. All rights reserved.
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
-- Filename:        synchronizers.vhd
--
-- Description:     
--
-- VHDL-Standard:   VHDL'93/02
-------------------------------------------------------------------------------
-- Structure:   
--              mb_sync_bit
--              mb_sync_vec
--                mb_sync_bit
--              mb_sync_reset
--
-------------------------------------------------------------------------------
-- Author:          rolandp
--
-- History:
--   rolandp 2014-09-01    First Version
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

entity mb_sync_bit is
  generic(
    C_LEVELS            : natural   := 2;
    C_RESET_VALUE       : std_logic := '0';
    C_RESET_SYNCHRONOUS : boolean   := true;
    C_RESET_ACTIVE_HIGH : boolean   := true);
  port(
    Clk            : in  std_logic;
    Rst            : in  std_logic;
    Scan_En        : in  std_logic;
    Scan_Reset_Sel : in  std_logic;
    Scan_Reset     : in  std_logic;
    Raw            : in  std_logic;
    Synced         : out std_logic);
end mb_sync_bit;

library iomodule_v3_1_6;
use iomodule_v3_1_6.xil_scan_reset_control;

architecture IMP of mb_sync_bit is

  component xil_scan_reset_control is
  port (
    Scan_En          : in  std_logic;
    Scan_Reset_Sel   : in  std_logic;
    Scan_Reset       : in  std_logic;
    Functional_Reset : in  std_logic;
    Reset            : out std_logic);
  end component xil_scan_reset_control;
  
  -- Downgrade Synth 8-3332 warnings
  attribute DowngradeIPIdentifiedWarnings: string;
  attribute DowngradeIPIdentifiedWarnings of IMP : architecture is "yes";

begin

  -- Generate synchronizer DFFs
  Synchronize : if C_LEVELS > 1 generate
    signal reset : std_logic; 
    signal sync  : std_logic_vector(1 to C_LEVELS) := (others => C_RESET_VALUE);
    attribute ASYNC_REG : string;
    attribute ASYNC_REG of sync : signal is "TRUE";
  begin
    
    -- Internal reset always has active high polarity 
    reset <= Rst when C_RESET_ACTIVE_HIGH else
             not Rst;

    -- Synchronous reset
    use_sync_reset: if C_RESET_SYNCHRONOUS generate
    begin
      
      Sync_Rst_DFFs : process(Clk)
      begin
        if Clk'event and Clk = '1' then
          if reset = '1' then
            sync <= (sync'range  => C_RESET_VALUE); 
          else
            for I in C_LEVELS downto 2 loop
              sync(I) <= sync(I-1);
            end loop;
            sync(1) <= Raw;
          end if;
        end if;
      end process;

    end generate use_sync_reset;

    -- Asychronous reset
    use_async_reset: if not C_RESET_SYNCHRONOUS generate
      signal async_reset : std_logic;
    begin

      -- Make sure asynchronous reset can be controlled during scan test
      scan_reset_control_i: xil_scan_reset_control
        port map (
          Scan_En          => Scan_En,
          Scan_Reset_Sel   => Scan_Reset_Sel,
          Scan_Reset       => Scan_Reset,
          Functional_Reset => reset,
          Reset            => async_reset);
      
      Async_Rst_DFFs : process(Clk, async_reset)
      begin
        if async_reset = '1' then
          sync <= (sync'range => C_RESET_VALUE); 
        elsif Clk'event and Clk = '1' then
          for I in C_LEVELS downto 2 loop
            sync(I) <= sync(I-1);
          end loop;
          sync(1) <= Raw;
        end if;
      end process;

    end generate use_async_reset;

    Synced <= sync(C_LEVELS);

  end generate Synchronize;

  -- 1 synchronizer DFF
  Single_Synchronize : if C_LEVELS = 1 generate
    signal reset : std_logic;
    signal sync  : std_logic := C_RESET_VALUE;
  begin
    
    -- Internal reset always has active high polarity 
    reset <= Rst when C_RESET_ACTIVE_HIGH else
             not Rst;

    -- Synchronous reset
    use_sync_reset: if C_RESET_SYNCHRONOUS generate
    begin
      
      Sync_Rst_DFFs : process(Clk)
      begin
        if Clk'event and Clk = '1' then
          if reset = '1' then
            sync <= C_RESET_VALUE; 
          else
            sync <= Raw;
          end if;
        end if;
      end process;

    end generate use_sync_reset;

    -- Asychronous reset
    use_async_reset: if not C_RESET_SYNCHRONOUS generate
      signal async_reset : std_logic;
    begin

      -- Make sure asynchronous reset can be controlled from during scan test
      scan_reset_control_i: xil_scan_reset_control
      port map (
        Scan_En          => Scan_En,
        Scan_Reset_Sel   => Scan_Reset_Sel,
        Scan_Reset       => Scan_Reset,
        Functional_Reset => reset,
        Reset            => async_reset);
      
      Async_Rst_DFFs : process(Clk, async_reset)
      begin
        if async_reset = '1' then
          sync <= C_RESET_VALUE; 
        elsif Clk'event and Clk = '1' then
          sync <= Raw;
        end if;
      end process;

    end generate use_async_reset;

    Synced <= sync;
    
  end generate Single_Synchronize;

  -- No synchronizer DFFs, connect input to output directly
  No_Synchronize : if C_LEVELS = 0 generate
  begin
    Synced <= Raw;
  end generate No_Synchronize;
      
end architecture IMP;  -- mb_sync_bit


library iomodule_v3_1_6;
use iomodule_v3_1_6.mb_sync_bit;

library IEEE;
use IEEE.std_logic_1164.all;

entity mb_sync_vec is
  generic(
    C_LEVELS            : natural   := 2;
    C_RESET_VALUE       : std_logic := '0';
    C_RESET_SYNCHRONOUS : boolean   := true;
    C_RESET_ACTIVE_HIGH : boolean   := true;
    C_WIDTH             : natural);
  port(
    Clk            : in  std_logic;
    Rst            : in  std_logic := '0';
    Scan_En        : in  std_logic;
    Scan_Reset_Sel : in  std_logic := '0';
    Scan_Reset     : in  std_logic := '0';
    Raw            : in  std_logic_vector(0 to C_WIDTH-1);
    Synced         : out std_logic_vector(0 to C_WIDTH-1));
end mb_sync_vec;

architecture IMP of mb_sync_vec is

  component mb_sync_bit
  generic(
    C_LEVELS            : natural;
    C_RESET_VALUE       : std_logic;
    C_RESET_SYNCHRONOUS : boolean;
    C_RESET_ACTIVE_HIGH : boolean);
  port(
    Clk            : in  std_logic;
    Rst            : in  std_logic;
    Scan_En        : in  std_logic;
    Scan_Reset_Sel : in  std_logic;
    Scan_Reset     : in  std_logic;
    Raw            : in  std_logic;
    Synced         : out std_logic);
  end component;
  
begin

  sync_bits: for I in 0 to C_WIDTH-1 generate
  begin
    
    sync_bit : mb_sync_bit
      generic map(
        C_LEVELS             => C_LEVELS,
        C_RESET_VALUE        => C_RESET_VALUE,
        C_RESET_SYNCHRONOUS  => C_RESET_SYNCHRONOUS,
        C_RESET_ACTIVE_HIGH  => C_RESET_ACTIVE_HIGH)
      port map (
        Clk            => Clk,
        Rst            => Rst,
        Scan_En        => Scan_En,
        Scan_Reset_Sel => Scan_Reset_Sel,
        Scan_Reset     => Scan_Reset,
        Raw            => Raw(I),
        Synced         => Synced(I));
    
  end generate sync_bits;  

end architecture IMP;   -- mb_sync_vec


library IEEE;
use IEEE.std_logic_1164.all;

entity mb_sync_reset is
  generic(
    C_LEVELS            : natural := 2;
    C_RESET_VALUE       : std_logic := '1';
    C_RESET_ACTIVE_HIGH : boolean := true);
  port(
    Clk            : in  std_logic;
    Scan_En        : in  std_logic;
    Scan_Reset_Sel : in  std_logic;
    Scan_Reset     : in  std_logic;
    Raw            : in  std_logic;
    Synced         : out std_logic);
end mb_sync_reset;

library iomodule_v3_1_6;
use iomodule_v3_1_6.xil_scan_reset_control;

architecture IMP of mb_sync_reset is

  component xil_scan_reset_control is
  port (
    Scan_En          : in  std_logic;
    Scan_Reset_Sel   : in  std_logic;
    Scan_Reset       : in  std_logic;
    Functional_Reset : in  std_logic;
    Reset            : out std_logic);
  end component xil_scan_reset_control;

  signal preset       : std_logic;
  signal async_preset : std_logic;

  -- Downgrade Synth 8-3332 warnings
  attribute DowngradeIPIdentifiedWarnings: string;
  attribute DowngradeIPIdentifiedWarnings of IMP : architecture is "yes";

begin

  -- Internal preset always has active high polarity 
  preset <= Raw when C_RESET_ACTIVE_HIGH else
            not Raw;

  -- Make sure asynchronous preset can be controlled during scan test
  scan_reset_control_i: xil_scan_reset_control
    port map (
      Scan_En          => Scan_En,
      Scan_Reset_Sel   => Scan_Reset_Sel,
      Scan_Reset       => Scan_Reset,
      Functional_Reset => preset,
      Reset            => async_preset);

  -- Generate synchronizer DFFs
  Synchronize : if C_LEVELS > 1 generate
    signal sync : std_logic_vector(1 to C_LEVELS) := (others => C_RESET_VALUE);
    attribute ASYNC_REG : string;
    attribute ASYNC_REG of sync : signal is "TRUE";
  begin

    Reset_DFFs : process(Clk)
    begin
      if async_preset = '1' then
        sync <= (sync'range  => C_RESET_VALUE); 
      elsif Clk'event and Clk = '1' then
        for I in C_LEVELS downto 2 loop
          sync(I) <= sync(I-1);
        end loop;
        sync(1) <= Raw;
      end if;
    end process;

    Synced <= sync(C_LEVELS);
  end generate Synchronize;

  -- 1 synchronizer DFF
  Single_Synchronize : if C_LEVELS = 1 generate
    signal sync : std_logic := C_RESET_VALUE;
  begin

    Reset_DFFs : process(Clk)
    begin
      if async_preset = '1' then
        sync <= C_RESET_VALUE;
      elsif Clk'event and Clk = '1' then
        sync <= Raw;
      end if;
    end process;

    Synced <= sync;
  end generate Single_Synchronize;

  -- No synchronizer DFFs, connect input to output directly
  No_Synchronize : if C_LEVELS = 0 generate
  begin
    Synced <= Raw;
  end generate No_Synchronize;

end architecture IMP;  -- mb_sync_reset


library iomodule_v3_1_6;
use iomodule_v3_1_6.mb_sync_bit;
use iomodule_v3_1_6.iomodule_vote_pkg.all;

library IEEE;
use IEEE.std_logic_1164.all;

entity pulse_sync is
  generic(
    C_LEVELS          : natural := 2;
    C_TMR             : natural := 0;
    C_LATE_ACK        : natural := 0;
    C_USE_TMR_DISABLE : integer := 0);
  port(
    FromAVote       : in  std_logic_vector(PULSE_SYNC_Pos);
    FromBVote       : in  std_logic_vector(PULSE_SYNC_Pos);
    ToVote          : out std_logic_vector(PULSE_SYNC_Pos);
    Clk_Src         : in  std_logic;
    Clk_Dst         : in  std_logic;
    Rst_Src         : in  std_logic;
    Rst_Dst         : in  std_logic;
    TMR_Disable_Src : in  std_logic;
    TMR_Disable_Dst : in  std_logic;
    Pulse_Src       : in  std_logic;
    Pulse_Keep_Src  : out std_logic;
    Pulse_Ack_Src   : out std_logic;
    Pulse_Dst       : out std_logic);
end pulse_sync;

architecture IMP of pulse_sync is

  component mb_sync_bit
  generic(
    C_LEVELS            : natural;
    C_RESET_VALUE       : std_logic;
    C_RESET_SYNCHRONOUS : boolean;
    C_RESET_ACTIVE_HIGH : boolean);
  port(
    Clk            : in  std_logic;
    Rst            : in  std_logic;
    Scan_En        : in  std_logic;
    Scan_Reset_Sel : in  std_logic;
    Scan_Reset     : in  std_logic;
    Raw            : in  std_logic;
    Synced         : out std_logic);
  end component;

  signal pulseQ_src            : std_logic;
  signal pulse_ack_src_I       : std_logic;
  signal pulse_keep_src_I      : std_logic;
  signal pulse_keepD_src       : std_logic;
  signal pulse_keepD_src_voted : std_logic;
  signal pulse_ack_dst         : std_logic;
  signal pulse_keep_dst        : std_logic; 
  signal pulse_keepQ_dst       : std_logic; 
  signal pulse_keepQQ_dst      : std_logic; 
  signal pulseD_dst            : std_logic;
  signal pulseD_dst_voted      : std_logic;
  
begin

  ---------------------------------------------------------------------------------------
  -- Edge detect means that pulse need to be transferred from Src to
  -- Dst clk region regardless of clock ratio between Clk_Src and Clk_Dst
  ---------------------------------------------------------------------------------------
  --  
  --             Clk_Src                  |             Clk_Dst
  --                                      |                         ____
  -- Pulse------------                    |             ---------->|    |    ____
  --       |   ____   |     ____          |            |           |    |   |    |
  --       |  |    |   --->|    |   ____  |   ______   |  ____Vote>|Edge|-->| FF |-> Pulse
  --        ->| FF |------>|Edge|  |    | |  |      |  | |    |    |    |   |_/\_| 
  --          |_/\_| Vote->|Keep|->| FF |--->| Sync |--->| FF |--->|    |
  --                 ----->|____|  |_/\_| |  |______| |  |_/\_|  | |____|
  --                |                     |           |          | 
  --                |  ______             |           |   ____   |  
  --                | |      |            |           |  |    |  |
  -- Pulse Ack <------| Sync |<---------------C_LATE_ACK-| FF |<- 
  --                  |______|            |              |_/\_|
  --                                      |
  --                                      
  --------------------------------------------------------------------------------------

  -- Clock once to enable rising edge detect
  Pulse_Src_DFF : process (Clk_Src) is
  begin
    if Clk_Src'event and Clk_Src = '1' then
      if Rst_Src = '1' then
        pulseQ_src <= '0';
      else
        pulseQ_src <= Pulse_Src;
      end if;
    end if;
  end process Pulse_Src_DFF;

  -- Detect rising Edge on Src and Ack (synced) from Dst
  Pulse_Keep_Logic : process (pulseQ_src, Pulse_Src, pulse_ack_src_I, pulse_keep_src_I) is
  begin
    if Pulse_Src = '0' and pulse_ack_src_I = '1' then
      pulse_keepD_src <= '0'; -- Pulse not active in Clk_Src and Ack from Clk_Dst region, done
    elsif pulseQ_src = '0' and Pulse_Src = '1' then 
      pulse_keepD_src <= '1'; -- Rising edge, set keep
    else
      pulse_keepD_src <= pulse_keep_src_I; -- else keep value
    end if;
  end process Pulse_Keep_Logic;

  TMR_Yes : if (C_TMR /= 0) generate
    signal tmr_disable_src_b : boolean;
    signal tmr_disable_dst_b : boolean;
  begin
    tmr_disable_src_b <= TMR_Disable_Src = '1' and C_USE_TMR_DISABLE = 1;
    tmr_disable_dst_b <= TMR_Disable_Dst = '1' and C_USE_TMR_DISABLE = 1;

    ToVote(PULSE_SYNC_PULSE_Pos) <= pulseD_dst;
    ToVote(PULSE_SYNC_KEEP_Pos)  <= pulse_keepD_src;

    pulse_keepD_src_voted <= vote(pulse_keepD_src,
                                  FromAVote(PULSE_SYNC_KEEP_Pos),
                                  FromBVote(PULSE_SYNC_KEEP_Pos), tmr_disable_src_b);

    pulseD_dst_voted <= vote(pulseD_dst,
                             FromAVote(PULSE_SYNC_PULSE_Pos),
                             FromBVote(PULSE_SYNC_PULSE_Pos), tmr_disable_dst_b);

  end generate TMR_Yes; 

  TMR_No : if (C_TMR = 0) generate
    ToVote <= (others => '0');

    pulse_keepD_src_voted <= pulse_keepD_src;
    pulseD_dst_voted      <= pulseD_dst;
  end generate TMR_No; 
  
  -- Keep DFF
  Pulse_Src_Keep_DFF : process (Clk_Src) is
  begin
    if Clk_Src'event and Clk_Src = '1' then
      if Rst_Src = '1' then
        pulse_keep_src_I <= '0';
      else
        pulse_keep_src_I <= pulse_keepD_src_voted;
      end if;
    end if;
  end process Pulse_Src_Keep_DFF;

  Pulse_Keep_Src <= pulse_keep_src_I;
  
  -- Sync keep to Clk_Dst region
  Pulse_Keep_Keep_Sync_I: mb_sync_bit
  generic map(
    C_LEVELS            => C_LEVELS,
    C_RESET_VALUE       => '0',
    C_RESET_SYNCHRONOUS => true,
    C_RESET_ACTIVE_HIGH => true)
  port map(
    Clk            => Clk_Dst,
    Rst            => Rst_Dst,
    Scan_En        => '0',
    Scan_Reset_Sel => '0',
    Scan_Reset     => '0',
    Raw            => pulse_keep_src_I,
    Synced         => pulse_keep_dst);

  -- Clock once to enable rising edge detect
  Pulse_Dst_Ack_DFF : process (Clk_Dst) is
  begin
    if Clk_Dst'event and Clk_Dst = '1' then
      if Rst_Dst = '1' then
        pulse_keepQ_dst <= '0';
        pulse_keepQQ_dst <= '0';
      else
        pulse_keepQQ_dst <= pulse_keepQ_dst;
        pulse_keepQ_dst <= pulse_keep_dst;
      end if;
    end if;
  end process Pulse_Dst_Ack_DFF;

  -- Detect Edge
  Pulse_Dst_Edge_Logic : process (pulse_keepQ_dst, pulse_keep_dst) is
  begin
    if pulse_keepQ_dst = '0' and pulse_keep_dst = '1' then
      pulseD_dst <= '1'; -- Rising edge
    else
      pulseD_dst <= '0';
    end if;  
  end process Pulse_Dst_Edge_Logic;
    
  -- Clock output 
  Pulse_Dst_DFF : process (Clk_Dst) is
  begin
    if Clk_Dst'event and Clk_Dst = '1' then
      if Rst_Dst = '1' then
        Pulse_Dst <= '0';
      else
        Pulse_Dst <= pulseD_dst_voted;
      end if;
    end if;
  end process Pulse_Dst_DFF;

  Early_Ack : if C_LATE_ACK = 0 generate
  begin
    pulse_ack_dst <= pulse_keepQ_dst;
  end generate Early_Ack;

  Late_Ack : if C_LATE_ACK = 1 generate
  begin
    pulse_ack_dst <= pulse_keepQQ_dst;
  end generate Late_Ack;
  
  -- Sync ack back to Clk_Src region to remove keep
  Pulse_Ack_Sync_I: mb_sync_bit
  generic map(
    C_LEVELS            => C_LEVELS,
    C_RESET_VALUE       => '0',
    C_RESET_SYNCHRONOUS => true,
    C_RESET_ACTIVE_HIGH => true)
  port map(
    Clk            => Clk_Src,
    Rst            => Rst_Src,
    Scan_En        => '0',
    Scan_Reset_Sel => '0',
    Scan_Reset     => '0',
    -- ToDo generic for delayed ack
    Raw            => pulse_ack_dst,
    Synced         => pulse_ack_src_I);

   Pulse_Ack_Src <= pulse_ack_src_I;
  
end architecture IMP;   -- irq_sync




-------------------------------------------------------------------------------
-- divide_part.vhd - Entity and architecture
-------------------------------------------------------------------------------
--
-- (c) Copyright 2011 Xilinx, Inc. All rights reserved.
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
-- Filename:        divide_part.vhd
--
-- Description:     
--                  
-- VHDL-Standard:   VHDL'93
-------------------------------------------------------------------------------
-- Structure:   
--              divide_part.vhd
--
-------------------------------------------------------------------------------
-- Author:          goran
--
-- History:
--   goran  2007-12-19    First Version
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
library iomodule_v3_1_6;
use iomodule_v3_1_6.iomodule_funcs.all;

entity Divide_part is
  generic (
    C_TARGET    : TARGET_FAMILY_TYPE;
    C_USE_SRL16 : string;
    Ratio       : natural;
    First       : boolean := true
    );
  port (
    Config_Reset : in  std_logic;
    Clk          : in  std_logic;
    Rst          : in  std_logic;
    Clk_En       : in  std_logic;
    Clk_En_Out   : out std_logic
    );

end entity Divide_part;

library ieee;
use ieee.numeric_std.all;

architecture VHDL_RTL of Divide_part is
  
  component XIL_SRL16E is
    generic (
      C_TARGET    : TARGET_FAMILY_TYPE;
      C_USE_SRL16 : string;
      C_STATIC    : boolean := false;
      INIT        : bit_vector);
    port (
      Config_Reset : in  std_logic;
      Q            : out std_logic;
      A0           : in  std_logic;
      A1           : in  std_logic;
      A2           : in  std_logic;
      A3           : in  std_logic;
      CE           : in  std_logic;
      CLK          : in  std_logic;
      D            : in  std_logic);
  end component XIL_SRL16E;
  
  component XIL_SRLC16E is
    generic (
      C_TARGET    : TARGET_FAMILY_TYPE;
      C_USE_SRL16 : string;
      INIT        : bit_vector);
    port (
      Config_Reset : in  std_logic;
      Q            : out std_logic;
      Q15          : out std_logic;
      A0           : in  std_logic;
      A1           : in  std_logic;
      A2           : in  std_logic;
      A3           : in  std_logic;
      CE           : in  std_logic;
      CLK          : in  std_logic;
      D            : in  std_logic);
  end component XIL_SRLC16E;
  
  signal loop_Bit   : std_logic;
  signal loop_Bit_i : std_logic;

  -- Set clock enable during reset
  signal Clk_En_i   : std_logic;

  -- Previous cycle reset, used to determine when to shift in a 1
  signal Rst_d1     : std_logic := '0';

  -- This prevents an X from showing up in ModelSim
  -- by simulating the default value in the hardware
  signal Clk_En_Out_i : std_logic := '0';

  constant Nr_Of_SRL16      : natural                      := 1 + ((Ratio-1)/16);
  constant Last_SRL16_Ratio : natural                      := ((Ratio-1) mod 16);
  constant A                : std_logic_vector(3 downto 0) :=
    std_logic_vector(to_unsigned(Last_SRL16_Ratio, 4));

begin  -- architecture VHDL_RTL
  
  One_SRL16 : if (Nr_Of_SRL16 = 1) generate
  begin
    SRL16E_I : XIL_SRL16E
      generic map (
        C_TARGET    => C_TARGET,
        C_USE_SRL16 => C_USE_SRL16,     -- [string]
        INIT        => X"0001")         -- [bit_vector]
      port map (
        Config_Reset => Config_Reset,   -- [in  std_logic]
        CE           => Clk_En_i,       -- [in  std_logic]
        D            => loop_Bit_i,     -- [in  std_logic]
        Clk          => Clk,            -- [in  std_logic]
        A0           => A(0),           -- [in  std_logic]
        A1           => A(1),           -- [in  std_logic]
        A2           => A(2),           -- [in  std_logic]
        A3           => A(3),           -- [in  std_logic]
        Q            => loop_Bit);      -- [out std_logic]
  end generate One_SRL16;

  Two_SRL16 : if (Nr_Of_SRL16 = 2) generate

    signal shift   : std_logic;
    signal shift_i : std_logic;
    -- signal Emptys : std_logic_vector(0 to Nr_Of_SRL16);
  begin
    -- Shift in 0's during reset
    shift_i <= shift;

    -- The first SRLC16E
    SRLC16E_1 : XIL_SRLC16E
      generic map (
        C_TARGET    => C_TARGET,
        C_USE_SRL16 => C_USE_SRL16,     -- [string]
        INIT        => X"0001")         -- [bit_vector]
      port map (
        Config_Reset => Config_Reset,   -- [in  std_logic]
        CE           => Clk_En_i,       -- [in  std_logic]
        D            => loop_Bit_i,     -- [in  std_logic]
        Clk          => Clk,            -- [in  std_logic]
        A0           => '1',            -- [in  std_logic]
        A1           => '1',            -- [in  std_logic]
        A2           => '1',            -- [in  std_logic]
        A3           => '1',            -- [in  std_logic]
        Q15          => shift,          -- [out  std_logic]
        Q            => open);          -- [out std_logic]

    SRL16E_2 : XIL_SRL16E
      generic map (
        C_TARGET    => C_TARGET,
        C_USE_SRL16 => C_USE_SRL16,     -- [string]
        INIT        => X"0000")         -- [bit_vector]
      port map (
        Config_Reset => Config_Reset,   -- [in  std_logic]
        CE           => Clk_En_i,       -- [in  std_logic]
        D            => shift_i,        -- [in  std_logic]
        Clk          => Clk,            -- [in  std_logic]
        A0           => A(0),           -- [in  std_logic]
        A1           => A(1),           -- [in  std_logic]
        A2           => A(2),           -- [in  std_logic]
        A3           => A(3),           -- [in  std_logic]
        Q            => loop_Bit);      -- [out std_logic]
  end generate Two_SRL16;

  More_Than_Two : if (Nr_Of_SRL16 > 2) generate

    signal shifts   : std_logic_vector(1 to Nr_Of_SRL16-1);
    signal shifts_i : std_logic_vector(1 to Nr_Of_SRL16-1);
    -- signal Emptys : std_logic_vector(0 to Nr_Of_SRL16);
  begin

    -- Shift in 0's during reset
    Shifts_I_Rst : for I in 1 to Nr_Of_SRL16-1 generate
       shifts_i(I) <= shifts(I);
    end generate Shifts_I_Rst;

    -- The first SRLC16E
    SRLC16E_1 : XIL_SRLC16E
      generic map (
        C_TARGET    => C_TARGET,
        C_USE_SRL16 => C_USE_SRL16,     -- [string]
        INIT        => X"0001")         -- [bit_vector]
      port map (
        Config_Reset => Config_Reset,   -- [in  std_logic]
        CE           => Clk_En_i,       -- [in  std_logic]
        D            => loop_Bit_i,     -- [in  std_logic]
        Clk          => Clk,            -- [in  std_logic]
        A0           => '1',            -- [in  std_logic]
        A1           => '1',            -- [in  std_logic]
        A2           => '1',            -- [in  std_logic]
        A3           => '1',            -- [in  std_logic]
        Q15          => shifts(1),      -- [out  std_logic]
        Q            => open);          -- [out std_logic]

    The_Rest : for I in 1 to Nr_Of_SRL16-2 generate
    begin
      SRLC16E_I : XIL_SRLC16E
        generic map (
          C_TARGET    => C_TARGET,
          C_USE_SRL16 => C_USE_SRL16,    -- [string]
          INIT        => X"0000")        -- [bit_vector]
        port map (
          Config_Reset => Config_Reset,  -- [in  std_logic]
          CE           => Clk_En_i,      -- [in  std_logic]
          D            => shifts_i(I),   -- [in  std_logic]
          Clk          => Clk,           -- [in  std_logic]
          A0           => '1',           -- [in  std_logic]
          A1           => '1',           -- [in  std_logic]
          A2           => '1',           -- [in  std_logic]
          A3           => '1',           -- [in  std_logic]
          Q15          => shifts(I+1),   -- [out  std_logic]
          Q            => open);         -- [out std_logic]

    end generate The_Rest;

    -- The last SRL16
    SRL16E_n : XIL_SRL16E
      generic map (
        C_TARGET    => C_TARGET,
        C_USE_SRL16 => C_USE_SRL16,               -- [string]
        INIT        => X"0000")                   -- [bit_vector]
      port map (
        Config_Reset => Config_Reset,             -- [in  std_logic]
        CE           => Clk_En_i,                 -- [in  std_logic]
        D            => shifts_i(Nr_Of_SRL16-1),  -- [in  std_logic]
        Clk          => Clk,                      -- [in  std_logic]
        A0           => A(0),                     -- [in  std_logic]
        A1           => A(1),                     -- [in  std_logic]
        A2           => A(2),                     -- [in  std_logic]
        A3           => A(3),                     -- [in  std_logic]
        Q            => loop_Bit);                -- [out std_logic]

  end generate More_Than_Two;

  -- Store if the previous cycle was a reset
  Clk_Rst_D1 : process (Clk) is
  begin
    if Clk'event and Clk = '1' then   -- rising clock edge
      Rst_d1 <= Rst;
    end if;
  end process Clk_Rst_D1;

  -- Set clock enable during reset, Rst_d1 is necessary to load
  -- the 1 bit in from loop_bit_i
  clk_en_i   <= Clk_En;-- or Rst or Rst_d1;

  -- Loops around from previous interrupt, or inserts after reset
  -- The reset pulse must be at least 17 cycles
  loop_Bit_i <= loop_Bit; --(loop_Bit or Rst_d1);

  -- Same signal, but internal version has default value for
  -- simulation
  Clk_En_Out <= Clk_En_Out_i;

  -----------------------------------------------------------------------------
  -- If the SRL16 is the first in a series then the output is a clean single
  -- clock pulse
  -----------------------------------------------------------------------------
  Is_First : if (First) generate
    Clk_En_Out_i <= loop_Bit;
  end generate Is_First;


  -----------------------------------------------------------------------------
  -- If not the first the output has to be masked so that it produce a single
  -- clock pulse
  -----------------------------------------------------------------------------
  not_First : if (not First) generate
    signal Out1 : std_logic;
  begin

    Out1_DFF : process (Clk) is
    begin  -- process Out1_DFF
      if Clk'event and Clk = '1' then   -- rising clock edge
        Out1 <= loop_Bit;
      end if;
    end process Out1_DFF;

    Out2_DFF : process (Clk) is
    begin  -- process Out2_DFF
      if Clk'event and Clk = '1' then   -- rising clock edge
        if (Out1 = '1') then
          Clk_En_Out_i <= Clk_En;
        end if;
      end if;
    end process Out2_DFF;
    
  end generate not_First;
end architecture VHDL_RTL;


-------------------------------------------------------------------------------
-- fit_module.vhd - Entity and architecture
-------------------------------------------------------------------------------
--
-- (c) Copyright 2011-2012,2016 Xilinx, Inc. All rights reserved.
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
-- Filename:        fit_module.vhd
--
-- Description:
--
-- VHDL-Standard:   VHDL'93
-------------------------------------------------------------------------------
-- Structure:
--              fit_module.vhd
--
-------------------------------------------------------------------------------
-- Author:          goran
--
-- History:
--   goran  2007-12-19    First Version
-- stefana  2012-05-30    Fixed log2 function
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
library iomodule_v3_1_6;
use iomodule_v3_1_6.iomodule_funcs.all;

entity FIT_Module is
  generic (
    C_TARGET          : TARGET_FAMILY_TYPE;
    C_TMR             : integer := 0;
    C_USE_TMR_DISABLE : integer := 0;
    C_VOTE_SIZE       : integer := 0;
    C_USE_SRL16       : string;
    C_USE_FIT         : integer := 1;
    C_NO_CLOCKS       : integer := 6216;  -- The number of clocks between each interrupt
    C_INACCURACY      : integer := 5      -- The maximum inaccuracy of the number
                                          -- of clocks allowed in per thousands
    );
  port (
    Config_Reset : in  std_logic;
    Clk          : in  std_logic;
    Reset        : in  boolean;
    TMR_Disable  : in  std_logic;
    FromAVote    : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
    FromBVote    : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
    ToVote       : out std_logic_vector(C_VOTE_SIZE-1 downto 0);
    Toggle       : out std_logic;
    Interrupt    : out std_logic);
end entity FIT_Module;

library iomodule_v3_1_6;
use iomodule_v3_1_6.all;
use iomodule_v3_1_6.iomodule_vote_pkg.all;

architecture VHDL_RTL of FIT_Module is

  constant C_NO_CLOCKS_MIN : integer := 3;

  component Divide_Part is
    generic (
      C_TARGET    : TARGET_FAMILY_TYPE;
      C_USE_SRL16 : string;
      Ratio       : natural;
      First       : boolean);
    port (
      Config_Reset : in  std_logic;
      Clk          : in  std_logic;
      Rst          : in  std_logic;
      Clk_En       : in  std_logic;
      Clk_En_Out   : out std_logic);
  end component Divide_Part;

  component MB_MUXCY_XORCY is
    generic (
      C_TARGET : TARGET_FAMILY_TYPE);
    port (
      O  : out std_logic;
      LO : out std_logic;
      CI : in  std_logic;
      DI : in  std_logic;
      S  : in  std_logic);
  end component MB_MUXCY_XORCY;

  -- log2 function returns the number of bits required to encode x choices
  function log2(x : natural) return integer is
    variable i : integer := 0;
  begin
    if x = 0 then return 0;
    elsif x > 2**30 then return 31;
    else
      while 2**i < x loop
        i := i+1;
      end loop;
      return i;
    end if;
  end function log2;

  -----------------------------------------------------------------------------
  -- All supported architectures have the SRL16C primitive, we will actually
  -- looking for factorials upto 128 (upto 7 SRL16s in a chain)
  -- looking for any more is not efficient since 128 can be done with 7 LUTs in
  -- a normal counter
  -----------------------------------------------------------------------------
  constant MAX_DIV_FACTOR : natural := 128;

  subtype SRL16_DIV_TYPE is natural range 2 to MAX_DIV_FACTOR;
  type FACTORS_LIST_TYPE is array (natural range 1 to 15) of SRL16_DIV_TYPE;

  type FACTORS_TYPE is
  record
    Good_Divide   : boolean;
    Nr_Of_Factors : natural;
    Factor_List   : FACTORS_LIST_TYPE;
    Nr_Of_SRL16s  : natural;
  end record FACTORS_TYPE;

  -----------------------------------------------------------------------------
  -- Trying to divide R into integer values of values 2-16 until the end result
  -- is between 2-16.
  --
  -- This function returns a FACTORS_TYPE which contains:
  -- FACTOR_LIST   - List of factors
  -- Nr_Of_Factors - Number of factors / Number of divide_parts needed
  -- Nr_Of_SRL16s  - Number of SRL16s
  -- Good_Divide   - Whether the number could be factored
  -----------------------------------------------------------------------------
  function Get_Factors (R : natural) return FACTORS_TYPE is
    variable N      : natural := R;
    variable Result : FACTORS_TYPE;
    variable no     : natural := 1;
    variable Found  : boolean;
  begin  -- function Get_Factors
    -- Initialize values
    Result.Nr_Of_Factors := 0;
    Result.Nr_Of_SRL16s  := 0;
    Result.Factor_List   := (2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2);

    -- Check if we can do it in one SRL16
    if (N < 16) then
      Result.FACTOR_LIST(1) := N;
      Result.Nr_Of_Factors  := 1;
      Result.Good_Divide    := true;
      Result.Nr_Of_SRL16s   := 1;
      return Result;
    end if;

    -- Each time through this loop it finds a factor
    -- The factor gets added to FACTOR_LIST(no)
    -- The Nr_Of_SRL16s is increased appropriately
    while N /= 1 loop
      Found := false;
      -- Trying first with a single SRL16 since it the most efficient implementation
      --
      -- Find largest factor from 16 down to 2, because no matter what value
      -- it is in this range, it will use a single SRL16
      for I in 16 downto 2 loop
        if ((N mod I = 0)) then         -- Found factor
          Result.FACTOR_LIST(no) := I;
          Result.Nr_Of_SRL16s    := Result.Nr_Of_SRL16s + 1;
          N                      := N / I;
          no                     := no + 1;
          Found                  := true;
          exit;
        end if;
      end loop;  -- I

      -- No factor from 2 to 16
      if (not(Found)) then
        -- Trying from 17 upto MAX_DIV_FACTOR to find if a chain of SRL16 can
        -- be used
        -- Find the smallest value for the smallest chain
        for I in 17 to MAX_DIV_FACTOR loop
          if ((N mod I = 0)) then       -- Found factor
            Result.FACTOR_LIST(no) := I;
            Result.Nr_Of_SRL16s    := Result.Nr_Of_SRL16s + (1 + ((I-1)/16));
            N                      := N / I;
            no                     := no + 1;
            Found                  := true;
            exit;
          end if;
        end loop;  -- I
      end if;

      -- No factor from 2 to MAX_DIV_FACTOR
      if (not(Found)) then
        -- Could not factor
        Result.Good_Divide := false;
        exit;
      end if;
    end loop;
    if (found) then
      Result.Good_Divide   := true;
      Result.Nr_Of_Factors := no-1;
    end if;
    return Result;
  end function Get_Factors;

  -----------------------------------------------------------------------------
  -- Trying to find a ratio that is within 1.5% of the asked ratio and that the
  -- ratio can be implemented with SRL16.
  -----------------------------------------------------------------------------
  function Find_Best_Factors (R : natural) return FACTORS_TYPE is
    constant Proc_Diff : natural := R*C_INACCURACY/1000;  -- Calculate the max difference
                                                          -- for the maximum inaccuracy
    variable Result    : FACTORS_TYPE;
  begin  -- function Find_Best_Factors
    Result := Get_Factors(R);

    if (Result.Good_Divide) then
      return Result;
    end if;

    -- This if statement gets rid of a warning if C_INACCURACY = 0
    if (Proc_Diff > 0) then
      for I in 1 to Proc_Diff loop
        Result := Get_Factors(R+I);
        if (Result.Good_Divide) then
          return Result;
        end if;
        Result := Get_Factors(R-I);
        if (Result.Good_Divide) then
          return Result;
        end if;
      end loop;  -- I
    end if;  -- Proc_Diff > 0

    Result.Good_Divide := false;
    return Result;
  end function Find_Best_Factors;

begin  -- architecture VHDL_RTL

  Implement_FIT : if (C_USE_FIT /= 0 and C_NO_CLOCKS >= C_NO_CLOCKS_MIN) generate

    constant Nr_Of_Bits     : natural := log2(C_NO_CLOCKS-1);
    constant Divide_Factors : FACTORS_TYPE := Find_Best_Factors(C_NO_CLOCKS);
    signal Interrupt_i : std_logic := '0';
    signal rst_i       : std_logic;
    signal toggle_i    : std_logic;

  begin

    -----------------------------------------------------------------------------
    -- handle the reset
    -----------------------------------------------------------------------------
    rst_i <= '1' when Reset else '0';

    -----------------------------------------------------------------------------
    -- A clean and good ratio was found that was within the 1.5% limit, so
    -- implement the fit_timer division using SRL16s but only if the number of
    -- SRL16 is less than what is needed for a standard down-counter
    --
    -- ex. the value 127*127 = 16129 can be split into two SRL16 chain where each
    -- chain is 8 SRL16 => a total of 16 SRL16. But a 14-bit counter can count to
    -- 16129 and it will only consume 14 LUTs so it's more area efficient
    -----------------------------------------------------------------------------
    Using_SRL16s : if (Divide_Factors.Good_Divide) and
                      (Divide_Factors.Nr_Of_SRL16s <= Nr_Of_Bits) and (C_TMR = 0) generate

      signal Clk_En_I : std_logic_vector(0 to Divide_Factors.Nr_Of_Factors);

    begin
      Clk_En_I(0) <= '1';

      SRL16s : for I in 1 to Divide_Factors.Nr_Of_Factors generate
      begin

        Divide_I : Divide_Part
          generic map (
            C_TARGET    => C_TARGET,
            C_USE_SRL16 => C_USE_SRL16,                    -- [string]
            Ratio       => Divide_Factors.FACTOR_LIST(I),  -- [natural range 2 to 16]
            First       => (I = 1))                        -- [boolean]
          port map (
            Config_Reset => Config_Reset,                  -- [in  std_logic]
            Clk          => Clk,                           -- [in  std_logic]
            Rst          => rst_i,                         -- [in  std_logic]
            Clk_En       => Clk_En_I(I-1),                 -- [in  std_logic]
            Clk_En_Out   => Clk_En_I(I));                  -- [out std_logic]

      end generate SRL16s;

      Interrupt_i <= Clk_En_I(Divide_Factors.Nr_Of_Factors);

      ToVote <= (others => '0');
    end generate Using_SRL16s;

    -----------------------------------------------------------------------------
    -- Couldn't find a good ratio within the 1.5% limit so implement the fit_timer
    -- generation using a standard counter or
    -- the number of SRL16 is greater than the number of LUTS a standard down-counter needs
    -----------------------------------------------------------------------------
    Using_Counter : if (not Divide_Factors.Good_Divide) or
                       (Divide_Factors.Nr_Of_SRL16s > Nr_Of_Bits) or (C_TMR /= 0) generate

      constant New_Value : std_logic_vector(0 to Nr_Of_Bits-1) :=
        std_logic_vector(to_unsigned(natural(C_NO_CLOCKS-2), Nr_Of_Bits));

      signal Cnt         : std_logic_vector(0 to Nr_Of_Bits-1);
      signal New_Cnt     : std_logic_vector(0 to Nr_Of_Bits-1);
      signal Carry       : std_logic_vector(0 to Nr_Of_Bits);
      signal Count       : std_logic_vector(0 to Nr_Of_Bits-1) := New_Value;
      signal rst_cnt     : std_logic                           := '0';

    begin

      -- Reset the counter
      rst_cnt <= Interrupt_i or rst_i;

      Carry(Nr_Of_Bits) <= '0';         -- Always subtracting

      All_Bits : for I in Nr_Of_Bits-1 downto 0 generate
      begin
        -- New_Cnt counts up
        -- New_Cnt(I) <= not(Count(I)) when Interrupt_i = '0' else New_Value(I);
        New_Cnt(I) <= not(Count(I));

        MUXCY_XORCY_L_I1 : MB_MUXCY_XORCY
          generic map (
            C_TARGET => C_TARGET)
          port map (
            DI => Count(I),             -- [in  std_logic S = 0]
            CI => Carry(I+1),           -- [in  std_logic S = 1]
            S  => New_Cnt(I),           -- [in  std_logic (Select)]
            LO => Carry(I),             -- [out std_logic]
            O  => Cnt(I));              -- [out std_logic]

      end generate All_Bits;

      TMR_No : if (C_TMR = 0) generate
      begin
        -- Count goes from all 1's during interrupt_i
        -- then C_NO_CLOCKS-1 down to 0 between interrupts
        Counter : process (Clk) is
        begin  -- process Counter
          if Clk'event and Clk = '1' then  -- rising clock edge
            if rst_cnt = '1' then
              Count       <= New_Value;
              Interrupt_i <= '0';
            else
              Count       <= Cnt;
              Interrupt_i <= not Carry(0);
            end if;
          end if;
        end process Counter;

        ToVote(FIT_COUNT_Pos)     <= (others => '0');
        ToVote(FIT_INTERRUPT_Pos) <= '0';

      end generate TMR_No;

      TMR_Yes : if (C_TMR /= 0) generate
        signal tmr_disable_b : boolean;
        signal Interrupt_i_d : std_logic;
        signal Count_d       : std_logic_vector(0 to Nr_Of_Bits-1);
      begin

        tmr_disable_b <= TMR_Disable = '1' and C_USE_TMR_DISABLE = 1;

        Counter_Logic : process (rst_cnt, Cnt, Carry) is
        begin
          if rst_cnt = '1' then
            Count_d       <= New_Value;
            Interrupt_i_d <= '0';
          else
            Count_d       <= Cnt;
            Interrupt_i_d <= not Carry(0);
          end if;
        end process Counter_Logic;

        ToVote(FIT_COUNT_Pos'low + Count_d'length - 1 downto FIT_COUNT_Pos'low) <= Count_d;
        ToVote(FIT_COUNT_Pos'high downto FIT_COUNT_POs'low + Count_d'length )   <= (others => '0');

        ToVote(FIT_INTERRUPT_Pos) <= Interrupt_i_d;

        Counter_DFF : process (Clk) is
        begin
          if Clk'event and Clk = '1' then  -- rising clock edge
            Count       <= vote(Count_d,
                                FromAVote(FIT_COUNT_Pos'low + Count_d'length - 1 downto FIT_COUNT_Pos'low),
                                FromBVote(FIT_COUNT_Pos'low + Count_d'length - 1 downto FIT_COUNT_Pos'low),
                                tmr_disable_b);
            Interrupt_i <= vote(Interrupt_i_d,FromAVote(FIT_INTERRUPT_Pos),FromBVote(FIT_INTERRUPT_Pos),
                                tmr_disable_b);
          end if;
        end process Counter_DFF;

      end generate TMR_Yes;

    end generate Using_Counter;

    Interrupt <= Interrupt_i;

    TMR_No_Toggle : if (C_TMR = 0) generate
    begin

      Toggle_Handler : process (Clk) is
      begin
        if Clk'event and Clk = '1' then
          if Reset then
            toggle_i <= '0';
          elsif Interrupt_i = '1' then
            toggle_i <= not toggle_i;
          end if;
        end if;
      end process Toggle_Handler;

      ToVote(FIT_TOGGLE_Pos) <= '0';

    end generate TMR_No_Toggle;

    TMR_Yes_Toggle : if (C_TMR /= 0) generate
      signal tmr_disable_b  : boolean;
      signal toggle_i_d     : std_logic;
    begin

      tmr_disable_b <= TMR_Disable = '1' and C_USE_TMR_DISABLE = 1;

      Toggle_Logic : process (Reset, toggle_i, Interrupt_i) is
      begin
        if Reset then
          toggle_i_d <= '0';
        elsif Interrupt_i = '1' then
          toggle_i_d <= not toggle_i;
        else
          toggle_i_d <= toggle_i;
        end if;
      end process Toggle_Logic;

      Toggle_DFF : process (Clk) is
      begin
        if Clk'event and Clk = '1' then
          toggle_i <= vote(toggle_i_d,FromAVote(FIT_TOGGLE_Pos),FromBVote(FIT_TOGGLE_Pos),tmr_disable_b);
        end if;
      end process Toggle_DFF;

      ToVote(FIT_TOGGLE_Pos) <= toggle_i_d;

    end generate TMR_Yes_Toggle;

    Toggle <= toggle_i;

  end generate Implement_FIT;

  Nothing : if (C_USE_FIT = 0 or C_NO_CLOCKS < C_NO_CLOCKS_MIN) generate
  begin
    Interrupt <= '0';
    Toggle    <= '0';
    ToVote    <= (others => '0');
  end generate Nothing;

end architecture VHDL_RTL;


-------------------------------------------------------------------------------
-- gpi_module.vhd - Entity and architecture
-------------------------------------------------------------------------------
--
-- (c) Copyright 2011-2013 Xilinx, Inc. All rights reserved.
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
-- Filename:        gpi_module.vhd
--
-- Description:     
--                  
-- VHDL-Standard:   VHDL'93/02
-------------------------------------------------------------------------------
-- Structure:   
--              gpi_module.vhd
--
-------------------------------------------------------------------------------
-- Author:          goran
--
-- History:
--   goran   2007-12-19    First Version
--   stefana 2012-03-20    Added interrupt
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

entity GPI_Module is
  generic (
    C_USE_GPI       : integer;
    C_GPI_SIZE      : integer;
    C_GPI_INTERRUPT : integer);
  port (
    Clk           : in  std_logic;
    Reset         : in  boolean;
    Config_Reset  : in  std_logic;
    GPI_Read      : in  std_logic;
    GPI           : in  std_logic_vector(C_GPI_SIZE-1 downto 0);
    GPI_In        : out std_logic_vector(C_GPI_SIZE-1 downto 0);
    GPI_Interrupt : out std_logic
    );
end entity GPI_Module;

architecture IMP of GPI_Module is

begin  -- architecture IMP

  Using_GPI : if (C_USE_GPI /= 0) generate
    signal GPI_Sampled : std_logic_vector(C_GPI_SIZE-1 downto 0);
  begin

    ----------------------------------------------------------------------------------------------
    -- Hold GPI_In signal in constant reset until we want to read the values.
    -- This allows us to just ORing all IO registers which we want to read
    ----------------------------------------------------------------------------------------------
    GPI_Sampling : process (Clk) is
    begin  -- process GPI_Sampling
      if Clk'event and Clk = '1' then  -- rising clock edge
        if (GPI_Read = '0' or Config_Reset = '1') then       -- synchronous reset (active high)
          GPI_In <= (others => '0');
        else
          GPI_In <= GPI;
        end if;
        if Config_Reset = '1' then
          GPI_Sampled <= (others => '0');
        else
          GPI_Sampled <= GPI;
        end if;
      end if;
    end process GPI_Sampling;

    ----------------------------------------------------------------------------------------------
    -- Generate interupt pulse whenever input differs from sampled value according to setting
    ----------------------------------------------------------------------------------------------
    Use_GPI_Interrupt : if (C_GPI_INTERRUPT /= 0) generate
      constant Zero : std_logic_vector(C_GPI_SIZE-1 downto 0) := (others => '0');
    begin

      GPI_Interrupt_DFF : process (Clk) is
      begin  -- process GPI_Interrupt_DFF
        if Clk'event and Clk = '1' then  -- rising clock edge
          if Reset then
            GPI_Interrupt <= '0';
          elsif (C_GPI_INTERRUPT = 1 and (GPI_Sampled /= GPI))              or    -- Both
                (C_GPI_INTERRUPT = 2 and (not GPI_Sampled and GPI) /= Zero) or    -- Rising
                (C_GPI_INTERRUPT = 3 and (GPI_Sampled and not GPI) /= Zero) then  -- Falling
            GPI_Interrupt <= '1';
          else
            GPI_Interrupt <= '0';
          end if;
        end if;
      end process GPI_Interrupt_DFF;

    end generate Use_GPI_Interrupt;

    No_GPI_Interrupt : if (C_GPI_INTERRUPT = 0) generate
    begin
      GPI_Interrupt <= '0';
    end generate No_GPI_Interrupt;

  end generate Using_GPI;

  No_GPI : if (C_USE_GPI = 0) generate
  begin
    GPI_In        <= (others => '0');
    GPI_Interrupt <= '0';
  end generate No_GPI;
  
end architecture IMP;


-------------------------------------------------------------------------------
-- gpo_module.vhd - Entity and architecture
-------------------------------------------------------------------------------
--
-- (c) Copyright 2011,2016 Xilinx, Inc. All rights reserved.
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
-- Filename:        gpo_module.vhd
--
-- Description:     
--                  
-- VHDL-Standard:   VHDL'93/02
-------------------------------------------------------------------------------
-- Structure:   
--              gpo_module.vhd
--
-------------------------------------------------------------------------------
-- Author:          goran
--
-- History:
--   goran  2007-12-19    First Version
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

entity GPO_Module is
  
  generic (
    C_TMR             : integer := 0;
    C_USE_TMR_DISABLE : integer := 0;
    C_VOTE_SIZE       : integer := 0;
    C_USE_GPO         : integer := 1;
    C_GPO_SIZE        : integer range 1 to 32 := 32;
    C_GPO_INIT        : std_logic_vector(31 downto 0) := (others => '0'));
  port (
    Clk         : in  std_logic;
    Reset       : in  boolean;
    GPO_Write   : in  std_logic;
    Write_Data  : in  std_logic_vector(31 downto 0);
    TMR_Disable : in  std_logic;
    FromAVote   : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
    FromBVote   : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
    ToVote      : out std_logic_vector(C_VOTE_SIZE-1 downto 0);
    GPO         : out std_logic_vector(C_GPO_SIZE-1 downto 0));    
end entity GPO_Module;

library iomodule_v3_1_6;
use iomodule_v3_1_6.iomodule_vote_pkg.all;

architecture IMP of GPO_Module is

  signal gpo_io_i : std_logic_vector(C_GPO_SIZE-1 downto 0);
  
begin  -- architecture IMP

  TMR_No : if (C_TMR = 0 and C_USE_GPO /= 0) generate
  begin

      GPO_DFF : process (Clk) is
      begin  -- process GPO_DFF
        if Clk'event and Clk = '1' then  -- rising clock edge
          if Reset then                  -- synchronous reset (active high)
            gpo_io_i <= C_GPO_INIT(gpo_io_i'range);
          elsif (GPO_Write = '1') then
            gpo_io_i <= Write_Data(gpo_io_i'range);
          end if;
        end if;
      end process GPO_DFF;
      
    ToVote <= (others => '0');

  end generate TMR_No;

  TMR_Yes : if (C_TMR /= 0 and C_USE_GPO /= 0) generate
    signal tmr_disable_b : boolean;
    signal gpo_io_i_d    : std_logic_vector(C_GPO_SIZE-1 downto 0);
  begin
    
    tmr_disable_b <= TMR_Disable = '1' and C_USE_TMR_DISABLE = 1;

     GPO_logic : process (Reset, GPO_Write, Write_Data, gpo_io_i) is
    begin 
      if Reset then
        gpo_io_i_d <= C_GPO_INIT(gpo_io_i'range);
      elsif (GPO_Write = '1') then
        gpo_io_i_d <= Write_Data(gpo_io_i'range);
      else
        gpo_io_i_d <= gpo_io_i;
      end if;
    end process GPO_Logic;

    ToVote(gpo_io_i_d'range)                          <= gpo_io_i_d;
    ToVote(C_MAX_GPO_SIZE-1 downto gpo_io_i_d'high+1) <= (others => '0');
    
    GPO_DFF : process (Clk) is
    begin
      if Clk'event and Clk = '1' then
        gpo_io_i <= vote(gpo_io_i_d, FromAVote(gpo_io_i_d'range), FromBVote(gpo_io_i_d'range),tmr_disable_b); 
      end if;
    end process GPO_DFF;

  end generate TMR_Yes;
  
  Empty : if (C_USE_GPO = 0) generate
  begin
    gpo_io_i <= (others => '0');
    ToVote   <= (others => '0');
  end generate Empty;

  GPO <= gpo_io_i;
end architecture IMP;


-------------------------------------------------------------------------------
-- intr_ctrl.vhd - Entity and architecture
-------------------------------------------------------------------------------
--
-- (c) Copyright 2011-2012,2016,2018 Xilinx, Inc. All rights reserved.
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
-- Filename:        intr_ctrl.vhd
--
-- Description:
--
-- VHDL-Standard:   VHDL'93/02
-------------------------------------------------------------------------------
-- Structure:
--              intr_ctrl.vhd
--
-------------------------------------------------------------------------------
-- Author:          goran
--
-- History:
--   goran  2008-01-08    First Version
--   stefan 2011-12-28    Added Fast Interrupt
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
library iomodule_v3_1_6;
use iomodule_v3_1_6.iomodule_funcs.all;

entity intr_ctrl is

  generic (
    C_TARGET            : TARGET_FAMILY_TYPE;
    C_TMR               : integer := 0;
    C_USE_TMR_DISABLE   : integer := 0;
    C_VOTE_SIZE         : integer := 0;
    C_USE_COMB_MUX      : integer := 0;
    C_ADDR_WIDTH        : integer range 32 to 64 := 32;
    C_INTC_ENABLED      : std_logic_vector(31 downto 0);
    C_INTC_LEVEL_EDGE   : std_logic_vector(31 downto 0);
    C_INTC_POSITIVE     : std_logic_vector(31 downto 0);
    C_INTC_ASYNC_INTR   : std_logic_vector(31 downto 0);
    C_INTC_HAS_FAST     : integer range 0 to 1  := 0;
    C_INTC_ADDR_WIDTH   : integer range 5 to 64 := 32;
    C_INTC_NUM_SYNC_FF  : integer range 0 to 7  := 2;
    C_INTC_BASE_VECTORS : std_logic_vector(63 downto 0);
    C_USE_LUTRAM        : string);
  port (
    Clk               : in  std_logic;
    Reset             : in  boolean;
    TMR_Disable       : in  std_logic;
    FromAVote         : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
    FromBVote         : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
    ToVote            : out std_logic_vector(C_VOTE_SIZE-1 downto 0);
    INTR              : in  std_logic_vector(31 downto 0);
    INTR_ACK          : in  std_logic_vector(1 downto 0);
    INTR_ADDR         : out std_logic_vector(C_ADDR_WIDTH-1 downto 0);
    INTC_WRITE_CIAR   : in  std_logic;
    INTC_WRITE_CIER   : in  std_logic;
    INTC_WRITE_CIMR   : in  std_logic;
    INTC_WRITE_CIVAR  : in  std_logic;
    INTC_WRITE_CIVEAR : in  std_logic;
    INTC_CIVAR_ADDR   : in  std_logic_vector(4 downto 0);
    Write_Data        : in  std_logic_vector(31 downto 0);
    INTC_READ_CISR    : in  std_logic;
    INTC_READ_CIPR    : in  std_logic;
    INTC_IRQ          : out std_logic;
    INTC_CISR         : out std_logic_vector(31 downto 0);
    INTC_CIPR         : out std_logic_vector(31 downto 0));
end entity intr_ctrl;

library iomodule_v3_1_6;
use iomodule_v3_1_6.iomodule_vote_pkg.all;
use iomodule_v3_1_6.mb_sync_bit;

architecture IMP of intr_ctrl is

  component MB_FDR is
    generic (
      C_TARGET : TARGET_FAMILY_TYPE;
      INIT : bit := '0');
    port(
      Q  : out std_logic;
      C  : in  std_logic;
      D  : in  std_logic;
      R  : in  std_logic);
  end component MB_FDR;

  component mb_sync_bit is
  generic(
    C_LEVELS            : natural   := 2;
    C_RESET_VALUE       : std_logic := '0';
    C_RESET_SYNCHRONOUS : boolean   := true;
    C_RESET_ACTIVE_HIGH : boolean   := true);
  port(
    Clk            : in  std_logic;
    Rst            : in  std_logic;
    Scan_En        : in  std_logic;
    Scan_Reset_Sel : in  std_logic;
    Scan_Reset     : in  std_logic;
    Raw            : in  std_logic;
    Synced         : out std_logic);
  end component mb_sync_bit;

  constant C_ENABLED_NONE : boolean := (C_INTC_ENABLED = (31 downto 0  => '0'));
  constant C_ENABLED_MSH  : boolean := (C_INTC_ENABLED(31 downto 16) /= X"0000");
  constant C_CIVAR_WIDTH  : integer := Boolean'Pos(C_ENABLED_MSH) + 4;
  constant C_CIVAR_SIZE   : integer := 2 ** C_CIVAR_WIDTH;

  constant C_BASE_VECTORS : std_logic_vector(63 downto 0) :=
    (C_INTC_BASE_VECTORS and X"FFFFFFFFFFFFFF80") or X"0000000000000010";
  constant C_DEFAULT_ADDR : std_logic_vector(C_ADDR_WIDTH - 1 downto 0) :=
    C_BASE_VECTORS(C_ADDR_WIDTH - 1 downto 0);

  constant USE_LUTRAM : boolean := C_USE_LUTRAM = "yes";

  signal interrupt    : std_logic_vector(31 downto 0);
  signal intr_present : std_logic_vector(31 downto 0);
  signal cisr         : std_logic_vector(31 downto 0);
  signal cier         : std_logic_vector(31 downto 0);
  signal cipr         : std_logic_vector(31 downto 0);
  signal rst_cipr_rd  : std_logic;
  signal rst_cipr_rd_voted : std_logic;
  signal civr         : std_logic_vector(4 downto 0);
  signal fast_ack     : std_logic_vector(31 downto 0);
  signal cimr         : std_logic_vector(31 downto 0);

  signal tmr_disable_b : boolean;

begin

  tmr_disable_b <= TMR_Disable = '1' and C_USE_TMR_DISABLE = 1 and C_TMR = 1;

  All_INTR_Bits : for I in 31 downto 0 generate
  begin

    Using_Intr : if (C_INTC_ENABLED(I) = '1') generate
    begin

      -- Clean the interrupt signals
      -- All internal sources are considered clean and only external needs to be registred once
      Ext_Intr : if (I > 15) generate
        constant C_RESET_VALUE : std_logic :=  not C_INTC_POSITIVE(I);
        signal synced_intr : std_logic;
      begin

        -- Synchronize the interrupt signals
        Async_Gen : if C_INTC_ASYNC_INTR(I) = '1' generate
          signal reset_std : std_logic;
        begin

          reset_std <= '1' when reset else '0';
          
          sync_bit_i : mb_sync_bit
          generic map(
            C_LEVELS            => C_INTC_NUM_SYNC_FF,
            C_RESET_VALUE       => C_RESET_VALUE,
            C_RESET_SYNCHRONOUS => true,
            C_RESET_ACTIVE_HIGH => true)
          port map(
            Clk            => Clk,
            Rst            => reset_std,
            Scan_En        => '0',
            Scan_Reset_Sel => '0',
            Scan_Reset     => '0',
            Raw            => INTR(I),
            Synced         => synced_intr);
          
        end generate Async_Gen;

        Sync_Gen: if C_INTC_ASYNC_INTR(I) = '0' generate
        begin
          synced_intr <= INTR(i);
        end generate Sync_Gen;

        Clean_TMR_No : if (C_TMR = 0) generate
        begin

          Clean_Signal : process (Clk) is
          begin  -- process Clean_Signal
            if Clk'event and Clk = '1' then  -- rising clock edge
              if Reset then                  -- synchronous reset (active high)
                interrupt(I) <= not C_INTC_POSITIVE(I);
              else
                interrupt(I) <= synced_intr;
              end if;
            end if;
          end process Clean_Signal;

          ToVote(IRQ_INTERRUPT_Pos'low + I) <= '0';

        end generate Clean_TMR_No;

        Clean_TMR_Yes : if (C_TMR /= 0) generate
          signal interrupt_d : std_logic;
        begin

          Clean_Signal : process (Reset,synced_intr) is
          begin
            if Reset then
              interrupt_d <= not C_INTC_POSITIVE(I);
            else
              interrupt_d <= synced_intr;
            end if;
          end process Clean_Signal;

          ToVote(IRQ_INTERRUPT_Pos'low + I) <= interrupt_d;

          Clean_Signal_DFF : process (Clk) is
          begin
            if Clk'event and Clk = '1' then
              interrupt(I) <= vote(interrupt_d,
                                   FromAVote(IRQ_INTERRUPT_Pos'low+I),
                                   FromBVote(IRQ_INTERRUPT_Pos'low+I), tmr_disable_b);
            end if;
          end process Clean_Signal_DFF;

        end generate Clean_TMR_Yes;

        -- Detect External Interrupt
        Level : if (C_INTC_LEVEL_EDGE(I) = '0') generate
        begin
          intr_present(I) <= interrupt(I) xnor C_INTC_POSITIVE(I);
        end generate Level;

        Edge_TMR_No : if (C_TMR = 0) generate
        begin

          Edge : if (C_INTC_LEVEL_EDGE(I) = '1') generate
          begin
            Reg_INTR : process (Clk) is
              variable s1 : std_logic;
            begin  -- process Reg_INTR
              if Clk'event and Clk = '1' then  -- rising clock edge
                if Reset then                  -- synchronous reset (active high)
                  intr_present(I) <= '0';
                  s1              := not C_INTC_POSITIVE(I);
                else
                  intr_present(I) <= '0';
                  if (C_INTC_POSITIVE(I) = '0') and (s1 = '1') and (interrupt(I) = '0') then
                    intr_present(I) <= '1';
                  end if;
                  if (C_INTC_POSITIVE(I) = '1') and (s1 = '0') and (interrupt(I) = '1') then
                    intr_present(I) <= '1';
                  end if;
                  s1 := interrupt(I);
                end if;
              end if;
            end process Reg_INTR;
          end generate Edge;

          ToVote(IRQ_INTR_PRESENT_Pos'low + I) <= '0';

        end generate Edge_TMR_No;

        Edge_TMR_Yes : if (C_TMR /= 0) generate
        begin

          Edge : if (C_INTC_LEVEL_EDGE(I) = '1') generate
            signal intr_present_d : std_logic;
            signal s1   : std_logic;
          begin

            Reg_INTR_Logic : process (Reset, s1, interrupt) is
            begin
              if Reset then
                intr_present_d <= '0';
              else
                if ((C_INTC_POSITIVE(I) = '0') and (s1 = '1') and (interrupt(I) = '0')) or
                   ((C_INTC_POSITIVE(I) = '1') and (s1 = '0') and (interrupt(I) = '1')) then
                  intr_present_d <= '1';
                else
                  intr_present_d <= '0';
                end if;
              end if;
            end process Reg_INTR_Logic;

            ToVote(IRQ_INTR_PRESENT_Pos'low + I) <= intr_present_d;

            Reg_INTR_DFF : process (Clk) is
            begin  -- process Reg_INTR
              if Clk'event and Clk = '1' then  -- rising clock edge
                if (Reset) then
                  s1 <= not C_INTC_POSITIVE(I);
                else
                  s1 <= interrupt(I);   -- no need to vote s1 as it follows interrupt which is voted
                end if;
                intr_present(I) <= vote(intr_present_d,
                                        FromAVote(IRQ_INTR_PRESENT_Pos'low+I),
                                        FromBVote(IRQ_INTR_PRESENT_Pos'low+I), tmr_disable_b);
              end if;
            end process Reg_INTR_DFF;

          end generate Edge;

          Level : if (C_INTC_LEVEL_EDGE(I) = '0') generate
          begin
            ToVote(IRQ_INTR_PRESENT_Pos'low + I) <= '0';
          end generate Level;

        end generate Edge_TMR_Yes;

      end generate Ext_Intr;

      Internal_Intr : if (I < 16) generate
      begin
        -- Internal source is always one-clock long and active high, no need to detect an edge
        intr_present(I)                       <= INTR(I);
        interrupt(I)                          <= '0'; -- Unused
        ToVote(IRQ_INTR_PRESENT_Pos'low + I)  <= '0'; -- no need to vote as it follows INTR
        ToVote(IRQ_INTERRUPT_Pos'low + I)     <= '0'; -- no need to vote as it is not used
      end generate Internal_Intr;

      CISR_CIER_TMR_No : if (C_TMR = 0) generate
      begin

        CISR_Reg : process (Clk) is
        begin  -- process CISR_Reg
          if Clk'event and Clk = '1' then  -- rising clock edge
            if Reset then                  -- synchronous reset (active high)
              cisr(I) <= '0';
            else
              if (intr_present(I) = '1') then
                cisr(I) <= '1';
              elsif (INTC_WRITE_CIAR = '1' and Write_Data(I) = '1') or (fast_ack(I) = '1') then
                cisr(I) <= '0';
              end if;
            end if;
          end if;
        end process CISR_Reg;

        CIER_Reg : process (Clk) is
        begin  -- process CIER_Reg
          if Clk'event and Clk = '1' then  -- rising clock edge
            if Reset then                  -- synchronous reset (active high)
              cier(I) <= '0';
            elsif (INTC_WRITE_CIER = '1') then
              cier(I) <= Write_Data(I);
            end if;
          end if;
        end process CIER_Reg;

        ToVote(IRQ_CISR_Pos'low + I) <= '0';
        ToVote(IRQ_CIER_Pos'low + I) <= '0';

      end generate CISR_CIER_TMR_No;

      CISR_CIER_TMR_Yes : if (C_TMR /= 0) generate
        signal cisr_d : std_logic;
        signal cier_d : std_logic;
      begin

        CISR_Logic : process (Reset, intr_present, INTC_WRITE_CIAR, Write_Data, fast_ack, cisr) is
        begin
          if Reset then
            cisr_d <= '0';
          else
            if (intr_present(I) = '1') then
              cisr_d <= '1';
            elsif (INTC_WRITE_CIAR = '1' and Write_Data(I) = '1') or (fast_ack(I) = '1') then
              cisr_d <= '0';
            else
              cisr_d <= cisr(I);
            end if;
          end if;
        end process CISR_Logic;

        ToVote(IRQ_CISR_Pos'low + I) <= cisr_d;

        CISR_DFF : process (Clk) is
        begin  -- process CISR_Reg
          if Clk'event and Clk = '1' then  -- rising clock edge
            cisr(I) <= vote(cisr_d, FromAVote(IRQ_CISR_Pos'low + I), FromBVote(IRQ_CISR_Pos'low + I), tmr_disable_b);
          end if;
        end process CISR_DFF;

        CIER_Reg : process (Reset, INTC_WRITE_CIER, Write_Data, cier) is
        begin
          if Reset then
            cier_d <= '0';
          elsif (INTC_WRITE_CIER = '1') then
            cier_d <= Write_Data(I);
          else
            cier_d <= cier(I);
          end if;
        end process CIER_Reg;

        ToVote(IRQ_CIER_Pos'low + I) <= cier_d;

        CIER_DFF : process (Clk) is
        begin  -- process CIER_Reg
          if Clk'event and Clk = '1' then  -- rising clock edge
            cier(I) <= vote(cier_d, FromAVote(IRQ_CIER_Pos'low + I), FromBVote(IRQ_CIER_Pos'low + I), tmr_disable_b);
          end if;
        end process CIER_DFF;

      end generate CISR_CIER_TMR_Yes;

      cipr(I) <= cisr(I) and cier(I);

    end generate Using_Intr;

    Not_Using_Intr : if (C_INTC_ENABLED(I) = '0') generate
    begin
      interrupt(I)                         <= '0';
      intr_present(I)                      <= '0';
      cier(I)                              <= '0';
      cisr(I)                              <= '0';
      cipr(I)                              <= '0';
      ToVote(IRQ_INTERRUPT_Pos'low    + I) <= '0';
      ToVote(IRQ_INTR_PRESENT_Pos'low + I) <= '0';
      ToVote(IRQ_CISR_Pos'low         + I) <= '0';
      ToVote(IRQ_CIER_Pos'low         + I) <= '0';
    end generate Not_Using_Intr;

    Using_CIMR : if (C_INTC_ENABLED(I) = '1') and (C_INTC_HAS_FAST = 1) generate
    begin

      CIMR_TMR_No : if (C_TMR = 0) generate
      begin

        CIMR_Reg : process (Clk) is
        begin  -- process CIMR_Reg
          if Clk'event and Clk = '1' then  -- rising clock edge
            if Reset then                  -- synchronous reset (active high)
              cimr(I) <= '0';
            elsif (INTC_WRITE_CIMR = '1') then
              cimr(I) <= Write_Data(I);
            end if;
          end if;
        end process CIMR_Reg;

        ToVote(IRQ_CIMR_Pos'low + I) <= '0';

      end generate CIMR_TMR_No;

      CIMR_TMR_Yes: if (C_TMR /= 0) generate
        signal cimr_d : std_logic;
      begin

        CIMR_Logic : process (Reset, cimr, INTC_WRITE_CIMR, Write_Data) is
        begin
          if Reset then
            cimr_d <= '0';
          elsif (INTC_WRITE_CIMR = '1') then
            cimr_d <= Write_Data(I);
          else
            cimr_d <= cimr(I);
          end if;
        end process CIMR_Logic;

        ToVote(IRQ_CIMR_Pos'low + I) <= cimr_d;

        CIMR_DFF : process (Clk) is
        begin  -- process CIMR_Reg
          if Clk'event and Clk = '1' then  -- rising clock edge
            cimr(I) <= vote(cimr_d, FromAVote(IRQ_CIMR_Pos'low + I), FromBVote(IRQ_CIMR_Pos'low + I), tmr_disable_b);
          end if;
        end process CIMR_DFF;

      end generate CIMR_TMR_Yes;

    end generate Using_CIMR;

    Not_Using_CIMR : if (C_INTC_ENABLED(I) = '0') or (C_INTC_HAS_FAST = 0) generate
    begin
      cimr(I) <= '0';
      ToVote(IRQ_CIMR_Pos'low + I) <= '0';
    end generate Not_Using_CIMR;

  end generate All_INTR_Bits;

  Using_Fast : if C_INTC_HAS_FAST = 1 and not C_ENABLED_NONE generate
    subtype byte_res_vec is std_logic_vector(2 downto 0);
    type byte_res_array is array (3 downto 0) of byte_res_vec;

    subtype mux_res_vec is std_logic_vector(4 downto 0);
    type mux_res_array is array (4 downto 0) of mux_res_vec;

    type civar_type is array (C_CIVAR_SIZE - 1 downto 0) of std_logic_vector(C_INTC_ADDR_WIDTH - 3 downto 0);

    constant Idle         : std_logic_vector(1 downto 0) := "00";
    constant Interrupting : std_logic_vector(1 downto 0) := "01";
    constant Handling     : std_logic_vector(1 downto 0) := "10";
    constant Acknowledge  : std_logic_vector(1 downto 0) := "11";

    signal byte_zeros       : std_logic_vector(3 downto 0);
    signal byte_res         : byte_res_array;
    signal mux_res          : mux_res_array;
    signal fast_state       : std_logic_vector(1 downto 0);
    signal do_fast_ack      : std_logic;
    signal civar            : civar_type := (others => C_DEFAULT_ADDR(C_INTC_ADDR_WIDTH - 1 downto 2));
    signal civar_read_addr  : std_logic_vector(C_CIVAR_WIDTH - 1 downto 0);
    signal civar_write_addr : std_logic_vector(C_CIVAR_WIDTH - 1 downto 0);
    signal intr_addr_i      : std_logic_vector(C_INTC_ADDR_WIDTH - 3 downto 0);
    signal early_ack        : std_logic;
    signal has_fast         : std_logic;

    attribute ram_style            : string;
    attribute ram_style of civar   : signal is "distributed";
    attribute ram_extract          : string;
    attribute ram_extract of civar : signal is C_USE_LUTRAM;

  begin

    -- Calculate first bit set to get highest priority interrupt number (civr)
    Calc_Byte_Res: for I in 0 to 3 generate
    begin
      byte_zeros(I)  <= '1' when cipr(8*I+7 downto 8*I) = "00000000" else '0';

      byte_res(I)(2) <= '1' when cipr(8*I+3 downto 8*I) = "0000" else '0';

      byte_res(I)(1) <= '0' when cipr(8*I+0) = '1' or cipr(8*I+1) = '1' else
                        '1' when cipr(8*I+2) = '1' or cipr(8*I+3) = '1' else
                        '0' when cipr(8*I+4) = '1' or cipr(8*I+5) = '1' else
                        '1';

      byte_res(I)(0) <= '0' when cipr(8*I+0)= '1' else
                        '1' when cipr(8*I+1)= '1' else
                        '0' when cipr(8*I+2)= '1' else
                        '1' when cipr(8*I+3)= '1' else
                        '0' when cipr(8*I+4)= '1' else
                        '1' when cipr(8*I+5)= '1' else
                        '0' when cipr(8*I+6)= '1' else
                        '1';
    end generate Calc_Byte_Res;

    mux_res(4) <= "00000";
    Mux_the_Results: for I in natural range 3 downto 0 generate
    begin
      mux_res(I) <= mux_res(I+1) when byte_zeros(I) = '1' else
                    std_logic_vector(to_unsigned(I,2)) & byte_res(I);
    end generate Mux_the_Results;

    Fast_FSM_TMR_No : if (C_TMR = 0) generate
    begin

      -- Handle interrupt occurrence and acknowledge
      Fast_FSM : process(Clk)
      begin
        if Clk'event and Clk = '1' then
          if Reset then                   -- synchronous reset (active high)
            fast_state  <= Idle;
            INTC_IRQ    <= '0';
            civr        <= (others => '0');
            do_fast_ack <= '0';
          else
            case fast_state is
              when Idle =>                -- wait for interrupt
                if byte_zeros /= "1111" then
                  fast_state <= Interrupting;
                end if;
                INTC_IRQ    <= '0';
                civr        <= mux_res(0);
                do_fast_ack <= '0';
              when Interrupting =>        -- wait for first ack
                if INTR_ACK = "01" then
                  fast_state  <= Handling;
                  INTC_IRQ    <= '0';
                  do_fast_ack <= early_ack and has_fast;
                else
                  INTC_IRQ    <= '1';
                  do_fast_ack <= '0';
                end if;
              when Handling =>            -- wait for second ack
                if INTR_ACK(1) = '1' then
                  fast_state  <= Acknowledge;
                  do_fast_ack <= not early_ack and has_fast;
                else
                  do_fast_ack <= '0';
                end if;
                INTC_IRQ <= '0';
              when Acknowledge =>         -- wait until acknowledged in cisr
                fast_state  <= Idle;
                do_fast_ack <= '0';
                INTC_IRQ    <= '0';
              when others =>
                null;
            end case;
          end if;
        end if;
      end process Fast_FSM;

      ToVote(IRQ_FAST_STATE_Pos)  <= (others => '0');
      ToVote(IRQ_INTC_IRQ_Pos)    <= '0';
      ToVote(IRQ_CIVR_Pos)        <= (others => '0');
      ToVote(IRQ_DO_FAST_ACK_Pos) <= '0';

    end generate Fast_FSM_TMR_No;

    Fast_FSM_TMR_Yes : if (C_TMR /= 0) generate
      signal fast_state_d  : std_logic_vector(1 downto 0);
      signal INTC_IRQ_d    : std_logic;
      signal civr_d        : std_logic_vector(4 downto 0);
      signal do_fast_ack_d : std_logic;
    begin
      -- Handle interrupt occurrence and acknowledge
      Fast_FSM_Logic : process(Reset, fast_state, civr, do_fast_ack,
                               byte_zeros, mux_res, early_ack, has_fast, INTR_ACK)
      begin
        if Reset then
          fast_state_d  <= Idle;
          INTC_IRQ_d    <= '0';
          civr_d        <= (others => '0');
          do_fast_ack_d <= '0';
        else
          case fast_state is
            when Idle =>                -- wait for interrupt
              if byte_zeros /= "1111" then
                fast_state_d <= Interrupting;
              else
                fast_state_d <= fast_state;
              end if;
              INTC_IRQ_d    <= '0';
              civr_d        <= mux_res(0);
              do_fast_ack_d <= '0';
            when Interrupting =>        -- wait for first ack
              if INTR_ACK = "01" then
                fast_state_d  <= Handling;
                INTC_IRQ_d    <= '0';
                do_fast_ack_d <= early_ack and has_fast;
              else
                fast_state_d  <= fast_state;
                INTC_IRQ_d    <= '1';
                do_fast_ack_d <= '0';
              end if;
              civr_d        <= civr;
            when Handling =>            -- wait for second ack
              if INTR_ACK(1) = '1' then
                fast_state_d  <= Acknowledge;
                do_fast_ack_d <= not early_ack and has_fast;
              else
                fast_state_d  <= fast_state;
                do_fast_ack_d <= '0';
              end if;
              civr_d     <= civr;
              INTC_IRQ_d <= '0';
            when Acknowledge =>         -- wait until acknowledged in cisr
              fast_state_d  <= Idle;
              do_fast_ack_d <= '0';
              INTC_IRQ_d    <= '0';
              civr_d        <= civr;
            when others =>
              null;
            end case;
        end if;
      end process Fast_FSM_Logic;

      ToVote(IRQ_FAST_STATE_Pos)  <= fast_state_d;
      ToVote(IRQ_INTC_IRQ_Pos)    <= INTC_IRQ_d;
      ToVote(IRQ_CIVR_Pos)        <= civr_d;
      ToVote(IRQ_DO_FAST_ACK_Pos) <= do_fast_ack_d;

      Fast_FSM_DFF : process(Clk)
      begin
        if Clk'event and Clk = '1' then
          fast_state  <= vote(fast_state_d,
                              FromAVote(IRQ_FAST_STATE_Pos),
                              FromBVote(IRQ_FAST_STATE_Pos), tmr_disable_b);
          INTC_IRQ    <= vote(INTC_IRQ_d,
                              FromAVote(IRQ_INTC_IRQ_Pos),
                              FromBVote(IRQ_INTC_IRQ_Pos), tmr_disable_b);
          civr        <= vote(civr_d,
                              FromAVote(IRQ_CIVR_Pos),
                              FromBVote(IRQ_CIVR_Pos), tmr_disable_b);
          do_fast_ack <= vote(do_fast_ack_d,
                              FromAVote(IRQ_DO_FAST_ACK_Pos),
                              FromBVote(IRQ_DO_FAST_ACK_Pos), tmr_disable_b);
        end if;
      end process Fast_FSM_DFF;

    end generate Fast_FSM_TMR_Yes;

    Fast_Ack_Assign : process(civr, do_fast_ack)
    begin
      fast_ack <= (others => '0');
      fast_ack(to_integer(unsigned(civr))) <= do_fast_ack;
    end process Fast_Ack_Assign;

    early_ack <= C_INTC_LEVEL_EDGE(to_integer(unsigned(civr)));
    has_fast  <= cimr(to_integer(unsigned(civr)));

    -- Vector address registers implemented as a LUTRAM
    civar_write_addr <= INTC_CIVAR_ADDR(C_CIVAR_WIDTH - 1 downto 0);
    civar_read_addr  <= civr(C_CIVAR_WIDTH - 1 downto 0);

    Using_EA: if C_INTC_ADDR_WIDTH > 32 generate
      signal write_data_hi : std_logic_vector(C_INTC_ADDR_WIDTH - 1 downto 32);
      signal write_data_lo : std_logic_vector(31 downto 2);
    begin
      write_data_hi  <= Write_Data(C_INTC_ADDR_WIDTH - 33 downto 0);
      write_data_lo  <= Write_Data(31 downto 2);

      Using_LUTRAM: if USE_LUTRAM generate
      begin

        civar_reg : process(Clk)
        begin
          if Clk'event and Clk = '1' then
            if (INTC_WRITE_CIVAR = '1') then
              civar(to_integer(unsigned(civar_write_addr)))(29 downto 0) <= write_data_lo;
            end if;
            if (INTC_WRITE_CIVEAR = '1') then
              civar(to_integer(unsigned(civar_write_addr)))(C_INTC_ADDR_WIDTH - 3 downto 30) <= write_data_hi;
            end if;
            intr_addr_i <= civar(to_integer(unsigned(civar_read_addr)));
          end if;
        end process civar_reg;

      end generate Using_LUTRAM;

      Not_Using_LUTRAM: if not USE_LUTRAM generate
      begin

        civar_reg : process(Clk)
        begin
          if Clk'event and Clk = '1' then
            if (Reset) then
              civar       <= (others => C_DEFAULT_ADDR(C_INTC_ADDR_WIDTH - 1 downto 2));
              intr_addr_i <= (others => '0');
            else
              if (INTC_WRITE_CIVAR = '1') then
                civar(to_integer(unsigned(civar_write_addr)))(29 downto 0) <= write_data_lo;
              end if;
              if (INTC_WRITE_CIVEAR = '1') then
                civar(to_integer(unsigned(civar_write_addr)))(C_INTC_ADDR_WIDTH - 3 downto 30) <= write_data_hi;
              end if;
              intr_addr_i <= civar(to_integer(unsigned(civar_read_addr)));
            end if;
          end if;
        end process civar_reg;

      end generate Not_Using_LUTRAM;
    end generate Using_EA;

    Not_Using_EA: if C_INTC_ADDR_WIDTH <= 32 generate
      signal write_data_i : std_logic_vector(C_INTC_ADDR_WIDTH - 3 downto 0);
    begin
      write_data_i <= Write_Data(C_INTC_ADDR_WIDTH - 1 downto 2);

      Using_LUTRAM: if USE_LUTRAM generate
      begin

        civar_reg : process(Clk)
        begin
          if Clk'event and Clk = '1' then
            if (INTC_WRITE_CIVAR = '1') then
              civar(to_integer(unsigned(civar_write_addr))) <= write_data_i;
              intr_addr_i <= civar(to_integer(unsigned(civar_read_addr)));
            else
              intr_addr_i <= civar(to_integer(unsigned(civar_read_addr)));
            end if;
          end if;
        end process civar_reg;

      end generate Using_LUTRAM;

      Not_Using_LUTRAM: if not USE_LUTRAM generate
      begin

        civar_reg : process(Clk)
        begin
          if Clk'event and Clk = '1' then
            if (Reset) then
              civar       <= (others => C_DEFAULT_ADDR(C_INTC_ADDR_WIDTH - 1 downto 2));
              intr_addr_i <= (others => '0');
            elsif (INTC_WRITE_CIVAR = '1') then
              civar(to_integer(unsigned(civar_write_addr))) <= write_data_i;
              intr_addr_i <= civar(to_integer(unsigned(civar_read_addr)));
            else
              intr_addr_i <= civar(to_integer(unsigned(civar_read_addr)));
            end if;
          end if;
        end process civar_reg;

      end generate Not_Using_LUTRAM;
    end generate Not_Using_EA;

    INTR_ADDR_Assign : process(intr_addr_i)
    begin
      INTR_ADDR <= C_DEFAULT_ADDR;
      INTR_ADDR(C_INTC_ADDR_WIDTH - 1 downto 2) <= intr_addr_i(C_INTC_ADDR_WIDTH - 3 downto 0);
    end process INTR_ADDR_Assign;

  end generate Using_Fast;

  Not_Using_Fast : if C_INTC_HAS_FAST = 0 or C_ENABLED_NONE generate
  begin
    civr                        <= (others => '0');
    fast_ack                    <= (others => '0');
    INTR_ADDR                   <= C_DEFAULT_ADDR;
    INTC_IRQ                    <= '1' when cipr /= X"00000000" else '0';
    ToVote(IRQ_FAST_STATE_Pos)  <= (others => '0');
    ToVote(IRQ_INTC_IRQ_Pos)    <= '0';
    ToVote(IRQ_CIVR_Pos)        <= (others => '0');
    ToVote(IRQ_DO_FAST_ACK_Pos) <= '0';
  end generate Not_Using_Fast;

  cisr_rd_dff : process (Clk) is
  begin  -- process cisr_rd_dff
    if Clk'event and Clk = '1' then   -- rising clock edge
      if (INTC_READ_CISR = '0' or Reset) then  -- synchronous reset (active high)
        INTC_CISR <= (others => '0');
      else
        INTC_CISR <= cisr;
      end if;
    end if;
  end process cisr_rd_dff;

  rst_cipr_rd <= not(INTC_READ_CIPR);

  ToVote(IRQ_RST_CIPR_RD_Pos) <= rst_cipr_rd;

  rst_cipr_rd_voted <= vote(rst_cipr_rd,
                            FromAVote(IRQ_RST_CIPR_RD_Pos),
                            FromBVote(IRQ_RST_CIPR_RD_Pos), tmr_disable_b, C_TMR);

  cipr_rd_dff_all : for I in 0 to 31 generate
  begin
    fdr_i : MB_FDR
      generic map (
        C_TARGET => C_TARGET)
      port map (
        Q => INTC_CIPR(I),
        C => Clk,
        D => cipr(I),
        R => rst_cipr_rd_voted);
  end generate cipr_rd_dff_all;

end architecture IMP;


-------------------------------------------------------------------------------
-- pit_module.vhd - Entity and architecture
-------------------------------------------------------------------------------
--
-- (c) Copyright 2011,2016-2017 Xilinx, Inc. All rights reserved.
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
-- Filename:        pit_module.vhd
--
-- Description:
--
-- VHDL-Standard:   VHDL'93/02
-------------------------------------------------------------------------------
-- Structure:
--              pit_module.vhd
--
-------------------------------------------------------------------------------
-- Author:          goran
--
-- History:
--   goran  2007-12-19    First Version
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
library iomodule_v3_1_6;
use iomodule_v3_1_6.iomodule_funcs.all;

entity PIT_Module is
  generic (
    C_TARGET          : TARGET_FAMILY_TYPE;
    C_TMR             : integer := 0;
    C_USE_TMR_DISABLE : integer := 0;
    C_VOTE_SIZE       : integer := 0;
    C_USE_PIT         : integer := 0;
    C_PIT_SIZE        : integer := 16;
    C_PIT_READABLE    : integer := 1
    );
  port (
    Clk               : in  std_logic;
    Reset             : in  boolean;
    Config_Reset      : in  std_logic;
    TMR_Disable       : in std_logic;
    FromAVote         : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
    FromBVote         : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
    ToVote            : out std_logic_vector(C_VOTE_SIZE-1 downto 0);
    PIT_Count_En      : in  std_logic;
    PIT_Write_Preload : in  std_logic;
    PIT_Write_Ctrl    : in  std_logic;
    PIT_Read          : in  std_logic;
    Write_Data        : in  std_logic_vector(31 downto 0);
    PIT_Data          : out std_logic_vector(C_PIT_SIZE-1 downto 0);
    PIT_Toggle        : out std_logic;
    PIT_Interrupt     : out std_logic);
end entity PIT_Module;

library iomodule_v3_1_6;
use iomodule_v3_1_6.iomodule_vote_pkg.all;

architecture IMP of PIT_Module is

  component MB_MUXCY_XORCY is
    generic (
      C_TARGET : TARGET_FAMILY_TYPE);
    port (
      O  : out std_logic;
      LO : out std_logic;
      CI : in  std_logic;
      DI : in  std_logic;
      S  : in  std_logic);
  end component MB_MUXCY_XORCY;

  component MB_LUT3 is
    generic (
      C_TARGET : TARGET_FAMILY_TYPE;
      INIT     : bit_vector := X"00");
    port (
      O  : out std_logic;
      I0 : in  std_logic;
      I1 : in  std_logic;
      I2 : in  std_logic);
  end component MB_LUT3;

  component MB_MULT_AND is
    generic (
      C_TARGET : TARGET_FAMILY_TYPE;
      INIT : bit := '0');
    port(
      LO : out std_logic;
      I0 : in  std_logic;
      I1 : in  std_logic);
  end component MB_MULT_AND;

begin  -- architecture IMP

  Using_PIT : if (C_USE_PIT /= 0) generate
    signal preload_value   : std_logic_vector(C_PIT_SIZE-1 downto 0);
    signal preload_written : std_logic;

    signal reload   : std_logic;
    signal count_en : std_logic;

    signal count_enabled : std_logic;

    -- Counter signals
    signal count_load_n    : std_logic;
    signal cnt             : std_logic_vector(C_PIT_SIZE-1 downto 0);
    signal carry           : std_logic_vector(C_PIT_SIZE   downto 0);
    signal count           : std_logic_vector(C_PIT_SIZE-1 downto 0);
    signal count_wrap      : std_logic;
    signal pit_interrupt_i : std_logic;
    signal pit_toggle_i    : std_logic;
  begin

    TMR_No : if (C_TMR = 0) generate
    begin
      --------------------------------------------------------------------------------------------------
      -- Preload register
      --------------------------------------------------------------------------------------------------
      PreLoad_Handler : process (Clk) is
      begin  -- process PreLoad_Handler
        if Clk'event and Clk = '1' then   -- rising clock edge
          if Reset then                   -- synchronous reset (active high)
            preload_value <= (others => '0');
          elsif (PIT_Write_Preload = '1') then
            preload_value <= Write_Data(C_PIT_SIZE-1 downto 0);
          end if;
        end if;
      end process PreLoad_Handler;

      --------------------------------------------------------------------------------------------------
      -- Control Register
      --------------------------------------------------------------------------------------------------
      Ctrl_Handler : process (Clk) is
      begin  -- process Ctrl_Handler
        if Clk'event and Clk = '1' then   -- rising clock edge
          if Reset then                   -- synchronous reset (active high)
            reload          <= '0';
            count_en        <= '0';
            count_load_n    <= '1';
            preload_written <= '0';
          else
            preload_written <= PIT_Write_Preload;
            if (PIT_Write_Ctrl = '1') then
              reload   <= Write_Data(1);
              count_en <= Write_Data(0);
            end if;
            if ((count_wrap = '1') and (reload = '0') and (count_enabled = '1') and (count_load_n = '1')) then
              count_en <= '0';
            end if;

            -- reach -1 and will load_counter with preload value
            if ((count_wrap = '1') and (reload = '1') and (count_enabled = '1')) then
              count_load_n <= '0';
            end if;

            -- if we have written to preload register, load counter with preload value next time we count
            if (preload_written = '1') then
              count_load_n <= '0';
            end if;

            -- Counter is now loaded so remove count_load_n
            if (count_load_n = '0') and (count_enabled = '1') then
              count_load_n <= '1';
            end if;

          end if;
        end if;
      end process Ctrl_Handler;

      count_enabled <= count_en and PIT_Count_En;

      Counter : process (Clk) is
      begin  -- process Counter
        if Clk'event and Clk = '1' then   -- rising clock edge
          if Reset then
            count <= (others => '0');
          elsif (count_enabled = '1') then
            count <= cnt;
          end if;
        end if;
      end process Counter;

      Interrupt_Handler : process (Clk) is
      begin  -- process Interrupt_Handler
        if Clk'event and Clk = '1' then   -- rising clock edge
          if Reset then                   -- synchronous reset (active high)
            pit_interrupt_i <= '0';
          else
            pit_interrupt_i <= count_wrap and count_enabled and count_load_n;
          end if;
        end if;
      end process Interrupt_Handler;

      Toggle_Handler : process (Clk) is
      begin
        if Clk'event and Clk = '1' then
          if Reset then
            pit_toggle_i <= '0';
          elsif pit_interrupt_i = '1' then
            pit_toggle_i <= not pit_toggle_i;
          end if;
        end if;
      end process Toggle_Handler;

      ToVote <= (others => '0');

    end generate TMR_No;

    --------------------------------------------------------------------------------------------------
    -- Counter
    --------------------------------------------------------------------------------------------------
    Using_FPGA: if (C_TARGET /= RTL) generate
      signal new_cnt    : std_logic_vector(C_PIT_SIZE-1 downto 0);
      signal new_cnt_di : std_logic_vector(C_PIT_SIZE-1 downto 0);
    begin
    
      carry(0) <= '0';

      All_Bits : for I in 0 to C_PIT_SIZE - 1 generate
      begin

        Count_LUT : MB_LUT3
          generic map(
            C_TARGET => C_TARGET,
            INIT => X"72"
            )
          port map (
            O  => new_cnt(I),             -- [out]
            I0 => count_load_n,           -- [in]
            I1 => count(I),               -- [in]
            I2 => preload_value(I));      -- [in]

        MULT_AND_I : MB_MULT_AND
          generic map(
            C_TARGET => C_TARGET)
          port map (
            I0 => count_load_n,           -- [in]
            I1 => count(I),               -- [in]
            LO => new_cnt_di(I));         -- [out]

        MUXCY_XORCY_L_I1 : MB_MUXCY_XORCY
          generic map(
            C_TARGET => C_TARGET)
          port map (
            DI => new_cnt_di(I),          -- [in  std_logic S = 0]
            CI => carry(I),               -- [in  std_logic S = 1]
            S  => new_cnt(I),             -- [in  std_logic (Select)]
            LO => carry(I+1),             -- [out std_logic]
            O  => cnt(I));                -- [out std_logic]

      end generate All_Bits;

      count_wrap <= not carry(C_PIT_SIZE);

    end generate Using_FPGA;

    Using_RTL : if (C_TARGET = RTL) generate
      signal count_extra : std_logic_vector(C_PIT_SIZE downto 0);
    begin
      count_extra <= '0' & count;
      carry       <= std_logic_vector(unsigned(count_extra) - 1);
      cnt         <= carry(C_PIT_SIZE-1 downto 0) when count_load_n = '1' else
                     preload_value;
      count_wrap  <= carry(C_PIT_SIZE);
    end generate Using_RTL;

    TMR_Yes : if (C_TMR /= 0) generate
      signal tmr_disable_b     : boolean;
      signal preload_value_d   : std_logic_vector(C_PIT_SIZE-1 downto 0);
      signal count_d           : std_logic_vector(C_PIT_SIZE-1 downto 0);
      signal reload_d          : std_logic;
      signal count_en_d        : std_logic;
      signal count_load_n_d    : std_logic;
      signal preload_written_d : std_logic;
      signal pit_interrupt_i_d : std_logic;
      signal pit_toggle_i_d    : std_logic;
    begin

      tmr_disable_b <= TMR_Disable = '1' and C_USE_TMR_DISABLE = 1;

      --------------------------------------------------------------------------------------------------
      -- Preload register
      -------------------------------------------------------------------------------------------------
      PreLoad_Handler_Logic : process (Reset, PIT_Write_Preload, Write_Data, preload_value) is
      begin
        if Reset then
          preload_value_d <= (others => '0');
        elsif (PIT_Write_Preload = '1') then
          preload_value_d <= Write_Data(C_PIT_SIZE-1 downto 0);
        else
          preload_value_d <= preload_value;
        end if;
      end process PreLoad_Handler_Logic;

      ToVote(PIT_PRELOAD_VALUE_Pos'low + C_PIT_SIZE - 1 downto PIT_PRELOAD_VALUE_Pos'low) <= preload_value_d;
      -- Work around spyglass bug report on null range to the left but not to the right
      spy1_g: if C_PIT_SIZE < 32 generate
      begin
        ToVote(PIT_PRELOAD_VALUE_Pos'high downto PIT_PRELOAD_VALUE_Pos'low + C_PIT_SIZE) <= (others => '0');
      end generate spy1_g;

      PreLoad_Handler_DFF : process (Clk) is
      begin
        if Clk'event and Clk = '1' then
          preload_value <= vote(preload_value_d,
                                FromAVote(PIT_PRELOAD_VALUE_Pos),
                                FromBVote(PIT_PRELOAD_VALUE_Pos), tmr_disable_b);
        end if;
      end process PreLoad_Handler_DFF;

      --------------------------------------------------------------------------------------------------
      -- Control Register
      --------------------------------------------------------------------------------------------------
      Ctrl_Handler_Logic : process (Reset, PIT_Write_Preload, PIT_Write_Ctrl, Write_Data, count_wrap,
                                    reload, count_en, count_enabled, count_load_n, preload_written) is
      begin
        if Reset then
          reload_d          <= '0';
          count_en_d        <= '0';
          count_load_n_d    <= '1';
          preload_written_d <= '0';
        else
          if (PIT_Write_Ctrl = '1') then
            reload_d <= Write_Data(1);
          else
            reload_d <= reload;
          end if;

          if ((count_wrap = '1') and (reload = '0') and (count_enabled = '1') and (count_load_n = '1')) then
            count_en_d <= '0';
          elsif (PIT_Write_Ctrl = '1') then
            count_en_d <= Write_Data(0);
          else
            count_en_d <= count_en;
          end if;

          -- Counter is now loaded so remove count_load_n
          if (count_load_n = '0') and (count_enabled = '1') then
            count_load_n_d <= '1';
          -- if we have written to preload register, load counter with preload value next time we count
          elsif (preload_written = '1') then
            count_load_n_d <= '0';
          -- reach -1 and will load_counter with preload value
          elsif ((count_wrap = '1') and (reload = '1') and (count_enabled = '1')) then
            count_load_n_d <= '0';
          else
            count_load_n_d <= count_load_n;
          end if;

          preload_written_d <= PIT_Write_Preload;

        end if;
      end process Ctrl_Handler_Logic;

      ToVote(PIT_RELOAD_Pos)          <= reload_d;
      ToVote(PIT_COUNT_EN_Pos)        <= count_en_d;
      ToVote(PIT_COUNT_LOAD_N_Pos)    <= count_load_n_d;
      ToVote(PIT_PRELOAD_WRITTEN_Pos) <= preload_written_d;

      Ctrl_Handler_DFF : process (Clk) is
      begin
        if Clk'event and Clk = '1' then
          reload          <= vote(reload_d,
                                  FromAVote(PIT_RELOAD_Pos),
                                  FromBVote(PIT_RELOAD_Pos), tmr_disable_b);
          count_en        <= vote(count_en_d,
                                  FromAVote(PIT_COUNT_EN_Pos),
                                  FromBVote(PIT_COUNT_EN_Pos), tmr_disable_b);
          count_load_n    <= vote(count_load_n_d,
                                  FromAVote(PIT_COUNT_LOAD_N_Pos),
                                  FromBVote(PIT_COUNT_LOAD_N_Pos), tmr_disable_b);
          preload_written <= vote(preload_written_d,
                                  FromAVote(PIT_PRELOAD_WRITTEN_Pos),
                                  FromBVote(PIT_PRELOAD_WRITTEN_Pos), tmr_disable_b);
        end if;
      end process Ctrl_Handler_DFF;

      count_enabled <= count_en and PIT_Count_En;

      Counter_Logic : process (Reset, count_enabled, count, cnt) is
      begin
        if Reset then
          count_d <= (others => '0');
        elsif (count_enabled = '1') then
          count_d <= cnt;
        else
          count_d <= count;
        end if;
      end process Counter_Logic;

      ToVote(PIT_COUNT_Pos'low + C_PIT_SIZE - 1 downto PIT_COUNT_Pos'low) <= count_d;
      -- Work around spyglass bug report on null range to the left but not to the right
      spy2_g: if C_PIT_SIZE < 32 generate
      begin
        ToVote(PIT_COUNT_Pos'high downto PIT_COUNT_Pos'low + C_PIT_SIZE)    <= (others => '0');
      end generate spy2_g;

      Counter_DFF : process (Clk) is
      begin
        if Clk'event and Clk = '1' then
          count <= vote(count_d, FromAVote(PIT_COUNT_Pos), FromBVote(PIT_COUNT_Pos),tmr_disable_b);
        end if;
      end process Counter_DFF;

      Interrupt_Handler_Logic : process (Reset, count_wrap, count_enabled, count_load_n) is
      begin
        if Reset then
          pit_interrupt_i_d <= '0';
        else
          pit_interrupt_i_d <= count_wrap and count_enabled and count_load_n;
        end if;
      end process Interrupt_Handler_Logic;

      ToVote(PIT_INTERRUPT_I_Pos) <= pit_interrupt_i_d;

      Interrupt_Handler_DFF : process (Clk) is
      begin
        if Clk'event and Clk = '1' then
          pit_interrupt_i <= vote(pit_interrupt_i_d,
                                  FromAVote(PIT_INTERRUPT_I_Pos),
                                  FromBVote(PIT_INTERRUPT_I_Pos), tmr_disable_b);
        end if;
      end process Interrupt_Handler_DFF;

      Toggle_Handler_Logic : process (Reset, pit_toggle_i, pit_interrupt_i) is
      begin
        if Reset then
          pit_toggle_i_d <= '0';
        elsif pit_interrupt_i = '1' then
          pit_toggle_i_d <= not pit_toggle_i;
        else
          pit_toggle_i_d <= pit_toggle_i;
        end if;
      end process Toggle_Handler_Logic;

      ToVote(PIT_TOGGLE_I_Pos) <= pit_toggle_i_d;

      Toggle_Handler_DFF : process (Clk) is
      begin
        if Clk'event and Clk = '1' then
          pit_toggle_i <= vote(pit_toggle_i_d,
                               FromAVote(PIT_TOGGLE_I_Pos),
                               FromBVote(PIT_TOGGLE_I_Pos), tmr_disable_b);
        end if;
      end process Toggle_Handler_DFF;

    end generate TMR_Yes;

    PIT_Interrupt <= pit_interrupt_i;
    PIT_Toggle <= pit_toggle_i;

    --------------------------------------------------------------------------------------------------
    -- Read register
    --------------------------------------------------------------------------------------------------
    Readable_Counter : if (C_PIT_READABLE /= 0) generate
    begin

      PIT_Read_Handler : process (Clk) is
      begin  -- process PIT_Read_Handler
        if Clk'event and Clk = '1' then  -- rising clock edge
          if PIT_Read = '0' or Config_Reset = '1' then
            PIT_Data <= (others => '0');
          else
            PIT_Data                        <= (others => '0');
            PIT_Data(C_PIT_SIZE-1 downto 0) <= count;
          end if;
        end if;
      end process PIT_Read_Handler;

    end generate Readable_Counter;

    Dont_Read_Counter: if (C_PIT_READABLE = 0) generate
    begin
      PIT_Data <= (others => '0');
    end generate Dont_Read_Counter;

  end generate Using_PIT;

  Not_Using_Pit : if (C_USE_PIT = 0) generate
  begin
    PIT_Data      <= (others => '0');
    PIT_Interrupt <= '0';
    PIT_Toggle    <= '0';
    ToVote        <= (others => '0');
  end generate Not_Using_Pit;

end architecture IMP;


-------------------------------------------------------------------------------
-- uart_control_status.vhd - Entity and architecture
-------------------------------------------------------------------------------
--
-- (c) Copyright 2011,2016 Xilinx, Inc. All rights reserved.
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
-- Filename:        uart_control_status.vhd
--
-- Description:
--
-- VHDL-Standard:   VHDL'93/02
-------------------------------------------------------------------------------
-- Structure:
--              uart_control_status.vhd
--
-------------------------------------------------------------------------------
-- Author:          goran
--
-- History:
--   goran  2007-12-18    First Version
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

library iomodule_v3_1_6;
use iomodule_v3_1_6.iomodule_vote_pkg.all;

entity Uart_Control_Status is
  generic (
    C_TMR             : integer              := 0;
    C_USE_TMR_DISABLE : integer              := 0;
    C_VOTE_SIZE       : integer              := 0;
    C_USE_UART_RX     : integer              := 1;
    C_USE_UART_TX     : integer              := 1;
    C_UART_DATA_BITS  : integer range 5 to 8 := 8;
    C_UART_USE_PARITY : integer              := 0;
    C_UART_ODD_PARITY : integer              := 0
    );
  port (
    CLK   : in std_logic;
    Reset : in boolean;
    Config_Reset        : in std_logic;

    TMR_Disable         : in std_logic;
    FromAVote           : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
    FromBVote           : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
    ToVote              : out std_logic_vector(C_VOTE_SIZE-1 downto 0);

    TX_Data_Transmitted : in std_logic;
    TX_Buffer_Empty     : in std_logic;
    RX_Data_Received    : in std_logic;
    RX_Data_Exists      : in std_logic;
    RX_Frame_Error      : in std_logic;
    RX_Overrun_Error    : in std_logic;
    RX_Parity_Error     : in std_logic;

    UART_Status_Read     : in  std_logic;
    UART_Status          : out std_logic_vector(7 downto 0);
    UART_Interrupt       : out std_logic;
    UART_Rx_Interrupt    : out std_logic;
    UART_Tx_Interrupt    : out std_logic;
    UART_Error_Interrupt : out std_logic
    );

end entity Uart_Control_Status;

architecture IMP of Uart_Control_Status is

  signal parity_error  : std_logic;
  signal frame_error   : std_logic;
  signal overrun_error : std_logic;

  signal error_interrupt : std_logic;

begin  -- architecture IMP

  --------------------------------------------------------------------------------------------------
  -- Status register
  --------------------------------------------------------------------------------------------------
  UART_Status_DFF: process (Clk) is
  begin  -- process UART_Status_DFF
    if Clk'event and Clk = '1' then     -- rising clock edge
      if (UART_Status_Read = '0' or Config_Reset = '1') then  -- synchronous reset (active high)
        UART_Status <= (others => '0');
      else
        if ((C_USE_UART_RX = 0) or (C_UART_USE_PARITY = 0)) then
          UART_Status(7) <= '0';
        else
          UART_Status(7) <= parity_error;
        end if;
        if (C_USE_UART_RX = 0) then
          UART_Status(6) <= '0';
          UART_Status(5) <= '0';
        else
          UART_Status(6) <= frame_error;
          UART_Status(5) <= overrun_error;
        end if;
        UART_Status(4) <= '0';
        if (C_USE_UART_TX = 0) then
          UART_Status(3) <= '0';
        else
          UART_Status(3) <= not TX_Buffer_Empty;
        end if;
        UART_Status(2) <= '0';
        UART_Status(1) <= '0';
        if (C_USE_UART_RX = 0) then
          UART_Status(0) <= '0';
        else
          UART_Status(0) <= RX_Data_Exists;
        end if;
      end if;
    end if;
  end process UART_Status_DFF;

  --------------------------------------------------------------------------------------------------
  -- Keep track of errors
  --------------------------------------------------------------------------------------------------

  TMR_No : if (C_TMR = 0) generate
  begin

    Error_Flags : process (Clk) is
    begin  -- process Error_Flags
      if Clk'event and Clk = '1' then     -- rising clock edge
        if Reset then                     -- synchronous reset (active high)
          parity_error    <= '0';
          frame_error     <= '0';
          overrun_error   <= '0';
          error_interrupt <= '0';
        else
          error_interrupt <= '0';
          if ((C_USE_UART_RX = 0) or (UART_Status_Read = '1')) then
            parity_error  <= '0';
            frame_error   <= '0';
            overrun_error <= '0';
          end if;
          if ((C_USE_UART_RX /= 0) and (RX_Frame_Error = '1')) then
            frame_error     <= '1';
            error_interrupt <= '1';
          end if;
          if ((C_USE_UART_RX /= 0) and (RX_Overrun_Error = '1')) then
            overrun_error   <= '1';
            error_interrupt <= '1';
          end if;
          if ((C_USE_UART_RX /= 0) and (C_UART_USE_PARITY /= 0) and (RX_Parity_Error = '1')) then
            parity_error    <= '1';
            error_interrupt <= '1';
          end if;
        end if;
      end if;
    end process Error_Flags;

    ToVote <= (others => '0');

  end generate TMR_No;

  TMR_Yes : if (C_TMR /= 0) generate
    signal tmr_disable_b     : boolean;
    signal parity_error_d    : std_logic;
    signal frame_error_d     : std_logic;
    signal overrun_error_d   : std_logic;
    signal error_interrupt_d : std_logic;
  begin

    tmr_disable_b <= TMR_Disable = '1' and C_USE_TMR_DISABLE = 1;

    Error_Flags_Logic : process (Reset, parity_error, UART_Status_Read, RX_Frame_Error, RX_Overrun_Error,
                                 RX_Parity_Error, frame_error, overrun_error) is
    begin
      if Reset then
        parity_error_d    <= '0';
        frame_error_d     <= '0';
        overrun_error_d   <= '0';
        error_interrupt_d <= '0';
      else
        if ((C_USE_UART_RX /= 0) and (RX_Frame_Error = '1')) or
           ((C_USE_UART_RX /= 0) and (RX_Overrun_Error = '1')) or
           ((C_USE_UART_RX /= 0) and (C_UART_USE_PARITY /= 0) and (RX_Parity_Error = '1')) then
          error_interrupt_d <= '1';
        else
          error_interrupt_d <= '0';
        end if;

        if ((C_USE_UART_RX /= 0) and (C_UART_USE_PARITY /= 0) and (RX_Parity_Error = '1')) then
          parity_error_d <= '1';
        elsif ((C_USE_UART_RX = 0) or (UART_Status_Read = '1')) then
          parity_error_d <= '0';
        else
          parity_error_d <= parity_error;
        end if;

        if ((C_USE_UART_RX /= 0) and (RX_Frame_Error = '1')) then
          frame_error_d <= '1';
        elsif ((C_USE_UART_RX = 0) or (UART_Status_Read = '1')) then
          frame_error_d <= '0';
        else
          frame_error_d <= frame_error;
        end if;

        if ((C_USE_UART_RX /= 0) and (RX_Overrun_Error = '1')) then
          overrun_error_d <= '1';
        elsif ((C_USE_UART_RX = 0) or (UART_Status_Read = '1')) then
          overrun_error_d <= '0';
        else
          overrun_error_d <= overrun_error;
        end if;

      end if;
    end process Error_Flags_Logic;

    ToVote(PARITY_ERROR_Pos)    <= parity_error_d;
    ToVote(FRAME_ERROR_Pos)     <= frame_error_d;
    ToVote(OVERRUN_ERROR_Pos)   <= overrun_error_d;
    ToVote(ERROR_INTERRUPT_Pos) <= error_interrupt_d;

    Error_Flags_DFF : process (Clk) is
    begin  -- process Error_Flags
      if Clk'event and Clk = '1' then     -- rising clock edge
        parity_error    <= vote(parity_error_d,
                                FromAVote(PARITY_ERROR_Pos),
                                FromBVote(PARITY_ERROR_Pos), tmr_disable_b);
        frame_error     <= vote(frame_error_d,
                                FromAVote(FRAME_ERROR_Pos),
                                FromBVote(FRAME_ERROR_Pos), tmr_disable_b);
        overrun_error   <= vote(overrun_error_d,
                                FromAVote(OVERRUN_ERROR_Pos),
                                FromBVote(OVERRUN_ERROR_Pos), tmr_disable_b);
        error_interrupt <= vote(error_interrupt_d,
                                FromAVote(ERROR_INTERRUPT_Pos),
                                FromBVote(ERROR_INTERRUPT_Pos), tmr_disable_b);
      end if;
    end process Error_Flags_DFF;

  end generate TMR_Yes;

  --------------------------------------------------------------------------------------------------
  -- Interrupt generation
  --------------------------------------------------------------------------------------------------
  UART_Error_Interrupt <= error_interrupt;
  UART_Rx_Interrupt    <= RX_Data_Received;
  UART_Tx_Interrupt    <= TX_Data_Transmitted;
  UART_Interrupt       <= error_interrupt or RX_Data_Received or TX_Data_Transmitted;
end architecture IMP;


-------------------------------------------------------------------------------
-- uart_receive.vhd - Entity and architecture
-------------------------------------------------------------------------------
--
-- (c) Copyright 2011,2016 Xilinx, Inc. All rights reserved.
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
-- Filename:        uart_receive.vhd
--
-- Description:
--
-- VHDL-Standard:   VHDL'93/02
-------------------------------------------------------------------------------
-- Structure:
--              uart_receive.vhd
--
-------------------------------------------------------------------------------
-- Author:          goran
--
-- History:
--   goran  2007-12-18    First Version
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
library iomodule_v3_1_6;
use iomodule_v3_1_6.iomodule_funcs.all;

entity UART_Receive is
  generic (
    C_TARGET          : TARGET_FAMILY_TYPE;
    C_TMR             : integer := 0;
    C_USE_TMR_DISABLE : integer := 0;
    C_VOTE_SIZE       : integer := 0;
    C_USE_SRL16       : string;
    C_DATA_BITS       : integer range 5 to 8 := 8;
    C_USE_PARITY      : integer              := 0;
    C_ODD_PARITY      : integer              := 1
    );
  port (
    Config_Reset : in std_logic;
    Clk          : in std_logic;
    Reset        : in boolean;
    EN_16x_Baud  : in std_logic;

    RX               : in  std_logic;
    Read_RX_Data     : in  std_logic;
    TMR_Disable      : in  std_logic;
    FromAVote        : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
    FromBVote        : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
    ToVote           : out std_logic_vector(C_VOTE_SIZE-1 downto 0);
    RX_Data          : out std_logic_vector(C_DATA_BITS-1 downto 0);
    RX_Data_Received : out std_logic;
    RX_Data_Exists   : out std_logic;
    RX_Frame_Error   : out std_logic;
    RX_Overrun_Error : out std_logic;
    RX_Parity_Error  : out std_logic
    );

end entity UART_Receive;

library iomodule_v3_1_6;
use iomodule_v3_1_6.iomodule_vote_pkg.all;

architecture IMP of UART_Receive is

  component XIL_SRL16E is
    generic (
      C_TARGET    : TARGET_FAMILY_TYPE;
      C_USE_SRL16 : string;
      C_STATIC    : boolean := false;
      INIT        : bit_vector);
    port (
      Config_Reset : in  std_logic;
      Q            : out std_logic;
      A0           : in  std_logic;
      A1           : in  std_logic;
      A2           : in  std_logic;
      A3           : in  std_logic;
      CE           : in  std_logic;
      CLK          : in  std_logic;
      D            : in  std_logic);
  end component XIL_SRL16E;

  component MB_FDSE is
  generic (
    C_TARGET : TARGET_FAMILY_TYPE;
    INIT : bit := '1');
  port(
    Q  : out std_logic;
    C  : in  std_logic;
    CE : in  std_logic;
    D  : in  std_logic;
    S  : in  std_logic);
  end component MB_FDSE;

  component MB_FDRE is
  generic (
    C_TARGET : TARGET_FAMILY_TYPE;
    INIT : bit := '0');
  port(
    Q  : out std_logic;
    C  : in  std_logic;
    CE : in  std_logic;
    D  : in  std_logic;
    R  : in  std_logic);
  end component MB_FDRE;

  signal previous_RX             : std_logic;
  signal start_Edge_Detected_Bit : std_logic;
  signal mid_Start_Bit           : std_logic;
  signal recycle                 : std_logic;
  signal sample_Point            : std_logic;
  signal stop_Bit_Position       : std_logic;

  function Calc_Length return integer is
  begin  -- function Calc_Length
    if (C_USE_PARITY = 1) then
      return 1 + C_DATA_BITS;
    else
      return C_DATA_BITS;
    end if;
  end function Calc_Length;

  constant SERIAL_TO_PAR_LENGTH : integer := Calc_Length;
  constant STOP_BIT_POS         : integer := SERIAL_TO_PAR_LENGTH;
  constant DATA_LSB_POS         : integer := SERIAL_TO_PAR_LENGTH;
  constant CALC_PAR_POS         : integer := SERIAL_TO_PAR_LENGTH;

  signal new_rx_data_write  : std_logic;
  signal new_rx_data        : std_logic_vector(0 to SERIAL_TO_PAR_LENGTH);
  signal serial_to_parallel : std_logic_vector(1 to SERIAL_TO_PAR_LENGTH);
  signal rx_data_exists_i   : std_logic;
  signal rx_frame_error_i   : std_logic;
  signal rx_parity_error_i  : std_logic;

  signal rx_1 : std_logic;
  signal rx_2 : std_logic;

  signal rx_data_i : std_logic_vector(C_DATA_BITS-1 downto 0);

  -- Preserve signals after synthesis for simulation UART support
  attribute KEEP : string;
  attribute KEEP of rx_frame_error_i  : signal is "TRUE";
  attribute KEEP of rx_parity_error_i : signal is "TRUE";
  attribute KEEP of new_rx_data_write : signal is "TRUE";
  attribute KEEP of new_rx_data       : signal is "TRUE";

begin  -- architecture IMP

  TMR_No : if (C_TMR = 0) generate
    signal start_Edge_Detected : boolean;
    signal running             : boolean;
    signal mid_Start_Bit_or_Config_Reset : std_logic;
  begin

    ToVote <= (others => '0');

    -----------------------------------------------------------------------------
    -- Double sample to avoid meta-stability
    -----------------------------------------------------------------------------
    RX_Sampling : process (Clk)
    begin  -- process RX_Sampling
      if Clk'event and Clk = '1' then     -- rising clock edge
        if Reset then                     -- asynchronous reset (active high)
          rx_1 <= '1';
          rx_2 <= '1';
        else
          rx_1 <= RX;
          rx_2 <= rx_1;
        end if;
      end if;
    end process RX_Sampling;

    -----------------------------------------------------------------------------
    -- Detect a falling edge on RX and start a new receiption if idle
    -----------------------------------------------------------------------------
    Prev_RX_DFF : process (Clk) is
    begin  -- process Prev_RX_DFF
      if Clk'event and Clk = '1' then     -- rising clock edge
        if Reset then
          previous_RX <= '0';
        else
          if (EN_16x_Baud = '1') then
            previous_RX <= rx_2;
          end if;
        end if;
      end if;
    end process Prev_RX_DFF;

    Start_Edge_DFF : process (Clk) is
    begin  -- process Start_Edge_DFF
      if Clk'event and Clk = '1' then     -- rising clock edge
        if Reset then
          start_Edge_Detected <= false;
        else
          if (EN_16x_Baud = '1') then
            start_Edge_Detected <= not running and (previous_RX = '1') and (rx_2 = '0');
          end if;
        end if;
      end if;
    end process Start_Edge_DFF;

    -----------------------------------------------------------------------------
    -- Running is '1' during a receiption
    -----------------------------------------------------------------------------
    Running_DFF : process (Clk) is
    begin  -- process Running_DFF
      if Clk'event and Clk = '1' then     -- rising clock edge
        if Reset then                     -- asynchronous reset (active high)
          running <= false;
        else
          if (EN_16x_Baud = '1') then
            if (start_Edge_Detected) then
              running <= true;
            elsif ((sample_Point = '1') and (stop_Bit_Position = '1')) then
              running <= false;
            end if;
          end if;
        end if;
      end if;
    end process Running_DFF;

    -----------------------------------------------------------------------------
    -- Delay start_Edge_Detected 7 clocks to get the mid-point in a bit
    -- The address needs to be 6 "0110" to get a delay of 7.
    -----------------------------------------------------------------------------

    start_Edge_Detected_Bit <= '1' when start_Edge_Detected else '0';

    Mid_Start_Bit_SRL16 : XIL_SRL16E
      generic map (
        C_TARGET    => C_TARGET,
        C_USE_SRL16 => C_USE_SRL16,               -- [string]
        INIT        => X"0000")
      port map (
        Config_Reset => Config_Reset,             -- [in  std_logic]
        CE           => EN_16x_Baud,              -- [in  std_logic]
        D            => start_Edge_Detected_Bit,  -- [in  std_logic]
        Clk          => Clk,                      -- [in  std_logic]
        A0           => '0',                      -- [in  std_logic]
        A1           => '1',                      -- [in  std_logic]
        A2           => '1',                      -- [in  std_logic]
        A3           => '0',                      -- [in  std_logic]
        Q            => mid_Start_Bit);           -- [out std_logic]

    mid_Start_Bit_or_Config_Reset <= mid_Start_Bit or Config_Reset;

    -- Keep regenerating new values into the 16 clock delay
    -- Starting with the first mid_Start_Bit and for every new sample_points
    -- until stop_Bit_Position is reached
    recycle <= not (stop_Bit_Position) and (mid_Start_Bit or sample_Point);

    Delay_16 : XIL_SRL16E
      generic map (
        C_TARGET    => C_TARGET,
        C_USE_SRL16 => C_USE_SRL16,       -- [string]
        INIT        => X"0000")
      port map (
        Config_Reset => Config_Reset,     -- [in  std_logic]
        CE           => EN_16x_Baud,      -- [in  std_logic]
        D            => recycle,          -- [in  std_logic]
        Clk          => Clk,              -- [in  std_logic]
        A0           => '1',              -- [in  std_logic]
        A1           => '1',              -- [in  std_logic]
        A2           => '1',              -- [in  std_logic]
        A3           => '1',              -- [in  std_logic]
        Q            => sample_Point);    -- [out std_logic]

    -----------------------------------------------------------------------------
    -- Detect when the stop bit is received
    -----------------------------------------------------------------------------
    Stop_Bit_Handler : process (Clk) is
    begin  -- process Stop_Bit_Handler
      if Clk'event and Clk = '1' then     -- rising clock edge
        if Reset then                     -- asynchronous reset (active high)
          stop_Bit_Position <= '0';
        else
          if (EN_16x_Baud = '1') then
            if (stop_Bit_Position = '0') then
              -- Start bit has reached the end of the shift register (Stop bit position)
              stop_Bit_Position <= sample_Point and new_rx_data(STOP_BIT_POS);
            elsif (sample_Point = '1') then
              -- if stop_Bit_Position = '1', then clear it at the next sample_Point
              stop_Bit_Position <= '0';
            end if;
          end if;
        end if;
      end if;
    end process Stop_Bit_Handler;

    -----------------------------------------------------------------------------
    -- Parity handling
    -----------------------------------------------------------------------------
    Using_Parity : if (C_USE_PARITY = 1) generate
      signal calc_Parity : std_logic;
      signal parity      : std_logic;
    begin

      Using_Odd_Parity : if (C_ODD_PARITY = 1) generate
      begin
        Parity_Bit : MB_FDSE
          generic map (
            C_TARGET => C_TARGET,
            INIT     => '1')                  -- [bit]
          port map (
            Q  => Parity,                 -- [out std_logic]
            C  => Clk,                    -- [in  std_logic]
            CE => EN_16x_Baud,            -- [in  std_logic]
            D  => calc_Parity,            -- [in  std_logic]
            S  => mid_Start_Bit_or_Config_Reset); -- [in std_logic]
      end generate Using_Odd_Parity;

      Using_Even_Parity : if (C_ODD_PARITY = 0) generate
      begin
        Parity_Bit : MB_FDRE
          generic map (
            C_TARGET => C_TARGET,
            INIT     => '0')                  -- [bit]
          port map (
            Q  => Parity,                 -- [out std_logic]
            C  => Clk,                    -- [in  std_logic]
            CE => EN_16x_Baud,            -- [in  std_logic]
            D  => calc_Parity,            -- [in  std_logic]
            R  => mid_Start_Bit_or_Config_Reset);  -- [in std_logic]
      end generate Using_Even_Parity;

      calc_Parity <= parity when (stop_Bit_Position or not sample_Point) = '1'
                     else parity xor rx_2;

      rx_parity_error_i <= (EN_16x_Baud and sample_Point) and (new_rx_data(CALC_PAR_POS)) and
                           not stop_Bit_Position
                           when running and (rx_2 /= Parity) else '0';
    end generate Using_Parity;

    Not_Using_Parity : if (C_USE_PARITY = 0) generate
    begin
      rx_parity_error_i <= '0';
    end generate Not_Using_Parity;


    -----------------------------------------------------------------------------
    -- Data part
    -----------------------------------------------------------------------------

    new_rx_data(0) <= rx_2;

    Convert_Serial_To_Parallel : for I in 1 to serial_to_parallel'length generate
    begin

      serial_to_parallel(I) <= new_rx_data(I) when (stop_Bit_Position or not sample_Point) = '1'
                               else new_rx_data(I-1);

      First_Bit : if (I = 1) generate
      begin
        First_Bit_I : MB_FDSE
          generic map (
            C_TARGET => C_TARGET,
            INIT     => '0')                  -- [bit]
          port map (
            Q  => new_rx_data(I),         -- [out std_logic]
            C  => Clk,                    -- [in  std_logic]
            CE => EN_16x_Baud,            -- [in  std_logic]
            D  => serial_to_parallel(I),  -- [in  std_logic]
            S  => mid_Start_Bit_or_Config_Reset); -- [in std_logic]
      end generate First_Bit;

      Rest_Bits : if (I /= 1) generate
      begin
        Others_I : MB_FDRE
          generic map (
            C_TARGET => C_TARGET,
            INIT     => '0')                  -- [bit]
          port map (
            Q  => new_rx_data(I),         -- [out std_logic]
            C  => Clk,                    -- [in  std_logic]
            CE => EN_16x_Baud,            -- [in  std_logic]
            D  => serial_to_parallel(I),  -- [in  std_logic]
            R  => mid_Start_Bit_or_Config_Reset); -- [in std_logic]
      end generate Rest_Bits;

    end generate Convert_Serial_To_Parallel;

    -----------------------------------------------------------------------------
    -- Write in the received word when the stop_bit has been received and it is a
    -- '1'
    -----------------------------------------------------------------------------
    NEW_RX_DATA_Write_DFF : process (Clk) is
    begin
      if Clk'event and Clk = '1' then
        if Reset then
          new_rx_data_write <= '0';
        else
          new_rx_data_Write <= stop_Bit_Position and rx_2 and sample_Point and EN_16x_Baud;
        end if;
      end if;
    end process NEW_RX_DATA_Write_DFF;

    Rx_Data_Exist_Handler : process (Clk) is
    begin
      if Clk'event and Clk = '1' then
        if Reset then
          rx_data_exists_i <= '0';
        else
          if (new_rx_data_write = '1') then
            rx_data_exists_i <= '1';
          end if;
          if (Read_RX_Data = '1') then
            rx_data_exists_i <= '0';
          end if;
        end if;
      end if;
    end process Rx_Data_Exist_Handler;

    Receive_Register : process (Clk) is
    begin
      if Clk'event and Clk = '1' then
        if Reset then
          rx_data_i <= (others => '0');
        elsif (NEW_RX_DATA_Write = '1') then
          rx_data_i <= new_rx_data(DATA_LSB_POS - C_DATA_BITS + 1 to DATA_LSB_POS);
        end if;
      end if;
    end process Receive_Register;

    UART_Read: process (Clk) is
    begin
      if Clk'event and Clk = '1' then
        if Read_RX_Data = '0' or Config_Reset = '1' then
          RX_Data <= (others => '0');
        else
          RX_Data <= rx_data_i;
        end if;
      end if;
    end process UART_Read;

  end generate TMR_No;

  RX_Data_Received <= new_rx_data_write;
  rx_frame_error_i <= stop_Bit_Position and sample_Point and EN_16x_Baud and not rx_2;
  RX_Overrun_Error <= rx_data_exists_i and new_rx_data_write;
  RX_Data_Exists   <= rx_data_exists_i;


  TMR_Yes : if (C_TMR /= 0) generate
    signal start_Edge_Detected       : boolean;
    signal running                   : boolean;

    signal tmr_disable_b             : boolean;
    -- Voted signals before DFF
    signal previous_RX_d             : std_logic;
    signal start_Edge_Detected_d     : boolean;
    signal running_d                 : boolean;
    signal recycle_voted             : std_logic;
    signal stop_Bit_Position_d       : std_logic;
    signal mid_Start_Bit_voted       : std_logic;
    signal mid_Start_Bit_voted_or_Config_Reset : std_logic;
    signal serial_to_parallel_voted  : std_logic_vector(1 to SERIAL_TO_PAR_LENGTH);
    signal new_rx_data_write_d       : std_logic;
    signal rx_data_exists_i_d        : std_logic;
    signal rx_data_i_d               : std_logic_vector(C_DATA_BITS-1 downto 0);
    signal RX_Data_d                 : std_logic_vector(C_DATA_BITS-1 downto 0);
  begin

    tmr_disable_b <= TMR_Disable = '1' and C_USE_TMR_DISABLE = 1;

    -----------------------------------------------------------------------------
    -- Double sample to avoid meta-stability
    -----------------------------------------------------------------------------
    RX_Sampling : process (Clk)
    begin  -- process RX_Sampling
      if Clk'event and Clk = '1' then     -- rising clock edge
        if Reset then                     -- asynchronous reset (active high)
          rx_1 <= '1';
          rx_2 <= '1';
        else
          rx_1 <= RX;
          rx_2 <= rx_1;
        end if;
      end if;
    end process RX_Sampling;

    -----------------------------------------------------------------------------
    -- Detect a falling edge on RX and start a new receiption if idle
    -----------------------------------------------------------------------------
    Prev_RX_Logic : process (Reset, EN_16x_Baud, rx_2, previous_RX) is
    begin
      if Reset then
        previous_RX_d <= '0';
      else
        if (EN_16x_Baud = '1') then
          previous_RX_d <= rx_2;
        else
          previous_RX_d <= previous_RX;
        end if;
       end if;
    end process Prev_RX_Logic;

    ToVote(UART_RX_PREVIOUS_RX_Pos) <= previous_RX_d;

    Prev_RX_DFF : process (Clk) is
    begin  -- process Prev_RX_DFF
      if Clk'event and Clk = '1' then     -- rising clock edge
         previous_RX <= vote(previous_RX_d,
                             FromAVote(UART_RX_PREVIOUS_RX_Pos),
                             FromBVote(UART_RX_PREVIOUS_RX_Pos), tmr_disable_b);
      end if;
    end process Prev_RX_DFF;

    Start_Edge_Logic : process (Reset, EN_16x_Baud, running, previous_RX, rx_2, start_Edge_Detected) is
    begin
      if Reset then
        start_Edge_Detected_d <= false;
      else
        if (EN_16x_Baud = '1') then
          start_Edge_Detected_d <= not running and (previous_RX = '1') and (rx_2 = '0');
        else
          start_Edge_Detected_d <= start_Edge_Detected;
        end if;
      end if;
    end process Start_Edge_Logic;

    ToVote(UART_RX_START_EDGE_DETECTED_Pos) <= '1' when start_Edge_Detected_d else
                                               '0';

    Start_Edge_DFF : process (Clk) is
    begin  -- process Start_Edge_DFF
      if Clk'event and Clk = '1' then     -- rising clock edge
        start_Edge_Detected <= vote(start_Edge_Detected_d,
                                    FromAVote(UART_RX_START_EDGE_DETECTED_Pos),
                                    FromBVote(UART_RX_START_EDGE_DETECTED_Pos), tmr_disable_b);
      end if;
    end process Start_Edge_DFF;

    -----------------------------------------------------------------------------
    -- Running is '1' during a receiption
    -----------------------------------------------------------------------------
    Running_Logic : process (Reset, EN_16x_Baud, start_Edge_Detected, sample_Point, stop_Bit_Position, running) is
    begin
      if Reset then
        running_d <= false;
      else
        if (EN_16x_Baud = '1') then
          if (start_Edge_Detected) then
            running_d <= true;
          elsif ((sample_Point = '1') and (stop_Bit_Position = '1')) then
            running_d <= false;
          else
            running_d <= running;
          end if;
        else
          running_d <= running;
        end if;
      end if;
    end process Running_Logic;

    ToVote(UART_RX_RUNNING_Pos) <= '1' when running_d else
                                   '0';

    Running_DFF : process (Clk) is
    begin
      if Clk'event and Clk = '1' then
        running <= vote(running_d, FromAVote(UART_RX_RUNNING_Pos), FromBVote(UART_RX_RUNNING_Pos),tmr_disable_b);
      end if;
    end process Running_DFF;

    -----------------------------------------------------------------------------
    -- Delay start_Edge_Detected 7 clocks to get the mid-point in a bit
    -- The address needs to be 6 "0110" to get a delay of 7.
    -----------------------------------------------------------------------------

    start_Edge_Detected_Bit <= '1' when start_Edge_Detected else '0';

    Mid_Start_Bit_SRL16 : XIL_SRL16E
      generic map (
        C_TARGET    => C_TARGET,
        C_USE_SRL16 => C_USE_SRL16,               -- [string]
        INIT        => X"0000")
      port map (
        Config_Reset => Config_Reset,             -- [in  std_logic]
        CE           => EN_16x_Baud,              -- [in  std_logic]
        D            => start_Edge_Detected_Bit,  -- [in  std_logic]
        Clk          => Clk,                      -- [in  std_logic]
        A0           => '0',                      -- [in  std_logic]
        A1           => '1',                      -- [in  std_logic]
        A2           => '1',                      -- [in  std_logic]
        A3           => '0',                      -- [in  std_logic]
        Q            => mid_Start_Bit);           -- [out std_logic]

    ToVote(UART_RX_MID_START_BIT_Pos) <= mid_Start_Bit;

    mid_Start_Bit_voted <= vote(mid_Start_Bit,
                                FromAVote(UART_RX_MID_START_BIT_Pos),
                                FromBVote(UART_RX_MID_START_BIT_Pos), tmr_disable_b);

    mid_Start_Bit_voted_or_Config_Reset <= mid_Start_Bit_voted or Config_Reset;

    -- Keep regenerating new values into the 16 clock delay
    -- Starting with the first mid_Start_Bit and for every new sample_points
    -- until stop_Bit_Position is reached
    recycle  <= not (stop_Bit_Position) and (mid_Start_Bit or sample_Point);

    ToVote(UART_RX_RECYCLE_Pos) <= recycle;

    recycle_voted <= vote(recycle, FromAVote(UART_RX_RECYCLE_Pos), FromBVote(UART_RX_RECYCLE_Pos), tmr_disable_b);

    Delay_16 : XIL_SRL16E
      generic map (
        C_TARGET    => C_TARGET,
        C_USE_SRL16 => C_USE_SRL16,       -- [string]
        INIT        => X"0000")
      port map (
        Config_Reset => Config_Reset,     -- [in  std_logic]
        CE           => EN_16x_Baud,      -- [in  std_logic]
        D            => recycle_voted,    -- [in  std_logic]
        Clk          => Clk,              -- [in  std_logic]
        A0           => '1',              -- [in  std_logic]
        A1           => '1',              -- [in  std_logic]
        A2           => '1',              -- [in  std_logic]
        A3           => '1',              -- [in  std_logic]
        Q            => sample_Point);    -- [out std_logic]

    -----------------------------------------------------------------------------
    -- Detect when the stop bit is received
    -----------------------------------------------------------------------------
    Stop_Bit_Handler_Logic : process (Reset, EN_16x_Baud, stop_Bit_Position, sample_Point, new_rx_data) is
    begin
      if Reset then
        stop_Bit_Position_d <= '0';
      else
        if (EN_16x_Baud = '1') then
          if (stop_Bit_Position = '0') then
            -- Start bit has reached the end of the shift register (Stop bit position)
            stop_Bit_Position_d <= sample_Point and new_rx_data(STOP_BIT_POS);
          elsif (sample_Point = '1') then
            -- if stop_Bit_Position = '1', then clear it at the next sample_Point
            stop_Bit_Position_d <= '0';
          else
            stop_Bit_Position_d <= stop_Bit_Position;
          end if;
        else
          stop_Bit_Position_d <= stop_Bit_Position;
        end if;
      end if;
    end process Stop_Bit_Handler_Logic;

    ToVote(UART_RX_STOP_BIT_POSITION_Pos) <= stop_Bit_Position_d;

    Stop_Bit_Handler_DFF : process (Clk) is
    begin
      if Clk'event and Clk = '1' then
        stop_Bit_Position <= vote(stop_Bit_Position_d,
                                  FromAVote(UART_RX_STOP_BIT_POSITION_Pos),
                                  FromBVote(UART_RX_STOP_BIT_POSITION_Pos), tmr_disable_b);
      end if;
    end process Stop_Bit_Handler_DFF;

    -----------------------------------------------------------------------------
    -- Parity handling
    -----------------------------------------------------------------------------
    Using_Parity : if (C_USE_PARITY = 1) generate
      signal calc_Parity       : std_logic;
      signal parity            : std_logic;
      signal calc_Parity_voted : std_logic;
    begin

      Using_Odd_Parity : if (C_ODD_PARITY = 1) generate
      begin
        Parity_Bit : MB_FDSE
          generic map (
            C_TARGET => C_TARGET,
            INIT => '1')                  -- [bit]
          port map (
            Q  => Parity,                 -- [out std_logic]
            C  => Clk,                    -- [in  std_logic]
            CE => EN_16x_Baud,            -- [in  std_logic]
            D  => calc_Parity_Voted,      -- [in  std_logic]
            S  => mid_Start_Bit_Voted_or_Config_Reset);   -- [in std_logic]
      end generate Using_Odd_Parity;

      Using_Even_Parity : if (C_ODD_PARITY = 0) generate
      begin
        Parity_Bit : MB_FDRE
          generic map (
            C_TARGET => C_TARGET,
            INIT => '0')                  -- [bit]
          port map (
            Q  => Parity,                 -- [out std_logic]
            C  => Clk,                    -- [in  std_logic]
            CE => EN_16x_Baud,            -- [in  std_logic]
            D  => calc_Parity_Voted,      -- [in  std_logic]
            R  => mid_Start_Bit_Voted_or_Config_Reset);   -- [in std_logic]
      end generate Using_Even_Parity;

      calc_Parity <= parity when (stop_Bit_Position or not sample_Point) = '1'
                     else parity xor rx_2;

      ToVote(UART_RX_CALC_PARITY_Pos) <= calc_Parity;

      calc_Parity_Voted <= vote(calc_Parity,
                                FromAVote(UART_RX_CALC_PARITY_Pos),
                                FromBVote(UART_RX_CALC_PARITY_Pos), tmr_disable_b);

      rx_parity_error_i <= (EN_16x_Baud and sample_Point) and (new_rx_data(CALC_PAR_POS)) and
                           not stop_Bit_Position
                           when running and (rx_2 /= Parity) else '0';


    end generate Using_Parity;

    Not_Using_Parity : if (C_USE_PARITY = 0) generate
    begin
      rx_parity_error_i <= '0';
      ToVote(UART_RX_CALC_PARITY_Pos) <= '0';
    end generate Not_Using_Parity;


    -----------------------------------------------------------------------------
    -- Data part
    -----------------------------------------------------------------------------

    new_rx_data(0) <= rx_2;

    ToVote(UART_RX_SERIAL_TO_PARALLEL_Pos'low + serial_to_parallel'length -1 downto
           UART_RX_SERIAL_TO_PARALLEL_Pos'low) <= serial_to_parallel;
    ToVote(UART_RX_SERIAL_TO_PARALLEL_Pos'high downto
           UART_RX_SERIAL_TO_PARALLEL_Pos'low + serial_to_parallel'length) <= (others => '0');

    serial_to_parallel_voted <=
      vote(serial_to_parallel,
           FromAVote(UART_RX_SERIAL_TO_PARALLEL_Pos'low + serial_to_parallel'length - 1 downto
                     UART_RX_SERIAL_TO_PARALLEL_Pos'low),
           FromBVote(UART_RX_SERIAL_TO_PARALLEL_Pos'low + serial_to_parallel'length - 1 downto
                     UART_RX_SERIAL_TO_PARALLEL_Pos'low), tmr_disable_b);

    Convert_Serial_To_Parallel : for I in 1 to serial_to_parallel'length generate
    begin

      serial_to_parallel(I) <= new_rx_data(I) when (stop_Bit_Position or not sample_Point) = '1'
                               else new_rx_data(I-1);

      First_Bit : if (I = 1) generate
      begin
        First_Bit_I : MB_FDSE
          generic map (
            C_TARGET => C_TARGET,
            INIT => '0')                        -- [bit]
          port map (
            Q  => new_rx_data(I),               -- [out std_logic]
            C  => Clk,                          -- [in  std_logic]
            CE => EN_16x_Baud,                  -- [in  std_logic]
            D  => serial_to_parallel_voted(I),  -- [in  std_logic]
            S  => mid_Start_Bit_Voted_or_Config_Reset);  -- [in std_logic]
      end generate First_Bit;

      Rest_Bits : if (I /= 1) generate
      begin
        Others_I : MB_FDRE
          generic map (
            C_TARGET => C_TARGET,
            INIT => '0')                        -- [bit]
          port map (
            Q  => new_rx_data(I),               -- [out std_logic]
            C  => Clk,                          -- [in  std_logic]
            CE => EN_16x_Baud,                  -- [in  std_logic]
            D  => serial_to_parallel_voted(I),  -- [in  std_logic]
            R  => mid_Start_Bit_Voted_or_Config_Reset);  -- [in std_logic]
      end generate Rest_Bits;

    end generate Convert_Serial_To_Parallel;

    -----------------------------------------------------------------------------
    -- Write in the received word when the stop_bit has been received and it is a
    -- '1'
    -----------------------------------------------------------------------------
    NEW_RX_DATA_Write_Logic : process (Reset, stop_Bit_Position, rx_2, sample_Point, EN_16x_Baud) is
    begin
      if Reset then
        new_rx_data_write_d <= '0';
      else
        new_rx_data_Write_d <= stop_Bit_Position and rx_2 and sample_Point and EN_16x_Baud;
      end if;
    end process NEW_RX_DATA_Write_Logic;

    ToVote(UART_RX_NEW_RX_DATA_WRITE_Pos) <= new_rx_data_write_d;

    NEW_RX_DATA_Write_DFF : process (Clk) is
    begin
      if Clk'event and Clk = '1' then
        new_rx_data_write <= vote(new_rx_data_write_d,
                                  FromAVote(UART_RX_NEW_RX_DATA_WRITE_Pos),
                                  FromBVote(UART_RX_NEW_RX_DATA_WRITE_Pos), tmr_disable_b);
      end if;
    end process NEW_RX_DATA_Write_DFF;

    Rx_Data_Exist_Handler_Logic : process (Reset, Read_RX_Data, new_rx_data_write, rx_data_exists_i) is
    begin
      if Reset then
        rx_data_exists_i_d <= '0';
      else
        if (Read_RX_Data = '1') then
          rx_data_exists_i_d <= '0';
        elsif (new_rx_data_write = '1') then
          rx_data_exists_i_d <= '1';
        else
          rx_data_exists_i_d <= rx_data_exists_i;
        end if;
      end if;
    end process Rx_Data_Exist_Handler_Logic;

    ToVote(UART_RX_DATA_EXISTS_Pos) <= rx_data_exists_i_d;

    Rx_Data_Exist_Handler_DFF : process (Clk) is
    begin
      if Clk'event and Clk = '1' then
        rx_data_exists_i <= vote(rx_data_exists_i_d,
                                 FromAVote(UART_RX_DATA_EXISTS_Pos),
                                 FromBVote(UART_RX_DATA_EXISTS_Pos), tmr_disable_b);
      end if;
    end process Rx_Data_Exist_Handler_DFF;

    Receive_Register_Logic : process (Reset, new_rx_data_write, new_rx_data, rx_data_i) is
    begin
      if Reset then
        rx_data_i_d <= (others => '0');
      elsif (new_rx_data_write = '1') then
        rx_data_i_d <= new_rx_data(DATA_LSB_POS - C_DATA_BITS + 1 to DATA_LSB_POS);
      else
        rx_data_i_d <= rx_data_i;
      end if;
    end process Receive_Register_Logic;

    ToVote(UART_RX_DATA_I_Pos'low+rx_data_i_d'length-1 downto UART_RX_DATA_I_Pos'low) <= rx_data_i_d;

    -- Work around spyglass bug report on null range to the left but not to the right
    spy1_g: if C_DATA_BITS < 8 generate
    begin
      ToVote(UART_RX_DATA_I_Pos'high downto UART_RX_DATA_I_Pos'low+rx_data_i_d'length)  <= (others => '0');
    end generate spy1_g;

    Receive_Register_DFF : process (Clk) is
    begin
      if Clk'event and Clk = '1' then
        rx_data_i <= vote(rx_data_i_d,
                          FromAVote(UART_RX_DATA_I_Pos'low+rx_data_i_d'length-1 downto UART_RX_DATA_I_Pos'low),
                          FromBVote(UART_RX_DATA_I_Pos'low+rx_data_i_d'length-1 downto UART_RX_DATA_I_Pos'low),
                          tmr_disable_b);
      end if;
    end process Receive_Register_DFF;

    UART_Read_Logic: process (Read_RX_Data, rx_data_i, Config_Reset) is
    begin
      if Read_RX_Data = '0' or Config_Reset = '1' then
        RX_Data_d <= (others => '0');
      else
        RX_Data_d <= rx_data_i;
      end if;
    end process UART_Read_Logic;

    ToVote(UART_RX_DATA_Pos'low+RX_Data_d'length-1 downto UART_RX_DATA_Pos'low)  <= RX_Data_d;

    -- Work around spyglass bug report on null range to the left but not to the right
    spy2_g: if C_DATA_BITS < 8 generate
    begin
      ToVote(UART_RX_DATA_Pos'high downto UART_RX_DATA_Pos'low+RX_Data_d'length) <= (others => '0');
    end generate spy2_g;

    UART_Read: process (Clk) is
    begin
      if Clk'event and Clk = '1' then
        RX_Data <= vote(RX_Data_d,
                        FromAVote(UART_RX_DATA_Pos'low+RX_Data_d'length-1 downto UART_RX_DATA_Pos'low),
                        FromBVote(UART_RX_DATA_Pos'low+RX_Data_d'length-1 downto UART_RX_DATA_Pos'low),
                        tmr_disable_b);
      end if;
    end process UART_Read;

  end generate TMR_Yes;

  RX_Frame_Error  <= rx_frame_error_i;
  RX_Parity_Error <= rx_parity_error_i;

end architecture IMP;


-------------------------------------------------------------------------------
-- uart_transmit.vhd - Entity and architecture
-------------------------------------------------------------------------------
--
-- (c) Copyright 2011,2016 Xilinx, Inc. All rights reserved.
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
-- Filename:        uart_transmit.vhd
--
-- Description:
--
-- VHDL-Standard:   VHDL'93/02
-------------------------------------------------------------------------------
-- Structure:
--              uart_transmit.vhd
--
-------------------------------------------------------------------------------
-- Author:          goran
--
-- History:
--   goran  2007-12-18    First Version
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
library iomodule_v3_1_6;
use iomodule_v3_1_6.iomodule_funcs.all;

entity UART_Transmit is
  generic (
    C_TARGET          : TARGET_FAMILY_TYPE;
    C_TMR             : integer := 0;
    C_USE_TMR_DISABLE : integer := 0;
    C_VOTE_SIZE       : integer := 0;
    C_USE_SRL16       : string;
    C_DATA_BITS       : integer range 5 to 8 := 8;
    C_USE_PARITY      : integer              := 0;
    C_ODD_PARITY      : integer              := 1
    );
  port (
    Config_Reset : in std_logic;
    Clk          : in std_logic;
    Reset        : in boolean;
    EN_16x_Baud  : in std_logic;

    TMR_Disable         : in std_logic;
    FromAVote           : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
    FromBVote           : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
    ToVote              : out std_logic_vector(C_VOTE_SIZE-1 downto 0);
    TX                  : out std_logic;
    Write_TX_Data       : in  std_logic;
    TX_Data             : in  std_logic_vector(C_DATA_BITS-1 downto 0);
    TX_Data_Transmitted : out std_logic;
    TX_Buffer_Empty     : out std_logic
    );

end entity UART_Transmit;

library ieee;
use ieee.numeric_std.all;
library iomodule_v3_1_6;
use iomodule_v3_1_6.iomodule_vote_pkg.all;

architecture IMP of UART_Transmit is

  component XIL_SRL16E is
    generic (
      C_TARGET    : TARGET_FAMILY_TYPE;
      C_USE_SRL16 : string;
      C_STATIC    : boolean := false;
      INIT        : bit_vector);
    port (
      Config_Reset : in  std_logic;
      Q            : out std_logic;
      A0           : in  std_logic;
      A1           : in  std_logic;
      A2           : in  std_logic;
      A3           : in  std_logic;
      CE           : in  std_logic;
      CLK          : in  std_logic;
      D            : in  std_logic);
  end component XIL_SRL16E;

  component MB_MUXCY is
    generic (
      C_TARGET : TARGET_FAMILY_TYPE);
    port (
      LO : out std_logic;
      CI : in  std_logic;
      DI : in  std_logic;
      S  : in  std_logic);
  end component MB_MUXCY;

  component MB_XORCY is
    generic (
      C_TARGET : TARGET_FAMILY_TYPE);
    port (
      O  : out std_logic;
      CI : in  std_logic;
      LI : in  std_logic);
  end component MB_XORCY;

  component MB_FDSE is
  generic (
    C_TARGET : TARGET_FAMILY_TYPE;
    INIT : bit := '1');
  port(
    Q  : out std_logic;
    C  : in  std_logic;
    CE : in  std_logic;
    D  : in  std_logic;
    S  : in  std_logic);
  end component MB_FDSE;

  component MB_FDRE is
  generic (
    C_TARGET : TARGET_FAMILY_TYPE;
    INIT : bit := '0');
  port(
    Q  : out std_logic;
    C  : in  std_logic;
    CE : in  std_logic;
    D  : in  std_logic;
    R  : in  std_logic);
  end component MB_FDRE;

  component MB_MUXF5 is
  generic (
    C_TARGET : TARGET_FAMILY_TYPE);
  port (
    O  : out std_logic;
    I0 : in  std_logic;
    I1 : in  std_logic;
    S  : in  std_logic);
  end component MB_MUXF5;

  component MB_MUXF6 is
  generic (
    C_TARGET : TARGET_FAMILY_TYPE);
  port (
    O  : out std_logic;
    I0 : in  std_logic;
    I1 : in  std_logic;
    S  : in  std_logic);
  end component MB_MUXF6;

  -- signals for parity
  signal parity           : std_logic;
  signal calc_Parity      : std_logic;
  signal tx_Run1          : std_logic;
  signal select_Parity    : std_logic;
  signal data_to_transfer : std_logic_vector(0 to C_DATA_BITS-1);

  signal div16          : std_logic;
  signal tx_Data_Enable : std_logic;
  signal tx_Start       : std_logic;
  signal tx_DataBits    : std_logic;
  signal tx_Run         : std_logic;

  signal cnt_cy          : std_logic_vector(1 to 3);
  signal h_Cnt           : std_logic_vector(0 to 2);
  signal sum_cnt         : std_logic_vector(0 to 2);
  signal mux_sel         : std_logic_vector(0 to 2);
  signal mux_sel_is_zero : std_logic;

  constant mux_sel_init : std_logic_vector(0 to 2) :=
    std_logic_vector(to_unsigned(C_DATA_BITS-1, 3));

  signal mux_01      : std_logic;
  signal mux_23      : std_logic;
  signal mux_45      : std_logic;
  signal mux_67      : std_logic;
  signal mux_0123    : std_logic;
  signal mux_4567    : std_logic;
  signal mux_Out     : std_logic;
  signal serial_Data : std_logic;

  signal data_is_sent      : std_logic;
  signal tx_buffer_empty_i : std_logic;
  signal tx_i              : std_logic;
  signal fifo_DOut         : std_logic_vector(0 to C_DATA_BITS-1);

  -- Preserve signals after synthesis for simulation UART support
  attribute KEEP : string;
  attribute KEEP of tx_buffer_empty_i : signal is "TRUE";
  attribute KEEP of tx_i              : signal is "TRUE";

begin  -- architecture IMP

  TMR_No : if (C_TMR = 0) generate
    signal tx_Data_Enable_or_Config_Reset : std_logic;
    signal tx_Start_or_Config_Reset       : std_logic;
  begin

    ToVote <= (others => '0');

    -----------------------------------------------------------------------------
    -- Divide the EN_16x_Baud by 16 to get the correct baudrate
    -----------------------------------------------------------------------------
    DIV16_SRL16E : XIL_SRL16E
      generic map (
        C_TARGET    => C_TARGET,
        C_USE_SRL16 => C_USE_SRL16,       -- [string]
        INIT        => X"0001")
      port map (
        Config_Reset => Config_Reset,     -- [in  std_logic]
        CE           => EN_16x_Baud,      -- [in  std_logic]
        D            => div16,            -- [in  std_logic]
        Clk          => Clk,              -- [in  std_logic]
        A0           => '1',              -- [in  std_logic]
        A1           => '1',              -- [in  std_logic]
        A2           => '1',              -- [in  std_logic]
        A3           => '1',              -- [in  std_logic]
        Q            => div16);           -- [out std_logic]

    FDRE_I : MB_FDRE
      generic map (
        C_TARGET    => C_TARGET,
        INIT => '0')                      -- [bit]
      port map (
        Q  => tx_Data_Enable,             -- [out std_logic]
        C  => Clk,                        -- [in  std_logic]
        CE => EN_16x_Baud,                -- [in  std_logic]
        D  => div16,                      -- [in  std_logic]
        R  => tx_Data_Enable_or_Config_Reset);  -- [in std_logic]

    tx_Data_Enable_or_Config_Reset <= tx_Data_Enable or Config_Reset;
    
    -----------------------------------------------------------------------------
    -- tx_start is '1' for the start bit in a transmission
    -----------------------------------------------------------------------------
    TX_Start_DFF : process (Clk) is
    begin  -- process TX_Start_DFF
      if Clk'event and Clk = '1' then  -- rising clock edge
        if Reset then                 -- asynchronous reset (active high)
          tx_Start <= '0';
        else
          tx_Start <= not(tx_Run) and (tx_Start or (not(tx_buffer_empty_i) and tx_Data_Enable));
        end if;
      end if;
    end process TX_Start_DFF;

    tx_Start_or_Config_Reset <= tx_Start or Config_Reset;
    
    -----------------------------------------------------------------------------
    -- tx_DataBits is '1' during all databits transmission
    -----------------------------------------------------------------------------
    TX_Data_DFF : process (Clk) is
    begin  -- process TX_Data_DFF
      if Clk'event and Clk = '1' then  -- rising clock edge
        if Reset then                  -- asynchronous reset (active high)
          tx_DataBits <= '0';
        else
          tx_DataBits <= not(data_is_sent) and (tx_DataBits or (tx_Start and tx_Data_Enable));
        end if;
      end if;
    end process TX_Data_DFF;

    -- only decrement during data bits transfer
    cnt_cy(3) <= not tx_DataBits;

    Counter : for I in 2 downto 0 generate
    begin

      ---------------------------------------------------------------------------
      -- If mux_sel is zero then reload with the init value else decrement
      ---------------------------------------------------------------------------
      h_Cnt(I) <= mux_sel_init(I) when mux_sel_is_zero = '1' else not mux_sel(I);

      -- Don't need the last muxcy, cnt_cy(0) is not used anywhere
      Used_MuxCY: if I> 0 generate
      begin
        MUXCY_L_I : MB_MUXCY
          generic map(
            C_TARGET => C_TARGET)
          port map (
            DI => mux_sel(I),               -- [in  std_logic]
            CI => cnt_cy(I+1),              -- [in  std_logic]
            S  => h_cnt(I),                 -- [in  std_logic]
            LO => cnt_cy(I));               -- [out std_logic]
      end generate Used_MuxCY;

      XORCY_I : MB_XORCY
        generic map(
          C_TARGET => C_TARGET)
        port map (
          LI => h_cnt(I),                 -- [in  std_logic]
          CI => cnt_cy(I+1),              -- [in  std_logic]
          O  => sum_cnt(I));              -- [out std_logic]
    end generate Counter;

    Mux_Addr_DFF : process (Clk) is
    begin  -- process Mux_Addr_DFF
      if Clk'event and Clk = '1' then  -- rising clock edge
        if Reset then                 -- asynchronous reset (active high)
          mux_sel <= std_logic_vector(to_unsigned(C_DATA_BITS-1, mux_sel'length));
        else
          if (tx_Data_Enable = '1') then
            mux_sel <= sum_cnt;
          end if;
        end if;
      end if;
    end process Mux_Addr_DFF;

    -- Detecting when mux_sel is zero ie. all data bits is transfered
    mux_sel_is_zero <= '1' when mux_sel = "000" else '0';

    -- Read out the next data from the transmit fifo when the data has been
    -- transmitted
    Data_is_Sent_DFF : process (Clk) is
    begin  -- process Data_is_Sent_DFF
      if Clk'event and Clk = '1' then  -- rising clock edge
        if Reset then                 -- asynchronous reset (active high)
          data_is_sent <= '0';
        else
          data_is_sent <= tx_Data_Enable and mux_sel_is_zero;
        end if;
      end if;
    end process Data_is_Sent_DFF;

    TX_Data_Transmitted <= data_is_sent;

    -----------------------------------------------------------------------------
    -- Select which bit within the data word to transmit
    -----------------------------------------------------------------------------

    -- Need special treatment for inserting the parity bit because of parity generation
    Parity_Bit_Insertion : process (parity, select_Parity, fifo_DOut) is
    begin  -- process Parity_Bit_Insertion
      data_to_transfer <= fifo_DOut;
      if (select_Parity = '1') then
        data_to_transfer(C_DATA_BITS-1) <= parity;
      end if;
    end process Parity_Bit_Insertion;

    mux_01 <= data_to_transfer(1) when mux_sel(2) = '1' else data_to_transfer(0);
    mux_23 <= data_to_transfer(3) when mux_sel(2) = '1' else data_to_transfer(2);

    Data_Bits_Is_5 : if (C_DATA_BITS = 5) generate
    begin
      mux_45 <= data_to_transfer(4);
      mux_67 <= '0';
    end generate Data_Bits_Is_5;

    Data_Bits_Is_6 : if (C_DATA_BITS = 6) generate
    begin
      mux_45 <= data_to_transfer(5) when mux_sel(2) = '1' else data_to_transfer(4);
      mux_67 <= '0';
    end generate Data_Bits_Is_6;

    Data_Bits_Is_7 : if (C_DATA_BITS = 7) generate
    begin
      mux_45 <= data_to_transfer(5) when mux_sel(2) = '1' else data_to_transfer(4);
      mux_67 <= data_to_transfer(6);
    end generate Data_Bits_Is_7;

    Data_Bits_Is_8 : if (C_DATA_BITS = 8) generate
    begin
      mux_45 <= data_to_transfer(5) when mux_sel(2) = '1' else data_to_transfer(4);
      mux_67 <= data_to_transfer(7) when mux_sel(2) = '1' else data_to_transfer(6);
    end generate Data_Bits_Is_8;

    MUX_F5_1 : MB_MUXF5
      generic map(
        C_TARGET => C_TARGET)
      port map (
        O  => mux_0123,                   -- [out std_logic]
        I0 => mux_01,                     -- [in  std_logic]
        I1 => mux_23,                     -- [in  std_logic]
        S  => mux_sel(1));                -- [in std_logic]

    MUX_F5_2 : MB_MUXF5
      generic map(
        C_TARGET => C_TARGET)
      port map (
        O  => mux_4567,                   -- [out std_logic]
        I0 => mux_45,                     -- [in  std_logic]
        I1 => mux_67,                     -- [in  std_logic]
        S  => mux_sel(1));                -- [in std_logic]

    MUXF6_I : MB_MUXF6
      generic map(
        C_TARGET => C_TARGET)
      port map (
        O  => mux_out,                    -- [out std_logic]
        I0 => mux_0123,                   -- [in  std_logic]
        I1 => mux_4567,                   -- [in  std_logic]
        S  => mux_sel(0));                -- [in std_logic]

    Serial_Data_DFF : process (Clk) is
    begin  -- process Serial_Data_DFF
      if Clk'event and Clk = '1' then  -- rising clock edge
        if Reset then                 -- asynchronous reset (active high)
          serial_Data <= '0';
        else
          serial_Data <= mux_Out;
        end if;
      end if;
    end process Serial_Data_DFF;

    -----------------------------------------------------------------------------
    -- Force a '0' when tx_start is '1', Start_bit
    -- Force a '1' when tx_run is '0',   Idle
    -- otherwise put out the serial_data
    -----------------------------------------------------------------------------
    Serial_Out_DFF : process (Clk) is
    begin  -- process Serial_Out_DFF
      if Clk'event and Clk = '1' then  -- rising clock edge
        if Reset then                 -- asynchronous reset (active high)
          tx_i <= '1';
        else
          tx_i <= (not(tx_run) or serial_Data) and not(tx_Start);
        end if;
      end if;
    end process Serial_Out_DFF;

    -----------------------------------------------------------------------------
    -- Parity handling
    -----------------------------------------------------------------------------
    Using_Parity : if (C_USE_PARITY = 1) generate
    begin

      Using_Odd_Parity : if (C_ODD_PARITY = 1) generate
      begin
        Parity_Bit : MB_FDSE
          generic map(
            C_TARGET => C_TARGET,
            INIT => '1')                  -- [bit]
          port map (
            Q  => Parity,                 -- [out std_logic]
            C  => Clk,                    -- [in  std_logic]
            CE => tx_Data_Enable,         -- [in  std_logic]
            D  => calc_Parity,            -- [in  std_logic]
            S  => tx_Start_or_Config_Reset);  -- [in std_logic]
      end generate Using_Odd_Parity;

      Using_Even_Parity : if (C_ODD_PARITY = 0) generate
      begin
        Parity_Bit : MB_FDRE
          generic map (
            C_TARGET => C_TARGET,
            INIT => '0')                  -- [bit]
          port map (
            Q  => Parity,                 -- [out std_logic]
            C  => Clk,                    -- [in  std_logic]
            CE => tx_Data_Enable,         -- [in  std_logic]
            D  => calc_Parity,            -- [in  std_logic]
            R  => tx_Start_or_Config_Reset);  -- [in std_logic]
      end generate Using_Even_Parity;

      calc_Parity <= parity xor serial_data;

      tx_Run_DFF : process (Clk) is
      begin  -- process tx_Run_DFF
        if Clk'event and Clk = '1' then  -- rising clock edge
          if Reset then                 -- asynchronous reset (active high)
            tx_Run1 <= '0';
          else
            if (tx_Data_Enable = '1') then
              tx_Run1 <= tx_DataBits;
            end if;
          end if;
        end if;
      end process tx_Run_DFF;

      tx_Run <= tx_Run1 or tx_DataBits;

      Select_Parity_DFF : process (Clk) is
      begin  -- process Select_Parity_DFF
        if Clk'event and Clk = '1' then  -- rising clock edge
          if Reset then                 -- asynchronous reset (active high)
            select_Parity <= '0';
          else
            if (tx_Data_Enable = '1') then
              select_Parity <= mux_sel_is_zero;
            end if;
          end if;
        end if;
      end process Select_Parity_DFF;
    end generate Using_Parity;

    No_Parity : if (C_USE_PARITY = 0) generate
    begin
      tx_Run1       <= '0';
      calc_Parity   <= '0';
      parity        <= '0';
      tx_Run        <= tx_DataBits;
      select_Parity <= '0';
    end generate No_Parity;

    Data_To_Transmit: process (Clk) is
    begin
      if Clk'event and Clk = '1' then
        if Reset then
          fifo_DOut <= (others => '0');
        elsif (Write_TX_Data = '1') then
          fifo_DOut <= TX_Data;
        end if;
      end if;
    end process Data_To_Transmit;

    TX_Reg_Status: process (Clk) is
    begin
      if Clk'event and Clk = '1' then
        if Reset then
          tx_buffer_empty_i <= '1';
        else
          if Write_TX_Data = '1' then
            tx_buffer_empty_i <= '0';
          end if;
          if (data_is_sent = '1') then
            tx_buffer_empty_i <= '1';
          end if;
        end if;
      end if;
    end process TX_Reg_Status;

    TX_Buffer_Empty <= tx_buffer_empty_i;

  end generate TMR_No;

  TMR_Yes : if (C_TMR /= 0) generate
    signal tmr_disable_b        : boolean;
    signal div16_voted          : std_logic;
    signal tx_Data_Enable_voted : std_logic;
    signal tx_Data_Enable_voted_or_Config_Reset : std_logic;
    signal tx_Start_d           : std_logic;
    signal tx_DataBits_d        : std_logic;
    signal mux_sel_d            : std_logic_vector(0 to 2);
    signal data_is_sent_d       : std_logic;
    signal TX_d                 : std_logic;
    signal select_Parity_d      : std_logic;
    signal fifo_DOut_d          : std_logic_vector(0 to C_DATA_BITS-1);
    signal tx_buffer_empty_i_d  : std_logic;
    signal serial_Data_d        : std_logic;
  begin

    tmr_disable_b <= TMR_Disable = '1' and C_USE_TMR_DISABLE = 1;

    -----------------------------------------------------------------------------
    -- Divide the EN_16x_Baud by 16 to get the correct baudrate
    -----------------------------------------------------------------------------
    DIV16_SRL16E : XIL_SRL16E
      generic map (
        C_TARGET    => C_TARGET,
        C_USE_SRL16 => C_USE_SRL16,       -- [string]
        INIT        => X"0001")
      port map (
        Config_Reset => Config_Reset,     -- [in  std_logic]
        CE           => EN_16x_Baud,      -- [in  std_logic]
        D            => div16_voted,      -- [in  std_logic]
        Clk          => Clk,              -- [in  std_logic]
        A0           => '1',              -- [in  std_logic]
        A1           => '1',              -- [in  std_logic]
        A2           => '1',              -- [in  std_logic]
        A3           => '1',              -- [in  std_logic]
        Q            => div16);           -- [out std_logic]

    ToVote(UART_TX_DIV16_Pos) <= div16;

    div16_voted <= vote(div16, FromAVote(UART_TX_DIV16_Pos), FromBVote(UART_TX_DIV16_Pos), tmr_disable_b);

    FDRE_I : MB_FDRE
      generic map (
        C_TARGET    => C_TARGET,
        INIT => '0')                      -- [bit]
      port map (
        Q  => tx_Data_Enable,             -- [out std_logic]
        C  => Clk,                        -- [in  std_logic]
        CE => EN_16x_Baud,                -- [in  std_logic]
        D  => div16_voted,                -- [in  std_logic]
        R  => tx_Data_Enable_voted_or_Config_Reset); -- [in std_logic]

    ToVote(UART_TX_DATA_ENABLE_Pos) <= tx_Data_Enable;

    tx_Data_Enable_voted <= vote(tx_Data_Enable,
                                 FromAVote(UART_TX_DATA_ENABLE_Pos),
                                 FromBVote(UART_TX_DATA_ENABLE_Pos), tmr_disable_b);

    tx_Data_Enable_voted_or_Config_Reset <= tx_Data_Enable_voted or Config_Reset;

    -----------------------------------------------------------------------------
    -- tx_start is '1' for the start bit in a transmission
    -----------------------------------------------------------------------------
    TX_Start_Logic : process (Reset, tx_Run, tx_Start, tx_buffer_empty_i, tx_Data_Enable) is
    begin
      if Reset then
        tx_Start_d <= '0';
      else
        tx_Start_d <= not(tx_Run) and (tx_Start or (not(tx_buffer_empty_i) and tx_Data_Enable));
      end if;
    end process TX_Start_Logic;

    ToVote(UART_TX_START_Pos) <= tx_Start_d;

    TX_Start_DFF : process (Clk) is
    begin
      if Clk'event and Clk = '1' then  -- rising clock edge
        tx_Start <= vote(tx_Start_d, FromAVote(UART_TX_START_Pos), FromBVote(UART_TX_START_Pos), tmr_disable_b);
      end if;
    end process TX_Start_DFF;

    -----------------------------------------------------------------------------
    -- tx_DataBits is '1' during all databits transmission
    -----------------------------------------------------------------------------
    TX_Data_Logic : process (Reset, data_is_sent, tx_DataBits, tx_Start, tx_Data_Enable) is
    begin
      if Reset then
        tx_DataBits_d <= '0';
      else
        tx_DataBits_d <= not(data_is_sent) and (tx_DataBits or (tx_Start and tx_Data_Enable));
      end if;
    end process TX_Data_Logic;

    ToVote(UART_TX_DATABITS_Pos) <= tx_DataBits_d;

    TX_Data_DFF : process (Clk) is
    begin
      if Clk'event and Clk = '1' then
        tx_DataBits <= vote(tx_DataBits_d,
                            FromAVote(UART_TX_DATABITS_Pos),
                            FromBVote(UART_TX_DATABITS_Pos), tmr_disable_b);
      end if;
    end process TX_Data_DFF;

    -- only decrement during data bits transfer
    cnt_cy(3) <= not tx_DataBits;

    Counter : for I in 2 downto 0 generate
    begin

      ---------------------------------------------------------------------------
      -- If mux_sel is zero then reload with the init value else decrement
      ---------------------------------------------------------------------------
      h_Cnt(I) <= mux_sel_init(I) when mux_sel_is_zero = '1' else not mux_sel(I);

      -- Don't need the last muxcy, cnt_cy(0) is not used anywhere
      Used_MuxCY: if I> 0 generate
      begin
        MUXCY_L_I : MB_MUXCY
          generic map(
            C_TARGET => C_TARGET)
          port map (
            DI => mux_sel(I),               -- [in  std_logic]
            CI => cnt_cy(I+1),              -- [in  std_logic]
            S  => h_cnt(I),                 -- [in  std_logic]
            LO => cnt_cy(I));               -- [out std_logic]
      end generate Used_MuxCY;

      XORCY_I : MB_XORCY
        generic map(
          C_TARGET => C_TARGET)
        port map (
          LI => h_cnt(I),                 -- [in  std_logic]
          CI => cnt_cy(I+1),              -- [in  std_logic]
          O  => sum_cnt(I));              -- [out std_logic]
    end generate Counter;

    Mux_Addr_Logic : process (Reset,tx_Data_Enable, sum_cnt, mux_sel) is
    begin  -- process Mux_Addr_DFF
      if Reset then                 -- asynchronous reset (active high)
        mux_sel_d <= std_logic_vector(to_unsigned(C_DATA_BITS-1, mux_sel'length));
      else
        if (tx_Data_Enable = '1') then
          mux_sel_d <= sum_cnt;
        else
          mux_sel_d <= mux_sel;
        end if;
      end if;
    end process Mux_Addr_Logic;

    ToVote(UART_TX_MUX_SEL_Pos) <= mux_sel_d;

    Mux_Addr_DFF : process (Clk) is
    begin
      if Clk'event and Clk = '1' then
        mux_sel <= vote(mux_sel_d, FromAVote(UART_TX_MUX_SEL_Pos), FromBVote(UART_TX_MUX_SEL_Pos), tmr_disable_b);
      end if;
    end process Mux_Addr_DFF;

    -- Detecting when mux_sel is zero ie. all data bits is transfered
    mux_sel_is_zero <= '1' when mux_sel = "000" else '0';

    -- Read out the next data from the transmit fifo when the data has been
    -- transmitted
    Data_is_Sent_Logic : process (Reset, tx_Data_Enable, mux_sel_is_zero) is
    begin
      if Reset then
        data_is_sent_d <= '0';
      else
        data_is_sent_d <= tx_Data_Enable and mux_sel_is_zero;
      end if;
    end process Data_is_Sent_Logic;

    ToVote(UART_TX_DATA_IS_SENT_Pos) <= data_is_sent_d;

    Data_is_Sent_DFF : process (Clk) is
    begin
      if Clk'event and Clk = '1' then
        data_is_sent <= vote(data_is_sent_d,
                             FromAVote(UART_TX_DATA_IS_SENT_Pos),
                             FromBVote(UART_TX_DATA_IS_SENT_Pos), tmr_disable_b);
      end if;
    end process Data_is_Sent_DFF;

    TX_Data_Transmitted <= data_is_sent;

    -----------------------------------------------------------------------------
    -- Select which bit within the data word to transmit
    -----------------------------------------------------------------------------

    -- Need special treatment for inserting the parity bit because of parity generation
    Parity_Bit_Insertion : process (parity, select_Parity, fifo_DOut) is
    begin  -- process Parity_Bit_Insertion
      data_to_transfer <= fifo_DOut;
      if (select_Parity = '1') then
        data_to_transfer(C_DATA_BITS-1) <= parity;
      end if;
    end process Parity_Bit_Insertion;

    mux_01 <= data_to_transfer(1) when mux_sel(2) = '1' else data_to_transfer(0);
    mux_23 <= data_to_transfer(3) when mux_sel(2) = '1' else data_to_transfer(2);

    Data_Bits_Is_5 : if (C_DATA_BITS = 5) generate
    begin
      mux_45 <= data_to_transfer(4);
      mux_67 <= '0';
    end generate Data_Bits_Is_5;

    Data_Bits_Is_6 : if (C_DATA_BITS = 6) generate
    begin
      mux_45 <= data_to_transfer(5) when mux_sel(2) = '1' else data_to_transfer(4);
      mux_67 <= '0';
    end generate Data_Bits_Is_6;

    Data_Bits_Is_7 : if (C_DATA_BITS = 7) generate
    begin
      mux_45 <= data_to_transfer(5) when mux_sel(2) = '1' else data_to_transfer(4);
      mux_67 <= data_to_transfer(6);
    end generate Data_Bits_Is_7;

    Data_Bits_Is_8 : if (C_DATA_BITS = 8) generate
    begin
      mux_45 <= data_to_transfer(5) when mux_sel(2) = '1' else data_to_transfer(4);
      mux_67 <= data_to_transfer(7) when mux_sel(2) = '1' else data_to_transfer(6);
    end generate Data_Bits_Is_8;

    MUX_F5_1 : MB_MUXF5
      generic map(
        C_TARGET => C_TARGET)
      port map (
        O  => mux_0123,                   -- [out std_logic]
        I0 => mux_01,                     -- [in  std_logic]
        I1 => mux_23,                     -- [in  std_logic]
        S  => mux_sel(1));                -- [in std_logic]

    MUX_F5_2 : MB_MUXF5
      generic map(
        C_TARGET => C_TARGET)
      port map (
        O  => mux_4567,                   -- [out std_logic]
        I0 => mux_45,                     -- [in  std_logic]
        I1 => mux_67,                     -- [in  std_logic]
        S  => mux_sel(1));                -- [in std_logic]

    MUXF6_I : MB_MUXF6
      generic map(
        C_TARGET => C_TARGET)
      port map (
        O  => mux_out,                    -- [out std_logic]
        I0 => mux_0123,                   -- [in  std_logic]
        I1 => mux_4567,                   -- [in  std_logic]
        S  => mux_sel(0));                -- [in std_logic]

    Serial_Data_Logic : process (Reset, mux_Out) is
    begin
      if Reset then
        serial_Data_d <= '0';
      else
        serial_Data_d <= mux_Out;
      end if;
    end process Serial_Data_Logic;

    ToVote(UART_TX_SERIAL_DATA_Pos) <= serial_Data_d;

    Serial_Data_DFF : process (Clk) is
    begin
      if Clk'event and Clk = '1' then
        serial_Data <= vote(serial_Data_d,
                            FromAVote(UART_TX_SERIAL_DATA_Pos),
                            FromBVote(UART_TX_SERIAL_DATA_Pos), tmr_disable_b);
      end if;
    end process Serial_Data_DFF;

    -----------------------------------------------------------------------------
    -- Force a '0' when tx_start is '1', Start_bit
    -- Force a '1' when tx_run is '0',   Idle
    -- otherwise put out the serial_data
    -----------------------------------------------------------------------------
    Serial_Out_Logic : process (Reset, tx_run, serial_Data, tx_Start) is
    begin
      if Reset then
        TX_d <= '1';
      else
        TX_d <= (not(tx_run) or serial_Data) and not(tx_Start);
      end if;
    end process Serial_Out_Logic;

    ToVote(UART_TX_Pos) <= TX_d;

    Serial_Out_DFF : process (Clk) is
    begin
      if Clk'event and Clk = '1' then
        tx_i <= vote(TX_d, FromAVote(UART_TX_Pos), FromBVote(UART_TX_Pos), tmr_disable_b);
      end if;
    end process Serial_Out_DFF;

    -----------------------------------------------------------------------------
    -- Parity handling
    -----------------------------------------------------------------------------
    Using_Parity : if (C_USE_PARITY = 1) generate
      signal calc_Parity_voted    : std_logic;
      signal tx_Run1_d            : std_logic;
      signal serial_Data_d        : std_logic;
    begin

      Using_Odd_Parity : if (C_ODD_PARITY = 1) generate
      begin
        Parity_Bit : MB_FDSE
          generic map(
            C_TARGET => C_TARGET,
            INIT => '1')                  -- [bit]
          port map (
            Q  => Parity,                 -- [out std_logic]
            C  => Clk,                    -- [in  std_logic]
            CE => tx_Data_Enable_voted,   -- [in  std_logic]
            D  => calc_Parity_voted,      -- [in  std_logic]
            S  => tx_Start_d);            -- [in std_logic]
      end generate Using_Odd_Parity;

      Using_Even_Parity : if (C_ODD_PARITY = 0) generate
      begin
        Parity_Bit : MB_FDRE
          generic map (
            C_TARGET => C_TARGET,
            INIT => '0')                  -- [bit]
          port map (
            Q  => Parity,                 -- [out std_logic]
            C  => Clk,                    -- [in  std_logic]
            CE => tx_Data_Enable_voted,   -- [in  std_logic]
            D  => calc_Parity_voted,      -- [in  std_logic]
            R  => tx_Start_d);            -- [in std_logic]
      end generate Using_Even_Parity;

      calc_Parity <= parity xor serial_data;

      calc_Parity_voted <= vote(calc_Parity,
                                FromAVote(UART_TX_CALC_PARITY_Pos),
                                FromBVote(UART_TX_CALC_PARITY_Pos), tmr_disable_b);

      ToVote(UART_TX_CALC_PARITY_Pos) <= calc_Parity;

      tx_Run_Logic : process (Reset, tx_Data_Enable, tx_DataBits, tx_Run1) is
      begin
        if Reset then
          tx_Run1_d <= '0';
        else
          if (tx_Data_Enable = '1') then
            tx_Run1_d <= tx_DataBits;
          else
            tx_Run1_d <= tx_Run1;
          end if;
        end if;
      end process tx_Run_Logic;

      ToVote(UART_TX_RUN_Pos) <= tx_Run1_d;

      tx_Run_DFF : process (Clk) is
      begin
        if Clk'event and Clk = '1' then
          tx_Run1 <= vote(tx_Run1_d, FromAVote(UART_TX_RUN_Pos), FromBVote(UART_TX_RUN_Pos), tmr_disable_b);
        end if;
      end process tx_Run_DFF;

      tx_Run <= tx_Run1 or tx_DataBits;

      Select_Parity_Logic: process (Reset, tx_Data_Enable, mux_sel_is_zero, select_Parity) is
      begin
        if Reset then
          select_Parity_d <= '0';
        else
          if (tx_Data_Enable = '1') then
            select_Parity_d <= mux_sel_is_zero;
          else
            select_Parity_d <= select_Parity;
          end if;
        end if;
      end process Select_Parity_Logic;

      ToVote(UART_TX_SEL_PARITY_Pos) <= select_Parity_d;

      Select_Parity_DFF : process (Clk) is
      begin
        if Clk'event and Clk = '1' then
          select_Parity <= vote(select_Parity_d,
                                FromAVote(UART_TX_SEL_PARITY_Pos),
                                FromBVote(UART_TX_SEL_PARITY_Pos), tmr_disable_b);
        end if;
      end process Select_Parity_DFF;

    end generate Using_Parity;

    No_Parity : if (C_USE_PARITY = 0) generate
    begin
      tx_Run1                         <= '0';
      calc_Parity                     <= '0';
      parity                          <= '0';
      tx_Run                          <= tx_DataBits;
      select_Parity                   <= '0';
      select_Parity_d                 <= '0';
      ToVote(UART_TX_CALC_PARITY_Pos) <= '0';
      ToVote(UART_TX_RUN_Pos)         <= '0';
      ToVote(UART_TX_SEL_PARITY_Pos)  <= '0';
    end generate No_Parity;

    Data_To_Transmit_Logic: process (Reset, Write_TX_Data, TX_Data, fifo_DOut) is
    begin
      if Reset then
        fifo_DOut_d <= (others => '0');
      elsif (Write_TX_Data = '1') then
        fifo_DOut_d <= TX_Data;
      else
        fifo_DOut_d <= fifo_DOut;
      end if;
    end process Data_To_Transmit_Logic;

    ToVote(UART_TX_FIFO_DOUT_Pos'low+fifo_DOut'length-1 downto UART_TX_FIFO_DOUT_Pos'low) <= fifo_DOut_d;

    -- Work around spyglass bug report on null range to the left but not to the right
    spy_g: if C_DATA_BITS < 8 generate
    begin
      ToVote(UART_TX_FIFO_DOUT_Pos'high downto UART_TX_FIFO_DOUT_Pos'low+fifo_DOut'length)  <= (others => '0');
    end generate spy_g;

    Data_To_Transmit_DFF: process (Clk) is
    begin
      if Clk'event and Clk = '1' then
        fifo_DOut <= vote(fifo_DOut_d,
                          FromAVote(UART_TX_FIFO_DOUT_Pos'low+fifo_DOut'length-1 downto UART_TX_FIFO_DOUT_Pos'low),
                          FromBVote(UART_TX_FIFO_DOUT_Pos'low+fifo_DOut'length-1 downto UART_TX_FIFO_DOUT_Pos'low),
                          tmr_disable_b);
      end if;
    end process Data_To_Transmit_DFF;

    TX_Reg_Status_Logic: process (Reset, Write_TX_Data, data_is_sent, tx_buffer_empty_i) is
    begin
      if Reset then
        tx_buffer_empty_i_d <= '1';
      else
        if (data_is_sent = '1') then
          tx_buffer_empty_i_d <= '1';
        elsif Write_TX_Data = '1' then
          tx_buffer_empty_i_d <= '0';
        else
          tx_buffer_empty_i_d <= tx_buffer_empty_i;
        end if;
      end if;
    end process TX_Reg_Status_Logic;

    ToVote(UART_TX_BUFFER_EMPTY_Pos) <= tx_buffer_empty_i_d;

    TX_Reg_Status_DFF: process (Clk) is
    begin
      if Clk'event and Clk = '1' then
        tx_buffer_empty_i <= vote(tx_buffer_empty_i_d,
                                  FromAVote(UART_TX_BUFFER_EMPTY_Pos),
                                  FromBVote(UART_TX_BUFFER_EMPTY_Pos), tmr_disable_b);
      end if;
    end process TX_Reg_Status_DFF;

    TX_Buffer_Empty <= tx_buffer_empty_i;

  end generate TMR_Yes;

  TX <= tx_i;

end architecture IMP;


-------------------------------------------------------------------------------
-- uart_core.vhd - Entity and architecture
-------------------------------------------------------------------------------
--
-- (c) Copyright 2011,2016 Xilinx, Inc. All rights reserved.
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
-- Filename:        uart_core.vhd
--
-- Description:
--
-- VHDL-Standard:   VHDL'93/02
-------------------------------------------------------------------------------
-- Structure:
--            uart
--              uart_core
--
-------------------------------------------------------------------------------
-- Author:          roland
--
-- History:
--   roland  2019-12-01    First Version
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

library iomodule_v3_1_6;
use iomodule_v3_1_6.iomodule_funcs.all;
use iomodule_v3_1_6.iomodule_vote_pkg.all;

entity UART_Core is
  generic (
    C_TARGET             : TARGET_FAMILY_TYPE;
    C_FREQ               : integer              := 100000000;
    C_TMR                : integer              := 0;
    C_USE_TMR_DISABLE    : integer              := 0;
    C_VOTE_SIZE          : integer              := 0;
    C_USE_SRL16          : string;
    C_UART_PROG_BAUDRATE : integer              := 0;
    C_UART_BAUDRATE      : integer              := 9600;
    C_USE_UART_RX        : integer              := 1;
    C_USE_UART_TX        : integer              := 1;
    C_UART_DATA_BITS     : integer range 5 to 8 := 8;
    C_UART_USE_PARITY    : integer              := 0;
    C_UART_ODD_PARITY    : integer              := 0);
  port (
    Clk                  : in  std_logic;
    Reset                : in  boolean;
    Config_Reset         : in  std_logic;

    TMR_Disable          : in  std_logic;
    FromAVote            : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
    FromBVote            : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
    ToVote               : out std_logic_vector(C_VOTE_SIZE-1 downto 0);

    TX                   : out std_logic;
    Write_TX_Data        : in  std_logic;
    Write_Data           : in  std_logic_vector(C_UART_DATA_BITS-1 downto 0);
    Write_Baud           : in  std_logic;
    Write_Baud_Data      : in  std_logic_vector(C_UART_PROG_CNT_SIZE-1 downto 0);

    RX                   : in  std_logic;
    Read_RX_Data         : in  std_logic;
    RX_Data_Received     : out std_logic;
    RX_Data              : out std_logic_vector(C_UART_DATA_BITS-1 downto 0);

    UART_Status_Read     : in  std_logic;
    UART_Status          : out std_logic_vector(7 downto 0);
    UART_Interrupt       : out std_logic;
    UART_Rx_Interrupt    : out std_logic;
    UART_Tx_Interrupt    : out std_logic;
    UART_Error_Interrupt : out std_logic);
end entity UART_Core;

architecture IMP of UART_Core is

  component FIT_Module is
    generic (
      C_TARGET          : TARGET_FAMILY_TYPE;
      C_TMR             : integer := 0;
      C_USE_TMR_DISABLE : integer := 0;
      C_VOTE_SIZE       : integer := 0;
      C_USE_SRL16       : string;
      C_USE_FIT         : integer;
      C_NO_CLOCKS       : integer;      -- The number of clocks between each interrupt
      C_INACCURACY      : integer);     -- The maximum inaccuracy of the number
    port (
      Config_Reset : in  std_logic;
      Clk          : in  std_logic;
      Reset        : in  boolean;
      TMR_Disable  : in  std_logic;
      FromAVote    : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
      FromBVote    : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
      ToVote       : out std_logic_vector(C_VOTE_SIZE-1 downto 0);
      Toggle       : out std_logic;
      Interrupt    : out std_logic);
  end component FIT_Module;

  component UART_Transmit is
    generic (
      C_TARGET          : TARGET_FAMILY_TYPE;
      C_TMR             : integer := 0;
      C_USE_TMR_DISABLE : integer := 0;
      C_VOTE_SIZE       : integer := 0;
      C_USE_SRL16       : string;
      C_DATA_BITS       : integer range 5 to 8;
      C_USE_PARITY      : integer;
      C_ODD_PARITY      : integer);
    port (
      Config_Reset : in std_logic;
      Clk          : in std_logic;
      Reset        : in boolean;
      EN_16x_Baud  : in std_logic;

      TMR_Disable         : in  std_logic;
      FromAVote           : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
      FromBVote           : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
      ToVote              : out std_logic_vector(C_VOTE_SIZE-1 downto 0);
      TX                  : out std_logic;
      Write_TX_Data       : in  std_logic;
      TX_Data             : in  std_logic_vector(C_UART_DATA_BITS-1 downto 0);
      TX_Data_Transmitted : out std_logic;
      TX_Buffer_Empty     : out std_logic);
  end component UART_Transmit;

  component UART_Receive is
    generic (
      C_TMR             : integer := 0;
      C_USE_TMR_DISABLE : integer := 0;
      C_VOTE_SIZE       : integer := 0;
      C_TARGET          : TARGET_FAMILY_TYPE;
      C_USE_SRL16       : string;
      C_DATA_BITS       : integer range 5 to 8;
      C_USE_PARITY      : integer;
      C_ODD_PARITY      : integer);
    port (
      Config_Reset : in std_logic;
      Clk          : in std_logic;
      Reset        : in boolean;
      EN_16x_Baud  : in std_logic;

      RX               : in  std_logic;
      Read_RX_Data     : in  std_logic;
      TMR_Disable      : in  std_logic;
      FromAVote        : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
      FromBVote        : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
      ToVote           : out std_logic_vector(C_VOTE_SIZE-1 downto 0);
      RX_Data          : out std_logic_vector(C_UART_DATA_BITS-1 downto 0);
      RX_Data_Received : out std_logic;
      RX_Data_Exists   : out std_logic;
      RX_Frame_Error   : out std_logic;
      RX_Overrun_Error : out std_logic;
      RX_Parity_Error  : out std_logic);
  end component UART_Receive;

  component Uart_Control_Status is
    generic (
      C_TMR             : integer := 0;
      C_USE_TMR_DISABLE : integer := 0;
      C_VOTE_SIZE       : integer := 0;
      C_USE_UART_RX     : integer;
      C_USE_UART_TX     : integer;
      C_UART_DATA_BITS  : integer range 5 to 8;
      C_UART_USE_PARITY : integer;
      C_UART_ODD_PARITY : integer);
    port (
      CLK   : in std_logic;
      Reset : in boolean;
      Config_Reset : in std_logic;      

      TMR_Disable : in  std_logic;
      FromAVote   : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
      FromBVote   : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
      ToVote      : out std_logic_vector(C_VOTE_SIZE-1 downto 0);

      TX_Data_Transmitted : in std_logic;
      TX_Buffer_Empty     : in std_logic;
      RX_Data_Received    : in std_logic;
      RX_Data_Exists      : in std_logic;
      RX_Frame_Error      : in std_logic;
      RX_Overrun_Error    : in std_logic;
      RX_Parity_Error     : in std_logic;

      UART_Status_Read     : in  std_logic;
      UART_Status          : out std_logic_vector(7 downto 0);
      UART_Interrupt       : out std_logic;
      UART_Rx_Interrupt    : out std_logic;
      UART_Tx_Interrupt    : out std_logic;
      UART_Error_Interrupt : out std_logic);
  end component Uart_Control_Status;

  --------------------------------------------------------------------------------------------------
  -- Calculate FIT period for generating 16*C_UART_BAUDRATE
  --------------------------------------------------------------------------------------------------
  function FIT_PERIOD (FREQ : integer; BAUDRATE : integer ) return natural is
    constant C_BAUDRATE_16_BY_2 : integer := (16 * BAUDRATE) / 2;
    constant C_REMAINDER        : integer := FREQ rem (16 * BAUDRATE);
    constant C_RATIO            : integer := FREQ / (16 * BAUDRATE);
  begin
    if (C_BAUDRATE_16_BY_2 < C_REMAINDER) then
      return (C_RATIO + 1);
    else
      return C_RATIO;
    end if;
  end function FIT_PERIOD;

  -- Enable for Divide by 16 UART clock
  signal en_16x_baud          : std_logic;

  -- TX Control
  signal tx_data_transmitted  : std_logic;
  signal tx_buffer_empty      : std_logic;

  -- RX Control
  signal rx_data_received_i   : std_logic;
  signal rx_data_exists       : std_logic;
  signal rx_frame_error       : std_logic;
  signal rx_overrun_error     : std_logic;
  signal rx_parity_error      : std_logic;

begin  -- architecture IMP

  Using_UART_TX : if (C_USE_UART_TX /= 0) generate
  begin

    UART_TX_I1 : UART_Transmit
      generic map (
        C_TARGET          => C_TARGET,
        C_TMR             => C_TMR,
        C_USE_TMR_DISABLE => C_USE_TMR_DISABLE,
        C_VOTE_SIZE       => UART_TRANSMIT_Pos'high-UART_TRANSMIT_Pos'low+1,
        C_USE_SRL16       => C_USE_SRL16,
        C_DATA_BITS       => C_UART_DATA_BITS,
        C_USE_PARITY      => C_UART_USE_PARITY,
        C_ODD_PARITY      => C_UART_ODD_PARITY)
      port map (
        Config_Reset => Config_Reset,
        Clk          => Clk,
        Reset        => Reset,
        EN_16x_Baud  => en_16x_baud,

        TMR_Disable         => TMR_Disable,
        FromAVote           => FromAVote(UART_TRANSMIT_Pos),
        FromBVote           => FromBVote(UART_TRANSMIT_Pos),
        ToVote              => ToVote(UART_TRANSMIT_Pos),
        TX                  => Tx,
        Write_TX_Data       => Write_TX_Data,
        TX_Data             => Write_Data(C_UART_DATA_BITS-1 downto 0),
        TX_Data_Transmitted => tx_data_transmitted,
        TX_Buffer_Empty     => tx_buffer_empty);
  end generate Using_UART_TX;

  No_UART_TX : if (C_USE_UART_TX = 0) generate
  begin
    tx_buffer_empty           <= '0';
    tx_data_transmitted       <= '0';
    Tx                        <= '0';
    ToVote(UART_TRANSMIT_Pos) <= (others => '0');
  end generate No_UART_TX;

  Using_UART_RX : if (C_USE_UART_RX /= 0) generate
  begin

    UART_RX_I1 : UART_Receive
      generic map (
        C_TARGET          => C_TARGET,
        C_TMR             => C_TMR,
        C_USE_TMR_DISABLE => C_USE_TMR_DISABLE,
        C_VOTE_SIZE       => UART_RECEIVE_Pos'high-UART_RECEIVE_Pos'low+1,
        C_USE_SRL16       => C_USE_SRL16,
        C_DATA_BITS       => C_UART_DATA_BITS,
        C_USE_PARITY      => C_UART_USE_PARITY,
        C_ODD_PARITY      => C_UART_ODD_PARITY)
      port map (
        Config_Reset => Config_Reset,
        Clk          => Clk,
        Reset        => Reset,
        EN_16x_Baud  => en_16x_baud,

        RX               => RX,
        Read_RX_Data     => Read_RX_Data,
        TMR_Disable      => TMR_Disable,
        FromAVote        => FromAVote(UART_RECEIVE_Pos),
        FromBVote        => FromBVote(UART_RECEIVE_Pos),
        ToVote           => ToVote(UART_RECEIVE_Pos),
        RX_Data          => RX_Data,
        RX_Data_Received => rx_data_received_i,
        RX_Data_Exists   => rx_data_exists,
        RX_Frame_Error   => rx_frame_error,
        RX_Overrun_Error => rx_overrun_error,
        RX_Parity_Error  => rx_parity_error);
  end generate Using_UART_RX;

  No_UART_RX : if (C_USE_UART_RX = 0) generate
  begin
    RX_Data                  <= (others => '0');
    rx_data_received_i       <= '0';
    rx_data_exists           <= '0';
    rx_frame_error           <= '0';
    rx_overrun_error         <= '0';
    rx_parity_error          <= '0';
    ToVote(UART_RECEIVE_Pos) <= (others => '0');
  end generate No_UART_RX;

  RX_Data_Received <= rx_data_received_i;
  
  Using_UART : if ((C_USE_UART_RX /= 0) or (C_USE_UART_TX /= 0)) generate
  begin

    No_Dynamic_BaudRate: if C_UART_PROG_BAUDRATE = 0 generate
    begin
      UART_FIT_I : FIT_Module
        generic map (
          C_TARGET          => C_TARGET,
          C_TMR             => C_TMR,
          C_USE_TMR_DISABLE => C_USE_TMR_DISABLE,
          C_VOTE_SIZE       => UART_BAUD_FIT_Pos'high-UART_BAUD_FIT_Pos'low+1,
          C_USE_SRL16       => C_USE_SRL16,
          C_USE_FIT         => 1,
          C_NO_CLOCKS       => FIT_PERIOD(C_FREQ, C_UART_BAUDRATE),
          C_INACCURACY      => 0)
        port map (
          Config_Reset => Config_Reset,
          Clk          => Clk,
          Reset        => Reset,
          TMR_Disable  => TMR_Disable,
          FromAVote    => FromAVote(UART_BAUD_FIT_Pos),
          FromBVote    => FromBVote(UART_BAUD_FIT_Pos),
          ToVote       => ToVote(UART_BAUD_FIT_Pos),
          Toggle       => open,
          Interrupt    => en_16x_baud);

      ToVote(UART_BAUD_REG_Pos)  <= (others => '0');
      ToVote(UART_BAUD_CNT_Pos)  <= (others => '0');
      ToVote(UART_BAUD_EN16_Pos) <= '0';

    end generate No_Dynamic_BaudRate;

    Programmable_BaudRate_TMR_No: if C_UART_PROG_BAUDRATE /= 0 and C_TMR = 0 generate
      signal baudrate_cnt : std_logic_vector(C_UART_PROG_CNT_SIZE-1 downto 0);
      signal baudrate_reg : std_logic_vector(C_UART_PROG_CNT_SIZE-1 downto 0);
    begin

      ToVote(UART_BAUD_FIT_Pos) <= (others => '0');

      BaudRate_Counter : process (Clk)
      begin  -- process BaudRate_Counter
        if Clk'event and Clk = '1' then  -- rising clock edge
          if Reset then                  -- synchronous reset (active high)
            baudrate_reg <=
              std_logic_vector(to_unsigned(FIT_PERIOD(C_FREQ, C_UART_BAUDRATE) - 1, baudrate_reg'length));
            baudrate_cnt <= (others => '0');
            en_16x_baud  <= '0';
          else
            en_16x_baud <= '0';
            if baudrate_cnt = "00000000000000000000" then
              baudrate_cnt <= baudrate_reg;
              en_16x_baud  <= '1';
            else
              baudrate_cnt <= std_logic_vector(unsigned(baudrate_cnt) - 1);
            end if;
            if Write_Baud = '1' then
              baudrate_reg <= Write_Baud_Data;
              baudrate_cnt <= (others => '0');
            end if;
          end if;
        end if;
      end process BaudRate_Counter;

      ToVote(UART_BAUD_REG_Pos)  <= (others => '0');
      ToVote(UART_BAUD_CNT_Pos)  <= (others => '0');
      ToVote(UART_BAUD_EN16_Pos) <= '0';

    end generate Programmable_BaudRate_TMR_No;

    Programmable_BaudRate_TMR_Yes: if C_UART_PROG_BAUDRATE /= 0 and C_TMR = 1 generate
      signal baudrate_cnt   : std_logic_vector(C_UART_PROG_CNT_SIZE-1 downto 0);
      signal baudrate_reg   : std_logic_vector(C_UART_PROG_CNT_SIZE-1 downto 0);
      signal baudrate_cnt_d : std_logic_vector(C_UART_PROG_CNT_SIZE-1 downto 0);
      signal baudrate_reg_d : std_logic_vector(C_UART_PROG_CNT_SIZE-1 downto 0);
      signal en_16x_baud_d  : std_logic;
      signal tmr_disable_b  : boolean;
    begin

      ToVote(UART_BAUD_FIT_Pos) <= (others => '0');

      tmr_disable_b <= TMR_Disable = '1' and C_USE_TMR_DISABLE = 1;

      BaudRate_Counter_Logic : process (Reset, baudrate_reg, baudrate_cnt, Write_Baud, Write_Baud_Data)
      begin
        if Reset then
          baudrate_reg_d <=
            std_logic_vector(to_unsigned(FIT_PERIOD(C_FREQ, C_UART_BAUDRATE) - 1, baudrate_reg'length));
          baudrate_cnt_d <= (others => '0');
          en_16x_baud_d  <= '0';
        else
          if baudrate_cnt = "00000000000000000000" then
            baudrate_cnt_d <= baudrate_reg;
            en_16x_baud_d  <= '1';
          else
            baudrate_cnt_d <= std_logic_vector(unsigned(baudrate_cnt) - 1);
            en_16x_baud_d  <= '0';
          end if;
          if Write_Baud = '1' then
            baudrate_reg_d <= Write_Baud_Data;
            baudrate_cnt_d <= (others => '0');
          else
            baudrate_reg_d <= baudrate_reg;
          end if;
        end if;
      end process BaudRate_Counter_Logic;

      ToVote(UART_BAUD_REG_Pos)  <= baudrate_reg_d;
      ToVote(UART_BAUD_CNT_Pos)  <= baudrate_cnt_d;
      ToVote(UART_BAUD_EN16_Pos) <= en_16x_baud_d;

      BaudRate_Counter_DFF : process (Clk)
      begin
        if Clk'event and Clk = '1' then
          baudrate_reg <= vote(baudrate_reg_d,
                               FromAVote(UART_BAUD_REG_Pos),
                               FromBVote(UART_BAUD_REG_Pos), tmr_disable_b);
          baudrate_cnt <= vote(baudrate_cnt_d,
                               FromAVote(UART_BAUD_CNT_Pos),
                               FromBVote(UART_BAUD_CNT_Pos), tmr_disable_b);
          en_16x_baud  <= vote(en_16x_baud_d,
                               FromAVote(UART_BAUD_EN16_Pos),
                               FromBVote(UART_BAUD_EN16_Pos), tmr_disable_b);
        end if;
      end process BaudRate_Counter_DFF;

    end generate Programmable_BaudRate_TMR_Yes;

    Uart_Control_Status_I1 : Uart_Control_Status
      generic map (
        C_TMR             => C_TMR,
        C_USE_TMR_DISABLE => C_USE_TMR_DISABLE,
        C_VOTE_SIZE       => UART_CONTROL_Pos'high-UART_CONTROL_Pos'low+1,
        C_USE_UART_RX     => C_USE_UART_RX,
        C_USE_UART_TX     => C_USE_UART_TX,
        C_UART_DATA_BITS  => C_UART_DATA_BITS,
        C_UART_USE_PARITY => C_UART_USE_PARITY,
        C_UART_ODD_PARITY => C_UART_ODD_PARITY)
      port map (
        CLK                  => CLK,
        Reset                => Reset,
        Config_Reset         => Config_Reset,
        TMR_Disable          => TMR_Disable,
        FromAVote            => FromAVote(UART_CONTROL_Pos),
        FromBVote            => FromBVote(UART_CONTROL_Pos),
        ToVote               => ToVote(UART_CONTROL_Pos),
        TX_Data_Transmitted  => tx_data_transmitted,
        TX_Buffer_Empty      => tx_buffer_empty,
        RX_Data_Received     => rx_data_received_i,
        RX_Data_Exists       => rx_data_exists,
        RX_Frame_Error       => rx_frame_error,
        RX_Overrun_Error     => rx_overrun_error,
        RX_Parity_Error      => rx_parity_error,
        UART_Status_Read     => UART_Status_Read,
        UART_Status          => uart_status,
        UART_Interrupt       => UART_Interrupt,
        UART_Rx_Interrupt    => UART_RX_Interrupt,
        UART_Tx_Interrupt    => UART_TX_Interrupt,
        UART_Error_Interrupt => UART_Error_Interrupt);
  end generate Using_UART;

  No_UART : if ((C_USE_UART_RX = 0) and (C_USE_UART_TX = 0)) generate
  begin
    uart_status                <= (others => '0');
    UART_Interrupt             <= '0';
    uart_rx_interrupt          <= '0';
    uart_tx_interrupt          <= '0';
    uart_error_interrupt       <= '0';
    ToVote(UART_BAUD_FIT_Pos)  <= (others => '0');
    ToVote(UART_BAUD_REG_Pos)  <= (others => '0');
    ToVote(UART_BAUD_CNT_Pos)  <= (others => '0');
    ToVote(UART_BAUD_EN16_Pos) <= '0';
    ToVote(UART_CONTROL_Pos)   <= (others => '0');
  end generate No_UART;

end architecture IMP;


-------------------------------------------------------------------------------
-- uart.vhd - Entity and architecture
-------------------------------------------------------------------------------
--
-- (c) Copyright 2011,2016 Xilinx, Inc. All rights reserved.
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
-- Filename:        uart.vhd
--
-- Description:
--
-- VHDL-Standard:   VHDL'93/02
-------------------------------------------------------------------------------
-- Structure:
--              uart.vhd
--
-------------------------------------------------------------------------------
-- Author:          roland
--
-- History:
--   roland  2019-12-01    First Version
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

library iomodule_v3_1_6;
use iomodule_v3_1_6.iomodule_funcs.all;
use iomodule_v3_1_6.iomodule_vote_pkg.all;

entity UART is
  generic (
    C_TARGET             : TARGET_FAMILY_TYPE;
    C_FREQ               : integer              := 100000000;
    C_UART_FREQ          : integer              := 100000000;
    C_TMR                : integer              := 0;
    C_USE_TMR_DISABLE    : integer              := 0;
    C_VOTE_SIZE          : integer              := 0;
    C_USE_SRL16          : string;
    C_UART_PROG_BAUDRATE : integer              := 0;
    C_UART_ASYNC         : integer              := 0;
    C_UART_NUM_SYNC_FF   : integer              := 2;
    C_UART_BAUDRATE      : integer              := 9600;
    C_USE_UART_RX        : integer              := 1;
    C_USE_UART_TX        : integer              := 1;
    C_UART_DATA_BITS     : integer range 5 to 8 := 8;
    C_UART_USE_PARITY    : integer              := 0;
    C_UART_ODD_PARITY    : integer              := 0);
  port (
    Clk                  : in std_logic;
    UART_Clk             : in std_logic;
    Reset                : in std_logic;
    Config_Reset         : in std_logic;
    Reset_UART_Clk       : in std_logic;
    
    TMR_Disable          : in  std_logic;
    FromAVote            : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
    FromBVote            : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
    ToVote               : out std_logic_vector(C_VOTE_SIZE-1 downto 0);

    TX                   : out std_logic;
    Write_TX_Data        : in  std_logic;
    Write_Baud           : in  std_logic;
    Write_Data           : in  std_logic_vector(31 downto 0);

    RX                   : in  std_logic;
    Read_RX_Data         : in  std_logic;
    Read_RX_Wait         : out std_logic;
    Read_RX_Ready        : out  std_logic;
    RX_Data              : out std_logic_vector(C_UART_DATA_BITS-1 downto 0);

    UART_Status_Read     : in  std_logic;
    UART_Status_Wait     : out std_logic;
    UART_Status_Ready    : out std_logic;
    UART_Status          : out std_logic_vector(7 downto 0);
    UART_Interrupt       : out std_logic;
    UART_Rx_Interrupt    : out std_logic;
    UART_Tx_Interrupt    : out std_logic;
    UART_Error_Interrupt : out std_logic);
end entity UART;

architecture IMP of Uart is

  component UART_Core is
  generic (
    C_TARGET             : TARGET_FAMILY_TYPE;
    C_FREQ               : integer              := 100000000;
    C_TMR                : integer              := 0;
    C_USE_TMR_DISABLE    : integer              := 0;
    C_VOTE_SIZE          : integer              := 0;
    C_USE_SRL16          : string;
    C_UART_PROG_BAUDRATE : integer              := 0;
    C_UART_BAUDRATE      : integer              := 9600;
    C_USE_UART_RX        : integer              := 1;
    C_USE_UART_TX        : integer              := 1;
    C_UART_DATA_BITS     : integer range 5 to 8 := 8;
    C_UART_USE_PARITY    : integer              := 0;
    C_UART_ODD_PARITY    : integer              := 0);
  port (
    Clk                  : in std_logic;
    Reset                : in boolean;
    Config_Reset         : in std_logic;

    TMR_Disable          : in  std_logic;
    FromAVote            : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
    FromBVote            : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
    ToVote               : out std_logic_vector(C_VOTE_SIZE-1 downto 0);

    TX                   : out std_logic;
    Write_TX_Data        : in  std_logic;
    Write_Data           : in  std_logic_vector(C_UART_DATA_BITS-1 downto 0);
    Write_Baud           : in  std_logic;
    Write_Baud_Data      : in  std_logic_vector(C_UART_PROG_CNT_SIZE-1 downto 0);

    RX                   : in  std_logic;
    Read_RX_Data         : in  std_logic;
    RX_Data_Received     : out std_logic;
    RX_Data              : out std_logic_vector(C_UART_DATA_BITS-1 downto 0);

    UART_Status_Read     : in  std_logic;
    UART_Status          : out std_logic_vector(7 downto 0);
    UART_Interrupt       : out std_logic;
    UART_Rx_Interrupt    : out std_logic;
    UART_Tx_Interrupt    : out std_logic;
    UART_Error_Interrupt : out std_logic);
  end component UART_Core;

  component mb_sync_bit is
  generic(
    C_LEVELS            : natural   := 2;
    C_RESET_VALUE       : std_logic := '0';
    C_RESET_SYNCHRONOUS : boolean   := true;
    C_RESET_ACTIVE_HIGH : boolean   := true);
  port(
    Clk            : in  std_logic;
    Rst            : in  std_logic;
    Scan_En        : in  std_logic;
    Scan_Reset_Sel : in  std_logic;
    Scan_Reset     : in  std_logic;
    Raw            : in  std_logic;
    Synced         : out std_logic);
  end component mb_sync_bit;

  component mb_sync_vec is
  generic(
    C_LEVELS            : natural   := 2;
    C_RESET_VALUE       : std_logic := '0';
    C_RESET_SYNCHRONOUS : boolean   := true;
    C_RESET_ACTIVE_HIGH : boolean   := true;
    C_WIDTH             : natural);
  port(
    Clk            : in  std_logic;
    Rst            : in  std_logic := '0';
    Scan_En        : in  std_logic;
    Scan_Reset_Sel : in  std_logic := '0';
    Scan_Reset     : in  std_logic := '0';
    Raw            : in  std_logic_vector(0 to C_WIDTH-1);
    Synced         : out std_logic_vector(0 to C_WIDTH-1));
  end component mb_sync_vec;

  component pulse_sync is
  generic(
    C_LEVELS          : natural := 2;
    C_TMR             : natural := 0;
    C_LATE_ACK        : natural := 0;
    C_USE_TMR_DISABLE : integer := 0);
  port(
    FromAVote       : in  std_logic_vector(PULSE_SYNC_Pos);
    FromBVote       : in  std_logic_vector(PULSE_SYNC_Pos);
    ToVote          : out std_logic_vector(PULSE_SYNC_Pos);

    Clk_Src         : in  std_logic;
    Clk_Dst         : in  std_logic;
    Rst_Src         : in  std_logic;
    Rst_Dst         : in  std_logic;
    TMR_Disable_Src : in  std_logic;
    TMR_Disable_Dst : in  std_logic;
    Pulse_Src       : in  std_logic;
    Pulse_Keep_Src  : out std_logic;
    Pulse_Ack_Src   : out std_logic;
    Pulse_Dst       : out std_logic);
  end component pulse_sync;

  signal reset_b  : boolean;
  signal ToVote_i : std_logic_vector(C_VOTE_SIZE-1 downto 0);

begin  -- architecture IMP

  reset_b <= Reset = '1';

  No_Async_UART: if C_UART_ASYNC = 0 generate
  begin  

    -- Not used
    ToVote_i(UART_ASYNC_Pos) <= (others => '0');
    UART_Status_Wait         <= '0';
    UART_Status_Ready        <= '0';
    Read_RX_Wait             <= '0';
    Read_RX_Ready            <= '0';
    
    UART_Core_I : UART_Core
      generic map (
        C_TARGET             => C_TARGET,
        C_FREQ               => C_FREQ,
        C_TMR                => C_TMR,
        C_USE_TMR_DISABLE    => C_USE_TMR_DISABLE,
        C_VOTE_SIZE          => UART_CORE_Pos'high-UART_CORE_Pos'low+1,
        C_USE_SRL16          => C_USE_SRL16,
        C_UART_PROG_BAUDRATE => C_UART_PROG_BAUDRATE,
        C_UART_BAUDRATE      => C_UART_BAUDRATE,
        C_USE_UART_RX        => C_USE_UART_RX,
        C_USE_UART_TX        => C_USE_UART_TX,
        C_UART_DATA_BITS     => C_UART_DATA_BITS,
        C_UART_USE_PARITY    => C_UART_USE_PARITY,
        C_UART_ODD_PARITY    => C_UART_ODD_PARITY)
      port map (
        Config_Reset         => Config_Reset,
        Clk                  => Clk,
        Reset                => reset_b,

        TMR_Disable          => TMR_Disable,
        FromAVote            => FromAVote(UART_CORE_Pos),
        FromBVote            => FromBVote(UART_CORE_Pos),
        ToVote               => ToVote_i(UART_CORE_Pos),

        TX                   => TX,
        Write_TX_Data        => Write_TX_Data,
        Write_Data           => Write_Data(C_UART_DATA_BITS-1 downto 0),
        Write_Baud           => Write_Baud,
        Write_Baud_Data      => Write_Data(C_UART_PROG_CNT_SIZE-1 downto 0),
        
        RX                   => RX,
        Read_RX_Data         => Read_RX_Data,
        RX_Data_Received     => open,
        RX_Data              => RX_Data,
        
        UART_Status_Read     => UART_Status_Read,
        UART_Status          => UART_Status,
        UART_Interrupt       => UART_Interrupt,
        UART_Rx_Interrupt    => UART_Rx_Interrupt,
        UART_Tx_Interrupt    => UART_Tx_Interrupt,
        UART_Error_Interrupt => UART_Error_Interrupt);

  end generate No_Async_UART;

  Async_UART: if C_UART_ASYNC = 1 generate
    signal reset_std                         : std_logic;
    signal reset_uart_clk_b                  : boolean;
    signal tmr_disable_b                     : boolean;
    signal tmr_disable_raw_uart_clk          : std_logic;
    signal tmr_disable_uart_clk              : std_logic;
    signal write_tx_data_uart_clk            : std_logic;
    signal write_data_clk                    : std_logic_vector(C_UART_DATA_BITS-1 downto 0);
    signal write_data_clkD                   : std_logic_vector(C_UART_DATA_BITS-1 downto 0);
    signal write_baud_uart_clk               : std_logic;
    signal baud_data_clk                     : std_logic_vector(C_UART_PROG_CNT_SIZE-1 downto 0);
    signal baud_data_clkD                    : std_logic_vector(C_UART_PROG_CNT_SIZE-1 downto 0);
    signal read_rx_uart_clk                  : std_logic;
    signal read_rx_uart_clkQ                 : std_logic;
    signal read_rx_ack_clk                   : std_logic;
    signal read_rx_ack_clkQ                  : std_logic;
    signal read_rx_keep                      : std_logic;
    signal read_rx_pulse_tovote_clk          : std_logic;
    signal read_rx_pulse_voted_clk           : std_logic;
    signal rx_data_tovote_uart_clk           : std_logic_vector(C_UART_DATA_BITS-1 downto 0);
    signal rx_data_voted_uart_clk            : std_logic_vector(C_UART_DATA_BITS-1 downto 0);
    signal rx_data_uart_clk                  : std_logic_vector(C_UART_DATA_BITS-1 downto 0);
    signal rx_data_received_uart_clk         : std_logic;
    signal rx_data_received_clk              : std_logic;
    signal uart_status_read_uart_clk         : std_logic; -- 1 cycle read pulse in UART_Clk region
    signal uart_status_read_uart_clkQ        : std_logic; -- 1 cycle read pulse in UART_Clk region
    signal uart_status_read_tovote_uart_clk  : std_logic; -- 1 cycle read pulse in UART_Clk region
    signal uart_status_read_voted_uart_clk   : std_logic; -- 1 cycle read pulse in UART_Clk region
    signal uart_status_read_ack_clk          : std_logic;
    signal uart_status_read_ack_clkQ         : std_logic;
    signal uart_status_read_keep             : std_logic;
    signal uart_status_read_pulse_tovote_clk : std_logic;
    signal uart_status_read_pulse_voted_clk  : std_logic;
    signal uart_status_uart_clk              : std_logic_vector(7 downto 0);
    signal uart_status_tovote_uart_clk       : std_logic_vector(7 downto 0);
    signal uart_status_voted_uart_clk        : std_logic_vector(7 downto 0);
    signal uart_rx_interrupt_uart_clk        : std_logic;
    signal uart_rx_interrupt_clk             : std_logic;
    signal uart_tx_interrupt_uart_clk        : std_logic;
    signal uart_tx_interrupt_clk             : std_logic;
    signal uart_error_interrupt_uart_clk     : std_logic;
    signal uart_error_interrupt_clk          : std_logic;
  begin

    TMR_Yes : if (C_TMR /= 0) generate

      Use_TMR_Disable: if C_USE_TMR_DISABLE = 1 generate
      begin
        
        TMR_Disable_Sync_I: mb_sync_bit
        generic map(
          C_LEVELS            => C_UART_NUM_SYNC_FF,
          C_RESET_VALUE       => '1',
          C_RESET_SYNCHRONOUS => true,
          C_RESET_ACTIVE_HIGH => true)
        port map(
          Clk            => UART_Clk,
          Rst            => Reset_UART_Clk,
          Scan_En        => '0',
          Scan_Reset_Sel => '0',
          Scan_Reset     => '0',
          Raw            => TMR_Disable,
          Synced         => tmr_disable_raw_uart_clk);

        TMR_Disable_UART_Clk_DFF : process (UART_Clk) is
        begin
          if UART_Clk'event and UART_Clk = '1' then
            tmr_disable_uart_clk <= vote(tmr_disable_raw_uart_clk,
                                         FromAVote(TMR_DISABLE_UART_CLK_Pos),
                                         FromBVote(TMR_DISABLE_UART_CLK_Pos),
                                         false);
          end if;
        end process TMR_Disable_UART_Clk_DFF;

        ToVote_i(TMR_DISABLE_UART_Clk_Pos) <= tmr_disable_raw_uart_clk;
        
        tmr_disable_b          <= TMR_Disable = '1';
        
      end generate Use_TMR_Disable;

      No_Use_TMR_Disable: if C_USE_TMR_DISABLE = 0 generate
      begin
        tmr_disable_raw_uart_clk           <= '0';
        tmr_disable_uart_clk               <= '0';
        tmr_disable_b                      <= false;
        ToVote_i(TMR_DISABLE_UART_Clk_Pos) <= '0';
      end generate No_Use_TMR_Disable;

    end generate TMR_Yes; 

    TMR_No : if (C_TMR = 0) generate
    begin
      tmr_disable_raw_uart_clk           <= '0';
      tmr_disable_uart_clk               <= '0';
      tmr_disable_b                      <= false;
      ToVote_i(TMR_DISABLE_UART_Clk_Pos) <= '0';
    end generate TMR_No; 

    reset_uart_clk_b <= Reset_UART_Clk = '1';

    UART_Core_I : UART_Core
      generic map (
        C_TARGET             => C_TARGET,
        C_FREQ               => C_UART_FREQ,
        C_TMR                => C_TMR,
        C_USE_TMR_DISABLE    => C_USE_TMR_DISABLE,
        C_VOTE_SIZE          => UART_CORE_Pos'high-UART_CORE_Pos'low+1,
        C_USE_SRL16          => C_USE_SRL16,
        C_UART_PROG_BAUDRATE => C_UART_PROG_BAUDRATE,
        C_UART_BAUDRATE      => C_UART_BAUDRATE,
        C_USE_UART_RX        => C_USE_UART_RX,
        C_USE_UART_TX        => C_USE_UART_TX,
        C_UART_DATA_BITS     => C_UART_DATA_BITS,
        C_UART_USE_PARITY    => C_UART_USE_PARITY,
        C_UART_ODD_PARITY    => C_UART_ODD_PARITY)
      port map (
        Config_Reset         => Reset_UART_Clk,
        Clk                  => UART_Clk,
        Reset                => reset_uart_clk_b,

        TMR_Disable          => tmr_disable_uart_clk,
        FromAVote            => FromAVote(UART_CORE_Pos),
        FromBVote            => FromBVote(UART_CORE_Pos),
        ToVote               => ToVote_i(UART_CORE_Pos),

        TX                   => TX,   -- In UART_Clk domain
        Write_TX_Data        => write_tx_data_uart_clk,
        Write_Data           => write_data_clk, -- Stable when write_tx_data_uart_clk is asserted
        Write_Baud           => write_baud_uart_clk,
        Write_Baud_Data      => baud_data_clk, -- Stable when write_baud_uart_clk is asserted

        RX                   => RX,   -- In UART_Clk domain
        Read_RX_Data         => read_rx_uart_clk,
        RX_Data_Received     => rx_data_received_uart_clk,
        RX_Data              => rx_data_uart_clk,
        
        UART_Status_Read     => uart_status_read_uart_clk,
        UART_Status          => uart_status_uart_clk,
        UART_Interrupt       => open,
        UART_Rx_Interrupt    => uart_rx_interrupt_uart_clk,
        UART_Tx_Interrupt    => uart_tx_interrupt_uart_clk,
        UART_Error_Interrupt => uart_error_interrupt_uart_clk);

    Write_TX_Data_Sync: pulse_sync
    generic map(
      C_LEVELS          => C_UART_NUM_SYNC_FF,
      C_TMR             => C_TMR,
      C_LATE_ACK        => 0,
      C_USE_TMR_DISABLE => C_USE_TMR_DISABLE)
    port map(
      FromAVote       => FromAVote(WRITE_TX_DATA_POS),
      FromBVote       => FromBVote(WRITE_TX_DATA_POS),
      ToVote          => ToVote_i(WRITE_TX_DATA_POS),
      Clk_Src         => Clk,
      Clk_Dst         => UART_Clk,
      Rst_Src         => Reset,
      Rst_Dst         => Reset_UART_Clk,
      TMR_Disable_Src => TMR_Disable,
      TMR_Disable_Dst => tmr_disable_uart_clk,
      Pulse_Src       => Write_TX_Data,
      Pulse_Keep_Src  => open,
      Pulse_Ack_Src   => open,
      Pulse_Dst       => write_tx_data_uart_clk);

    Write_Data_P : process(Reset, Write_TX_Data, Write_Data, write_data_clk) is
    begin
      if Reset = '1' then
        write_data_clkD <= (others => '0');
      elsif Write_TX_Data = '1' then
        write_data_clkD <= Write_Data(C_UART_DATA_BITS-1 downto 0);
      else
        write_data_clkD <= write_data_clk;
      end if;
    end process Write_Data_P;

    ToVote_i(WRITE_DATA_Pos'low+write_data_clkD'length-1 downto WRITE_DATA_Pos'low) <= write_data_clkD;

    -- Work around spyglass bug report on null range to the left but not to the right
    spy1_g: if C_UART_DATA_BITS < 8 generate
    begin
      ToVote_i(WRITE_DATA_Pos'high downto WRITE_DATA_Pos'low+write_data_clkD'length)  <= (others => '0');
    end generate spy1_g;
    
    Write_Data_DFF : process (Clk)
    begin
      if Clk'event and Clk = '1' then
        write_data_clk <= vote(write_data_clkD,
                               FromAVote(WRITE_DATA_Pos),
                               FromBVote(WRITE_DATA_Pos),
                               tmr_disable_b, C_TMR);
      end if;
    end process Write_Data_DFF;
    
    Write_Baud_Sync: pulse_sync
    generic map(
      C_LEVELS          => C_UART_NUM_SYNC_FF,
      C_TMR             => C_TMR,
      C_LATE_ACK        => 0,
      C_USE_TMR_DISABLE => C_USE_TMR_DISABLE)
    port map(
      FromAVote       => FromAVote(WRITE_BAUD_Pos),
      FromBVote       => FromBVote(WRITE_BAUD_Pos),
      ToVote          => ToVote_i(WRITE_BAUD_Pos),
      Clk_Src         => Clk,
      Clk_Dst         => UART_Clk,
      Rst_Src         => Reset,
      Rst_Dst         => Reset_UART_Clk,
      TMR_Disable_Src => TMR_Disable,
      TMR_Disable_Dst => tmr_disable_uart_clk,
      Pulse_Src       => Write_Baud,
      Pulse_Keep_Src  => open,
      Pulse_Ack_Src   => open,
      Pulse_Dst       => write_baud_uart_clk);

    Baud_Data_P : process(Reset, Write_Baud, Write_Data, baud_data_clk) is
    begin
      if Reset = '1' then
        baud_data_clkD <= (others => '0');
      elsif Write_Baud = '1' then
        baud_data_clkD <= Write_Data(C_UART_PROG_CNT_SIZE-1 downto 0);
      else
        baud_data_clkD <= baud_data_clk;
      end if;
    end process Baud_Data_P;

    ToVote_i(BAUD_DATA_Pos) <= baud_data_clkD;
    
    TX_Baud_Data_DFF : process (Clk)
    begin
      if Clk'event and Clk = '1' then
        baud_data_clk <= vote(baud_data_clkD,
                              FromAVote(BAUD_DATA_Pos),
                              FromBVote(BAUD_DATA_Pos),
                              tmr_disable_b, C_TMR);
      end if;
    end process TX_Baud_Data_DFF;
    
    RX_Data_Received_Sync: pulse_sync
    generic map(
      C_LEVELS          => C_UART_NUM_SYNC_FF,
      C_TMR             => C_TMR,
      C_LATE_ACK        => 0,
      C_USE_TMR_DISABLE => C_USE_TMR_DISABLE)
    port map(
      FromAVote       => FromAVote(RX_DATA_RECEIVED_Pos),
      FromBVote       => FromBVote(RX_DATA_RECEIVED_Pos),
      ToVote          => ToVote_i(RX_DATA_RECEIVED_Pos),
      Clk_Src         => UART_Clk,
      Clk_Dst         => Clk,
      Rst_Src         => Reset_UART_Clk,
      Rst_Dst         => Reset,
      TMR_Disable_Src => tmr_disable_uart_clk,
      TMR_Disable_Dst => TMR_Disable,
      Pulse_Src       => rx_data_received_uart_clk,
      Pulse_Keep_Src  => open,
      Pulse_Ack_Src   => open,
      Pulse_Dst       => rx_data_received_clk);

    Read_RX_Data_Sync: pulse_sync
    generic map(
      C_LEVELS          => C_UART_NUM_SYNC_FF,
      C_TMR             => C_TMR,
      C_LATE_ACK        => 1,
      C_USE_TMR_DISABLE => C_USE_TMR_DISABLE)
    port map(
      FromAVote       => FromAVote(READ_RX_DATA_Pos),
      FromBVote       => FromBVote(READ_RX_DATA_Pos),
      ToVote          => ToVote_i(READ_RX_DATA_Pos),
      Clk_Src         => Clk,
      Clk_Dst         => UART_Clk,
      Rst_Src         => Reset,
      Rst_Dst         => Reset_UART_Clk,
      TMR_Disable_Src => TMR_Disable,
      TMR_Disable_Dst => tmr_disable_uart_clk,
      Pulse_Src       => Read_RX_Data,
      Pulse_Keep_Src  => read_rx_keep,
      Pulse_Ack_Src   => read_rx_ack_clk,
      Pulse_Dst       => read_rx_uart_clk);

    -- Create Read RX Data pulse on returning acknowledged read
    Read_RX_Ack_DFF : process (Clk)
    begin
      if Clk'event and Clk = '1' then
        if Reset = '1' then
          read_rx_ack_clkQ <= '0';
        else
          read_rx_ack_clkQ <= read_rx_ack_clk;
        end if;
      end if;
    end process Read_RX_Ack_DFF;

    -- Vote to handle any misalignment when synchronizing in the different TMR instances
    read_rx_pulse_tovote_clk <= '1' when read_rx_ack_clk  = '0' and
                                         read_rx_ack_clkQ = '1' else
                                         '0';
    
    ToVote_i(READ_RX_PULSE_Pos) <= read_rx_pulse_tovote_clk;

    Read_RX_Pulse_DFF : process (Clk)
    begin
      if Clk'event and Clk = '1' then
        if Reset = '1' then
          read_rx_pulse_voted_clk <= '0';
        else
          read_rx_pulse_voted_clk <= vote(read_rx_pulse_tovote_clk,
                                          FromAVote(READ_RX_PULSE_Pos),
                                          FromBVote(READ_RX_PULSE_Pos),
                                          tmr_disable_b, C_TMR);
        end if;
      end if;
    end process Read_RX_Pulse_DFF;

    Read_RX_DFF : process (UART_Clk)
    begin
      if UART_Clk'event and UART_Clk = '1' then
        if Reset_UART_Clk = '1' then
          read_rx_uart_clkQ <= '0';
        else
          read_rx_uart_clkQ <= read_rx_uart_clk;
        end if;
      end if;
    end process Read_RX_DFF;
    
    RX_Data_Logic : process (Reset_UART_Clk, read_rx_uart_clkQ, rx_data_uart_clk, rx_data_voted_uart_clk)
    begin
      if Reset_UART_Clk = '1' then
        rx_data_tovote_uart_clk <= (others => '0');
      elsif read_rx_uart_clkQ = '1' then
        rx_data_tovote_uart_clk <= rx_data_uart_clk;
      else
        rx_data_tovote_uart_clk <= rx_data_voted_uart_clk;
      end if;
    end process RX_Data_Logic;
    
   ToVote_i(RX_DATA_Pos'low+rx_data_tovote_uart_clk'length-1 downto RX_DATA_Pos'low) <= rx_data_tovote_uart_clk;

    -- Work around spyglass bug report on null range to the left but not to the right
    spy2_g: if C_UART_DATA_BITS < 8 generate
    begin
      ToVote_i(RX_DATA_Pos'high downto RX_DATA_Pos'low+rx_data_tovote_uart_clk'length)  <= (others => '0');
    end generate spy2_g;
    
    RX_Data_DFF : process (UART_Clk)
    begin
      if UART_Clk'event and UART_Clk = '1' then
        -- Stable in Clk region due to system events (sync of UART Status Read)
        rx_data_voted_uart_clk <= vote(rx_data_tovote_uart_clk,
                                       FromAVote(RX_DATA_Pos),
                                       FromBVote(RX_DATA_Pos),
                                       tmr_disable_b, C_TMR);
      end if;
    end process RX_Data_DFF;

    RX_Data <= rx_data_voted_uart_clk when read_rx_pulse_voted_clk = '1' else
               (others => '0');

    Read_RX_Wait  <= read_rx_keep or read_rx_ack_clkQ;
    Read_RX_Ready <= read_rx_pulse_voted_clk;

    UART_Status_Read_Sync: pulse_sync
    generic map(
      C_LEVELS          => C_UART_NUM_SYNC_FF,
      C_TMR             => C_TMR,
      C_LATE_ACK        => 1,
      C_USE_TMR_DISABLE => C_USE_TMR_DISABLE)
    port map(
      FromAVote       => FromAVote(UART_STATUS_READ_Pos),
      FromBVote       => FromBVote(UART_STATUS_READ_Pos),
      ToVote          => ToVote_i(UART_STATUS_READ_Pos),
      Clk_Src         => Clk,
      Clk_Dst         => UART_Clk,
      Rst_Src         => Reset,
      Rst_Dst         => Reset_UART_Clk,
      TMR_Disable_Src => TMR_Disable,
      TMR_Disable_Dst => tmr_disable_uart_clk,
      Pulse_Src       => UART_Status_Read,
      Pulse_Keep_Src  => uart_status_read_keep,
      Pulse_Ack_Src   => uart_status_read_ack_clk,
      Pulse_Dst       => uart_status_read_uart_clk);

    -- Create Read UART Status pulse on returning acknowledged read
    UART_Status_Read_Ack_DFF : process (Clk)
    begin
      if Clk'event and Clk = '1' then
        if Reset = '1' then
          uart_status_read_ack_clkQ <= '0';
        else
          uart_status_read_ack_clkQ <= uart_status_read_ack_clk;
        end if;
      end if;
    end process UART_Status_Read_Ack_DFF;
      
    -- Vote to handle any misalignment when synchronizing in the different TMR instances
    uart_status_read_pulse_tovote_clk <= '1' when uart_status_read_ack_clk  = '0' and
                                                  uart_status_read_ack_clkQ = '1' else
                                         '0';

    ToVote_i(UART_STATUS_READ_PULSE_Pos) <= uart_status_read_pulse_tovote_clk;
    
    UART_Status_Read_Pulse_DFF : process (Clk)
    begin
      if Clk'event and Clk = '1' then
        if Reset = '1' then
          uart_status_read_pulse_voted_clk <= '0';
        else
          uart_status_read_pulse_voted_clk <= vote(uart_status_read_pulse_tovote_clk,
                                                   FromAVote(UART_STATUS_READ_PULSE_Pos),
                                                   FromBVote(UART_STATUS_READ_PULSE_Pos),
                                                   tmr_disable_b, C_TMR);
        end if;
      end if;
    end process UART_Status_Read_Pulse_DFF;

    UART_Status_Read_DFF : process (UART_Clk)
    begin
      if UART_Clk'event and UART_Clk = '1' then
        if Reset_UART_Clk = '1' then
          uart_status_read_uart_clkQ <= '0';
        else
          uart_status_read_uart_clkQ <= uart_status_read_uart_clk;
        end if;
      end if;
    end process UART_Status_Read_DFF;

    UART_Status_Logic : process (Reset_UART_Clk, uart_status_read_uart_clkQ, uart_status_uart_clk, uart_status_voted_uart_clk)
    begin
      if Reset_UART_Clk = '1' then
        uart_status_tovote_uart_clk <= (others => '0');
      elsif uart_status_read_uart_clkQ = '1' then
        uart_status_tovote_uart_clk <= uart_status_uart_clk;
      else
        uart_status_tovote_uart_clk <= uart_status_voted_uart_clk;
      end if;
    end process UART_Status_Logic;

    ToVote_i(UART_STATUS_Pos) <= uart_status_tovote_uart_clk;
    
    UART_Status_DFF : process (UART_Clk)
    begin
      if UART_Clk'event and UART_Clk = '1' then
        -- Stable in Clk region due to system events (sync of UART Status Read)
        uart_status_voted_uart_clk <= vote(uart_status_tovote_uart_clk,
                                           FromAVote(UART_STATUS_Pos),
                                           FromBVote(UART_STATUS_Pos),
                                           tmr_disable_b, C_TMR);
      end if;
    end process UART_Status_DFF;

    UART_Status <= uart_status_voted_uart_clk when uart_status_read_pulse_voted_clk = '1' else
                   (others => '0');

    UART_Status_Wait  <= uart_status_read_keep or uart_status_read_ack_clkQ;
    UART_Status_Ready <= uart_status_read_pulse_voted_clk;
    
    UART_RX_Sync: pulse_sync
    generic map(
      C_LEVELS          => C_UART_NUM_SYNC_FF,
      C_TMR             => C_TMR,
      C_LATE_ACK        => 0,
      C_USE_TMR_DISABLE => C_USE_TMR_DISABLE)
    port map(
      FromAVote       => FromAVote(UART_RX_INTERRUPT_Pos),
      FromBVote       => FromBVote(UART_RX_INTERRUPT_Pos),
      ToVote          => ToVote_i(UART_RX_INTERRUPT_Pos),
      Clk_Src         => UART_Clk,
      Clk_Dst         => Clk,
      Rst_Src         => Reset_UART_Clk,
      Rst_Dst         => Reset,
      TMR_Disable_Src => tmr_disable_uart_clk,
      TMR_Disable_Dst => TMR_Disable,
      Pulse_Src       => uart_rx_interrupt_uart_clk,
      Pulse_Keep_Src  => open,
      Pulse_Ack_Src   => open,
      Pulse_Dst       => uart_rx_interrupt_clk);

    UART_TX_Sync: pulse_sync
    generic map(
      C_LEVELS          => C_UART_NUM_SYNC_FF,
      C_TMR             => C_TMR,
      C_LATE_ACK        => 0,
      C_USE_TMR_DISABLE => C_USE_TMR_DISABLE)
    port map(
      FromAVote       => FromAVote(UART_TX_INTERRUPT_Pos),
      FromBVote       => FromBVote(UART_TX_INTERRUPT_Pos),
      ToVote          => ToVote_i(UART_TX_INTERRUPT_Pos),
      Clk_Src         => UART_Clk,
      Clk_Dst         => Clk,
      Rst_Src         => Reset_UART_Clk,
      Rst_Dst         => Reset,
      TMR_Disable_Src => tmr_disable_uart_clk,
      TMR_Disable_Dst => TMR_Disable,
      Pulse_Src       => uart_tx_interrupt_uart_clk,
      Pulse_Keep_Src  => open,
      Pulse_Ack_Src   => open,
      Pulse_Dst       => uart_tx_interrupt_clk);

    Error_Sync: pulse_sync
    generic map(
      C_LEVELS          => C_UART_NUM_SYNC_FF,
      C_TMR             => C_TMR,
      C_LATE_ACK        => 0,
      C_USE_TMR_DISABLE => C_USE_TMR_DISABLE)
    port map(
      FromAVote       => FromAVote(UART_ERROR_INTERRUPT_Pos),
      FromBVote       => FromBVote(UART_ERROR_INTERRUPT_Pos),
      ToVote          => ToVote_i(UART_ERROR_INTERRUPT_Pos),
      Clk_Src         => UART_Clk,
      Clk_Dst         => Clk,
      Rst_Src         => Reset_UART_Clk,
      Rst_Dst         => Reset,
      TMR_Disable_Src => tmr_disable_uart_clk,
      TMR_Disable_Dst => TMR_Disable,
      Pulse_Src       => uart_error_interrupt_uart_clk,
      Pulse_Keep_Src  => open,
      Pulse_Ack_Src   => open,
      Pulse_Dst       => uart_error_interrupt_clk);

   UART_Rx_Interrupt    <= uart_rx_interrupt_clk;
   UART_Tx_Interrupt    <= uart_tx_interrupt_clk;
   UART_Error_Interrupt <= uart_error_interrupt_clk;
    
   UART_Interrupt  <= uart_rx_interrupt_clk or uart_tx_interrupt_clk or uart_error_interrupt_clk;

  end generate Async_UART;

  
  TMR_Yes : if (C_TMR = 1) generate
    ToVote <= ToVote_i;
  end generate TMR_Yes; 

  TMR_No : if (C_TMR = 0) generate
    ToVote <= (others => '0');
  end generate TMR_No; 

end architecture IMP;


-------------------------------------------------------------------------------
-- iomodule_core.vhd - Entity and architecture
-------------------------------------------------------------------------------
--
-- (c) Copyright 2011-2012,2016,2018 Xilinx, Inc. All rights reserved.
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
-- Filename:        iomodule_core.vhd
--
-- Description:
--
-- VHDL-Standard:   VHDL'93/02
-------------------------------------------------------------------------------
-- Structure:
--              iomodule_core.vhd
--
-------------------------------------------------------------------------------
-- Author:          goran
--
-- History:
--   goran   2007-12-18    First Version
--   stefana 2012-03-20    Added GPI interrupt
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
--      pipelined or register delay signals:    "*_d#" cx
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
library iomodule_v3_1_6;
use iomodule_v3_1_6.iomodule_funcs.all;

entity Iomodule_core is

  generic (
    C_TARGET               : TARGET_FAMILY_TYPE;
    C_FREQ                 : integer               := 100000000;
    C_USE_CONFIG_RESET     : integer               := 0;
    C_AVOID_PRIMITIVES     : integer               := 0;
    C_TMR                  : integer               := 0;
    C_USE_TMR_DISABLE      : integer               := 0;

    -- UART generics
    C_USE_UART_RX          : integer               := 0;
    C_USE_UART_TX          : integer               := 0;
    C_UART_BAUDRATE        : integer               := 9600;
    C_UART_DATA_BITS       : integer range 5 to 8  := 8;
    C_UART_USE_PARITY      : integer               := 0;
    C_UART_ODD_PARITY      : integer               := 0;
    C_UART_RX_INTERRUPT    : integer               := 0;
    C_UART_TX_INTERRUPT    : integer               := 0;
    C_UART_ERROR_INTERRUPT : integer               := 0;
    C_UART_PROG_BAUDRATE   : integer               := 0;
    C_UART_FREQ            : integer               := 100000000;
    C_UART_ASYNC           : integer               := 0;
    C_UART_NUM_SYNC_FF     : integer               := 2;

    -- FIT generics
    C_USE_FIT1             : integer               := 0;
    C_FIT1_No_CLOCKS       : integer               := 1000;
    C_FIT1_INTERRUPT       : integer               := 0;
    C_USE_FIT2             : integer               := 0;
    C_FIT2_No_CLOCKS       : integer               := 1000;
    C_FIT2_INTERRUPT       : integer               := 0;
    C_USE_FIT3             : integer               := 0;
    C_FIT3_No_CLOCKS       : integer               := 1000;
    C_FIT3_INTERRUPT       : integer               := 0;
    C_USE_FIT4             : integer               := 0;
    C_FIT4_No_CLOCKS       : integer               := 1000;
    C_FIT4_INTERRUPT       : integer               := 0;

    -- PIT generics
    C_USE_PIT1       : integer               := 0;
    C_PIT1_SIZE      : integer               := 32;
    C_PIT1_READABLE  : integer               := 1;
    C_PIT1_PRESCALER : integer range 0 to 9  := 0;
    C_PIT1_INTERRUPT : integer               := 0;
    C_USE_PIT2       : integer               := 0;
    C_PIT2_SIZE      : integer               := 32;
    C_PIT2_READABLE  : integer               := 1;
    C_PIT2_PRESCALER : integer range 0 to 9  := 0;
    C_PIT2_INTERRUPT : integer               := 0;
    C_USE_PIT3       : integer               := 0;
    C_PIT3_SIZE      : integer               := 32;
    C_PIT3_READABLE  : integer               := 1;
    C_PIT3_PRESCALER : integer range 0 to 9  := 0;
    C_PIT3_INTERRUPT : integer               := 0;
    C_USE_PIT4       : integer               := 0;
    C_PIT4_SIZE      : integer               := 32;
    C_PIT4_READABLE  : integer               := 1;
    C_PIT4_PRESCALER : integer range 0 to 9  := 0;
    C_PIT4_INTERRUPT : integer               := 0;

    -- GPO Generics
    C_USE_GPO1  : integer := 0;
    C_GPO1_SIZE : integer range 1 to 32 := 32;
    C_GPO1_INIT : std_logic_vector(31 downto 0) := (others => '0');
    C_USE_GPO2  : integer := 0;
    C_GPO2_SIZE : integer range 1 to 32 := 32;
    C_GPO2_INIT : std_logic_vector(31 downto 0) := (others => '0');
    C_USE_GPO3  : integer := 0;
    C_GPO3_SIZE : integer range 1 to 32 := 32;
    C_GPO3_INIT : std_logic_vector(31 downto 0) := (others => '0');
    C_USE_GPO4  : integer := 0;
    C_GPO4_SIZE : integer range 1 to 32 := 32;
    C_GPO4_INIT : std_logic_vector(31 downto 0) := (others => '0');

    -- GPI Generics
    C_USE_GPI1       : integer := 0;
    C_GPI1_SIZE      : integer range 1 to 32 := 32;
    C_GPI1_INTERRUPT : integer               := 0;
    C_USE_GPI2       : integer := 0;
    C_GPI2_SIZE      : integer range 1 to 32 := 32;
    C_GPI2_INTERRUPT : integer               := 0;
    C_USE_GPI3       : integer := 0;
    C_GPI3_SIZE      : integer range 1 to 32 := 32;
    C_GPI3_INTERRUPT : integer               := 0;
    C_USE_GPI4       : integer := 0;
    C_GPI4_SIZE      : integer range 1 to 32 := 32;
    C_GPI4_INTERRUPT : integer               := 0;

    -- Interrupt Handler Generics
    C_ADDR_WIDTH        : integer range 32 to 64    := 32;
    C_INTC_USE_EXT_INTR : integer                   := 0;
    C_INTC_INTR_SIZE    : integer range 1 to 16     := 1;
    C_INTC_LEVEL_EDGE   : std_logic_vector(15 downto 0) := X"0000";
    C_INTC_POSITIVE     : std_logic_vector(15 downto 0) := X"0000";
    C_INTC_HAS_FAST     : integer range 0 to 1      := 0;
    C_INTC_ADDR_WIDTH   : integer range 5 to 64     := 32;
    C_INTC_BASE_VECTORS : std_logic_vector(63 downto 0) := X"0000000000000000";
    C_INTC_ASYNC_INTR   : std_logic_vector(15 downto 0) := X"FFFF";
    C_INTC_NUM_SYNC_FF  : integer range 0 to 7      := 2
    );

  port (
    Config_Reset : in std_logic := '0';
    CLK          : in std_logic;
    Rst          : in std_logic;
    TMR_Rst      : in std_logic;
    TMR_Disable  : in std_logic;

    -- TMR voting inbetween redundant IO Modules
    ToVote       : out std_logic_vector(1023 downto 0);
    FromAVote    : in  std_logic_vector(1023 downto 0);
    FromBVote    : in  std_logic_vector(1023 downto 0);

    -- UART I/O
    UART_Clk       : in std_logic;
    UART_Rst       : in std_logic;
    UART_Rx        : in  std_logic;
    UART_Tx        : out std_logic;
    UART_Interrupt : out std_logic;

    -- FIT I/O
    FIT1_Interrupt : out std_logic;
    FIT1_Toggle    : out std_logic;
    FIT2_Interrupt : out std_logic;
    FIT2_Toggle    : out std_logic;
    FIT3_Interrupt : out std_logic;
    FIT3_Toggle    : out std_logic;
    FIT4_Interrupt : out std_logic;
    FIT4_Toggle    : out std_logic;

    -- PIT I/O
    PIT1_Enable    : in  std_logic;
    PIT1_Interrupt : out std_logic;
    PIT1_Toggle    : out std_logic;
    PIT2_Enable    : in  std_logic;
    PIT2_Interrupt : out std_logic;
    PIT2_Toggle    : out std_logic;
    PIT3_Enable    : in  std_logic;
    PIT3_Interrupt : out std_logic;
    PIT3_Toggle    : out std_logic;
    PIT4_Enable    : in  std_logic;
    PIT4_Interrupt : out std_logic;
    PIT4_Toggle    : out std_logic;

    -- GPO IO
    GPO1 : out std_logic_vector(C_GPO1_SIZE-1 downto 0);
    GPO2 : out std_logic_vector(C_GPO2_SIZE-1 downto 0);
    GPO3 : out std_logic_vector(C_GPO3_SIZE-1 downto 0);
    GPO4 : out std_logic_vector(C_GPO4_SIZE-1 downto 0);

    -- GPI IO
    GPI1           : in  std_logic_vector(C_GPI1_SIZE-1 downto 0);
    GPI1_Interrupt : out std_logic;
    GPI2           : in  std_logic_vector(C_GPI2_SIZE-1 downto 0);
    GPI2_Interrupt : out std_logic;
    GPI3           : in  std_logic_vector(C_GPI3_SIZE-1 downto 0);
    GPI3_Interrupt : out std_logic;
    GPI4           : in  std_logic_vector(C_GPI4_SIZE-1 downto 0);
    GPI4_Interrupt : out std_logic;

    -- Interrupt IO
    INTC_Interrupt         : in  std_logic_vector(C_INTC_INTR_SIZE-1 downto 0);
    INTC_IRQ               : out std_logic;
    INTC_Processor_Ack     : in  std_logic_vector(1 downto 0);
    INTC_Interrupt_Address : out std_logic_vector(C_ADDR_WIDTH-1 downto 0);

    -- Register access
    PIT1_Read          : in  std_logic;
    PIT1_Write_Preload : in  std_logic;
    PIT1_Write_Ctrl    : in  std_logic;
    PIT2_Read          : in  std_logic;
    PIT2_Write_Preload : in  std_logic;
    PIT2_Write_Ctrl    : in  std_logic;
    PIT3_Read          : in  std_logic;
    PIT3_Write_Preload : in  std_logic;
    PIT3_Write_Ctrl    : in  std_logic;
    PIT4_Read          : in  std_logic;
    PIT4_Write_Preload : in  std_logic;
    PIT4_Write_Ctrl    : in  std_logic;
    GPI1_Read          : in  std_logic;
    GPI2_Read          : in  std_logic;
    GPI3_Read          : in  std_logic;
    GPI4_Read          : in  std_logic;
    UART_TX_Write      : in  std_logic;
    UART_Baud_Write    : in  std_logic;
    GPO1_Write         : in  std_logic;
    GPO2_Write         : in  std_logic;
    GPO3_Write         : in  std_logic;
    GPO4_Write         : in  std_logic;
    UART_Status_Read   : in  std_logic;
    UART_Status_Wait   : out std_logic;
    UART_Status_Ready  : out std_logic;
    UART_Rx_Read       : in  std_logic;
    UART_Rx_Wait       : out std_logic;
    UART_Rx_Ready      : out std_logic;
    INTC_WRITE_CIAR    : in  std_logic;
    INTC_WRITE_CIER    : in  std_logic;
    INTC_WRITE_CIMR    : in  std_logic;
    INTC_WRITE_CIVAR   : in  std_logic;
    INTC_WRITE_CIVEAR  : in  std_logic;
    INTC_CIVAR_ADDR    : in  std_logic_vector(4 downto 0);
    INTC_READ_CISR     : in  std_logic;
    INTC_READ_CIPR     : in  std_logic;
    Write_Data         : in  std_logic_vector(31 downto 0);
    Read_Data          : out std_logic_vector(31 downto 0)
    );

end entity Iomodule_core;

library iomodule_v3_1_6;
use iomodule_v3_1_6.all;
use iomodule_v3_1_6.iomodule_vote_pkg.all;

architecture IMP of iomodule_core is

  component UART is
  generic (
    C_TARGET             : TARGET_FAMILY_TYPE;
    C_FREQ               : integer              := 100000000;
    C_UART_FREQ          : integer              := 100000000;
    C_TMR                : integer              := 0;
    C_USE_TMR_DISABLE    : integer              := 0;
    C_VOTE_SIZE          : integer              := 0;
    C_USE_SRL16          : string;
    C_UART_PROG_BAUDRATE : integer              := 0;
    C_UART_ASYNC         : integer              := 0;
    C_UART_NUM_SYNC_FF   : integer              := 2;
    C_UART_BAUDRATE      : integer              := 9600;
    C_USE_UART_RX        : integer              := 1;
    C_USE_UART_TX        : integer              := 1;
    C_UART_DATA_BITS     : integer range 5 to 8 := 8;
    C_UART_USE_PARITY    : integer              := 0;
    C_UART_ODD_PARITY    : integer              := 0);
  port (
    Clk                  : in std_logic;
    UART_Clk             : in std_logic;
    Reset                : in std_logic;
    Config_Reset         : in std_logic;
    Reset_UART_Clk       : in std_logic;

    TMR_Disable          : in std_logic;
    FromAVote            : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
    FromBVote            : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
    ToVote               : out std_logic_vector(C_VOTE_SIZE-1 downto 0);

    TX                   : out std_logic;
    Write_TX_Data        : in  std_logic;
    Write_Baud           : in  std_logic;
    Write_Data           : in  std_logic_vector(31 downto 0);

    RX                   : in  std_logic;
    Read_RX_Data         : in  std_logic;
    Read_RX_Wait         : out std_logic;
    Read_RX_Ready        : out std_logic;
    RX_Data              : out std_logic_vector(C_UART_DATA_BITS-1 downto 0);

    UART_Status_Read     : in  std_logic;
    UART_Status_Wait     : out std_logic;
    UART_Status_Ready    : out std_logic;
    UART_Status          : out std_logic_vector(7 downto 0);
    UART_Interrupt       : out std_logic;
    UART_Rx_Interrupt    : out std_logic;
    UART_Tx_Interrupt    : out std_logic;
    UART_Error_Interrupt : out std_logic);
  end component UART;

  component FIT_Module is
    generic (
      C_TARGET          : TARGET_FAMILY_TYPE;
      C_TMR             : integer := 0;
      C_USE_TMR_DISABLE : integer := 0;
      C_VOTE_SIZE       : integer := 0;
      C_USE_SRL16       : string;
      C_USE_FIT         : integer;
      C_NO_CLOCKS       : integer;      -- The number of clocks between each interrupt
      C_INACCURACY      : integer);     -- The maximum inaccuracy of the number
    port (
      Config_Reset : in  std_logic;
      Clk          : in  std_logic;
      Reset        : in  boolean;
      TMR_Disable  : in std_logic;
      FromAVote    : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
      FromBVote    : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
      ToVote       : out std_logic_vector(C_VOTE_SIZE-1 downto 0);
      Toggle       : out std_logic;
      Interrupt    : out std_logic);
  end component FIT_Module;

  component PIT_Module is
    generic (
      C_TARGET          : TARGET_FAMILY_TYPE;
      C_TMR             : integer := 0;
      C_USE_TMR_DISABLE : integer := 0;
      C_VOTE_SIZE       : integer := 0;
      C_USE_PIT         : integer;
      C_PIT_SIZE        : integer;
      C_PIT_READABLE    : integer);
    port (
      Clk               : in  std_logic;
      Reset             : in  boolean;
      Config_Reset      : in  std_logic;
      TMR_Disable       : in std_logic;
      FromAVote         : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
      FromBVote         : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
      ToVote            : out std_logic_vector(C_VOTE_SIZE-1 downto 0);
      PIT_Count_En      : in  std_logic;
      PIT_Write_Preload : in  std_logic;
      PIT_Write_Ctrl    : in  std_logic;
      PIT_Read          : in  std_logic;
      Write_Data        : in  std_logic_vector(31 downto 0);
      PIT_Data          : out std_logic_vector(C_PIT_SIZE-1 downto 0);
      PIT_Toggle        : out std_logic;
      PIT_Interrupt     : out std_logic);
  end component PIT_Module;

  component GPO_Module is
    generic (
      C_TMR             : integer := 0;
      C_USE_TMR_DISABLE : integer := 0;
      C_VOTE_SIZE       : integer := 0;
      C_USE_GPO         : integer := 1;
      C_GPO_SIZE        : integer range 1 to 32 := 32;
      C_GPO_INIT        : std_logic_vector(31 downto 0) := (others => '0'));
    port (
      Clk         : in  std_logic;
      Reset       : in  boolean;
      GPO_Write   : in  std_logic;
      Write_Data  : in  std_logic_vector(31 downto 0);
      TMR_Disable : in std_logic;
      FromAVote   : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
      FromBVote   : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
      ToVote      : out std_logic_vector(C_VOTE_SIZE-1 downto 0);
      GPO         : out std_logic_vector(C_GPO_SIZE-1 downto 0));
  end component GPO_Module;

  component GPI_Module is
    generic (
      C_USE_GPI       : integer;
      C_GPI_SIZE      : integer;
      C_GPI_INTERRUPT : integer);
    port (
      Clk           : in  std_logic;
      Reset         : in  boolean;
      Config_Reset  : in  std_logic;
      GPI_Read      : in  std_logic;
      GPI           : in  std_logic_vector(C_GPI_SIZE-1 downto 0);
      GPI_In        : out std_logic_vector(C_GPI_SIZE-1 downto 0);
      GPI_Interrupt : out std_logic);
  end component GPI_Module;

  component intr_ctrl is
    generic (
      C_TARGET            : TARGET_FAMILY_TYPE;
      C_TMR               : integer := 0;
      C_USE_TMR_DISABLE   : integer := 0;
      C_VOTE_SIZE         : integer := 0;
      C_ADDR_WIDTH        : integer range 32 to 64 := 32;
      C_INTC_ENABLED      : std_logic_vector(31 downto 0);
      C_INTC_LEVEL_EDGE   : std_logic_vector(31 downto 0);
      C_INTC_POSITIVE     : std_logic_vector(31 downto 0);
      C_INTC_ASYNC_INTR   : std_logic_vector(31 downto 0);
      C_INTC_HAS_FAST     : integer range 0 to 1;
      C_INTC_ADDR_WIDTH   : integer range 5 to 64;
      C_INTC_NUM_SYNC_FF  : integer range 0 to 7;
      C_INTC_BASE_VECTORS : std_logic_vector(63 downto 0);
      C_USE_LUTRAM        : string);
    port (
      Clk               : in  std_logic;
      Reset             : in  boolean;
      TMR_Disable       : in  std_logic;
      FromAVote         : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
      FromBVote         : in  std_logic_vector(C_VOTE_SIZE-1 downto 0);
      ToVote            : out std_logic_vector(C_VOTE_SIZE-1 downto 0);
      INTR              : in  std_logic_vector(31 downto 0);
      INTR_ACK          : in  std_logic_vector(1 downto 0);
      INTR_ADDR         : out std_logic_vector(C_ADDR_WIDTH-1 downto 0);
      INTC_WRITE_CIAR   : in  std_logic;
      INTC_WRITE_CIER   : in  std_logic;
      INTC_WRITE_CIMR   : in  std_logic;
      INTC_WRITE_CIVAR  : in  std_logic;
      INTC_WRITE_CIVEAR : in  std_logic;
      INTC_CIVAR_ADDR   : in  std_logic_vector(4 downto 0);
      Write_Data        : in  std_logic_vector(31 downto 0);
      INTC_READ_CISR    : in  std_logic;
      INTC_READ_CIPR    : in  std_logic;
      INTC_IRQ          : out std_logic;
      INTC_CISR         : out std_logic_vector(31 downto 0);
      INTC_CIPR         : out std_logic_vector(31 downto 0));
  end component intr_ctrl;

  --------------------------------------------------------------------------------------------------
  -- Interrupt functions and constant calculation
  --------------------------------------------------------------------------------------------------
  function int2std (i : integer) return std_logic is
  begin  -- function int2std
    if (i = 0) then
      return '0';
    else
      return '1';
    end if;
  end function int2std;

  function INTR_IMPLEMENTED return std_logic_vector is
    variable t : std_logic_vector(31 downto 0);
  begin
    t(31 downto 16) := (others => '0');
    if (C_INTC_USE_EXT_INTR /= 0) then
      t(C_INTC_INTR_SIZE+15 downto 16) := (others => '1');
    end if;
    t(15) := '0';
    t(14) := int2std(C_GPI4_INTERRUPT);
    t(13) := int2std(C_GPI3_INTERRUPT);
    t(12) := int2std(C_GPI2_INTERRUPT);
    t(11) := int2std(C_GPI1_INTERRUPT);
    t(10) := int2std(C_FIT4_INTERRUPT);
    t(9)  := int2std(C_FIT3_INTERRUPT);
    t(8)  := int2std(C_FIT2_INTERRUPT);
    t(7)  := int2std(C_FIT1_INTERRUPT);
    t(6)  := int2std(C_PIT4_INTERRUPT);
    t(5)  := int2std(C_PIT3_INTERRUPT);
    t(4)  := int2std(C_PIT2_INTERRUPT);
    t(3)  := int2std(C_PIT1_INTERRUPT);
    t(2)  := int2std(C_UART_RX_INTERRUPT);
    t(1)  := int2std(C_UART_TX_INTERRUPT);
    t(0)  := int2std(C_UART_ERROR_INTERRUPT);
    return t;
  end function INTR_IMPLEMENTED;

  constant C_INTR_IMPL : std_logic_vector(31 downto 0) := INTR_IMPLEMENTED;

  -----------------------------------------------------------------------------
  -- bool_to_string conversion for C_AVOID_PRIMITIVES
  -----------------------------------------------------------------------------
  function bool_to_string (b : boolean) return string is
  begin  -- function bool_to_string
    if (b) then
      return "yes";
    else
      return "no";
    end if;
  end function bool_to_string;

  constant C_USE_SRL16  : string := bool_to_string(((C_AVOID_PRIMITIVES = 0) or (C_AVOID_PRIMITIVES = 2)) and (C_TARGET /= RTL));
  constant C_USE_LUTRAM : string := bool_to_string(((C_AVOID_PRIMITIVES = 0) or (C_AVOID_PRIMITIVES = 1)) and (C_TARGET /= RTL));

  signal reset   : boolean;
  --------------------------------------------------------------------------------------------------
  -- GPI signal
  --------------------------------------------------------------------------------------------------
  signal gpi1_in          : std_logic_vector(C_GPI1_SIZE-1 downto 0);
  signal gpi1_interrupt_i : std_logic;
  signal gpi2_in          : std_logic_vector(C_GPI2_SIZE-1 downto 0);
  signal gpi2_interrupt_i : std_logic;
  signal gpi3_in          : std_logic_vector(C_GPI3_SIZE-1 downto 0);
  signal gpi3_interrupt_i : std_logic;
  signal gpi4_in          : std_logic_vector(C_GPI4_SIZE-1 downto 0);
  signal gpi4_interrupt_i : std_logic;

  --------------------------------------------------------------------------------------------------
  -- UART signals
  --------------------------------------------------------------------------------------------------
  signal uart_rx_data         : std_logic_vector(C_UART_DATA_BITS-1 downto 0);
  signal uart_status          : std_logic_vector(7 downto 0);
  signal uart_rx_interrupt    : std_logic;
  signal uart_tx_interrupt    : std_logic;
  signal uart_error_interrupt : std_logic;

  --------------------------------------------------------------------------------------------------
  -- FIT signals
  --------------------------------------------------------------------------------------------------
  signal fit1_interrupt_i : std_logic;
  signal fit2_interrupt_i : std_logic;
  signal fit3_interrupt_i : std_logic;
  signal fit4_interrupt_i : std_logic;

  --------------------------------------------------------------------------------------------------
  -- PIT signals
  --------------------------------------------------------------------------------------------------
  signal pit1_interrupt_i : std_logic;
  signal pit1_count_en    : std_logic;
  signal pit1_data        : std_logic_vector(C_PIT1_SIZE-1 downto 0);
  signal pit2_interrupt_i : std_logic;
  signal pit2_count_en    : std_logic;
  signal pit2_data        : std_logic_vector(C_PIT2_SIZE-1 downto 0);
  signal pit3_interrupt_i : std_logic;
  signal pit3_count_en    : std_logic;
  signal pit3_data        : std_logic_vector(C_PIT3_SIZE-1 downto 0);
  signal pit4_interrupt_i : std_logic;
  signal pit4_count_en    : std_logic;
  signal pit4_data        : std_logic_vector(C_PIT4_SIZE-1 downto 0);

  --------------------------------------------------------------------------------------------------
  -- INTC signals
  --------------------------------------------------------------------------------------------------
  signal intr      : std_logic_vector(31 downto 0);
  signal intc_cisr : std_logic_vector(31 downto 0);
  signal intc_cipr : std_logic_vector(31 downto 0);


  signal config_reset_i : std_logic;

  --------------------------------------------------------------------------------------------------
  -- TMR
  --------------------------------------------------------------------------------------------------
  signal ToVote_i      : std_logic_vector(VOTE_SIZE-1 downto 0);
  signal FromAVote_i   : std_logic_vector(VOTE_SIZE-1 downto 0);
  signal FromBVote_i   : std_logic_vector(VOTE_SIZE-1 downto 0);

begin  -- architecture IMP

  TMR_Yes : if (C_TMR /= 0) generate
  begin
    ToVote(ToVote_i'range)                     <= ToVote_i;
    ToVote(ToVote'high downto ToVote_i'high+1) <= (others => '0');
    FromAVote_i                                <= FromAVote(FromAVote_i'range);
    FromBVote_i                                <= FromBVote(FromBVote_i'range);
  end generate TMR_Yes;

  TMR_No : if (C_TMR = 0) generate
  begin
    ToVote      <= (others => '0');
    FromAVote_i <= (others => '0');
    FromBVote_i <= (others => '0');
  end generate TMR_No;

  Reset <= (Rst = '1');

  config_reset_i <= Config_Reset when C_USE_CONFIG_RESET /= 0 else '0';

  --------------------------------------------------------------------------------------------------
  -- UART Section
  --------------------------------------------------------------------------------------------------
  UART_I1 : UART
    generic map (
      C_TARGET             => C_TARGET,
      C_FREQ               => C_FREQ,
      C_UART_FREQ          => C_UART_FREQ,
      C_TMR                => C_TMR,
      C_USE_TMR_DISABLE    => C_USE_TMR_DISABLE,
      C_VOTE_SIZE          => UART_high-UART_low+1,
      C_USE_SRL16          => C_USE_SRL16,
      C_UART_PROG_BAUDRATE => C_UART_PROG_BAUDRATE,
      C_UART_ASYNC         => C_UART_ASYNC,
      C_UART_NUM_SYNC_FF   => C_UART_NUM_SYNC_FF,
      C_UART_BAUDRATE      => C_UART_BAUDRATE,
      C_USE_UART_RX        => C_USE_UART_RX,
      C_USE_UART_TX        => C_USE_UART_TX,
      C_UART_DATA_BITS     => C_UART_DATA_BITS,
      C_UART_USE_PARITY    => C_UART_USE_PARITY,
      C_UART_ODD_PARITY    => C_UART_ODD_PARITY)
    port map (
      Clk                  => Clk,
      UART_Clk             => UART_Clk,
      Reset                => Rst,
      Config_Reset         => config_reset_i,
      Reset_UART_Clk       => UART_Rst,
        
      TMR_Disable          => TMR_Disable,
      FromAVote            => FromAVote_i(UART_Pos),
      FromBVote            => FromBVote_i(UART_Pos),
      ToVote               => ToVote_i(UART_Pos),

      TX                   => UART_Tx,
      Write_TX_Data        => UART_TX_Write,
      Write_Baud           => UART_Baud_Write,
      Write_Data           => Write_Data,

      RX                   => UART_RX,
      Read_RX_Data         => UART_Rx_Read,
      Read_RX_Wait         => UART_Rx_Wait,
      Read_RX_Ready        => UART_Rx_Ready,
      RX_Data              => uart_rx_data,
        
      UART_Status_Read     => UART_Status_Read,
      UART_Status_Wait     => UART_Status_Wait,
      UART_Status_Ready    => UART_Status_Ready,
      UART_Status          => uart_status,
      UART_Interrupt       => UART_Interrupt,
      UART_Rx_Interrupt    => uart_rx_interrupt,
      UART_Tx_Interrupt    => uart_tx_interrupt,
      UART_Error_Interrupt => uart_error_interrupt);

  --------------------------------------------------------------------------------------------------
  -- FIT Section
  --------------------------------------------------------------------------------------------------
  FIT_I1 : FIT_Module
    generic map (
      C_TARGET          => C_TARGET,
      C_TMR             => C_TMR,
      C_USE_TMR_DISABLE => C_USE_TMR_DISABLE,
      C_VOTE_SIZE       => FIT1_Pos'high-FIT1_Pos'low+1,
      C_USE_SRL16       => C_USE_SRL16,
      C_USE_FIT         => C_USE_FIT1,
      C_NO_CLOCKS       => C_FIT1_NO_CLOCKS,
      C_INACCURACY      => 0)
    port map (
      Config_Reset => config_reset_i,
      Clk          => Clk,
      Reset        => Reset,
      TMR_Disable  => TMR_Disable,
      FromAVote    => FromAVote_i(FIT1_Pos),
      FromBVote    => FromBVote_i(FIT1_Pos),
      ToVote       => ToVote_i(FIT1_Pos),
      Toggle       => FIT1_Toggle,
      Interrupt    => fit1_interrupt_i);

  FIT1_Interrupt <= fit1_interrupt_i;

  FIT_I2 : FIT_Module
    generic map (
      C_TARGET          => C_TARGET,
      C_TMR             => C_TMR,
      C_USE_TMR_DISABLE => C_USE_TMR_DISABLE,
      C_VOTE_SIZE       => FIT2_Pos'high-FIT2_Pos'low+1,
      C_USE_SRL16       => C_USE_SRL16,
      C_USE_FIT         => C_USE_FIT2,
      C_NO_CLOCKS       => C_FIT2_NO_CLOCKS,
      C_INACCURACY      => 0)
    port map (
      Config_Reset => config_reset_i,
      Clk          => Clk,
      Reset        => Reset,
      TMR_Disable  => TMR_Disable,
      FromAVote    => FromAVote_i(FIT2_Pos),
      FromBVote    => FromBVote_i(FIT2_Pos),
      ToVote       => ToVote_i(FIT2_Pos),
      Toggle       => FIT2_Toggle,
      Interrupt    => fit2_interrupt_i);

  FIT2_Interrupt <= fit2_interrupt_i;

  FIT_I3 : FIT_Module
    generic map (
      C_TARGET          => C_TARGET,
      C_TMR             => C_TMR,
      C_USE_TMR_DISABLE => C_USE_TMR_DISABLE,
      C_VOTE_SIZE       => FIT3_Pos'high-FIT3_Pos'low+1,
      C_USE_SRL16       => C_USE_SRL16,
      C_USE_FIT         => C_USE_FIT3,
      C_NO_CLOCKS       => C_FIT3_NO_CLOCKS,
      C_INACCURACY      => 0)
    port map (
      Config_Reset => config_reset_i,
      Clk          => Clk,
      Reset        => Reset,
      TMR_Disable  => TMR_Disable,
      FromAVote    => FromAVote_i(FIT3_Pos),
      FromBVote    => FromBVote_i(FIT3_Pos),
      ToVote       => ToVote_i(FIT3_Pos),
      Toggle       => FIT3_Toggle,
      Interrupt    => fit3_interrupt_i);

  FIT3_Interrupt <= fit3_interrupt_i;

  FIT_I4 : FIT_Module
    generic map (
      C_TARGET          => C_TARGET,
      C_TMR             => C_TMR,
      C_USE_TMR_DISABLE => C_USE_TMR_DISABLE,
      C_VOTE_SIZE       => FIT4_Pos'high-FIT4_Pos'low+1,
      C_USE_SRL16       => C_USE_SRL16,
      C_USE_FIT         => C_USE_FIT4,
      C_NO_CLOCKS       => C_FIT4_NO_CLOCKS,
      C_INACCURACY      => 0)
    port map (
      Config_Reset => config_reset_i,
      Clk          => Clk,
      Reset        => Reset,
      TMR_Disable  => TMR_Disable,
      FromAVote    => FromAVote_i(FIT4_Pos),
      FromBVote    => FromBVote_i(FIT4_Pos),
      ToVote       => ToVote_i(FIT4_Pos),
      Toggle       => FIT4_Toggle,
      Interrupt    => fit4_interrupt_i);

  FIT4_Interrupt <= fit4_interrupt_i;

  --------------------------------------------------------------------------------------------------
  -- PIT Section
  --------------------------------------------------------------------------------------------------

  pit1_count_en <= '1'              when C_PIT1_PRESCALER = 0 else
                   fit1_interrupt_i when C_PIT1_PRESCALER = 1 else
                   fit2_interrupt_i when C_PIT1_PRESCALER = 2 else
                   fit3_interrupt_i when C_PIT1_PRESCALER = 3 else
                   fit4_interrupt_i when C_PIT1_PRESCALER = 4 else
                   pit2_interrupt_i when C_PIT1_PRESCALER = 6 else
                   pit3_interrupt_i when C_PIT1_PRESCALER = 7 else
                   pit4_interrupt_i when C_PIT1_PRESCALER = 8 else
                   PIT1_Enable      when C_PIT1_PRESCALER = 9 else
                   '0';

  PIT_I1 : PIT_Module
    generic map (
      C_TARGET          => C_TARGET,
      C_TMR             => C_TMR,
      C_USE_TMR_DISABLE => C_USE_TMR_DISABLE,
      C_VOTE_SIZE       => PIT1_Pos'high-PIT1_Pos'low+1,
      C_USE_PIT         => C_USE_PIT1,
      C_PIT_SIZE        => C_PIT1_SIZE,
      C_PIT_READABLE    => C_PIT1_READABLE)
    port map (
      Clk               => Clk,
      Reset             => Reset,
      Config_Reset      => config_reset_i,
      TMR_Disable       => TMR_Disable,
      FromAVote         => FromAVote_i(PIT1_Pos),
      FromBVote         => FromBVote_i(PIT1_Pos),
      ToVote            => ToVote_i(PIT1_Pos),
      PIT_Count_En      => pit1_count_en,
      PIT_Write_Preload => PIT1_Write_Preload,
      PIT_Write_Ctrl    => PIT1_Write_Ctrl,
      PIT_Read          => PIT1_Read,
      Write_Data        => Write_Data,
      PIT_Data          => pit1_data,
      PIT_Toggle        => PIT1_Toggle,
      PIT_Interrupt     => pit1_interrupt_i);

  PIT1_Interrupt <= pit1_interrupt_i;

  pit2_count_en <= '1'              when C_PIT2_PRESCALER = 0 else
                   fit1_interrupt_i when C_PIT2_PRESCALER = 1 else
                   fit2_interrupt_i when C_PIT2_PRESCALER = 2 else
                   fit3_interrupt_i when C_PIT2_PRESCALER = 3 else
                   fit4_interrupt_i when C_PIT2_PRESCALER = 4 else
                   pit1_interrupt_i when C_PIT2_PRESCALER = 5 else
                   pit3_interrupt_i when C_PIT2_PRESCALER = 7 else
                   pit4_interrupt_i when C_PIT2_PRESCALER = 8 else
                   PIT2_Enable      when C_PIT2_PRESCALER = 9 else
                   '0';

  PIT_I2 : PIT_Module
    generic map (
      C_TARGET          => C_TARGET,
      C_TMR             => C_TMR,
      C_USE_TMR_DISABLE => C_USE_TMR_DISABLE,
      C_VOTE_SIZE       => PIT2_Pos'high-PIT2_Pos'low+1,
      C_USE_PIT         => C_USE_PIT2,
      C_PIT_SIZE        => C_PIT2_SIZE,
      C_PIT_READABLE    => C_PIT2_READABLE)
    port map (
      Clk               => Clk,
      Reset             => Reset,
      Config_Reset      => config_reset_i,
      TMR_Disable       => TMR_Disable,
      FromAVote         => FromAVote_i(PIT2_Pos),
      FromBVote         => FromBVote_i(PIT2_Pos),
      ToVote            => ToVote_i(PIT2_Pos),
      PIT_Count_En      => pit2_count_en,
      PIT_Write_Preload => PIT2_Write_Preload,
      PIT_Write_Ctrl    => PIT2_Write_Ctrl,
      PIT_Read          => PIT2_Read,
      Write_Data        => Write_Data,
      PIT_Data          => pit2_data,
      PIT_Toggle        => PIT2_Toggle,
      PIT_Interrupt     => pit2_interrupt_i);

  PIT2_Interrupt <= pit2_interrupt_i;

  pit3_count_en <= '1'              when C_PIT3_PRESCALER = 0 else
                   fit1_interrupt_i when C_PIT3_PRESCALER = 1 else
                   fit2_interrupt_i when C_PIT3_PRESCALER = 2 else
                   fit3_interrupt_i when C_PIT3_PRESCALER = 3 else
                   fit4_interrupt_i when C_PIT3_PRESCALER = 4 else
                   pit1_interrupt_i when C_PIT3_PRESCALER = 5 else
                   pit2_interrupt_i when C_PIT3_PRESCALER = 6 else
                   pit4_interrupt_i when C_PIT3_PRESCALER = 8 else
                   PIT3_Enable      when C_PIT3_PRESCALER = 9 else
                   '0';

  PIT_I3 : PIT_Module
    generic map (
      C_TARGET          => C_TARGET,
      C_TMR             => C_TMR,
      C_USE_TMR_DISABLE => C_USE_TMR_DISABLE,
      C_VOTE_SIZE       => PIT3_Pos'high-PIT3_Pos'low+1,
      C_USE_PIT         => C_USE_PIT3,
      C_PIT_SIZE        => C_PIT3_SIZE,
      C_PIT_READABLE    => C_PIT3_READABLE)
    port map (
      Clk               => Clk,
      Reset             => Reset,
      Config_Reset      => config_reset_i,
      TMR_Disable       => TMR_Disable,
      FromAVote         => FromAVote_i(PIT3_Pos),
      FromBVote         => FromBVote_i(PIT3_Pos),
      ToVote            => ToVote_i(PIT3_Pos),
      PIT_Count_En      => pit3_count_en,
      PIT_Write_Preload => PIT3_Write_Preload,
      PIT_Write_Ctrl    => PIT3_Write_Ctrl,
      PIT_Read          => PIT3_Read,
      Write_Data        => Write_Data,
      PIT_Data          => pit3_data,
      PIT_Toggle        => PIT3_Toggle,
      PIT_Interrupt     => pit3_interrupt_i);

  PIT3_Interrupt <= pit3_interrupt_i;

  pit4_count_en <= '1'              when C_PIT4_PRESCALER = 0 else
                   fit1_interrupt_i when C_PIT4_PRESCALER = 1 else
                   fit2_interrupt_i when C_PIT4_PRESCALER = 2 else
                   fit3_interrupt_i when C_PIT4_PRESCALER = 3 else
                   fit4_interrupt_i when C_PIT4_PRESCALER = 4 else
                   pit1_interrupt_i when C_PIT4_PRESCALER = 5 else
                   pit2_interrupt_i when C_PIT4_PRESCALER = 6 else
                   pit3_interrupt_i when C_PIT4_PRESCALER = 7 else
                   PIT4_Enable      when C_PIT4_PRESCALER = 9 else
                   '0';

  PIT_I4 : PIT_Module
    generic map (
      C_TARGET          => C_TARGET,
      C_TMR             => C_TMR,
      C_USE_TMR_DISABLE => C_USE_TMR_DISABLE,
      C_VOTE_SIZE       => PIT4_Pos'high-PIT4_Pos'low+1,
      C_USE_PIT         => C_USE_PIT4,
      C_PIT_SIZE        => C_PIT4_SIZE,
      C_PIT_READABLE    => C_PIT4_READABLE)
    port map (
      Clk               => Clk,
      Reset             => Reset,
      Config_Reset      => config_reset_i,
      TMR_Disable       => TMR_Disable,
      FromAVote         => FromAVote_i(PIT4_Pos),
      FromBVote         => FromBVote_i(PIT4_Pos),
      ToVote            => ToVote_i(PIT4_Pos),
      PIT_Count_En      => pit4_count_en,
      PIT_Write_Preload => PIT4_Write_Preload,
      PIT_Write_Ctrl    => PIT4_Write_Ctrl,
      PIT_Read          => PIT4_Read,
      Write_Data        => Write_Data,
      PIT_Data          => pit4_data,
      PIT_Toggle        => PIT4_Toggle,
      PIT_Interrupt     => pit4_interrupt_i);

  PIT4_Interrupt <= pit4_interrupt_i;

  GPO_I1 : GPO_Module
    generic map (
      C_TMR             => C_TMR,
      C_USE_TMR_DISABLE => C_USE_TMR_DISABLE,
      C_VOTE_SIZE       => GPO1_Pos'high-GPO1_Pos'low+1,
      C_USE_GPO         => C_USE_GPO1,
      C_GPO_SIZE        => C_GPO1_SIZE,
      C_GPO_INIT        => C_GPO1_INIT)
    port map (
      Clk         => Clk,
      Reset       => Reset,
      GPO_Write   => GPO1_Write,
      Write_Data  => Write_Data,
      TMR_Disable => TMR_Disable,
      FromAVote   => FromAVote_i(GPO1_Pos),
      FromBVote   => FromBVote_i(GPO1_Pos),
      ToVote      => ToVote_i(GPO1_Pos),
      GPO         => GPO1);

  GPO_I2 : GPO_Module
    generic map (
      C_TMR             => C_TMR,
      C_USE_TMR_DISABLE => C_USE_TMR_DISABLE,
      C_VOTE_SIZE       => GPO2_Pos'high-GPO2_Pos'low+1,
      C_USE_GPO         => C_USE_GPO2,
      C_GPO_SIZE        => C_GPO2_SIZE,
      C_GPO_INIT        => C_GPO2_INIT)
    port map (
      Clk         => Clk,
      Reset       => Reset,
      GPO_Write   => GPO2_Write,
      Write_Data  => Write_Data,
      TMR_Disable => TMR_Disable,
      FromAVote   => FromAVote_i(GPO2_Pos),
      FromBVote   => FromBVote_i(GPO2_Pos),
      ToVote      => ToVote_i(GPO2_Pos),
      GPO         => GPO2);

  GPO_I3 : GPO_Module
    generic map (
      C_TMR             => C_TMR,
      C_USE_TMR_DISABLE => C_USE_TMR_DISABLE,
      C_VOTE_SIZE       => GPO3_Pos'high-GPO3_Pos'low+1,
      C_USE_GPO         => C_USE_GPO3,
      C_GPO_SIZE        => C_GPO3_SIZE,
      C_GPO_INIT        => C_GPO3_INIT)
    port map (
      Clk         => Clk,
      Reset       => Reset,
      GPO_Write   => GPO3_Write,
      Write_Data  => Write_Data,
      TMR_Disable => TMR_Disable,
      FromAVote   => FromAVote_i(GPO3_Pos),
      FromBVote   => FromBVote_i(GPO3_Pos),
      ToVote      => ToVote_i(GPO3_Pos),
      GPO         => GPO3);

  GPO_I4 : GPO_Module
    generic map (
      C_TMR             => C_TMR,
      C_USE_TMR_DISABLE => C_USE_TMR_DISABLE,
      C_VOTE_SIZE       => GPO4_Pos'high-GPO4_Pos'low+1,
      C_USE_GPO         => C_USE_GPO4,
      C_GPO_SIZE        => C_GPO4_SIZE,
      C_GPO_INIT        => C_GPO4_INIT)
    port map (
      Clk         => Clk,
      Reset       => Reset,
      GPO_Write   => GPO4_Write,
      Write_Data  => Write_Data,
      TMR_Disable => TMR_Disable,
      FromAVote   => FromAVote_i(GPO4_Pos),
      FromBVote   => FromBVote_i(GPO4_Pos),
      ToVote      => ToVote_i(GPO4_Pos),
      GPO         => GPO4);

  --------------------------------------------------------------------------------------------------
  -- GPI Section
  --------------------------------------------------------------------------------------------------
  GPI_I1 : GPI_Module
    generic map (
      C_USE_GPI       => C_USE_GPI1,
      C_GPI_SIZE      => C_GPI1_SIZE,
      C_GPI_INTERRUPT => C_GPI1_INTERRUPT)
    port map (
      Clk           => Clk,
      Reset         => Reset,
      Config_Reset  => config_reset_i,
      GPI_Read      => GPI1_Read,
      GPI           => GPI1,
      gpi_in        => gpi1_in,
      GPI_Interrupt => gpi1_interrupt_i);

  GPI1_Interrupt <= gpi1_interrupt_i;

  GPI_I2 : GPI_Module
    generic map (
      C_USE_GPI       => C_USE_GPI2,
      C_GPI_SIZE      => C_GPI2_SIZE,
      C_GPI_INTERRUPT => C_GPI2_INTERRUPT)
    port map (
      Clk           => Clk,
      Reset         => Reset,
      Config_Reset  => config_reset_i,
      GPI_Read      => GPI2_Read,
      GPI           => GPI2,
      gpi_in        => gpi2_in,
      GPI_Interrupt => gpi2_interrupt_i);

  GPI2_Interrupt <= gpi2_interrupt_i;

  GPI_I3 : GPI_Module
    generic map (
      C_USE_GPI       => C_USE_GPI3,
      C_GPI_SIZE      => C_GPI3_SIZE,
      C_GPI_INTERRUPT => C_GPI3_INTERRUPT)
    port map (
      Clk           => Clk,
      Reset         => Reset,
      Config_Reset  => config_reset_i,
      GPI_Read      => GPI3_Read,
      GPI           => GPI3,
      gpi_in        => gpi3_in,
      GPI_Interrupt => gpi3_interrupt_i);

  GPI3_Interrupt <= gpi3_interrupt_i;

  GPI_I4 : GPI_Module
    generic map (
      C_USE_GPI       => C_USE_GPI4,
      C_GPI_SIZE      => C_GPI4_SIZE,
      C_GPI_INTERRUPT => C_GPI4_INTERRUPT)
    port map (
      Clk           => Clk,
      Reset         => Reset,
      Config_Reset  => config_reset_i,
      GPI_Read      => GPI4_Read,
      GPI           => GPI4,
      gpi_in        => gpi4_in,
      GPI_Interrupt => gpi4_interrupt_i);

  GPI4_Interrupt <= gpi4_interrupt_i;

  --------------------------------------------------------------------------------------------------
  -- Interrupt Handler section
  --------------------------------------------------------------------------------------------------
  Intr_Assign : if C_INTC_INTR_SIZE < 16 generate
  begin
    intr(31 downto C_INTC_INTR_SIZE+16) <= (others => '0');
  end generate Intr_Assign;

  intr(C_INTC_INTR_SIZE+15 downto 16) <= INTC_Interrupt;
  intr(15)                            <= '0';
  intr(14)                            <= gpi4_interrupt_i;
  intr(13)                            <= gpi3_interrupt_i;
  intr(12)                            <= gpi2_interrupt_i;
  intr(11)                            <= gpi1_interrupt_i;
  intr(10)                            <= fit4_interrupt_i;
  intr(9)                             <= fit3_interrupt_i;
  intr(8)                             <= fit2_interrupt_i;
  intr(7)                             <= fit1_interrupt_i;
  intr(6)                             <= pit4_interrupt_i;
  intr(5)                             <= pit3_interrupt_i;
  intr(4)                             <= pit2_interrupt_i;
  intr(3)                             <= pit1_interrupt_i;
  intr(2)                             <= uart_rx_interrupt;
  intr(1)                             <= uart_tx_interrupt;
  intr(0)                             <= uart_error_interrupt;

  intr_ctrl_I1 : intr_ctrl
    generic map (
      C_TARGET            => C_TARGET,
      C_TMR               => C_TMR,
      C_USE_TMR_DISABLE   => C_USE_TMR_DISABLE,
      C_VOTE_SIZE         => IRQ_Pos'high-IRQ_Pos'low+1,
      C_ADDR_WIDTH        => C_ADDR_WIDTH,
      C_INTC_LEVEL_EDGE   => C_INTC_LEVEL_EDGE & X"FFFF",
      C_INTC_POSITIVE     => C_INTC_POSITIVE & X"FFFF",
      C_INTC_ASYNC_INTR   => C_INTC_ASYNC_INTR & X"0000",
      C_INTC_ENABLED      => C_INTR_IMPL,
      C_INTC_HAS_FAST     => C_INTC_HAS_FAST,
      C_INTC_ADDR_WIDTH   => C_INTC_ADDR_WIDTH,
      C_INTC_NUM_SYNC_FF  => C_INTC_NUM_SYNC_FF,
      C_INTC_BASE_VECTORS => C_INTC_BASE_VECTORS,
      C_USE_LUTRAM        => C_USE_LUTRAM)
    port map (
      Clk               => Clk,
      Reset             => Reset,
      TMR_Disable       => TMR_Disable,
      FromAVote         => FromAVote_i(IRQ_Pos),
      FromBVote         => FromBVote_i(IRQ_Pos),
      ToVote            => ToVote_i(IRQ_Pos),
      INTR              => intr,
      INTR_ACK          => INTC_Processor_Ack,
      INTR_ADDR         => INTC_Interrupt_Address,
      INTC_WRITE_CIAR   => INTC_WRITE_CIAR,
      INTC_WRITE_CIER   => INTC_WRITE_CIER,
      INTC_WRITE_CIMR   => INTC_WRITE_CIMR,
      INTC_WRITE_CIVAR  => INTC_WRITE_CIVAR,
      INTC_WRITE_CIVEAR => INTC_WRITE_CIVEAR,
      INTC_CIVAR_ADDR   => INTC_CIVAR_ADDR,
      Write_Data        => Write_Data,
      INTC_READ_CISR    => INTC_READ_CISR,
      INTC_READ_CIPR    => INTC_READ_CIPR,
      INTC_IRQ          => INTC_IRQ,
      INTC_CISR         => intc_cisr,
      INTC_CIPR         => intc_cipr);

  --------------------------------------------------------------------------------------------------
  -- Read MUX section
  --------------------------------------------------------------------------------------------------
  Simple_OR_Mux : process (gpi1_in, gpi2_in, gpi3_in, gpi4_in, intc_cipr, intc_cisr, pit1_data,
                           pit2_data, pit3_data, pit4_data, uart_rx_data, uart_status) is
    variable u1  : std_logic_vector(31 downto 0);
    variable u2  : std_logic_vector(31 downto 0);
    variable gi1 : std_logic_vector(31 downto 0);
    variable gi2 : std_logic_vector(31 downto 0);
    variable gi3 : std_logic_vector(31 downto 0);
    variable gi4 : std_logic_vector(31 downto 0);
    variable pi1 : std_logic_vector(31 downto 0);
    variable pi2 : std_logic_vector(31 downto 0);
    variable pi3 : std_logic_vector(31 downto 0);
    variable pi4 : std_logic_vector(31 downto 0);
  begin  -- process Simple_OR_Mux
    u1  := (others => '0');
    u2  := (others => '0');
    gi1 := (others => '0');
    gi2 := (others => '0');
    gi3 := (others => '0');
    gi4 := (others => '0');
    pi1 := (others => '0');
    pi2 := (others => '0');
    pi3 := (others => '0');
    pi4 := (others => '0');

    if (C_USE_UART_RX /= 0) then
      u1(uart_rx_data'range) := uart_rx_data;
    end if;

    if ((C_USE_UART_TX /= 0) or (C_USE_UART_RX /= 0)) then
      u2(uart_status'range) := uart_status;
    end if;

    if (C_USE_GPI1 /= 0) then
      gi1(gpi1_in'range) := gpi1_in;
    end if;

    if (C_USE_GPI2 /= 0) then
      gi2(gpi2_in'range) := gpi2_in;
    end if;

    if (C_USE_GPI3 /= 0) then
      gi3(gpi3_in'range) := gpi3_in;
    end if;

    if (C_USE_GPI4 /= 0) then
      gi4(gpi4_in'range) := gpi4_in;
    end if;

    if (C_USE_PIT1 /= 0) then
      pi1(pit1_data'range) := pit1_data;
    end if;

    if (C_USE_PIT2 /= 0) then
      pi2(pit2_data'range) := pit2_data;
    end if;

    if (C_USE_PIT3 /= 0) then
      pi3(pit3_data'range) := pit3_data;
    end if;

    if (C_USE_PIT4 /= 0) then
      pi4(pit4_data'range) := pit4_data;
    end if;

    Read_Data <= u1 or u2 or gi1 or gi2 or gi3 or gi4 or pi1 or pi2 or pi3 or pi4 or intc_cisr or intc_cipr;

  end process Simple_OR_Mux;

end architecture IMP;


-------------------------------------------------------------------------------
-- pselect_mask.vhd - Entity and architecture
-------------------------------------------------------------------------------
--
-- (c) Copyright 2011,2015 Xilinx, Inc. All rights reserved.
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
-- iomodule.vhd - Entity and architecture
-------------------------------------------------------------------------------
--
-- (c) Copyright 2011-2015,2018 Xilinx, Inc. All rights reserved.
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
-- Filename:        iomodule.vhd
--
-- Description:     
--                  
-- VHDL-Standard:   VHDL'93/02
-------------------------------------------------------------------------------
-- Structure:   
--              iomodule.vhd
--
-------------------------------------------------------------------------------
-- Author:          goran
--
-- History:
--   goran   2008-01-08    First Version
--   stefana 2012-03-20    Added GPI interrupt
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

library iomodule_v3_1_6;
use iomodule_v3_1_6.iomodule_core;
use iomodule_v3_1_6.pselect_mask;

entity iomodule is
  generic (
    C_FAMILY                   : string                    := "Virtex7";
    C_FREQ                     : integer                   := 100000000;
    C_INSTANCE                 : string                    := "iomodule";
    C_USE_CONFIG_RESET         : integer                   := 0;
    C_AVOID_PRIMITIVES         : integer                   := 0;
    C_TMR                      : integer                   := 0;
    C_USE_TMR_DISABLE          : integer                   := 0;

    -- Local Memory Bus generics
    C_HIGHADDR                 : std_logic_vector(0 to 63) := X"0000000000000000";
    C_BASEADDR                 : std_logic_vector(0 to 63) := X"FFFFFFFFFFFFFFFF";
    C_MASK                     : std_logic_vector(0 to 63) := X"FFFFFFFFFFFFFFFF";
    C_IO_HIGHADDR              : std_logic_vector(0 to 63) := X"0000000000000000";
    C_IO_BASEADDR              : std_logic_vector(0 to 63) := X"FFFFFFFFFFFFFFFF";
    C_IO_MASK                  : std_logic_vector(0 to 63) := X"FFFFFFFFFFFFFFFF";
    C_LMB_AWIDTH               : integer                   := 32;
    C_LMB_DWIDTH               : integer                   := 32;
    C_LMB_PROTOCOL             : integer                   := 0;

    -- IO Bus
    C_USE_IO_BUS           : integer               := 0;
    
    -- UART generics
    C_USE_UART_RX          : integer               := 0;
    C_USE_UART_TX          : integer               := 0;
    C_UART_BAUDRATE        : integer               := 9600;
    C_UART_DATA_BITS       : integer range 5 to 8  := 8;
    C_UART_USE_PARITY      : integer               := 0;
    C_UART_ODD_PARITY      : integer               := 0;
    C_UART_RX_INTERRUPT    : integer               := 0;
    C_UART_TX_INTERRUPT    : integer               := 0;
    C_UART_ERROR_INTERRUPT : integer               := 0;
    C_UART_PROG_BAUDRATE   : integer               := 0;
    C_UART_FREQ            : integer               := 100000000;
    C_UART_ASYNC           : integer               := 0;
    C_UART_NUM_SYNC_FF     : integer               := 2;
    
    -- FIT generics
    C_USE_FIT1        : integer               := 0;
    C_FIT1_No_CLOCKS  : integer               := 6216;
    C_FIT1_INTERRUPT  : integer               := 0;
    C_USE_FIT2        : integer               := 0;
    C_FIT2_No_CLOCKS  : integer               := 6216;
    C_FIT2_INTERRUPT  : integer               := 0;
    C_USE_FIT3        : integer               := 0;
    C_FIT3_No_CLOCKS  : integer               := 6216;
    C_FIT3_INTERRUPT  : integer               := 0;
    C_USE_FIT4        : integer               := 0;
    C_FIT4_No_CLOCKS  : integer               := 6216;
    C_FIT4_INTERRUPT  : integer               := 0;

    -- PIT generics
    C_USE_PIT1       : integer               := 0;
    C_PIT1_SIZE      : integer range 1 to 32 := 32;
    C_PIT1_READABLE  : integer               := 1;
    C_PIT1_PRESCALER : integer range 0 to 9  := 0;
    C_PIT1_INTERRUPT : integer               := 0;
    C_USE_PIT2       : integer               := 0;
    C_PIT2_SIZE      : integer range 1 to 32 := 32;
    C_PIT2_READABLE  : integer               := 1;
    C_PIT2_PRESCALER : integer range 0 to 9  := 0;
    C_PIT2_INTERRUPT : integer               := 0;
    C_USE_PIT3       : integer               := 0;
    C_PIT3_SIZE      : integer range 1 to 32 := 32;
    C_PIT3_READABLE  : integer               := 1;
    C_PIT3_PRESCALER : integer range 0 to 9  := 0;
    C_PIT3_INTERRUPT : integer               := 0;
    C_USE_PIT4       : integer               := 0;
    C_PIT4_SIZE      : integer range 1 to 32 := 32;
    C_PIT4_READABLE  : integer               := 1;
    C_PIT4_PRESCALER : integer range 0 to 9  := 0;
    C_PIT4_INTERRUPT : integer               := 0;

    -- GPO Generics
    C_USE_GPO1  : integer := 0;
    C_GPO1_SIZE : integer range 1 to 32 := 32;
    C_GPO1_INIT : std_logic_vector(31 downto 0) := (others => '0');
    C_USE_GPO2  : integer := 0;
    C_GPO2_SIZE : integer range 1 to 32 := 32;
    C_GPO2_INIT : std_logic_vector(31 downto 0) := (others => '0');
    C_USE_GPO3  : integer := 0;
    C_GPO3_SIZE : integer range 1 to 32 := 32;
    C_GPO3_INIT : std_logic_vector(31 downto 0) := (others => '0');
    C_USE_GPO4  : integer := 0;
    C_GPO4_SIZE : integer range 1 to 32 := 32;
    C_GPO4_INIT : std_logic_vector(31 downto 0) := (others => '0');

    -- GPI Generics
    C_USE_GPI1       : integer := 0;
    C_GPI1_SIZE      : integer range 1 to 32 := 32;
    C_GPI1_INTERRUPT : integer               := 0;
    C_USE_GPI2       : integer := 0;
    C_GPI2_SIZE      : integer range 1 to 32 := 32;
    C_GPI2_INTERRUPT : integer               := 0;
    C_USE_GPI3       : integer := 0;
    C_GPI3_SIZE      : integer range 1 to 32 := 32;
    C_GPI3_INTERRUPT : integer               := 0;
    C_USE_GPI4       : integer := 0;
    C_GPI4_SIZE      : integer range 1 to 32 := 32;
    C_GPI4_INTERRUPT : integer               := 0;

    -- Interrupt Handler Generics
    C_INTC_USE_EXT_INTR : integer                       := 0;
    C_INTC_INTR_SIZE    : integer range 1 to 16         := 1;
    C_INTC_LEVEL_EDGE   : std_logic_vector(15 downto 0) := X"0000";
    C_INTC_POSITIVE     : std_logic_vector(15 downto 0) := X"FFFF";
    C_INTC_HAS_FAST     : integer range 0 to 1          := 0;
    C_INTC_ADDR_WIDTH   : integer range 5 to 64         := 32;
    C_INTC_BASE_VECTORS : std_logic_vector(63 downto 0) := X"0000000000000000";
    C_INTC_ASYNC_INTR   : std_logic_vector(15 downto 0) := X"FFFF";
    C_INTC_NUM_SYNC_FF  : integer range 0 to 7          := 2
    );
  port (
    Clk          : in std_logic;
    Rst          : in std_logic;
    Config_Reset : in std_logic := '0';
    TMR_Rst      : in std_logic;
    TMR_Disable  : in std_logic;
    
    -- TMR voting inbetween redundant IO Modules
    ToVote       : out std_logic_vector(1023 downto 0);
    FromAVote    : in  std_logic_vector(1023 downto 0);
    FromBVote    : in  std_logic_vector(1023 downto 0);

    -- IO Interface
    IO_Addr_Strobe  : out std_logic;
    IO_Read_Strobe  : out std_logic;
    IO_Write_Strobe : out std_logic;
    IO_Address      : out std_logic_vector(C_LMB_AWIDTH-1 downto 0);
    IO_Byte_Enable  : out std_logic_vector((C_LMB_DWIDTH/8 - 1) downto 0);
    IO_Write_Data   : out std_logic_vector(C_LMB_DWIDTH-1 downto 0);
    IO_Read_Data    : in  std_logic_vector(C_LMB_DWIDTH-1 downto 0);
    IO_Ready        : in  std_logic;

    -- UART I/O
    UART_Clk       : in std_logic;
    UART_Rst       : in std_logic;
    UART_Rx        : in  std_logic;
    UART_Tx        : out std_logic;
    UART_Interrupt : out std_logic;

    -- FIT I/O
    FIT1_Interrupt : out std_logic;
    FIT1_Toggle    : out std_logic;
    FIT2_Interrupt : out std_logic;
    FIT2_Toggle    : out std_logic;
    FIT3_Interrupt : out std_logic;
    FIT3_Toggle    : out std_logic;
    FIT4_Interrupt : out std_logic;
    FIT4_Toggle    : out std_logic;

    -- PIT I/O
    PIT1_Enable    : in  std_logic;
    PIT1_Interrupt : out std_logic;
    PIT1_Toggle    : out std_logic;
    PIT2_Enable    : in  std_logic;
    PIT2_Interrupt : out std_logic;
    PIT2_Toggle    : out std_logic;
    PIT3_Enable    : in  std_logic;
    PIT3_Interrupt : out std_logic;
    PIT3_Toggle    : out std_logic;
    PIT4_Enable    : in  std_logic;
    PIT4_Interrupt : out std_logic;
    PIT4_Toggle    : out std_logic;

    -- GPO IO
    GPO1 : out std_logic_vector(C_GPO1_SIZE-1 downto 0);
    GPO2 : out std_logic_vector(C_GPO2_SIZE-1 downto 0);
    GPO3 : out std_logic_vector(C_GPO3_SIZE-1 downto 0);
    GPO4 : out std_logic_vector(C_GPO4_SIZE-1 downto 0);

    -- GPI IO
    GPI1           : in  std_logic_vector(C_GPI1_SIZE-1 downto 0);
    GPI1_Interrupt : out std_logic;
    GPI2           : in  std_logic_vector(C_GPI2_SIZE-1 downto 0);
    GPI2_Interrupt : out std_logic;
    GPI3           : in  std_logic_vector(C_GPI3_SIZE-1 downto 0);
    GPI3_Interrupt : out std_logic;
    GPI4           : in  std_logic_vector(C_GPI4_SIZE-1 downto 0);
    GPI4_Interrupt : out std_logic;

    -- Interrupt IO
    INTC_Interrupt         : in  std_logic_vector(C_INTC_INTR_SIZE-1 downto 0);
    INTC_IRQ               : out std_logic;
    INTC_Processor_Ack     : in  std_logic_vector(1 downto 0);
    INTC_Interrupt_Address : out std_logic_vector(((C_INTC_ADDR_WIDTH+31) / 64) * (C_INTC_ADDR_WIDTH-32) + 31 downto 0);
    INTC_IRQ_OUT           : out std_logic;

    -- Local Memory Bus, LMB
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
    Sl_CE           : out std_logic
    );

end entity iomodule;

library iomodule_v3_1_6;
use iomodule_v3_1_6.iomodule_funcs.all;

architecture IMP of iomodule is

  component iomodule_core is
    generic (
      C_TARGET           : TARGET_FAMILY_TYPE;
      C_FREQ             : integer := 100000000;
      C_USE_CONFIG_RESET : integer := 0;
      C_AVOID_PRIMITIVES : integer := 0;
      C_TMR              : integer := 0;
      C_USE_TMR_DISABLE  : integer := 0;

      -- UART generics
      C_USE_UART_RX          : integer;
      C_USE_UART_TX          : integer;
      C_UART_BAUDRATE        : integer;
      C_UART_DATA_BITS       : integer range 5 to 8;
      C_UART_USE_PARITY      : integer;
      C_UART_ODD_PARITY      : integer;
      C_UART_RX_INTERRUPT    : integer;
      C_UART_TX_INTERRUPT    : integer;
      C_UART_ERROR_INTERRUPT : integer;
      C_UART_PROG_BAUDRATE   : integer;
      C_UART_FREQ            : integer;
      C_UART_ASYNC           : integer;
      C_UART_NUM_SYNC_FF     : integer;

      -- FIT generics
      C_USE_FIT1       : integer;
      C_FIT1_No_CLOCKS : integer;
      C_FIT1_INTERRUPT : integer;
      C_USE_FIT2       : integer;
      C_FIT2_No_CLOCKS : integer;
      C_FIT2_INTERRUPT : integer;
      C_USE_FIT3       : integer;
      C_FIT3_No_CLOCKS : integer;
      C_FIT3_INTERRUPT : integer;
      C_USE_FIT4       : integer;
      C_FIT4_No_CLOCKS : integer;
      C_FIT4_INTERRUPT : integer;

      -- PIT generics
      C_USE_PIT1       : integer;
      C_PIT1_SIZE      : integer;
      C_PIT1_READABLE  : integer;
      C_PIT1_PRESCALER : integer range 0 to 9;
      C_PIT1_INTERRUPT : integer;
      C_USE_PIT2       : integer;
      C_PIT2_SIZE      : integer;
      C_PIT2_READABLE  : integer;
      C_PIT2_PRESCALER : integer range 0 to 9;
      C_PIT2_INTERRUPT : integer;
      C_USE_PIT3       : integer;
      C_PIT3_SIZE      : integer;
      C_PIT3_READABLE  : integer;
      C_PIT3_PRESCALER : integer range 0 to 9;
      C_PIT3_INTERRUPT : integer;
      C_USE_PIT4       : integer;
      C_PIT4_SIZE      : integer;
      C_PIT4_READABLE  : integer;
      C_PIT4_PRESCALER : integer range 0 to 9;
      C_PIT4_INTERRUPT : integer;

      -- GPO Generics
      C_USE_GPO1  : integer                       := 0;
      C_GPO1_SIZE : integer range 1 to 32         := 32;
      C_GPO1_INIT : std_logic_vector(31 downto 0) := (others => '0');
      C_USE_GPO2  : integer                       := 0;
      C_GPO2_SIZE : integer range 1 to 32         := 32;
      C_GPO2_INIT : std_logic_vector(31 downto 0) := (others => '0');
      C_USE_GPO3  : integer                       := 0;
      C_GPO3_SIZE : integer range 1 to 32         := 32;
      C_GPO3_INIT : std_logic_vector(31 downto 0) := (others => '0');
      C_USE_GPO4  : integer                       := 0;
      C_GPO4_SIZE : integer range 1 to 32         := 32;
      C_GPO4_INIT : std_logic_vector(31 downto 0) := (others => '0');

      -- GPI Generics
      C_USE_GPI1       : integer               := 0;
      C_GPI1_SIZE      : integer range 1 to 32 := 32;
      C_GPI1_INTERRUPT : integer               := 0;
      C_USE_GPI2       : integer               := 0;
      C_GPI2_SIZE      : integer range 1 to 32 := 32;
      C_GPI2_INTERRUPT : integer               := 0;
      C_USE_GPI3       : integer               := 0;
      C_GPI3_SIZE      : integer range 1 to 32 := 32;
      C_GPI3_INTERRUPT : integer               := 0;
      C_USE_GPI4       : integer               := 0;
      C_GPI4_SIZE      : integer range 1 to 32 := 32;
      C_GPI4_INTERRUPT : integer               := 0;

      -- Interrupt Handler Generics
      C_ADDR_WIDTH        : integer range 32 to 64;
      C_INTC_USE_EXT_INTR : integer;
      C_INTC_INTR_SIZE    : integer range 1 to 16;
      C_INTC_LEVEL_EDGE   : std_logic_vector(15 downto 0);
      C_INTC_POSITIVE     : std_logic_vector(15 downto 0);
      C_INTC_HAS_FAST     : integer range 0 to 1;
      C_INTC_ADDR_WIDTH   : integer range 5 to 64;
      C_INTC_BASE_VECTORS : std_logic_vector(63 downto 0);
      C_INTC_ASYNC_INTR   : std_logic_vector(15 downto 0) := X"FFFF";
      C_INTC_NUM_SYNC_FF  : integer range 0 to 7);
    port (
      Config_Reset : in std_logic := '0';
      CLK          : in std_logic;
      Rst          : in std_logic;
      TMR_Rst      : in std_logic;
      TMR_Disable  : in std_logic;

      -- TMR voting inbetween redundant IO Modules
      ToVote       : out std_logic_vector(1023 downto 0);
      FromAVote    : in  std_logic_vector(1023 downto 0);
      FromBVote    : in  std_logic_vector(1023 downto 0);

      -- UART I/O
      UART_Clk       : in std_logic;
      UART_Rst       : in std_logic;
      UART_Rx        : in  std_logic;
      UART_Tx        : out std_logic;
      UART_Interrupt : out std_logic;

      -- FIT I/O
      FIT1_Interrupt : out std_logic;
      FIT1_Toggle    : out std_logic;
      FIT2_Interrupt : out std_logic;
      FIT2_Toggle    : out std_logic;
      FIT3_Interrupt : out std_logic;
      FIT3_Toggle    : out std_logic;
      FIT4_Interrupt : out std_logic;
      FIT4_Toggle    : out std_logic;

      -- PIT I/O
      PIT1_Enable    : in  std_logic;
      PIT1_Interrupt : out std_logic;
      PIT1_Toggle    : out std_logic;
      PIT2_Enable    : in  std_logic;
      PIT2_Interrupt : out std_logic;
      PIT2_Toggle    : out std_logic;
      PIT3_Enable    : in  std_logic;
      PIT3_Interrupt : out std_logic;
      PIT3_Toggle    : out std_logic;
      PIT4_Enable    : in  std_logic;
      PIT4_Interrupt : out std_logic;
      PIT4_Toggle    : out std_logic;

      -- GPO IO
      GPO1 : out std_logic_vector(C_GPO1_SIZE-1 downto 0);
      GPO2 : out std_logic_vector(C_GPO2_SIZE-1 downto 0);
      GPO3 : out std_logic_vector(C_GPO3_SIZE-1 downto 0);
      GPO4 : out std_logic_vector(C_GPO4_SIZE-1 downto 0);

      -- GPI IO
      GPI1           : in  std_logic_vector(C_GPI1_SIZE-1 downto 0);
      GPI1_Interrupt : out std_logic;
      GPI2           : in  std_logic_vector(C_GPI2_SIZE-1 downto 0);
      GPI2_Interrupt : out std_logic;
      GPI3           : in  std_logic_vector(C_GPI3_SIZE-1 downto 0);
      GPI3_Interrupt : out std_logic;
      GPI4           : in  std_logic_vector(C_GPI4_SIZE-1 downto 0);
      GPI4_Interrupt : out std_logic;

      -- Interrupt IO
      INTC_Interrupt         : in  std_logic_vector(C_INTC_INTR_SIZE-1 downto 0);
      INTC_IRQ               : out std_logic;
      INTC_Processor_Ack     : in  std_logic_vector(1 downto 0);
      INTC_Interrupt_Address : out std_logic_vector(C_ADDR_WIDTH-1 downto 0);

      -- Register access
      PIT1_Read          : in  std_logic;
      PIT1_Write_Preload : in  std_logic;
      PIT1_Write_Ctrl    : in  std_logic;
      PIT2_Read          : in  std_logic;
      PIT2_Write_Preload : in  std_logic;
      PIT2_Write_Ctrl    : in  std_logic;
      PIT3_Read          : in  std_logic;
      PIT3_Write_Preload : in  std_logic;
      PIT3_Write_Ctrl    : in  std_logic;
      PIT4_Read          : in  std_logic;
      PIT4_Write_Preload : in  std_logic;
      PIT4_Write_Ctrl    : in  std_logic;
      GPI1_Read          : in  std_logic;
      GPI2_Read          : in  std_logic;
      GPI3_Read          : in  std_logic;
      GPI4_Read          : in  std_logic;
      UART_TX_Write      : in  std_logic;
      UART_Baud_Write    : in  std_logic;
      GPO1_Write         : in  std_logic;
      GPO2_Write         : in  std_logic;
      GPO3_Write         : in  std_logic;
      GPO4_Write         : in  std_logic;
      UART_Status_Read   : in  std_logic;
      UART_Status_Wait   : out std_logic;
      UART_Status_Ready  : out std_logic;
      UART_Rx_Read       : in  std_logic;
      UART_Rx_Wait       : out std_logic;
      UART_Rx_Ready      : out std_logic;
      INTC_WRITE_CIAR    : in  std_logic;
      INTC_WRITE_CIER    : in  std_logic;
      INTC_WRITE_CIMR    : in  std_logic;
      INTC_WRITE_CIVAR   : in  std_logic;
      INTC_WRITE_CIVEAR  : in  std_logic;
      INTC_CIVAR_ADDR    : in  std_logic_vector(4 downto 0);
      INTC_READ_CISR     : in  std_logic;
      INTC_READ_CIPR     : in  std_logic;
      Write_Data         : in  std_logic_vector(31 downto 0);
      Read_Data          : out std_logic_vector(31 downto 0));
  end component iomodule_core;

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

  function c_use(size : integer) return integer is
  begin
    if size = 0 then
      return 0;
    else
      return 1;
    end if;
  end function c_use;

  -- Interrupt controller extended address
  constant C_INTC_HAS_AE : integer := Boolean'Pos(C_INTC_ADDR_WIDTH > 32);
  constant C_ADDR_WIDTH  : natural := ((C_INTC_ADDR_WIDTH + 31) / 64) * (C_INTC_ADDR_WIDTH - 32) + 32;

  -- Target
  constant C_TARGET : TARGET_FAMILY_TYPE := String_To_Family(C_FAMILY, false);
  
  -- Register Address Map
  constant C_UART_RX      : std_logic_vector(0 to 4) := "00000";
  constant C_UART_TX      : std_logic_vector(0 to 4) := "00001";
  constant C_UART_STATUS  : std_logic_vector(0 to 4) := "00010";
  constant C_IRQ_MODE     : std_logic_vector(0 to 4) := "00011";
  constant C_GPO1         : std_logic_vector(0 to 4) := "00100";
  constant C_GPO2         : std_logic_vector(0 to 4) := "00101";
  constant C_GPO3         : std_logic_vector(0 to 4) := "00110";
  constant C_GPO4         : std_logic_vector(0 to 4) := "00111";
  constant C_GPI1         : std_logic_vector(0 to 4) := "01000";
  constant C_GPI2         : std_logic_vector(0 to 4) := "01001";
  constant C_GPI3         : std_logic_vector(0 to 4) := "01010";
  constant C_GPI4         : std_logic_vector(0 to 4) := "01011";
  constant C_IRQ_STATUS   : std_logic_vector(0 to 4) := "01100";
  constant C_IRQ_PENDING  : std_logic_vector(0 to 4) := "01101";
  constant C_IRQ_ENABLE   : std_logic_vector(0 to 4) := "01110";
  constant C_IRQ_ACK      : std_logic_vector(0 to 4) := "01111";
  constant C_PIT1_PRELOAD : std_logic_vector(0 to 4) := "10000";
  constant C_PIT1_COUNTER : std_logic_vector(0 to 4) := "10001";
  constant C_PIT1_CONTROL : std_logic_vector(0 to 4) := "10010";
  constant C_UART_BAUD    : std_logic_vector(0 to 4) := "10011";
  constant C_PIT2_PRELOAD : std_logic_vector(0 to 4) := "10100";
  constant C_PIT2_COUNTER : std_logic_vector(0 to 4) := "10101";
  constant C_PIT2_CONTROL : std_logic_vector(0 to 4) := "10110";
  constant C_SPARE2       : std_logic_vector(0 to 4) := "10111";
  constant C_PIT3_PRELOAD : std_logic_vector(0 to 4) := "11000";
  constant C_PIT3_COUNTER : std_logic_vector(0 to 4) := "11001";
  constant C_PIT3_CONTROL : std_logic_vector(0 to 4) := "11010";
  constant C_SPARE3       : std_logic_vector(0 to 4) := "11011";
  constant C_PIT4_PRELOAD : std_logic_vector(0 to 4) := "11100";
  constant C_PIT4_COUNTER : std_logic_vector(0 to 4) := "11101";
  constant C_PIT4_CONTROL : std_logic_vector(0 to 4) := "11110";
  constant C_SPARE4       : std_logic_vector(0 to 4) := "11111";

  signal lmb_reg_select     : std_logic;
  signal lmb_io_select      : std_logic;
  signal lmb_io_select_keep : std_logic;
  signal lmb_abus_Q         : std_logic_vector(2 - C_INTC_HAS_FAST - C_INTC_HAS_AE to 6);
  signal lmb_reg_read       : std_logic;
  signal lmb_reg_read_Q     : std_logic;
  signal lmb_reg_write      : std_logic;
  signal io_ready_Q         : std_logic;
  signal io_bus_read_data   : std_logic_vector(C_LMB_DWIDTH-1 downto 0);
  
  -- Register access
  signal wen                : std_logic;
  signal regaddr            : std_logic_vector(0 to 4);
  signal pit1_read          : std_logic;
  signal pit1_write_preload : std_logic;
  signal pit1_write_ctrl    : std_logic;
  signal pit2_read          : std_logic;
  signal pit2_write_preload : std_logic;
  signal pit2_write_ctrl    : std_logic;
  signal pit3_read          : std_logic;
  signal pit3_write_preload : std_logic;
  signal pit3_write_ctrl    : std_logic;
  signal pit4_read          : std_logic;
  signal pit4_write_preload : std_logic;
  signal pit4_write_ctrl    : std_logic;
  signal gpi1_read          : std_logic;
  signal gpi2_read          : std_logic;
  signal gpi3_read          : std_logic;
  signal gpi4_read          : std_logic;
  signal uart_tx_write      : std_logic;
  signal gpo1_write         : std_logic;
  signal gpo2_write         : std_logic;
  signal gpo3_write         : std_logic;
  signal gpo4_write         : std_logic;
  signal uart_status_read   : std_logic;
  signal uart_status_wait   : std_logic;
  signal uart_status_ready  : std_logic;
  signal uart_rx_read       : std_logic;
  signal uart_rx_wait       : std_logic;
  signal uart_rx_ready      : std_logic;
  signal uart_baud_write    : std_logic;
  signal intc_write_ciar    : std_logic;
  signal intc_write_cier    : std_logic;
  signal intc_write_cimr    : std_logic;
  signal intc_write_civar   : std_logic;
  signal intc_write_civear  : std_logic;
  signal intc_read_cisr     : std_logic;
  signal intc_read_cipr     : std_logic;
  signal write_data         : std_logic_vector(31 downto 0);
  signal io_reg_read_data   : std_logic_vector(31 downto 0);

  signal fit1_interrupt_i : std_logic;
  signal fit2_interrupt_i : std_logic;
  signal fit3_interrupt_i : std_logic;
  signal fit4_interrupt_i : std_logic;
  signal pit1_interrupt_i : std_logic;
  signal pit2_interrupt_i : std_logic;
  signal pit3_interrupt_i : std_logic;
  signal pit4_interrupt_i : std_logic;

  signal intc_irq_i       : std_logic;

  signal One : std_logic;               -- tied to '1';

  -- Preserve signals after synthesis for simulation UART support
  attribute KEEP : string;
  attribute KEEP of uart_tx_write : signal is "TRUE";
  attribute KEEP of write_data    : signal is "TRUE";

  signal config_reset_i : std_logic;

begin  -- architecture IMP

  config_reset_i <= Config_Reset when C_USE_CONFIG_RESET /= 0 else '0';

  -----------------------------------------------------------------------------
  -- Do the LMB address decoding
  -----------------------------------------------------------------------------
  One <= '1';
  -- Detect if IO Module register is accessed
  pselect_mask_reg : pselect_mask
    generic map (
      C_AW   => LMB_ABus'length,
      C_BAR  => C_BASEADDR,
      C_MASK => C_MASK)
    port map (
      A     => LMB_ABus,
      CS    => lmb_reg_select,
      Valid => One);

  -- Remember address, read, write and write data
  AccessReg : process(Clk) is
  begin
    if (Clk'event and Clk = '1') then
      if config_reset_i = '1' then
        lmb_abus_Q <= (others => '0');

        lmb_reg_read_Q <= '0';
        lmb_reg_read   <= '0';
        lmb_reg_write  <= '0';

        Write_Data(31 downto 0) <= (others => '0');
      else
        lmb_abus_Q <= LMB_ABus(LMB_ABus'high-LMB_ABus_Q'length+1-2 to LMB_ABus'high-2);

        if (uart_status_read = '1' or uart_rx_read = '1') and C_UART_ASYNC = 1 then
          lmb_reg_read_Q <= '0';
        else
          lmb_reg_read_Q <= lmb_reg_read;
        end if;
        lmb_reg_read   <= LMB_ReadStrobe  and lmb_reg_select and LMB_AddrStrobe;
        lmb_reg_write  <= LMB_WriteStrobe and lmb_reg_select and LMB_AddrStrobe;

        Write_Data(31 downto 0) <= LMB_WriteDBus(0 to 31);  -- Data to write to IO module
      end if;
    end if;
  end process AccessReg;

  Using_IO_Bus : if (C_USE_IO_BUS /= 0) generate

    signal io_read_keep   : std_logic;

  begin
    
    -- Detect if IO Module IO extension is accessed
    pselect_mask_io : pselect_mask
      generic map (
        C_AW   => LMB_ABus'length,
        C_BAR  => C_IO_BASEADDR,
        C_MASK => C_IO_MASK)
      port map (
        A     => LMB_ABus,
        CS    => lmb_io_select,
        Valid => One);

    AccessIO : process(Clk) is
    begin
      if (Clk'event and Clk = '1') then
        if Rst = '1' or TMR_Rst = '1' then
          IO_Addr_Strobe     <= '0';
          IO_Read_Strobe     <= '0';
          IO_Write_Strobe    <= '0';
          IO_Address         <= (others => '0');
          IO_Byte_Enable     <= (others => '0');
          IO_Write_Data      <= (others => '0');
          lmb_io_select_keep <= '0';
          io_read_keep       <= '0';
        elsif lmb_io_select = '1' and LMB_AddrStrobe = '1' then
          IO_Addr_Strobe     <= '1';
          IO_Read_Strobe     <= LMB_ReadStrobe;
          IO_Write_Strobe    <= LMB_WriteStrobe;
          IO_Address         <= LMB_ABus;
          IO_Byte_Enable     <= LMB_BE;
          IO_Write_Data      <= LMB_WriteDBus;
          lmb_io_select_keep <= '1';
          io_read_keep       <= LMB_ReadStrobe;
        else
          if IO_Ready = '1' then
            lmb_io_select_keep <= '0';
            io_read_keep       <= '0';
          end if;
          IO_Addr_Strobe  <= '0';
          IO_Read_Strobe  <= '0';
          IO_Write_Strobe <= '0';
        end if;
      end if;
    end process AccessIO;

    ReadyReg : process(Clk) is
    begin
      if (Clk'event and Clk = '1') then
        if config_reset_i = '1' then
          io_ready_Q <= '0';
        else
          io_ready_Q <= lmb_io_select_keep and IO_Ready;
        end if;
      end if;
    end process ReadyReg;

    ReadDataReg : process(Clk) is
    begin
      if (Clk'event and Clk = '1') then
        if config_reset_i = '1' then
          io_bus_read_data <= (others => '0');
        else
          if IO_Ready = '1' and io_read_keep = '1' then
            io_bus_read_data <= IO_Read_Data;
          else
            io_bus_read_data <= (others => '0');
          end if;
        end if;
      end if;
    end process ReadDataReg;
    
  end generate Using_IO_Bus;
  
  Not_Using_IO_Bus : if (C_USE_IO_BUS = 0) generate
    io_ready_Q         <= '0';
    io_bus_read_data   <= (others => '0');
    lmb_io_select      <= '0';
    lmb_io_select_keep <= '0';
    IO_Addr_Strobe     <= '0';
    IO_Read_Strobe     <= '0';
    IO_Write_Strobe    <= '0';
    IO_Address         <= (others => '0');
    IO_Byte_Enable     <= (others => '0');
    IO_Write_Data      <= (others => '0');
  end generate Not_Using_IO_Bus;
  
  -- Data read from IO module

  -- Standard LMB protocol with RAM data read combinatorial through LMB controller 
  Sl_DBus_LMB_Protocol_0 : if (C_LMB_PROTOCOL = 0) generate
  begin
    Sl_DBus(0 to 31) <= io_reg_read_data(31 downto 0) or io_bus_read_data(31 downto 0);
  end generate Sl_DBus_LMB_Protocol_0;

  -- Timing optimized LMB protocol with RAM data read clocked in LMB controller
  -- Sl_DBus needs to be clocked once to match clocked timing of RAM data read clocked
  -- Only works with MicroBlaze 8-stage pipe and C_LMB_PROTOCOL set to 1 on MicroBlaze
  Sl_DBus_LMB_Protocol_1 : if (C_LMB_PROTOCOL = 1) generate
  begin
    Sl_DBus_DFF : process(Clk) is
    begin
      if (Clk'event and Clk = '1') then
        if config_reset_i = '1' then
          Sl_DBus <= (others => '0');
        else        
          Sl_DBus(0 to 31) <= io_reg_read_data(31 downto 0) or io_bus_read_data(31 downto 0);
        end if;
      end if;
    end process Sl_DBus_DFF;
  end generate Sl_DBus_LMB_Protocol_1;
  
  Sl_Wait <= '1' when lmb_reg_read = '1' or
                      lmb_io_select_keep = '1' or
                      ((uart_status_wait = '1' or uart_rx_wait= '1') and C_UART_ASYNC = 1) else
             '0';

  Sl_UE   <= '0'; -- No Uncorrectable Errors
  Sl_CE   <= '0'; -- No Correctable Errors

  Sl_Ready <= '1' when lmb_reg_write  = '1' or
                       lmb_reg_read_Q = '1' or
                       io_ready_Q = '1' or
                       ((uart_status_ready = '1' or uart_rx_ready = '1') and C_UART_ASYNC = 1) else
              '0';

  uart_rx_read       <= '1' when regaddr = C_UART_RX      and lmb_reg_read  = '1' else '0'; 
  uart_tx_write      <= wen when regaddr = C_UART_TX      and lmb_reg_write = '1' else '0';
  uart_status_read   <= '1' when regaddr = C_UART_STATUS  and lmb_reg_read  = '1' else '0';
  uart_baud_write    <= wen when regaddr = C_UART_BAUD    and lmb_reg_write = '1' else '0';
  intc_write_cimr    <= wen when regaddr = C_IRQ_MODE     and lmb_reg_write = '1' else '0';
  gpo1_write         <= wen when regaddr = C_GPO1         and lmb_reg_write = '1' else '0';
  gpo2_write         <= wen when regaddr = C_GPO2         and lmb_reg_write = '1' else '0';
  gpo3_write         <= wen when regaddr = C_GPO3         and lmb_reg_write = '1' else '0';
  gpo4_write         <= wen when regaddr = C_GPO4         and lmb_reg_write = '1' else '0';
  gpi1_read          <= '1' when regaddr = C_GPI1         and lmb_reg_read  = '1' else '0';
  gpi2_read          <= '1' when regaddr = C_GPI2         and lmb_reg_read  = '1' else '0';
  gpi3_read          <= '1' when regaddr = C_GPI3         and lmb_reg_read  = '1' else '0';
  gpi4_read          <= '1' when regaddr = C_GPI4         and lmb_reg_read  = '1' else '0';
  intc_write_ciar    <= wen when regaddr = C_IRQ_ACK      and lmb_reg_write = '1' else '0';
  intc_write_cier    <= wen when regaddr = C_IRQ_ENABLE   and lmb_reg_write = '1' else '0';
  intc_read_cisr     <= '1' when regaddr = C_IRQ_STATUS   and lmb_reg_read  = '1' else '0';
  intc_read_cipr     <= '1' when regaddr = C_IRQ_PENDING  and lmb_reg_read  = '1' else '0';
  pit1_read          <= '1' when regaddr = C_PIT1_COUNTER and lmb_reg_read  = '1' else '0';
  pit1_write_preload <= wen when regaddr = C_PIT1_PRELOAD and lmb_reg_write = '1' else '0';
  pit1_write_ctrl    <= wen when regaddr = C_PIT1_CONTROL and lmb_reg_write = '1' else '0';
  pit2_read          <= '1' when regaddr = C_PIT2_COUNTER and lmb_reg_read  = '1' else '0';
  pit2_write_preload <= wen when regaddr = C_PIT2_PRELOAD and lmb_reg_write = '1' else '0';
  pit2_write_ctrl    <= wen when regaddr = C_PIT2_CONTROL and lmb_reg_write = '1' else '0';
  pit3_read          <= '1' when regaddr = C_PIT3_COUNTER and lmb_reg_read  = '1' else '0';
  pit3_write_preload <= wen when regaddr = C_PIT3_PRELOAD and lmb_reg_write = '1' else '0';
  pit3_write_ctrl    <= wen when regaddr = C_PIT3_CONTROL and lmb_reg_write = '1' else '0';
  pit4_read          <= '1' when regaddr = C_PIT4_COUNTER and lmb_reg_read  = '1' else '0';
  pit4_write_preload <= wen when regaddr = C_PIT4_PRELOAD and lmb_reg_write = '1' else '0';
  pit4_write_ctrl    <= wen when regaddr = C_PIT4_CONTROL and lmb_reg_write = '1' else '0';

  Using_Fast : if C_INTC_HAS_FAST = 1 and C_INTC_HAS_AE = 0 generate
  begin
    intc_write_civar  <= lmb_reg_write when lmb_abus_Q(1) = '1' else '0';
    intc_write_civear <= '0';
    wen <= not lmb_abus_Q(1);
    regaddr <= lmb_abus_Q(2 to 6);
  end generate Using_Fast;

  Using_Fast_AE : if C_INTC_HAS_FAST = 1 and C_INTC_HAS_AE = 1 generate
  begin
    intc_write_civar  <= lmb_reg_write when (lmb_abus_Q(0) = '0' and lmb_abus_Q(1) = '1') or
                                            (lmb_abus_Q(0) = '1' and lmb_abus_Q(6) = '0') else '0';
    intc_write_civear <= lmb_reg_write when (lmb_abus_Q(0) = '1' and lmb_abus_Q(6) = '1') else '0';
    wen <= not (lmb_abus_Q(0) or lmb_abus_Q(1));
    regaddr <= lmb_abus_Q(2 to 6) when lmb_abus_Q(0) = '0' else
               lmb_abus_Q(1 to 5);
  end generate Using_Fast_AE;

  Not_Using_Fast : if C_INTC_HAS_FAST = 0 generate
  begin
    intc_write_civar  <= '0';
    intc_write_civear <= '0';
    wen <= '1';
    regaddr <= lmb_abus_Q(2 to 6);
  end generate Not_Using_Fast;


  IOModule_Core_I1: iomodule_core
    generic map (
      C_TARGET               => C_TARGET,
      C_FREQ                 => C_FREQ,
      C_USE_CONFIG_RESET     => C_USE_CONFIG_RESET,
      C_AVOID_PRIMITIVES     => C_AVOID_PRIMITIVES,
      C_TMR                  => C_TMR,
      C_USE_TMR_DISABLE      => C_USE_TMR_DISABLE,

      -- UART generics
      C_USE_UART_RX          => C_USE_UART_RX,           -- [integer]
      C_USE_UART_TX          => C_USE_UART_TX,           -- [integer]
      C_UART_BAUDRATE        => C_UART_BAUDRATE,         -- [integer]
      C_UART_DATA_BITS       => C_UART_DATA_BITS,        -- [integer range 5 to 8]
      C_UART_USE_PARITY      => C_UART_USE_PARITY,       -- [integer]
      C_UART_ODD_PARITY      => C_UART_ODD_PARITY,       -- [integer]
      C_UART_RX_INTERRUPT    => C_UART_RX_INTERRUPT,     -- [integer]
      C_UART_TX_INTERRUPT    => C_UART_TX_INTERRUPT,     -- [integer]
      C_UART_ERROR_INTERRUPT => C_UART_ERROR_INTERRUPT,  -- [integer]
      C_UART_PROG_BAUDRATE   => C_UART_PROG_BAUDRATE,    -- [integer]
      C_UART_FREQ            => C_UART_FREQ,             -- [integer]
      C_UART_ASYNC           => C_UART_ASYNC,            -- [integer]
      C_UART_NUM_SYNC_FF     => C_UART_NUM_SYNC_FF,      -- [integer]

      -- FIT generics
      C_USE_FIT1        => C_USE_FIT1,         -- [integer]
      C_FIT1_No_CLOCKS  => C_FIT1_No_CLOCKS,   -- [integer]
      C_FIT1_INTERRUPT  => C_FIT1_INTERRUPT,   -- [integer]
      C_USE_FIT2        => C_USE_FIT2,         -- [integer]
      C_FIT2_No_CLOCKS  => C_FIT2_No_CLOCKS,   -- [integer]
      C_FIT2_INTERRUPT  => C_FIT2_INTERRUPT,   -- [integer]
      C_USE_FIT3        => C_USE_FIT3,         -- [integer]
      C_FIT3_No_CLOCKS  => C_FIT3_No_CLOCKS,   -- [integer]
      C_FIT3_INTERRUPT  => C_FIT3_INTERRUPT,   -- [integer]
      C_USE_FIT4        => C_USE_FIT4,         -- [integer]
      C_FIT4_No_CLOCKS  => C_FIT4_No_CLOCKS,   -- [integer]
      C_FIT4_INTERRUPT  => C_FIT4_INTERRUPT,   -- [integer]

      -- PIT generics
      C_USE_PIT1           => C_USE_PIT1,            -- [integer]
      C_PIT1_SIZE          => C_PIT1_SIZE,           -- [integer]
      C_PIT1_READABLE      => C_PIT1_READABLE,       -- [integer]
      C_PIT1_PRESCALER     => C_PIT1_PRESCALER,      -- [integer range 0 to 9]
      C_PIT1_INTERRUPT     => C_PIT1_INTERRUPT,      -- [integer]
      C_USE_PIT2           => C_USE_PIT2,            -- [integer]
      C_PIT2_SIZE          => C_PIT2_SIZE,           -- [integer]
      C_PIT2_READABLE      => C_PIT2_READABLE,       -- [integer]
      C_PIT2_PRESCALER     => C_PIT2_PRESCALER,      -- [integer range 0 to 9]
      C_PIT2_INTERRUPT     => C_PIT2_INTERRUPT,      -- [integer]
      C_USE_PIT3           => C_USE_PIT3,            -- [integer]
      C_PIT3_SIZE          => C_PIT3_SIZE,           -- [integer]
      C_PIT3_READABLE      => C_PIT3_READABLE,       -- [integer]
      C_PIT3_PRESCALER     => C_PIT3_PRESCALER,      -- [integer range 0 to 9]
      C_PIT3_INTERRUPT     => C_PIT3_INTERRUPT,      -- [integer]
      C_USE_PIT4           => C_USE_PIT4,            -- [integer]
      C_PIT4_SIZE          => C_PIT4_SIZE,           -- [integer]
      C_PIT4_READABLE      => C_PIT4_READABLE,       -- [integer]
      C_PIT4_PRESCALER     => C_PIT4_PRESCALER,      -- [integer range 0 to 9]
      C_PIT4_INTERRUPT     => C_PIT4_INTERRUPT,      -- [integer]

      -- GPO Generics
      C_USE_GPO1  => C_USE_GPO1,
      C_GPO1_SIZE => C_GPO1_SIZE,
      C_GPO1_INIT => C_GPO1_INIT,
      C_USE_GPO2  => C_USE_GPO2,
      C_GPO2_SIZE => C_GPO2_SIZE,
      C_GPO2_INIT => C_GPO2_INIT,
      C_USE_GPO3  => C_USE_GPO3,
      C_GPO3_SIZE => C_GPO3_SIZE,
      C_GPO3_INIT => C_GPO3_INIT,
      C_USE_GPO4  => C_USE_GPO4,
      C_GPO4_SIZE => C_GPO4_SIZE,
      C_GPO4_INIT => C_GPO4_INIT,

      -- GPI Generics
      C_USE_GPI1       => C_USE_GPI1,
      C_GPI1_SIZE      => C_GPI1_SIZE,
      C_GPI1_INTERRUPT => C_GPI1_INTERRUPT,
      C_USE_GPI2       => C_USE_GPI2, 
      C_GPI2_SIZE      => C_GPI2_SIZE,
      C_GPI2_INTERRUPT => C_GPI2_INTERRUPT,
      C_USE_GPI3       => C_USE_GPI3, 
      C_GPI3_SIZE      => C_GPI3_SIZE,
      C_GPI3_INTERRUPT => C_GPI3_INTERRUPT,
      C_USE_GPI4       => C_USE_GPI4, 
      C_GPI4_SIZE      => C_GPI4_SIZE,
      C_GPI4_INTERRUPT => C_GPI4_INTERRUPT,

      -- Interrupt Handler Generics
      C_ADDR_WIDTH        => C_ADDR_WIDTH,
      C_INTC_USE_EXT_INTR => C_INTC_USE_EXT_INTR,
      C_INTC_INTR_SIZE    => C_INTC_INTR_SIZE,
      C_INTC_LEVEL_EDGE   => C_INTC_LEVEL_EDGE,
      C_INTC_POSITIVE     => C_INTC_POSITIVE,
      C_INTC_HAS_FAST     => C_INTC_HAS_FAST,
      C_INTC_ADDR_WIDTH   => C_INTC_ADDR_WIDTH,
      C_INTC_BASE_VECTORS => C_INTC_BASE_VECTORS,
      C_INTC_ASYNC_INTR   => C_INTC_ASYNC_INTR,
      C_INTC_NUM_SYNC_FF  => C_INTC_NUM_SYNC_FF)

    port map (
      Config_Reset => Config_Reset,
      CLK          => CLK,
      Rst          => Rst,
      TMR_Rst      => TMR_Rst,
      TMR_Disable  => TMR_Disable,

      -- TMR voting inbetween redundant IO Modules
      ToVote       => ToVote,
      FromAVote    => FromAVote,
      FromBVote    => FromBVote,

      -- UART I/O
      UART_Clk       => UART_Clk,
      UART_Rst       => UART_Rst,
      UART_Rx        => UART_Rx,
      UART_Tx        => UART_Tx,
      UART_Interrupt => UART_Interrupt,

      -- FIT I/O
      FIT1_Interrupt => fit1_interrupt_i,
      FIT1_Toggle    => FIT1_Toggle,
      FIT2_Interrupt => fit2_interrupt_i,
      FIT2_Toggle    => FIT2_Toggle,
      FIT3_Interrupt => fit3_interrupt_i,
      FIT3_Toggle    => FIT3_Toggle,
      FIT4_Interrupt => fit4_interrupt_i,
      FIT4_Toggle    => FIT4_Toggle,

      -- PIT I/O
      PIT1_Enable    => PIT1_Enable,
      PIT1_Interrupt => pit1_interrupt_i,
      PIT1_Toggle    => PIT1_Toggle,
      PIT2_Enable    => PIT2_Enable,
      PIT2_Interrupt => pit2_interrupt_i,
      PIT2_Toggle    => PIT2_Toggle,
      PIT3_Enable    => PIT3_Enable,
      PIT3_Interrupt => pit3_interrupt_i,
      PIT3_Toggle    => PIT3_Toggle,
      PIT4_Enable    => PIT4_Enable,
      PIT4_Interrupt => pit4_interrupt_i,
      PIT4_Toggle    => PIT4_Toggle,

      -- GPO IO
      GPO1 => GPO1,
      GPO2 => GPO2,
      GPO3 => GPO3,
      GPO4 => GPO4,

      -- GPI IO
      GPI1           => GPI1,
      GPI1_Interrupt => GPI1_Interrupt,
      GPI2           => GPI2,
      GPI2_Interrupt => GPI2_Interrupt,
      GPI3           => GPI3,
      GPI3_Interrupt => GPI3_Interrupt,
      GPI4           => GPI4,
      GPI4_Interrupt => GPI4_Interrupt,

      -- Interrupt IO
      INTC_Interrupt         => INTC_Interrupt,
      INTC_IRQ               => intc_irq_i,
      INTC_Processor_Ack     => INTC_Processor_Ack,
      INTC_Interrupt_Address => INTC_Interrupt_Address,

      -- Register access
      PIT1_Read          => pit1_read,
      PIT1_Write_Preload => pit1_write_preload,
      PIT1_Write_Ctrl    => pit1_write_ctrl,
      PIT2_Read          => pit2_read,
      PIT2_Write_Preload => pit2_write_preload,
      PIT2_Write_Ctrl    => pit2_write_ctrl,
      PIT3_Read          => pit3_read,
      PIT3_Write_Preload => pit3_write_preload,
      PIT3_Write_Ctrl    => pit3_write_ctrl,
      PIT4_Read          => pit4_read,
      PIT4_Write_Preload => pit4_write_preload,
      PIT4_Write_Ctrl    => pit4_write_ctrl,
      GPI1_Read          => gpi1_read,
      GPI2_Read          => gpi2_read,
      GPI3_Read          => gpi3_read,
      GPI4_Read          => gpi4_read,
      UART_TX_Write      => uart_tx_write,
      UART_Baud_Write    => uart_baud_write,
      GPO1_Write         => gpo1_write,
      GPO2_Write         => gpo2_write,
      GPO3_Write         => gpo3_write,
      GPO4_Write         => gpo4_write,
      UART_Status_Read   => uart_status_read,
      UART_Status_Wait   => uart_status_wait,
      UART_Status_Ready  => uart_status_ready,
      UART_Rx_Read       => uart_rx_read,
      UART_Rx_Wait       => uart_rx_wait,
      UART_Rx_Ready      => uart_rx_ready,
      INTC_WRITE_CIAR    => intc_write_ciar,
      INTC_WRITE_CIER    => intc_write_cier,
      INTC_WRITE_CIMR    => intc_write_cimr,
      INTC_WRITE_CIVAR   => intc_write_civar,
      INTC_WRITE_CIVEAR  => intc_write_civear,
      INTC_CIVAR_ADDR    => regaddr,
      INTC_READ_CISR     => intc_read_cisr,
      INTC_READ_CIPR     => intc_read_cipr,
      Write_Data         => write_data,
      Read_Data          => io_reg_read_data);

   INTC_IRQ     <= intc_irq_i;
   INTC_IRQ_OUT <= intc_irq_i;

   FIT1_Interrupt <= fit1_interrupt_i;
   FIT2_Interrupt <= fit2_interrupt_i;
   FIT3_Interrupt <= fit3_interrupt_i;
   FIT4_Interrupt <= fit4_interrupt_i;
   PIT1_Interrupt <= pit1_interrupt_i;
   PIT2_Interrupt <= pit2_interrupt_i;
   PIT3_Interrupt <= pit3_interrupt_i;
   PIT4_Interrupt <= pit4_interrupt_i;
  
end architecture IMP;


