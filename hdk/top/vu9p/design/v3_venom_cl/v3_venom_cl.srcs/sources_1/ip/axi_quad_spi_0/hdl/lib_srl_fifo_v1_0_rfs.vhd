-- cntr_incr_decr_addn_f - entity / architecture pair
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
-- ** Copyright (c) 2005 - 2010 Xilinx, Inc. All rights reserved.         **
-- **                                                                     **
-- ** This copyright and support notice must be retained as part          **
-- ** of this text at all times.                                          **
-- **                                                                     **
-- *************************************************************************
--
-------------------------------------------------------------------------------
-- Filename:        cntr_incr_decr_addn_f.vhd
--
-- Description:     This counter can increment, decrement or skip ahead
--                  by an arbitrary amount.
--
--                  If Reset is active, the value Cnt synchronously resets
--                  to all ones. (This reset value, different than the
--                  customary reset value of zero, caters to the original
--                  application of cntr_incr_decr_addn_f as the address
--                  counter for srl_fifo_rbu_f.)
--
--                  Otherwise, on each Clk, one is added to Cnt if Incr is
--                  asserted and one is subtracted if Decr is asserted. (If
--                  both are asserted, then there is no change to Cnt.)
--
--                  If Decr is not asserted, then the input value,
--                  Nm_to_add, is added. (Simultaneous assertion of Incr
--                  would add one more.) If Decr is asserted, then
--                  N_to_add, is ignored, i.e., it is possible to decrement
--                  by one or add N, but not both, and Decr overrides. 
--
--                  The value that Cnt will take on at the next clock
--                  is available as Cnt_p1.
--
--
-- VHDL-Standard:   VHDL'93
-------------------------------------------------------------------------------
-- Structure:   
--              cntr_incr_decr_addn_f.vhd
--
-------------------------------------------------------------------------------
--
-- History:
--   FLO   12/30/05   First Version.
--
-- ~~~~~~
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
--      predecessor value by # clks:            "*_p#"
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
--
entity cntr_incr_decr_addn_f is
  generic (
    C_SIZE   : natural;
    C_FAMILY : string  := "nofamily"
  );
  port (
    Clk           : in  std_logic;
    Reset         : in  std_logic; -- Note: the counter resets to all ones!
    Incr          : in  std_logic;
    Decr          : in  std_logic;
    N_to_add      : in  std_logic_vector(C_SIZE-1 downto 0);
    Cnt           : out std_logic_vector(C_SIZE-1 downto 0);
    Cnt_p1        : out std_logic_vector(C_SIZE-1 downto 0)
  );
end entity cntr_incr_decr_addn_f;


---(
library lib_srl_fifo_v1_0_2;
library ieee;
use     ieee.numeric_std.UNSIGNED;
use     ieee.numeric_std."+";
library unisim;
use     unisim.all; -- Make unisim entities available for default binding.
--
architecture imp of cntr_incr_decr_addn_f is


--  constant COUNTER_PRIMS_AVAIL : boolean :=
--               supported(C_FAMILY, (u_MUXCY_L, u_XORCY, u_FDS));
  constant COUNTER_PRIMS_AVAIL : boolean := false;
            

  signal cnt_i             : std_logic_vector(Cnt'range);  
  signal cnt_i_p1          : std_logic_vector(Cnt'range);

   ---------------------------------------------------------------------------- 
   -- Unisim components declared locally for maximum avoidance of default
   -- binding and vcomponents version issues.
   ---------------------------------------------------------------------------- 
  component MUXCY_L
      port
      (
          LO : out std_ulogic;
          CI : in std_ulogic;
          DI : in std_ulogic;
          S : in std_ulogic
      );
  end component;

  component XORCY
      port
      (
          O : out std_ulogic;
          CI : in std_ulogic;
          LI : in std_ulogic
      );
  end component;

  component FDS
      generic
      (
          INIT : bit := '1'
      );
      port
      (
          Q : out std_ulogic;
          C : in std_ulogic;
          D : in std_ulogic;
          S : in std_ulogic
      );
  end component;

begin  -- architecture imp


  ---(
  INFERRED_GEN : if COUNTER_PRIMS_AVAIL = false generate
    --
    CNT_I_P1_PROC : process( cnt_i, N_to_add, Decr, Incr
                         ) is
        --
        function qual_n_to_add(N_to_add : std_logic_vector;
                           Decr : std_logic
                          ) return UNSIGNED is
            variable r: UNSIGNED(N_to_add'range);
        begin
            for i in r'range loop
                r(i) := N_to_add(i) or Decr;
            end loop;
            return r;
        end;
        --
        function to_singleton_unsigned(s : std_logic) return unsigned is
            variable r : unsigned(0 to 0) := (others => s);
        begin
            return r;
        end;
        --
    begin
        cnt_i_p1 <= std_logic_vector(   UNSIGNED(cnt_i)
                                      + qual_n_to_add(N_to_add, Decr)
                                      + to_singleton_unsigned(Incr)
                                    );
    end process;
    --
    CNT_I_PROC : process(Clk) is
    begin
        if Clk'event and Clk = '1' then
            if Reset = '1' then
                cnt_i <= (others => '1');
            else
                cnt_i <= cnt_i_p1;
            end if;
        end if;
    end process;
    --
  end generate INFERRED_GEN;
  ---)

  Cnt    <= cnt_i; 
  Cnt_p1 <= cnt_i_p1; 

end architecture imp;
---)


-- srl_fifo_rbu_f - entity / architecture pair
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
-- ** Copyright (c) 2005-2010 Xilinx, Inc. All rights reserved.           **
-- **                                                                     **
-- ** This copyright and support notice must be retained as part          **
-- ** of this text at all times.                                          **
-- **                                                                     **
-- *************************************************************************
--
-------------------------------------------------------------------------------
-- Filename:      dynshreg_f.vhd
--
-- Description:   This module implements a dynamic shift register with clock
--                enable. (Think, for example, of the function of the SRL16E.)
--                The width and depth of the shift register are selectable
--                via generics C_WIDTH and C_DEPTH, respectively. The C_FAMILY
--                allows the implementation to be tailored to the target
--                FPGA family. An inferred implementation is used if C_FAMILY
--                is "nofamily" (the default) or if synthesis will not produce
--                an optimal implementation.  Otherwise, a structural
--                implementation will be generated.
--
--                There is no restriction on the values of C_WIDTH and
--                C_DEPTH and, in particular, the C_DEPTH does not have
--                to be a power of two.
--
--
-- VHDL-Standard:   VHDL'93
-------------------------------------------------------------------------------
-- Structure:   
--
-------------------------------------------------------------------------------
-- Author:          Farrell Ostler
--
-- History:
--   FLO   12/05/05   First Version. Derived from srl_fifo_rbu.
--
-- ~~~~~~
--  FLO         06/07/15
-- ^^^^^^
--  -XST was observed in some cases to produce a suboptimal implementation when
--   the depth, C_DEPTH, is a power of two and less than the native depth
--   of the SRL. Now a structural implementation is used for these cases.
--   (The particular case where a problem was found was for C_DEPTH=4 and
--    C_FAMILY="virtex5". In this case, rather than use an SRL, XST
--    made an implementation out of discrete FFs and LUTs.)
--  -Added Description.
-- ~~~~~~
--  FLO         07/12/12
-- ^^^^^^
--  Using function clog2 now instead of log2 to eliminate superfluous warnings.
-- ~~~~~~
--
--     DET     1/17/2008     v5_0
-- ~~~~~~
--     - Changed proc_common library version to v5_0
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
--      predecessor value by # clks:            "*_p#"

---(
library ieee;
use     ieee.std_logic_1164.all;
use     ieee.numeric_std.UNSIGNED;
use     ieee.numeric_std.TO_INTEGER;
library lib_pkg_v1_0_2;
use     lib_pkg_v1_0_2.lib_pkg.clog2;

entity dynshreg_f is
  generic (
    C_DEPTH  : positive := 32;
    C_DWIDTH : natural := 1;
    C_FAMILY : string := "nofamily"
  );
  port (
    Clk   : in  std_logic;
    Clken : in  std_logic;
    Addr  : in  std_logic_vector(0 to clog2(C_DEPTH)-1);
    Din   : in  std_logic_vector(0 to C_DWIDTH-1);
    Dout  : out std_logic_vector(0 to C_DWIDTH-1)
  );
end dynshreg_f;


library unisim;
use     unisim.all; -- Make unisim entities available for default binding.
architecture behavioral of dynshreg_f is

--  constant K_FAMILY : families_type := str2fam(C_FAMILY);
  --
--  constant W32 : boolean := supported(K_FAMILY, u_SRLC32E) and
--                            (C_DEPTH > 16 or not supported(K_FAMILY, u_SRL16E));
--  constant W16 : boolean := supported(K_FAMILY, u_SRLC16E) and not W32;
  constant W32 : boolean := (C_DEPTH > 16);
  constant W16 : boolean := (not W32);
  -- XST faster if these two constants are declared here
  -- instead of in STRUCTURAL_A_GEN. (I.25)
  --
  function power_of_2(n: positive) return boolean is
      variable i: positive := 1;
  begin
      while n > i loop i := i*2; end loop;
      return n = i;
  end power_of_2;
  --
--  constant USE_INFERRED     : boolean :=    (    power_of_2(C_DEPTH)
--                                             and (   (W16 and C_DEPTH >= 16)
--                                                  or (W32 and C_DEPTH >= 32)
--                                                 )
--                                            )
--                                         or (not W32 and not W16);

   constant USE_INFERRED : boolean := true;
  -- As of I.32, XST is not infering optimal dynamic shift registers for
  -- depths not a power of two (by not taking advantage of don't care
  -- at output when address not within the range of the depth)
  -- or a power of two less than the native SRL depth (by building shift
  -- register out of discrete FFs and LUTs instead of SRLs).
  constant USE_STRUCTURAL_A : boolean := not USE_INFERRED;

  function min(a, b: natural) return natural is
  begin
      if a<b then return a; else return b; end if;
  end min;

 ---------------------------------------------------------------------------- 
 -- Unisim components declared locally for maximum avoidance of default
 -- binding and vcomponents version issues.
 ---------------------------------------------------------------------------- 
  component SRLC16E
      generic
      (
          INIT : bit_vector := X"0000"
      );
      port
      (
          Q : out STD_ULOGIC;
          Q15 : out STD_ULOGIC;
          A0 : in STD_ULOGIC;
          A1 : in STD_ULOGIC;
          A2 : in STD_ULOGIC;
          A3 : in STD_ULOGIC;
          CE : in STD_ULOGIC;
          CLK : in STD_ULOGIC;
          D : in STD_ULOGIC
      );
  end component;

  component SRLC32E
      generic
      (
          INIT : bit_vector := X"00000000"
      );
      port
      (
          Q : out STD_ULOGIC;
          Q31 : out STD_ULOGIC;
          A : in STD_LOGIC_VECTOR (4 downto 0);
          CE : in STD_ULOGIC;
          CLK : in STD_ULOGIC;
          D : in STD_ULOGIC
      );
  end component;


begin

  ---(


  ---(
  INFERRED_GEN : if USE_INFERRED = true generate
    type dataType is array (0 to C_DEPTH-1) of std_logic_vector(0 to C_DWIDTH-1);
    signal data: dataType;
  begin
    process(Clk)
    begin
      if Clk'event and Clk = '1' then
        if Clken = '1' then
          data <= Din & data(0 to C_DEPTH-2);
        end if;
      end if;
    end process;

    Dout <= data(TO_INTEGER(UNSIGNED(Addr)))
                when (TO_INTEGER(UNSIGNED(Addr)) < C_DEPTH)
                else
            (others => '-');
  end generate INFERRED_GEN;
  ---)

end behavioral;
---)


-- srl_fifo_rbu_f - entity / architecture pair
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
-- ** Copyright (c) 2007-2010 Xilinx, Inc. All rights reserved.           **
-- **                                                                     **
-- ** This copyright and support notice must be retained as part          **
-- ** of this text at all times.                                          **
-- **                                                                     **
-- *************************************************************************
--
-------------------------------------------------------------------------------
-- Filename:        srl_fifo_rbu_f.vhd
--
-- Description:     A small-to-medium depth FIFO with optional
--                  capability to back up and reread data.  For
--                  data storage, the SRL elements native to the
--                  target FGPA family are used. If the FIFO depth
--                  exceeds the available depth of the SRL elements,
--                  then SRLs are cascaded and MUXFN elements are
--                  used to select the output of the appropriate SRL stage.
--
--                  Features:
--                      - Width and depth are arbitrary, but each doubling of
--                        depth, starting from the native SRL depth, adds
--                        a level of MUXFN. Generally, in performance-oriented
--                        applications, the fifo depth may need to be limited to
--                        not exceed the SRL cascade depth supported by local
--                        fast interconnect or the number of MUXFN levels.
--                        However, deeper fifos will correctly build.
--                      - Commands: read, write, and reread n.
--                      - Flags: empty and full.
--                      - The reread n command (executed by applying
--                        a non-zero value, n, to signal Num_To_Reread
--                        for one clock period) allows n
--                        previously read elements to be restored to the FIFO,
--                        limited, however, to the number of elements that have
--                        not been overwritten. (It is the user's responsibility
--                        to assure that the elements being restored are
--                        actually in the FIFO storage; once the depth of the
--                        FIFO has been written, the maximum number that can
--                        be restored is equal to the vacancy.)
--                        The reread capability does not cost extra LUTs or FFs.
--                      - Commands may be asserted simultaneously.
--                        However, if read and reread n are asserted
--                        simultaneously, only the read is carried out.
--                      - Overflow and underflow are detected and latched until
--                        Reset. The state of the FIFO is undefined during
--                        status of underflow or overflow.
--                        Underflow can occur only by reading the FIFO when empty.
--                        Overflow can occur either from a write, a reread n,
--                        or a combination of both that would result in more
--                        elements occupying the FIFO that its C_DEPTH.
--                      - Any of the signals FIFO_Full, Underflow, or Overflow
--                        left unconnected can be expected to be trimmed.
--                      - The Addr output is always one less than the current
--                        occupancy when the FIFO is non-empty, and is all ones
--                        otherwise. Therefore, the value <FIFO_Empty, Addr>--
--                        i.e. FIFO_Empty concatenated on the left with Addr--
--                        when taken as a signed value, is one less than the
--                        current occupancy.
--                        This information can be used to generate additional
--                        flags, if needed.
--
-- VHDL-Standard:   VHDL'93
-------------------------------------------------------------------------------
-- Structure:   
--              srl_fifo_rbu_f.vhd
--                  dynshreg_f.vhd
--                  cntr_incr_decr_addn_f.vhd
--
-------------------------------------------------------------------------------
-- Author:          Farrell Ostler
--
-- History:
--   FLO   12/05/05   First Version. Derived from srl_fifo_rbu.
-- ~~~~~~
--  FLO         2007-12-12
-- ^^^^^^
--  Using function clog2 now instead of log2 to eliminate superfluous warnings.
-- ~~~~~~
--
--     DET     1/17/2008     v5_0
-- ~~~~~~
--     - Changed lib library version to v5_0
--     - Incorporated new disclaimer header
-- ^^^^^^
--  FLO         2008-11-25
-- ^^^^^^
--  Changed to functionally equivalent code to generate FIFO_Full. The new code
--  steers the current XST toward a better implementation. CR 496211.
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
--      predecessor value by # clks:            "*_p#"
--      counter signals:                        "*cnt*"
--      clock enable signals:                   "*_ce" 
--      internal version of output port         "*_i"
--      device pins:                            "*_pin" 
--      ports:                                  - Names begin with Uppercase 
--      processes:                              "*_PROCESS" 
--      component instantiations:               "<ENTITY_>I_<#|FUNC>
-------------------------------------------------------------------------------


library ieee;
use     ieee.std_logic_1164.all;
use     ieee.numeric_std.UNSIGNED;
use     ieee.numeric_std.">=";
use     ieee.numeric_std.TO_UNSIGNED;
library lib_pkg_v1_0_2;
use     lib_pkg_v1_0_2.lib_pkg.clog2;
library lib_srl_fifo_v1_0_2;

entity srl_fifo_rbu_f is
  generic (
    C_DWIDTH : natural;
    C_DEPTH  : positive := 16;
    C_FAMILY : string   := "nofamily"
    );
  port (
    Clk           : in  std_logic;
    Reset         : in  std_logic;
    FIFO_Write    : in  std_logic;
    Data_In       : in  std_logic_vector(0 to C_DWIDTH-1);
    FIFO_Read     : in  std_logic;
    Data_Out      : out std_logic_vector(0 to C_DWIDTH-1);
    FIFO_Full     : out std_logic;
    FIFO_Empty    : out std_logic;
    Addr          : out std_logic_vector(0 to clog2(C_DEPTH)-1);
    Num_To_Reread : in  std_logic_vector(0 to clog2(C_DEPTH)-1);
    Underflow     : out std_logic;
    Overflow      : out std_logic
    );
end entity srl_fifo_rbu_f;


architecture imp of srl_fifo_rbu_f is

  function bitwise_or(s: std_logic_vector) return std_logic is
    variable v: std_logic := '0';
  begin
    for i in s'range loop v := v or s(i); end loop;
    return v;
  end bitwise_or;

  constant ADDR_BITS : integer := clog2(C_DEPTH);
  
    -- An extra bit will be carried as the empty flag.
  signal addr_i                 : std_logic_vector(ADDR_BITS downto 0);  
  signal addr_i_p1              : std_logic_vector(ADDR_BITS downto 0);
  signal num_to_reread_zeroext  : std_logic_vector(ADDR_BITS downto 0);
  signal fifo_empty_i           : std_logic;
  signal overflow_i             : std_logic;
  signal underflow_i            : std_logic;
  signal fifo_full_p1           : std_logic;

begin

    fifo_empty_i           <= addr_i(ADDR_BITS);
    Addr(0 to ADDR_BITS-1) <= addr_i(ADDR_BITS-1 downto 0);
    FIFO_Empty             <= fifo_empty_i;
  
    num_to_reread_zeroext <= '0' & Num_To_Reread;
  

    ----------------------------------------------------------------------------
    -- The FIFO address counter. Addresses the next element to be read.
    -- All ones when the FIFO is empty. 
    ----------------------------------------------------------------------------
    CNTR_INCR_DECR_ADDN_F_I : entity lib_srl_fifo_v1_0_2.cntr_incr_decr_addn_f
        generic map (
          C_SIZE   => ADDR_BITS + 1,
          C_FAMILY => C_FAMILY 
        )
        port map (
          Clk           => Clk,
          Reset         => Reset,
          Incr          => FIFO_Write,
          Decr          => FIFO_Read,
          N_to_add      => num_to_reread_zeroext,
          Cnt           => addr_i,
          Cnt_p1        => addr_i_p1
        );


    ----------------------------------------------------------------------------
    -- The dynamic shift register that holds the FIFO elements.
    ----------------------------------------------------------------------------
    DYNSHREG_F_I : entity lib_srl_fifo_v1_0_2.dynshreg_f
        generic map (
            C_DEPTH   => C_DEPTH,
            C_DWIDTH  => C_DWIDTH,
            C_FAMILY  => C_FAMILY
        )
        port map (
            Clk   => Clk,
            Clken => FIFO_Write,
            Addr  => addr_i(ADDR_BITS-1 downto 0),
            Din   => Data_In,
            Dout  => Data_Out
        );

    
    ----------------------------------------------------------------------------
    -- Full flag.
    ----------------------------------------------------------------------------
    fifo_full_p1 <= '1' when (  addr_i_p1
                              = std_logic_vector(
                                    TO_UNSIGNED(C_DEPTH-1, ADDR_BITS+1)
                                )
                             )
                    else '0';

    FULL_PROCESS: process (Clk)
    begin
        if Clk'event and Clk='1' then
          if Reset='1' then
              FIFO_Full <= '0';
          else
              FIFO_Full <= fifo_full_p1;
          end if;
        end if;
    end process;

  
    ----------------------------------------------------------------------------
    -- Underflow detection.
    ----------------------------------------------------------------------------
    UNDERFLOW_PROCESS: process (Clk)
    begin
        if Clk'event and Clk='1' then
            if Reset = '1' then
                underflow_i <= '0';
            elsif underflow_i = '1' then
                underflow_i <= '1';      -- Underflow sticks until reset
            else
                underflow_i <= fifo_empty_i and FIFO_Read;
            end if;
        end if;
    end process;
  
    Underflow <= underflow_i;
  

    ----------------------------------------------------------------------------
    -- Overflow detection.
    -- The only case of non-erroneous operation for which addr_i (including
    -- the high-order bit used as the empty flag) taken as an unsigned value
    -- may be greater than or equal to C_DEPTH is when the FIFO is empty.
    -- No overflow is possible when FIFO_Read, since Num_To_Reread is
    -- overriden in this case and the number elements can at most remain
    -- unchanged (that being when there is a simultaneous FIFO_Write).
    -- However, when there is no FIFO_Read and there is either a
    -- FIFO_Write or a restoration of one or more read elements, or both, then
    -- addr_i, extended by the carry-out bit, becoming greater than
    -- or equal to C_DEPTH indicates an overflow.
    ----------------------------------------------------------------------------
    OVERFLOW_PROCESS: process (Clk)
    begin
        if Clk'event and Clk='1' then
            if Reset = '1' then
                overflow_i <= '0';
            elsif overflow_i = '1' then
                overflow_i <= '1';       -- Overflow sticks until Reset
            elsif FIFO_Read = '0' and
                  (FIFO_Write= '1' or bitwise_or(Num_To_Reread)='1') and
                  UNSIGNED(addr_i_p1) >= C_DEPTH then
                overflow_i <= '1';
            else
                overflow_i <= '0';
            end if;
        end if;
    end process;
  
    Overflow <= overflow_i;

end architecture imp;


-- srl_fifo_f - entity / architecture pair
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
-- ** Copyright (c) 2005-2010 Xilinx, Inc. All rights reserved.           **
-- **                                                                     **
-- ** This copyright and support notice must be retained as part          **
-- ** of this text at all times.                                          **
-- **                                                                     **
-- *************************************************************************
--
-------------------------------------------------------------------------------
-- Filename:        srl_fifo_f.vhd
--
-- Description:     A small-to-medium depth FIFO. For
--                  data storage, the SRL elements native to the
--                  target FGPA family are used. If the FIFO depth
--                  exceeds the available depth of the SRL elements,
--                  then SRLs are cascaded and MUXFN elements are
--                  used to select the output of the appropriate SRL stage.
--
--                  Features:
--                      - Width and depth are arbitrary, but each doubling of
--                        depth, starting from the native SRL depth, adds
--                        a level of MUXFN. Generally, in performance-oriented
--                        applications, the fifo depth may need to be limited to
--                        not exceed the SRL cascade depth supported by local
--                        fast interconnect or the number of MUXFN levels.
--                        However, deeper fifos will correctly build.
--                      - Commands: read, write.
--                      - Flags: empty and full.
--                      - The Addr output is always one less than the current
--                        occupancy when the FIFO is non-empty, and is all ones
--                        otherwise. Therefore, the value <FIFO_Empty, Addr>--
--                        i.e. FIFO_Empty concatenated on the left to Addr--
--                        when taken as a signed value, is one less than the
--                        current occupancy.
--
-- VHDL-Standard:   VHDL'93
-------------------------------------------------------------------------------
-- Structure:   
--              srl_fifo_f.vhd
--                srl_fifo_rbu_f.vhd
--                proc_common_pkg.vhd
--
-------------------------------------------------------------------------------
-- Author:          Farrell Ostler
--
-- History:
--   FLO   12/13/05   First Version.
--
-- FLO            04/27/06
-- ^^^^^^
--   C_FAMILY made to default to "nofamily".
-- ~~~~~~
--  FLO         2007-12-12
-- ^^^^^^
--  Using function clog2 now instead of log2 to eliminate superfluous warnings.
-- ~~~~~~
--
--     DET     1/17/2008     v5_0
-- ~~~~~~
--     - Changed proc_common library version to v5_0
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
--      predecessor value by # clks:            "*_p#"


library ieee;
use     ieee.std_logic_1164.all;
library lib_srl_fifo_v1_0_2;
library lib_pkg_v1_0_2;
use     lib_pkg_v1_0_2.lib_pkg.clog2;
--
entity srl_fifo_f is
  generic (
    C_DWIDTH : natural;
    C_DEPTH  : positive := 16;
    C_FAMILY : string := "nofamily"
    );
  port (
    Clk           : in  std_logic;
    Reset         : in  std_logic;
    FIFO_Write    : in  std_logic;
    Data_In       : in  std_logic_vector(0 to C_DWIDTH-1);
    FIFO_Read     : in  std_logic;
    Data_Out      : out std_logic_vector(0 to C_DWIDTH-1);
    FIFO_Empty    : out std_logic;
    FIFO_Full     : out std_logic;
    Addr          : out std_logic_vector(0 to clog2(C_DEPTH)-1)
    );

end entity srl_fifo_f;


--
architecture imp of srl_fifo_f is

attribute DowngradeIPIdentifiedWarnings: string;

attribute DowngradeIPIdentifiedWarnings of imp : architecture is "yes";

    constant ZEROES : std_logic_vector(0 to clog2(C_DEPTH)-1) := (others => '0');
begin

    I_SRL_FIFO_RBU_F : entity lib_srl_fifo_v1_0_2.srl_fifo_rbu_f
    generic map (
                 C_DWIDTH => C_DWIDTH,
                 C_DEPTH  => C_DEPTH,
                 C_FAMILY => C_FAMILY
    )
    port map (
                 Clk           => Clk,
                 Reset         => Reset,
                 FIFO_Write    => FIFO_Write,
                 Data_In       => Data_In,
                 FIFO_Read     => FIFO_Read,
                 Data_Out      => Data_Out,
                 FIFO_Full     => FIFO_Full,
                 FIFO_Empty    => FIFO_Empty,
                 Addr          => Addr,
                 Num_To_Reread => ZEROES,
                 Underflow     => open,
                 Overflow      => open
    );

end architecture imp;


