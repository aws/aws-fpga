
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
-- File          : clk_wiz_drp.vhd
-- Version       : v1.0
-- Description   : AXI bus slave interface for dynamic clock configuration.
--                 This file containts actual interface between the core
--                 and MMCM/PLL hard macro.
-- Standard      : VHDL-93
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-- Structure:
--             axi_clk_wiz.vhd
--               -clk_wiz_drp.vhd
-------------------------------------------------------------------------------
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
    use IEEE.std_logic_unsigned.all;
    use ieee.std_logic_misc.all;


library work;
    use work.clk_mmcm_a_ipif_pkg.all;
    use work.clk_mmcm_a_proc_common_pkg.all;

Library UNISIM;
use UNISIM.VCOMPONENTS.ALL;

-------------------------------------------------------------------------------
--                     Definition of Generics
-------------------------------------------------------------------------------
-- AXI4 Slave Single block generics
-------------------------------------------------------------------------------
--    C_S_AXI_ADDR_WIDTH     -- AXI4 address bus width
--    C_S_AXI_DATA_WIDTH     -- AXI4 Slave bus width
--    CE_NUMBERS             -- read/write chip enble no.
-------------------------------------------------------------------------------
--                  Definition of Ports
-------------------------------------------------------------------------------
-- AXI Slave Interface --   INPUT/OUTPUT Signals
-------------------------------------------------------------------------------
--    Bus2IP_Clk             -- bus clock
--    Bus2IP_Rst             -- bus reset
--    -- Bus 2 IP IPIC interface
--    Bus2IP_RdCE            -- bus read chip enable signals
--    Bus2IP_WrCE            -- bus write chip enable signals
--    Bus2IP_Addr            -- bus address bits
--    Bus2IP_Data            -- bus to ip data
--    -- IP 2 Bus IPIC interface
--    IP2Bus_Data     -- data 
--    IP2Bus_WrAck    -- write ack 
--    IP2Bus_RdAck    -- read ack 

-------------------------------------------------------------------------------

entity clk_mmcm_a_clk_wiz_drp is
  generic
  (
    ----------------
    C_S_AXI_ADDR_WIDTH     : integer;
    C_S_AXI_DATA_WIDTH     : integer;
    C_FAMILY               : string;
    ----------------
    CE_NUMBERS             : integer
    ----------------
  );
  port
  (
   -- IP Interconnect (IPIC) port signals ---------
  Bus2IP_Clk             : in  std_logic;
  Bus2IP_Rst             : in  std_logic;
  -- Bus 2 IP IPIC interface
  Bus2IP_RdCE            : in std_logic_vector(0 to CE_NUMBERS-1);
  Bus2IP_WrCE            : in std_logic_vector(0 to CE_NUMBERS-1);
  Bus2IP_Addr            : in std_logic_vector(0 to (C_S_AXI_ADDR_WIDTH-1));
  Bus2IP_Data            : in std_logic_vector(0 to (C_S_AXI_DATA_WIDTH-1));
  -- IP 2 Bus IPIC interface
  IP2Bus_Data     : out std_logic_vector(0 to (C_S_AXI_DATA_WIDTH-1));
  IP2Bus_WrAck    : out std_logic;
  IP2Bus_RdAck    : out std_logic;
  ----------------  clocking macro interface  -------------------
  -- Clock in ports
  -- Clock out ports
  clk_out1          : out    std_logic;
  clk_out2          : out    std_logic;
  clk_out3          : out    std_logic;
  -- Status and control signals
  locked            : out    std_logic;
  clk_in1           : in     std_logic
  );

end entity clk_mmcm_a_clk_wiz_drp;
-------------------------------------------------------------------------------
-- Architecture Section
-------------------------------------------------------------------------------
architecture imp of clk_mmcm_a_clk_wiz_drp is


component clk_mmcm_a_clk_wiz
port
 (-- Clock in ports
  -- Clock out ports
  clk_out1          : out    std_logic;
  clk_out2          : out    std_logic;
  clk_out3          : out    std_logic;
  -- Dynamic reconfiguration ports
  daddr             : in     std_logic_vector(6 downto 0);
  dclk              : in     std_logic;
  den               : in     std_logic;
  din                : in     std_logic_vector(15 downto 0);
  dout                : out    std_logic_vector(15 downto 0);
  dwe               : in     std_logic;
  drdy              : out    std_logic;
  -- Status and control signals
  reset             : in     std_logic;
  locked            : out    std_logic;
  clk_in1           : in     std_logic
 );
end component;

  component clk_mmcm_a_mmcm_drp 
  generic (
  S1_CLKFBOUT_MULT          : integer := 5;
  S1_CLKFBOUT_PHASE         : integer := 0;
  S1_CLKFBOUT_FRAC          : integer := 125; 
  S1_CLKFBOUT_FRAC_EN       : integer := 1; 
  S1_BANDWIDTH              : string := "LOW";
  S1_DIVCLK_DIVIDE          : integer := 1;
  S1_CLKOUT0_DIVIDE         : integer := 1;
  S1_CLKOUT0_PHASE          : integer := 0;
  S1_CLKOUT0_DUTY           : integer := 50000;
  S1_CLKOUT0_FRAC           : integer := 125; 
  S1_CLKOUT0_FRAC_EN        : integer := 1; 
  
  S1_CLKOUT1_DIVIDE         : integer := 1;
  S1_CLKOUT1_PHASE          : integer := 0;
  S1_CLKOUT1_DUTY           : integer := 50000;
  
  S1_CLKOUT2_DIVIDE         : integer := 1;
  S1_CLKOUT2_PHASE          : integer := 0;
  S1_CLKOUT2_DUTY           : integer := 50000;
  
  S1_CLKOUT3_DIVIDE         : integer := 1;
  S1_CLKOUT3_PHASE          : integer := 0;
  S1_CLKOUT3_DUTY           : integer := 50000;
  
  S1_CLKOUT4_DIVIDE         : integer := 1;
  S1_CLKOUT4_PHASE          : integer := 0;
  S1_CLKOUT4_DUTY           : integer := 50000;
  
  S1_CLKOUT5_DIVIDE         : integer := 1;
  S1_CLKOUT5_PHASE          : integer := 0;
  S1_CLKOUT5_DUTY           : integer := 50000;
  
  S1_CLKOUT6_DIVIDE         : integer := 1;
  S1_CLKOUT6_PHASE          : integer := 0;
  S1_CLKOUT6_DUTY           : integer := 50000
  );
  port (
  S2_CLKFBOUT_MULT : in std_logic_vector( 7 downto 0);
  S2_CLKFBOUT_FRAC: in std_logic_vector( 9 downto 0);     
  S2_CLKFBOUT_FRAC_EN: in std_logic;
  S2_DIVCLK_DIVIDE: in std_logic_vector( 7 downto 0);     
  S2_CLKOUT0_DIVIDE: in std_logic_vector( 7 downto 0);    
  S2_CLKOUT0_FRAC: in std_logic_vector( 9 downto 0);      
  S2_CLKOUT0_FRAC_EN: in std_logic;
  S2_CLKOUT1_DIVIDE: in std_logic_vector( 7 downto 0);    
  S2_CLKOUT2_DIVIDE: in std_logic_vector( 7 downto 0);    
  S2_CLKOUT3_DIVIDE: in std_logic_vector( 7 downto 0);    
  S2_CLKOUT4_DIVIDE: in std_logic_vector( 7 downto 0);    
  S2_CLKOUT5_DIVIDE: in std_logic_vector( 7 downto 0);    
  S2_CLKOUT6_DIVIDE: in std_logic_vector( 7 downto 0);    
  LOAD : in std_logic;
  SADDR: in std_logic;
  SEN  : in std_logic;
  RST  : in std_logic;
  SRDY : out std_logic;
  SCLK : in std_logic;
  DO  : in std_logic_vector(15 downto 0);
  DRDY  : in std_logic;
  LOCKED  : in std_logic;
  DWE  : out std_logic;
  DEN  : out std_logic;
  DADDR  : out std_logic_vector( 6 downto 0);
  DI  : out std_logic_vector(15 downto 0);
  DCLK  : out std_logic;
  RST_MMCM_PLL  : out std_logic
  );
  end component;
-------------------------------------------------------------------------------
-- Constant Declarations
-------------------------------------------------------------------------------
constant DATA_SIZE_DRP     : integer := 16;

constant ADDR_SIZE_DRP     : integer := 7;

type mem_type is array (0 to 31) of std_logic_vector(31 downto 0);

signal ram_clk_config : mem_type := (
-- initialize memory with valid clock configuration
   X"00000F01", 
   X"00000000",
   X"0000000C", 
   X"00000000",
   X"0000C350",
   X"00000004",
   X"00000000",
   X"0000C350",
   X"00000003",
   X"00000000",
   X"0000C350",
   X"00000001",
   X"00000000",
   X"0000C350",
   X"00000001",
   X"00000000",
   X"0000C350",
   X"00000001",
   X"00000000",
   X"0000C350",
   X"00000001",
   X"00000000",
   X"0000C350",
   X"00000000",
   X"00000000",
   X"00000000",
   X"00000000",
   X"00000000",
   X"00000000",
   X"00000000",
   X"00000000",
   X"00000000"
 );
-------------------------------------------------------------------------------
-- Signal Declarations
-------------------------------------------------------------------------------
signal ram_addr     : std_logic_vector(4 downto 0);
signal daddr        : std_logic_vector(ADDR_SIZE_DRP-1 downto 0);
signal dout         : std_logic_vector(DATA_SIZE_DRP-1 downto 0);
signal din          : std_logic_vector(DATA_SIZE_DRP-1 downto 0);
signal den          : std_logic;
signal dwe          : std_logic;
signal drdy         : std_logic;
signal dclk         : std_logic;
signal register_rdce_select      : std_logic_vector(0 to 7);
signal register_wrce_select      : std_logic_vector(0 to 7);
-------------------------------------------------------------------------------
signal wrack_reg_1               : std_logic;
signal wrack_reg_2               : std_logic;
signal rdack_reg_1               : std_logic;
signal rdack_reg_2               : std_logic;
-------------------------------------------------------------------------------
signal locked_int                : std_logic;
signal srdy                      : std_logic;
signal reset                     : std_logic;
signal program_status            : std_logic_vector(0 to 1);
signal clk_mon_error_reg         :std_logic_vector(15 downto 0);
signal clk_mon_error_reg_sig         :std_logic_vector(15 downto 0);
signal clk_mon_error         :std_logic_vector(15 downto 0);
signal clk_mon_error_reg_d       :std_logic_vector(15 downto 0);
signal interrupt_enable_reg         :std_logic_vector(15 downto 0) ;
signal interrupt_status_reg         :std_logic_vector(15 downto 0) ;
signal interrupt_status_reg_wr         :std_logic_vector(15 downto 0) ;
signal load_enable_reg_d         :std_logic;
signal load_enable_reg_actual         :std_logic;
signal SEN         :std_logic;
signal Reset_axi         :std_logic;
signal load_enable_reg           :std_logic_vector(0 to 31);
signal clkfbout_reg           :std_logic_vector(0 to 31) := X"00000F01";
signal clkout0_reg           :std_logic_vector(0 to 31) := X"0000000C" ;
signal config_reg           :std_logic_vector(0 to 31);
begin

-------------------------------------------------------------------------------
-- Assign temporary internal signal to separate out Addr bit 23 to Addr bit 29
-- from PLB address lines
-- As the addresses are word aligned, it is required to trim the
-- address bit 30 and 31. The incoming address from PLB is word aligned.
-- The internal register file interface are at sequential address like
-- 0x00h, 0x01h...etc
-------------------------------------------------------------------------------
--  daddr_i <= Bus2IP_Addr(23 to 29);
  ram_addr <= Bus2IP_Addr(C_S_AXI_ADDR_WIDTH-7 to C_S_AXI_ADDR_WIDTH-3);

-------------------------------------------------------------------------------
   WR_RD_ACK_PROCESS:process(Bus2IP_Clk) is
   begin
       if Bus2IP_Clk'event and Bus2IP_Clk='1' then
         if(Bus2IP_Rst = RESET_ACTIVE or Bus2IP_Addr = x"000") then
           wrack_reg_1    <= '0';
           wrack_reg_2    <= '0';
           rdack_reg_1    <= '0';
           rdack_reg_2    <= '0';
           IP2Bus_WrAck   <= '0';
           IP2Bus_RdAck   <= '0';
         else
           wrack_reg_1    <= Bus2IP_WrCE(CE_NUMBERS-1);
           wrack_reg_2    <= wrack_reg_1;
           rdack_reg_1    <= Bus2IP_RdCE(CE_NUMBERS-1) or Bus2IP_RdCE(0);
           rdack_reg_2    <= rdack_reg_1;
           -- Generate the WRITE ACK back to PLB
           IP2Bus_WrAck   <=  wrack_reg_1 and (not wrack_reg_2);
           -- Generate the READ ACK back to PLB
           IP2Bus_RdAck   <=  rdack_reg_1 and (not rdack_reg_2);
         end if;
       end if;
   end process WR_RD_ACK_PROCESS;

-------------------------------------------------------------------------------

register_wrce_select <= Bus2IP_WrCE(1) & Bus2IP_WrCE(2) & Bus2IP_WrCE(3) & Bus2IP_WrCE(4) & Bus2IP_WrCE(CE_NUMBERS-1) & 
                        Bus2IP_Addr(C_S_AXI_ADDR_WIDTH-9 to C_S_AXI_ADDR_WIDTH-8) & Bus2IP_Addr(C_S_AXI_ADDR_WIDTH-11);

-------------------------------------------------------------------------------
DATA_WR_PROCESS: process(Bus2IP_Clk) is
begin
    if (Bus2IP_Clk'event and Bus2IP_Clk='1') then
      if(Bus2IP_Rst = RESET_ACTIVE) then
       -- reset values
	    ram_clk_config(0)  <=    X"00000F01";
	    ram_clk_config(1)  <=    X"00000000";
	    ram_clk_config(2)  <=    X"0000000C";
	    ram_clk_config(3)  <=    X"00000000";
	    ram_clk_config(4)  <=    X"0000C350";
	    ram_clk_config(5)  <=    X"00000004";
	    ram_clk_config(6)  <=    X"00000000";
	    ram_clk_config(7)  <=    X"0000C350";
	    ram_clk_config(8)  <=    X"00000003";
	    ram_clk_config(9)  <=    X"00000000";
	    ram_clk_config(10) <=    X"0000C350";
	    ram_clk_config(11) <=    X"00000001";
	    ram_clk_config(12) <=    X"00000000";
	    ram_clk_config(13) <=    X"0000C350";
	    ram_clk_config(14) <=    X"00000001";
	    ram_clk_config(15) <=    X"00000000";
	    ram_clk_config(16) <=    X"0000C350";
	    ram_clk_config(17) <=    X"00000001";
	    ram_clk_config(18) <=    X"00000000";
	    ram_clk_config(19) <=    X"0000C350";
	    ram_clk_config(20) <=    X"00000001";
	    ram_clk_config(21) <=    X"00000000";
	    ram_clk_config(22) <=    X"0000C350";
	    ram_clk_config(23) <=    X"00000000";
	    ram_clk_config(24) <=    X"00000000";
	    ram_clk_config(25) <=    X"00000000";
	    ram_clk_config(26) <=    X"00000000";
	    ram_clk_config(27) <=    X"00000000";
	    ram_clk_config(28) <=    X"00000000";
	    ram_clk_config(29) <=    X"00000000";
	    ram_clk_config(30) <=    X"00000000";
	    ram_clk_config(31) <=    X"00000000";
        load_enable_reg    <=    X"00000000";
        interrupt_enable_reg <=  X"0000";
        interrupt_status_reg_wr <= X"0000";
      else
        case register_wrce_select is
          when "00001000"   => 
            if(Bus2IP_Addr = x"25C")  then
              load_enable_reg <= Bus2IP_Data;
            elsif(Bus2IP_Addr = x"200" ) then
              clkfbout_reg <= Bus2IP_Data;
              ram_clk_config(0) <= "00000" & or_reduce(clkfbout_reg(6 to 15)) & clkfbout_reg(6 to 31);
            elsif(Bus2IP_Addr = x"208" ) then
              clkout0_reg <= Bus2IP_Data;
              ram_clk_config(2) <= "0000000000000" & or_reduce(clkout0_reg(14 to 23)) & clkout0_reg(14 to 31);
            elsif(Bus2IP_Addr = x"25C")  then
              load_enable_reg <= Bus2IP_Data;
            elsif(Bus2IP_Addr /= x"000" ) then
            ram_clk_config(conv_integer(ram_addr)) <= Bus2IP_Data;
             end if;
          when "00001100"   => 
            if(Bus2IP_Addr = x"35C")  then
              load_enable_reg <= Bus2IP_Data;
            elsif(Bus2IP_Addr /= x"000" ) then
            ram_clk_config(conv_integer(ram_addr)) <= Bus2IP_Data;
             end if;
          when "00011000"   => 
              interrupt_enable_reg <= Bus2IP_Data(16 to 31);
         when "00101000"   =>
              interrupt_status_reg_wr <= Bus2IP_Data(16 to 31) ;
            -- coverage off
            when others =>   null;
            -- coverage on
        end case;
      end if;
    end if;	  
end process DATA_WR_PROCESS;



  locked <= locked_int;
  program_status(0) <= srdy; -- used for testing purpose
  program_status(1) <= locked_int;
-------------------------------------------------------------------------------
-- Status Register,DRP Register File Interface (RFI) can be READ
-------------------------------------------------------------------------------
  register_rdce_select <= Bus2IP_RdCE(1) & -- Status Register
                          Bus2IP_RdCE(2) & 
                          Bus2IP_RdCE(3) & 
                          Bus2IP_RdCE(4) & 
        Bus2IP_RdCE(CE_NUMBERS-1) & Bus2IP_Addr(C_S_AXI_ADDR_WIDTH-9 to C_S_AXI_ADDR_WIDTH-8) & Bus2IP_Addr(C_S_AXI_ADDR_WIDTH-11);

-------------------------------------------------------------------------------
-- The upper bits are always '0'.
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- LOCAL_REG_READ_PROCESS
-------------------------
LOCAL_REG_READ_PROCESS: process (register_rdce_select,
                                 program_status,
                                 clk_mon_error_reg,
                                 interrupt_status_reg,
                                 interrupt_enable_reg,
                                 ram_clk_config,ram_addr,Bus2IP_Addr,config_reg) is
begin
    case  register_rdce_select is
    -- bus2ip_rdce(1,2,8)
      when "00001000"   =>
         if(Bus2IP_Addr = x"25C") then
        IP2Bus_Data <= config_reg;
       else 
         IP2Bus_Data <= ram_clk_config(conv_integer(ram_addr));
       end if;
      when "00001100"   =>
         if(Bus2IP_Addr = x"35C") then
        IP2Bus_Data <= config_reg;
       else 
         IP2Bus_Data <= ram_clk_config(conv_integer(ram_addr));
       end if;
      when "10001000"   =>
         IP2Bus_Data(30 to 31) <= program_status;
         IP2Bus_Data(0 to 29) <= (others => '0');
      when "01001000"   =>
         IP2Bus_Data(0 to 15) <=  (others => '0') ; --clock monitor error status register
         IP2Bus_Data(16 to 31) <= clk_mon_error_reg;
      when "00101000"   =>
         IP2Bus_Data(0 to 15) <= (others => '0'); -- clock monitor interrupt status register
         IP2Bus_Data(16 to 31) <= interrupt_status_reg;
      when "00011000"   =>
         IP2Bus_Data(0 to 15) <= (others => '0'); -- clock monitor interrupt enable register
         IP2Bus_Data(16 to 31) <= interrupt_enable_reg;
      -- coverage off
      when others  =>
         IP2Bus_Data <= (others => '0');
      -- coverage on
    end case;
end process LOCAL_REG_READ_PROCESS;

Interrupt_Enable_proc: process ( Bus2IP_Clk  ) is
begin
 if (Bus2IP_Clk'event and Bus2IP_Clk='1') then
   if(Bus2IP_Rst = RESET_ACTIVE) then
    clk_mon_error_reg <= X"0000";
    clk_mon_error_reg_d <= X"0000";
    clk_mon_error_reg_sig <= X"0000";
    interrupt_status_reg <= X"0000";
   else 
   clk_mon_error_reg <= clk_mon_error_reg_sig;
    for I in 15 downto 0 loop
    case  register_wrce_select is
      when "00101000"   =>
        interrupt_status_reg(I) <= interrupt_status_reg(I) and (not(interrupt_status_reg_wr(I)));
        clk_mon_error_reg_d <= clk_mon_error_reg_sig;
      when others  =>
        interrupt_status_reg(I) <= interrupt_enable_reg(I) and ((clk_mon_error_reg_sig(I) and (not(clk_mon_error_reg_d(I)))) or interrupt_status_reg(I)) ;
    end case;
    end loop;
    end if;
    end if;
end process Interrupt_Enable_proc;


Load_Enable_proc: process (Bus2IP_Clk) is
begin
  if (Bus2IP_Clk'event and Bus2IP_Clk='1') then
    if(Bus2IP_Rst = RESET_ACTIVE) then
     load_enable_reg_actual <= '0';
     load_enable_reg_d <= '0';
     SEN <= '0';
  else
      if(((Bus2IP_Addr = x"25C") or (Bus2IP_Addr = x"35C")) and ((register_wrce_select = "00001000") or (register_wrce_select = "00001100")) and (Bus2IP_Data(31) = '1')) then
        load_enable_reg_d <= '1';
        else
          if (locked_int = '1') then
            load_enable_reg_d <= '0';
          else
            load_enable_reg_d <= '1';
          end if;
      end if;
      load_enable_reg_actual <= load_enable_reg_d; 
      SEN <=  load_enable_reg_d and (not(load_enable_reg_actual ));
   end if;
 end if;     
end process Load_Enable_proc;
config_reg <= load_enable_reg(0 to 30) & load_enable_reg_d;

  clk_inst: clk_mmcm_a_clk_wiz
   port map ( 
  -- Clock out ports  
   clk_out1 => clk_out1,
   clk_out2 => clk_out2,
   clk_out3 => clk_out3,
  -- Dynamic reconfiguration ports             
   daddr => daddr,
   dclk => dclk,
   den => den,
   din => din,
   dout => dout,
   drdy => drdy,
   dwe => dwe,
  -- Status and control signals                
   reset => reset, 
   locked => locked_int,
   -- Clock in ports
   clk_in1 => clk_in1
 );
mmcm_drp_inst: clk_mmcm_a_mmcm_drp generic map (
  S1_CLKFBOUT_MULT          =>  15,
  S1_CLKFBOUT_PHASE         =>  0,
  S1_CLKFBOUT_FRAC          =>  0,
  S1_CLKFBOUT_FRAC_EN       =>  0, 
  S1_BANDWIDTH              => "OPTIMIZED",
  S1_DIVCLK_DIVIDE          =>  1,
  S1_CLKOUT0_DIVIDE         =>  12,
  S1_CLKOUT0_PHASE          =>  0,
  S1_CLKOUT0_DUTY           =>  50000, 
  S1_CLKOUT0_FRAC           =>  0, 
  S1_CLKOUT0_FRAC_EN        =>  0,  
  
  S1_CLKOUT1_DIVIDE         =>  4,
  S1_CLKOUT1_PHASE          =>  0,
  S1_CLKOUT1_DUTY           =>  50000,
  
  S1_CLKOUT2_DIVIDE         =>  3,         
  S1_CLKOUT2_PHASE          =>  0,          
  S1_CLKOUT2_DUTY           =>  50000,
  
  S1_CLKOUT3_DIVIDE         =>  1,         
  S1_CLKOUT3_PHASE          =>  0,          
  S1_CLKOUT3_DUTY           =>  50000,
  
  S1_CLKOUT4_DIVIDE         =>  1,         
  S1_CLKOUT4_PHASE          =>  0,          
  S1_CLKOUT4_DUTY           =>  50000,
  
  S1_CLKOUT5_DIVIDE         =>  1,         
  S1_CLKOUT5_PHASE          =>  0,          
 
  S1_CLKOUT5_DUTY           =>  50000,
  
  S1_CLKOUT6_DIVIDE         =>  1,     
  S1_CLKOUT6_PHASE          =>  0,      
  S1_CLKOUT6_DUTY           =>  50000
  )
  port map (
  S2_CLKFBOUT_MULT => ram_clk_config(0)(15 downto 8),
  S2_CLKFBOUT_FRAC => ram_clk_config(0)(25 downto 16),     
  S2_CLKFBOUT_FRAC_EN => ram_clk_config(0)(26),  
  S2_DIVCLK_DIVIDE => ram_clk_config(0)(7 downto 0),     
  S2_CLKOUT0_DIVIDE => ram_clk_config(2)(7 downto 0),    
  S2_CLKOUT0_FRAC => ram_clk_config(2)(17 downto 8),      
  S2_CLKOUT0_FRAC_EN => ram_clk_config(2)(18),   
  S2_CLKOUT1_DIVIDE => ram_clk_config(5)(7 downto 0),    
  S2_CLKOUT2_DIVIDE => ram_clk_config(8)(7 downto 0),    
  S2_CLKOUT3_DIVIDE => ram_clk_config(11)(7 downto 0),    
  S2_CLKOUT4_DIVIDE => ram_clk_config(14)(7 downto 0),    
  S2_CLKOUT5_DIVIDE => ram_clk_config(17)(7 downto 0),    
  S2_CLKOUT6_DIVIDE => ram_clk_config(20)(7 downto 0),    
  LOAD => SEN,                 
  SADDR => config_reg(30), 
  SEN   => SEN,
  RST  => Bus2IP_Rst,
  SRDY => srdy,
  SCLK => bus2ip_clk,
  DO  => dout,
  DRDY  => drdy,
  LOCKED  => locked_int,
  DWE  => dwe,
  DEN  => den,
  DADDR  => daddr,
  DI  => din,
  DCLK  => dclk,
  RST_MMCM_PLL  => reset
  );
end architecture imp;
--------------------------------------------------------------------------------

