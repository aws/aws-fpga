-- Copyright 1986-2022 Xilinx, Inc. All Rights Reserved.
-- Copyright 2022-2024 Advanced Micro Devices, Inc. All Rights Reserved.
-- --------------------------------------------------------------------------------
-- Tool Version: Vivado v.2024.2 (lin64) Build 5239630 Fri Nov 08 22:34:34 MST 2024
-- Date        : Mon Oct 13 02:16:27 2025
-- Host        : ip-192-168-0-99 running 64-bit Ubuntu 24.04.1 LTS
-- Command     : write_vhdl -force -mode funcsim
--               /home/ubuntu/chipyard/sims/firesim/platforms/f2/aws-fpga-firesim-f2/hdk/cl/developer_designs/cl_f2-midasexamples-GCD-NoConfig-DefaultF1Config/ip/clk_wiz_0_firesim/clk_wiz_0_firesim_sim_netlist.vhdl
-- Design      : clk_wiz_0_firesim
-- Purpose     : This VHDL netlist is a functional simulation representation of the design and should not be modified or
--               synthesized. This netlist cannot be used for SDF annotated simulation.
-- Device      : xcvu47p-fsvh2892-2-e
-- --------------------------------------------------------------------------------
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
entity clk_wiz_0_firesim_clk_wiz is
  port (
    clk_out1 : out STD_LOGIC;
    clk_out2 : out STD_LOGIC;
    clk_out3 : out STD_LOGIC;
    clk_out4 : out STD_LOGIC;
    clk_out5 : out STD_LOGIC;
    clk_out6 : out STD_LOGIC;
    reset : in STD_LOGIC;
    locked : out STD_LOGIC;
    clk_in1 : in STD_LOGIC
  );
end clk_wiz_0_firesim_clk_wiz;

architecture STRUCTURE of clk_wiz_0_firesim_clk_wiz is
  signal clk_in1_clk_wiz_0_firesim : STD_LOGIC;
  signal clk_out1_clk_wiz_0_firesim : STD_LOGIC;
  signal clk_out2_clk_wiz_0_firesim : STD_LOGIC;
  signal clk_out3_clk_wiz_0_firesim : STD_LOGIC;
  signal clk_out4_clk_wiz_0_firesim : STD_LOGIC;
  signal clk_out5_clk_wiz_0_firesim : STD_LOGIC;
  signal clk_out6_clk_wiz_0_firesim : STD_LOGIC;
  signal clkfbout_buf_clk_wiz_0_firesim : STD_LOGIC;
  signal clkfbout_clk_wiz_0_firesim : STD_LOGIC;
  signal NLW_mmcme4_adv_inst_CDDCDONE_UNCONNECTED : STD_LOGIC;
  signal NLW_mmcme4_adv_inst_CLKFBOUTB_UNCONNECTED : STD_LOGIC;
  signal NLW_mmcme4_adv_inst_CLKFBSTOPPED_UNCONNECTED : STD_LOGIC;
  signal NLW_mmcme4_adv_inst_CLKINSTOPPED_UNCONNECTED : STD_LOGIC;
  signal NLW_mmcme4_adv_inst_CLKOUT0B_UNCONNECTED : STD_LOGIC;
  signal NLW_mmcme4_adv_inst_CLKOUT1B_UNCONNECTED : STD_LOGIC;
  signal NLW_mmcme4_adv_inst_CLKOUT2B_UNCONNECTED : STD_LOGIC;
  signal NLW_mmcme4_adv_inst_CLKOUT3B_UNCONNECTED : STD_LOGIC;
  signal NLW_mmcme4_adv_inst_CLKOUT6_UNCONNECTED : STD_LOGIC;
  signal NLW_mmcme4_adv_inst_DRDY_UNCONNECTED : STD_LOGIC;
  signal NLW_mmcme4_adv_inst_PSDONE_UNCONNECTED : STD_LOGIC;
  signal NLW_mmcme4_adv_inst_DO_UNCONNECTED : STD_LOGIC_VECTOR ( 15 downto 0 );
  attribute BOX_TYPE : string;
  attribute BOX_TYPE of clkf_buf : label is "PRIMITIVE";
  attribute XILINX_LEGACY_PRIM : string;
  attribute XILINX_LEGACY_PRIM of clkf_buf : label is "BUFG";
  attribute XILINX_TRANSFORM_PINMAP : string;
  attribute XILINX_TRANSFORM_PINMAP of clkf_buf : label is "VCC:CE";
  attribute BOX_TYPE of clkin1_ibuf : label is "PRIMITIVE";
  attribute CAPACITANCE : string;
  attribute CAPACITANCE of clkin1_ibuf : label is "DONT_CARE";
  attribute IBUF_DELAY_VALUE : string;
  attribute IBUF_DELAY_VALUE of clkin1_ibuf : label is "0";
  attribute IFD_DELAY_VALUE : string;
  attribute IFD_DELAY_VALUE of clkin1_ibuf : label is "AUTO";
  attribute BOX_TYPE of clkout1_buf : label is "PRIMITIVE";
  attribute XILINX_LEGACY_PRIM of clkout1_buf : label is "BUFG";
  attribute XILINX_TRANSFORM_PINMAP of clkout1_buf : label is "VCC:CE";
  attribute BOX_TYPE of clkout2_buf : label is "PRIMITIVE";
  attribute XILINX_LEGACY_PRIM of clkout2_buf : label is "BUFG";
  attribute XILINX_TRANSFORM_PINMAP of clkout2_buf : label is "VCC:CE";
  attribute BOX_TYPE of clkout3_buf : label is "PRIMITIVE";
  attribute XILINX_LEGACY_PRIM of clkout3_buf : label is "BUFG";
  attribute XILINX_TRANSFORM_PINMAP of clkout3_buf : label is "VCC:CE";
  attribute BOX_TYPE of clkout4_buf : label is "PRIMITIVE";
  attribute XILINX_LEGACY_PRIM of clkout4_buf : label is "BUFG";
  attribute XILINX_TRANSFORM_PINMAP of clkout4_buf : label is "VCC:CE";
  attribute BOX_TYPE of clkout5_buf : label is "PRIMITIVE";
  attribute XILINX_LEGACY_PRIM of clkout5_buf : label is "BUFG";
  attribute XILINX_TRANSFORM_PINMAP of clkout5_buf : label is "VCC:CE";
  attribute BOX_TYPE of clkout6_buf : label is "PRIMITIVE";
  attribute XILINX_LEGACY_PRIM of clkout6_buf : label is "BUFG";
  attribute XILINX_TRANSFORM_PINMAP of clkout6_buf : label is "VCC:CE";
  attribute BOX_TYPE of mmcme4_adv_inst : label is "PRIMITIVE";
begin
clkf_buf: unisim.vcomponents.BUFGCE
    generic map(
      CE_TYPE => "ASYNC",
      SIM_DEVICE => "ULTRASCALE_PLUS"
    )
        port map (
      CE => '1',
      I => clkfbout_clk_wiz_0_firesim,
      O => clkfbout_buf_clk_wiz_0_firesim
    );
clkin1_ibuf: unisim.vcomponents.IBUF
    generic map(
      IOSTANDARD => "DEFAULT"
    )
        port map (
      I => clk_in1,
      O => clk_in1_clk_wiz_0_firesim
    );
clkout1_buf: unisim.vcomponents.BUFGCE
    generic map(
      CE_TYPE => "ASYNC",
      SIM_DEVICE => "ULTRASCALE_PLUS"
    )
        port map (
      CE => '1',
      I => clk_out1_clk_wiz_0_firesim,
      O => clk_out1
    );
clkout2_buf: unisim.vcomponents.BUFGCE
    generic map(
      CE_TYPE => "ASYNC",
      SIM_DEVICE => "ULTRASCALE_PLUS"
    )
        port map (
      CE => '1',
      I => clk_out2_clk_wiz_0_firesim,
      O => clk_out2
    );
clkout3_buf: unisim.vcomponents.BUFGCE
    generic map(
      CE_TYPE => "ASYNC",
      SIM_DEVICE => "ULTRASCALE_PLUS"
    )
        port map (
      CE => '1',
      I => clk_out3_clk_wiz_0_firesim,
      O => clk_out3
    );
clkout4_buf: unisim.vcomponents.BUFGCE
    generic map(
      CE_TYPE => "ASYNC",
      SIM_DEVICE => "ULTRASCALE_PLUS"
    )
        port map (
      CE => '1',
      I => clk_out4_clk_wiz_0_firesim,
      O => clk_out4
    );
clkout5_buf: unisim.vcomponents.BUFGCE
    generic map(
      CE_TYPE => "ASYNC",
      SIM_DEVICE => "ULTRASCALE_PLUS"
    )
        port map (
      CE => '1',
      I => clk_out5_clk_wiz_0_firesim,
      O => clk_out5
    );
clkout6_buf: unisim.vcomponents.BUFGCE
    generic map(
      CE_TYPE => "ASYNC",
      SIM_DEVICE => "ULTRASCALE_PLUS"
    )
        port map (
      CE => '1',
      I => clk_out6_clk_wiz_0_firesim,
      O => clk_out6
    );
mmcme4_adv_inst: unisim.vcomponents.MMCME4_ADV
    generic map(
      BANDWIDTH => "OPTIMIZED",
      CLKFBOUT_MULT_F => 63.000000,
      CLKFBOUT_PHASE => 0.000000,
      CLKFBOUT_USE_FINE_PS => "FALSE",
      CLKIN1_PERIOD => 8.000000,
      CLKIN2_PERIOD => 0.000000,
      CLKOUT0_DIVIDE_F => 31.500000,
      CLKOUT0_DUTY_CYCLE => 0.500000,
      CLKOUT0_PHASE => 0.000000,
      CLKOUT0_USE_FINE_PS => "FALSE",
      CLKOUT1_DIVIDE => 9,
      CLKOUT1_DUTY_CYCLE => 0.500000,
      CLKOUT1_PHASE => 0.000000,
      CLKOUT1_USE_FINE_PS => "FALSE",
      CLKOUT2_DIVIDE => 10,
      CLKOUT2_DUTY_CYCLE => 0.500000,
      CLKOUT2_PHASE => 0.000000,
      CLKOUT2_USE_FINE_PS => "FALSE",
      CLKOUT3_DIVIDE => 18,
      CLKOUT3_DUTY_CYCLE => 0.500000,
      CLKOUT3_PHASE => 0.000000,
      CLKOUT3_USE_FINE_PS => "FALSE",
      CLKOUT4_CASCADE => "FALSE",
      CLKOUT4_DIVIDE => 19,
      CLKOUT4_DUTY_CYCLE => 0.500000,
      CLKOUT4_PHASE => 0.000000,
      CLKOUT4_USE_FINE_PS => "FALSE",
      CLKOUT5_DIVIDE => 21,
      CLKOUT5_DUTY_CYCLE => 0.500000,
      CLKOUT5_PHASE => 0.000000,
      CLKOUT5_USE_FINE_PS => "FALSE",
      CLKOUT6_DIVIDE => 1,
      CLKOUT6_DUTY_CYCLE => 0.500000,
      CLKOUT6_PHASE => 0.000000,
      CLKOUT6_USE_FINE_PS => "FALSE",
      COMPENSATION => "ZHOLD",
      DIVCLK_DIVIDE => 5,
      IS_CLKFBIN_INVERTED => '0',
      IS_CLKIN1_INVERTED => '0',
      IS_CLKIN2_INVERTED => '0',
      IS_CLKINSEL_INVERTED => '0',
      IS_PSEN_INVERTED => '0',
      IS_PSINCDEC_INVERTED => '0',
      IS_PWRDWN_INVERTED => '0',
      IS_RST_INVERTED => '0',
      REF_JITTER1 => 0.010000,
      REF_JITTER2 => 0.010000,
      SS_EN => "FALSE",
      SS_MODE => "CENTER_HIGH",
      SS_MOD_PERIOD => 10000,
      STARTUP_WAIT => "FALSE"
    )
        port map (
      CDDCDONE => NLW_mmcme4_adv_inst_CDDCDONE_UNCONNECTED,
      CDDCREQ => '0',
      CLKFBIN => clkfbout_buf_clk_wiz_0_firesim,
      CLKFBOUT => clkfbout_clk_wiz_0_firesim,
      CLKFBOUTB => NLW_mmcme4_adv_inst_CLKFBOUTB_UNCONNECTED,
      CLKFBSTOPPED => NLW_mmcme4_adv_inst_CLKFBSTOPPED_UNCONNECTED,
      CLKIN1 => clk_in1_clk_wiz_0_firesim,
      CLKIN2 => '0',
      CLKINSEL => '1',
      CLKINSTOPPED => NLW_mmcme4_adv_inst_CLKINSTOPPED_UNCONNECTED,
      CLKOUT0 => clk_out1_clk_wiz_0_firesim,
      CLKOUT0B => NLW_mmcme4_adv_inst_CLKOUT0B_UNCONNECTED,
      CLKOUT1 => clk_out2_clk_wiz_0_firesim,
      CLKOUT1B => NLW_mmcme4_adv_inst_CLKOUT1B_UNCONNECTED,
      CLKOUT2 => clk_out3_clk_wiz_0_firesim,
      CLKOUT2B => NLW_mmcme4_adv_inst_CLKOUT2B_UNCONNECTED,
      CLKOUT3 => clk_out4_clk_wiz_0_firesim,
      CLKOUT3B => NLW_mmcme4_adv_inst_CLKOUT3B_UNCONNECTED,
      CLKOUT4 => clk_out5_clk_wiz_0_firesim,
      CLKOUT5 => clk_out6_clk_wiz_0_firesim,
      CLKOUT6 => NLW_mmcme4_adv_inst_CLKOUT6_UNCONNECTED,
      DADDR(6 downto 0) => B"0000000",
      DCLK => '0',
      DEN => '0',
      DI(15 downto 0) => B"0000000000000000",
      DO(15 downto 0) => NLW_mmcme4_adv_inst_DO_UNCONNECTED(15 downto 0),
      DRDY => NLW_mmcme4_adv_inst_DRDY_UNCONNECTED,
      DWE => '0',
      LOCKED => locked,
      PSCLK => '0',
      PSDONE => NLW_mmcme4_adv_inst_PSDONE_UNCONNECTED,
      PSEN => '0',
      PSINCDEC => '0',
      PWRDWN => '0',
      RST => reset
    );
end STRUCTURE;
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
entity clk_wiz_0_firesim is
  port (
    clk_out1 : out STD_LOGIC;
    clk_out2 : out STD_LOGIC;
    clk_out3 : out STD_LOGIC;
    clk_out4 : out STD_LOGIC;
    clk_out5 : out STD_LOGIC;
    clk_out6 : out STD_LOGIC;
    reset : in STD_LOGIC;
    locked : out STD_LOGIC;
    clk_in1 : in STD_LOGIC
  );
  attribute NotValidForBitStream : boolean;
  attribute NotValidForBitStream of clk_wiz_0_firesim : entity is true;
end clk_wiz_0_firesim;

architecture STRUCTURE of clk_wiz_0_firesim is
begin
inst: entity work.clk_wiz_0_firesim_clk_wiz
     port map (
      clk_in1 => clk_in1,
      clk_out1 => clk_out1,
      clk_out2 => clk_out2,
      clk_out3 => clk_out3,
      clk_out4 => clk_out4,
      clk_out5 => clk_out5,
      clk_out6 => clk_out6,
      locked => locked,
      reset => reset
    );
end STRUCTURE;
