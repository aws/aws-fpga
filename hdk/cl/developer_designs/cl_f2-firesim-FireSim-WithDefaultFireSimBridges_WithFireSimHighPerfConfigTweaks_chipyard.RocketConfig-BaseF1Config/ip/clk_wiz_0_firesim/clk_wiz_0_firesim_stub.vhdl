-- Copyright 1986-2022 Xilinx, Inc. All Rights Reserved.
-- Copyright 2022-2024 Advanced Micro Devices, Inc. All Rights Reserved.
-- --------------------------------------------------------------------------------
-- Tool Version: Vivado v.2024.2 (lin64) Build 5239630 Fri Nov 08 22:34:34 MST 2024
-- Date        : Mon Dec 29 04:36:14 2025
-- Host        : ip-192-168-0-221 running 64-bit Ubuntu 24.04.1 LTS
-- Command     : write_vhdl -force -mode synth_stub
--               /home/ubuntu/chipyard-bitstream/sims/firesim/platforms/f2/aws-fpga-firesim-f2/hdk/cl/developer_designs/cl_f2-firesim-FireSim-WithDefaultFireSimBridges_WithFireSimHighPerfConfigTweaks_chipyard.RocketConfig-BaseF1Config/ip/clk_wiz_0_firesim/clk_wiz_0_firesim_stub.vhdl
-- Design      : clk_wiz_0_firesim
-- Purpose     : Stub declaration of top-level module interface
-- Device      : xcvu47p-fsvh2892-2-e
-- --------------------------------------------------------------------------------
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;

entity clk_wiz_0_firesim is
  Port ( 
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

  attribute CORE_GENERATION_INFO : string;
  attribute CORE_GENERATION_INFO of clk_wiz_0_firesim : entity is "clk_wiz_0_firesim,clk_wiz_v6_0_15_0_0,{component_name=clk_wiz_0_firesim,use_phase_alignment=true,use_min_o_jitter=false,use_max_i_jitter=false,use_dyn_phase_shift=false,use_inclk_switchover=false,use_dyn_reconfig=false,enable_axi=0,feedback_source=FDBK_AUTO,PRIMITIVE=MMCM,num_out_clk=6,clkin1_period=8.000,clkin2_period=10.000,use_power_down=false,use_reset=true,use_locked=true,use_inclk_stopped=false,feedback_type=SINGLE,CLOCK_MGR_TYPE=NA,manual_override=false}";
end clk_wiz_0_firesim;

architecture stub of clk_wiz_0_firesim is
  attribute syn_black_box : boolean;
  attribute black_box_pad_pin : string;
  attribute syn_black_box of stub : architecture is true;
  attribute black_box_pad_pin of stub : architecture is "clk_out1,clk_out2,clk_out3,clk_out4,clk_out5,clk_out6,reset,locked,clk_in1";
begin
end;
