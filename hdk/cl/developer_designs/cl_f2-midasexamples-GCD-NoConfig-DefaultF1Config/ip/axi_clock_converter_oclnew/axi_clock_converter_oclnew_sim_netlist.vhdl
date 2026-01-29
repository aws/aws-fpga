-- Copyright 1986-2017 Xilinx, Inc. All Rights Reserved.
-- --------------------------------------------------------------------------------
-- Tool Version: Vivado v.2017.1 (lin64) Build 1846317 Fri Apr 14 18:54:47 MDT 2017
-- Date        : Fri Jul  7 23:13:16 2017
-- Host        : ip-172-31-17-184.ec2.internal running 64-bit CentOS Linux release 7.3.1611 (Core)
-- Command     : write_vhdl -force -mode funcsim
--               /home/centos/firesim_ip2/axi_clock_converter_oclnew/axi_clock_converter_oclnew_sim_netlist.vhdl
-- Design      : axi_clock_converter_oclnew
-- Purpose     : This VHDL netlist is a functional simulation representation of the design and should not be modified or
--               synthesized. This netlist cannot be used for SDF annotated simulation.
-- Device      : xcvu9p-flgb2104-2-i
-- --------------------------------------------------------------------------------
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
entity axi_clock_converter_oclnew_xpm_cdc_single is
  port (
    src_clk : in STD_LOGIC;
    src_in : in STD_LOGIC;
    dest_clk : in STD_LOGIC;
    dest_out : out STD_LOGIC
  );
  attribute DEST_SYNC_FF : integer;
  attribute DEST_SYNC_FF of axi_clock_converter_oclnew_xpm_cdc_single : entity is 2;
  attribute ORIG_REF_NAME : string;
  attribute ORIG_REF_NAME of axi_clock_converter_oclnew_xpm_cdc_single : entity is "xpm_cdc_single";
  attribute SIM_ASSERT_CHK : integer;
  attribute SIM_ASSERT_CHK of axi_clock_converter_oclnew_xpm_cdc_single : entity is 0;
  attribute SRC_INPUT_REG : integer;
  attribute SRC_INPUT_REG of axi_clock_converter_oclnew_xpm_cdc_single : entity is 0;
  attribute VERSION : integer;
  attribute VERSION of axi_clock_converter_oclnew_xpm_cdc_single : entity is 0;
  attribute XPM_MODULE : string;
  attribute XPM_MODULE of axi_clock_converter_oclnew_xpm_cdc_single : entity is "TRUE";
  attribute xpm_cdc : string;
  attribute xpm_cdc of axi_clock_converter_oclnew_xpm_cdc_single : entity is "SINGLE";
end axi_clock_converter_oclnew_xpm_cdc_single;

architecture STRUCTURE of axi_clock_converter_oclnew_xpm_cdc_single is
  signal syncstages_ff : STD_LOGIC_VECTOR ( 1 downto 0 );
  attribute RTL_KEEP : string;
  attribute RTL_KEEP of syncstages_ff : signal is "true";
  attribute async_reg : string;
  attribute async_reg of syncstages_ff : signal is "true";
  attribute xpm_cdc of syncstages_ff : signal is "SINGLE";
  attribute ASYNC_REG_boolean : boolean;
  attribute ASYNC_REG_boolean of \syncstages_ff_reg[0]\ : label is std.standard.true;
  attribute XPM_CDC of \syncstages_ff_reg[0]\ : label is "SINGLE";
  attribute ASYNC_REG_boolean of \syncstages_ff_reg[1]\ : label is std.standard.true;
  attribute XPM_CDC of \syncstages_ff_reg[1]\ : label is "SINGLE";
begin
  dest_out <= syncstages_ff(1);
\syncstages_ff_reg[0]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => '1',
      D => src_in,
      Q => syncstages_ff(0),
      R => '0'
    );
\syncstages_ff_reg[1]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => '1',
      D => syncstages_ff(0),
      Q => syncstages_ff(1),
      R => '0'
    );
end STRUCTURE;
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
entity \axi_clock_converter_oclnew_xpm_cdc_single__10\ is
  port (
    src_clk : in STD_LOGIC;
    src_in : in STD_LOGIC;
    dest_clk : in STD_LOGIC;
    dest_out : out STD_LOGIC
  );
  attribute DEST_SYNC_FF : integer;
  attribute DEST_SYNC_FF of \axi_clock_converter_oclnew_xpm_cdc_single__10\ : entity is 2;
  attribute ORIG_REF_NAME : string;
  attribute ORIG_REF_NAME of \axi_clock_converter_oclnew_xpm_cdc_single__10\ : entity is "xpm_cdc_single";
  attribute SIM_ASSERT_CHK : integer;
  attribute SIM_ASSERT_CHK of \axi_clock_converter_oclnew_xpm_cdc_single__10\ : entity is 0;
  attribute SRC_INPUT_REG : integer;
  attribute SRC_INPUT_REG of \axi_clock_converter_oclnew_xpm_cdc_single__10\ : entity is 0;
  attribute VERSION : integer;
  attribute VERSION of \axi_clock_converter_oclnew_xpm_cdc_single__10\ : entity is 0;
  attribute XPM_MODULE : string;
  attribute XPM_MODULE of \axi_clock_converter_oclnew_xpm_cdc_single__10\ : entity is "TRUE";
  attribute xpm_cdc : string;
  attribute xpm_cdc of \axi_clock_converter_oclnew_xpm_cdc_single__10\ : entity is "SINGLE";
end \axi_clock_converter_oclnew_xpm_cdc_single__10\;

architecture STRUCTURE of \axi_clock_converter_oclnew_xpm_cdc_single__10\ is
  signal syncstages_ff : STD_LOGIC_VECTOR ( 1 downto 0 );
  attribute RTL_KEEP : string;
  attribute RTL_KEEP of syncstages_ff : signal is "true";
  attribute async_reg : string;
  attribute async_reg of syncstages_ff : signal is "true";
  attribute xpm_cdc of syncstages_ff : signal is "SINGLE";
  attribute ASYNC_REG_boolean : boolean;
  attribute ASYNC_REG_boolean of \syncstages_ff_reg[0]\ : label is std.standard.true;
  attribute XPM_CDC of \syncstages_ff_reg[0]\ : label is "SINGLE";
  attribute ASYNC_REG_boolean of \syncstages_ff_reg[1]\ : label is std.standard.true;
  attribute XPM_CDC of \syncstages_ff_reg[1]\ : label is "SINGLE";
begin
  dest_out <= syncstages_ff(1);
\syncstages_ff_reg[0]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => '1',
      D => src_in,
      Q => syncstages_ff(0),
      R => '0'
    );
\syncstages_ff_reg[1]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => '1',
      D => syncstages_ff(0),
      Q => syncstages_ff(1),
      R => '0'
    );
end STRUCTURE;
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
entity \axi_clock_converter_oclnew_xpm_cdc_single__2\ is
  port (
    src_clk : in STD_LOGIC;
    src_in : in STD_LOGIC;
    dest_clk : in STD_LOGIC;
    dest_out : out STD_LOGIC
  );
  attribute DEST_SYNC_FF : integer;
  attribute DEST_SYNC_FF of \axi_clock_converter_oclnew_xpm_cdc_single__2\ : entity is 2;
  attribute ORIG_REF_NAME : string;
  attribute ORIG_REF_NAME of \axi_clock_converter_oclnew_xpm_cdc_single__2\ : entity is "xpm_cdc_single";
  attribute SIM_ASSERT_CHK : integer;
  attribute SIM_ASSERT_CHK of \axi_clock_converter_oclnew_xpm_cdc_single__2\ : entity is 0;
  attribute SRC_INPUT_REG : integer;
  attribute SRC_INPUT_REG of \axi_clock_converter_oclnew_xpm_cdc_single__2\ : entity is 0;
  attribute VERSION : integer;
  attribute VERSION of \axi_clock_converter_oclnew_xpm_cdc_single__2\ : entity is 0;
  attribute XPM_MODULE : string;
  attribute XPM_MODULE of \axi_clock_converter_oclnew_xpm_cdc_single__2\ : entity is "TRUE";
  attribute xpm_cdc : string;
  attribute xpm_cdc of \axi_clock_converter_oclnew_xpm_cdc_single__2\ : entity is "SINGLE";
end \axi_clock_converter_oclnew_xpm_cdc_single__2\;

architecture STRUCTURE of \axi_clock_converter_oclnew_xpm_cdc_single__2\ is
  signal syncstages_ff : STD_LOGIC_VECTOR ( 1 downto 0 );
  attribute RTL_KEEP : string;
  attribute RTL_KEEP of syncstages_ff : signal is "true";
  attribute async_reg : string;
  attribute async_reg of syncstages_ff : signal is "true";
  attribute xpm_cdc of syncstages_ff : signal is "SINGLE";
  attribute ASYNC_REG_boolean : boolean;
  attribute ASYNC_REG_boolean of \syncstages_ff_reg[0]\ : label is std.standard.true;
  attribute XPM_CDC of \syncstages_ff_reg[0]\ : label is "SINGLE";
  attribute ASYNC_REG_boolean of \syncstages_ff_reg[1]\ : label is std.standard.true;
  attribute XPM_CDC of \syncstages_ff_reg[1]\ : label is "SINGLE";
begin
  dest_out <= syncstages_ff(1);
\syncstages_ff_reg[0]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => '1',
      D => src_in,
      Q => syncstages_ff(0),
      R => '0'
    );
\syncstages_ff_reg[1]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => '1',
      D => syncstages_ff(0),
      Q => syncstages_ff(1),
      R => '0'
    );
end STRUCTURE;
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
entity \axi_clock_converter_oclnew_xpm_cdc_single__3\ is
  port (
    src_clk : in STD_LOGIC;
    src_in : in STD_LOGIC;
    dest_clk : in STD_LOGIC;
    dest_out : out STD_LOGIC
  );
  attribute DEST_SYNC_FF : integer;
  attribute DEST_SYNC_FF of \axi_clock_converter_oclnew_xpm_cdc_single__3\ : entity is 2;
  attribute ORIG_REF_NAME : string;
  attribute ORIG_REF_NAME of \axi_clock_converter_oclnew_xpm_cdc_single__3\ : entity is "xpm_cdc_single";
  attribute SIM_ASSERT_CHK : integer;
  attribute SIM_ASSERT_CHK of \axi_clock_converter_oclnew_xpm_cdc_single__3\ : entity is 0;
  attribute SRC_INPUT_REG : integer;
  attribute SRC_INPUT_REG of \axi_clock_converter_oclnew_xpm_cdc_single__3\ : entity is 0;
  attribute VERSION : integer;
  attribute VERSION of \axi_clock_converter_oclnew_xpm_cdc_single__3\ : entity is 0;
  attribute XPM_MODULE : string;
  attribute XPM_MODULE of \axi_clock_converter_oclnew_xpm_cdc_single__3\ : entity is "TRUE";
  attribute xpm_cdc : string;
  attribute xpm_cdc of \axi_clock_converter_oclnew_xpm_cdc_single__3\ : entity is "SINGLE";
end \axi_clock_converter_oclnew_xpm_cdc_single__3\;

architecture STRUCTURE of \axi_clock_converter_oclnew_xpm_cdc_single__3\ is
  signal syncstages_ff : STD_LOGIC_VECTOR ( 1 downto 0 );
  attribute RTL_KEEP : string;
  attribute RTL_KEEP of syncstages_ff : signal is "true";
  attribute async_reg : string;
  attribute async_reg of syncstages_ff : signal is "true";
  attribute xpm_cdc of syncstages_ff : signal is "SINGLE";
  attribute ASYNC_REG_boolean : boolean;
  attribute ASYNC_REG_boolean of \syncstages_ff_reg[0]\ : label is std.standard.true;
  attribute XPM_CDC of \syncstages_ff_reg[0]\ : label is "SINGLE";
  attribute ASYNC_REG_boolean of \syncstages_ff_reg[1]\ : label is std.standard.true;
  attribute XPM_CDC of \syncstages_ff_reg[1]\ : label is "SINGLE";
begin
  dest_out <= syncstages_ff(1);
\syncstages_ff_reg[0]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => '1',
      D => src_in,
      Q => syncstages_ff(0),
      R => '0'
    );
\syncstages_ff_reg[1]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => '1',
      D => syncstages_ff(0),
      Q => syncstages_ff(1),
      R => '0'
    );
end STRUCTURE;
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
entity \axi_clock_converter_oclnew_xpm_cdc_single__4\ is
  port (
    src_clk : in STD_LOGIC;
    src_in : in STD_LOGIC;
    dest_clk : in STD_LOGIC;
    dest_out : out STD_LOGIC
  );
  attribute DEST_SYNC_FF : integer;
  attribute DEST_SYNC_FF of \axi_clock_converter_oclnew_xpm_cdc_single__4\ : entity is 2;
  attribute ORIG_REF_NAME : string;
  attribute ORIG_REF_NAME of \axi_clock_converter_oclnew_xpm_cdc_single__4\ : entity is "xpm_cdc_single";
  attribute SIM_ASSERT_CHK : integer;
  attribute SIM_ASSERT_CHK of \axi_clock_converter_oclnew_xpm_cdc_single__4\ : entity is 0;
  attribute SRC_INPUT_REG : integer;
  attribute SRC_INPUT_REG of \axi_clock_converter_oclnew_xpm_cdc_single__4\ : entity is 0;
  attribute VERSION : integer;
  attribute VERSION of \axi_clock_converter_oclnew_xpm_cdc_single__4\ : entity is 0;
  attribute XPM_MODULE : string;
  attribute XPM_MODULE of \axi_clock_converter_oclnew_xpm_cdc_single__4\ : entity is "TRUE";
  attribute xpm_cdc : string;
  attribute xpm_cdc of \axi_clock_converter_oclnew_xpm_cdc_single__4\ : entity is "SINGLE";
end \axi_clock_converter_oclnew_xpm_cdc_single__4\;

architecture STRUCTURE of \axi_clock_converter_oclnew_xpm_cdc_single__4\ is
  signal syncstages_ff : STD_LOGIC_VECTOR ( 1 downto 0 );
  attribute RTL_KEEP : string;
  attribute RTL_KEEP of syncstages_ff : signal is "true";
  attribute async_reg : string;
  attribute async_reg of syncstages_ff : signal is "true";
  attribute xpm_cdc of syncstages_ff : signal is "SINGLE";
  attribute ASYNC_REG_boolean : boolean;
  attribute ASYNC_REG_boolean of \syncstages_ff_reg[0]\ : label is std.standard.true;
  attribute XPM_CDC of \syncstages_ff_reg[0]\ : label is "SINGLE";
  attribute ASYNC_REG_boolean of \syncstages_ff_reg[1]\ : label is std.standard.true;
  attribute XPM_CDC of \syncstages_ff_reg[1]\ : label is "SINGLE";
begin
  dest_out <= syncstages_ff(1);
\syncstages_ff_reg[0]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => '1',
      D => src_in,
      Q => syncstages_ff(0),
      R => '0'
    );
\syncstages_ff_reg[1]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => '1',
      D => syncstages_ff(0),
      Q => syncstages_ff(1),
      R => '0'
    );
end STRUCTURE;
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
entity \axi_clock_converter_oclnew_xpm_cdc_single__5\ is
  port (
    src_clk : in STD_LOGIC;
    src_in : in STD_LOGIC;
    dest_clk : in STD_LOGIC;
    dest_out : out STD_LOGIC
  );
  attribute DEST_SYNC_FF : integer;
  attribute DEST_SYNC_FF of \axi_clock_converter_oclnew_xpm_cdc_single__5\ : entity is 2;
  attribute ORIG_REF_NAME : string;
  attribute ORIG_REF_NAME of \axi_clock_converter_oclnew_xpm_cdc_single__5\ : entity is "xpm_cdc_single";
  attribute SIM_ASSERT_CHK : integer;
  attribute SIM_ASSERT_CHK of \axi_clock_converter_oclnew_xpm_cdc_single__5\ : entity is 0;
  attribute SRC_INPUT_REG : integer;
  attribute SRC_INPUT_REG of \axi_clock_converter_oclnew_xpm_cdc_single__5\ : entity is 0;
  attribute VERSION : integer;
  attribute VERSION of \axi_clock_converter_oclnew_xpm_cdc_single__5\ : entity is 0;
  attribute XPM_MODULE : string;
  attribute XPM_MODULE of \axi_clock_converter_oclnew_xpm_cdc_single__5\ : entity is "TRUE";
  attribute xpm_cdc : string;
  attribute xpm_cdc of \axi_clock_converter_oclnew_xpm_cdc_single__5\ : entity is "SINGLE";
end \axi_clock_converter_oclnew_xpm_cdc_single__5\;

architecture STRUCTURE of \axi_clock_converter_oclnew_xpm_cdc_single__5\ is
  signal syncstages_ff : STD_LOGIC_VECTOR ( 1 downto 0 );
  attribute RTL_KEEP : string;
  attribute RTL_KEEP of syncstages_ff : signal is "true";
  attribute async_reg : string;
  attribute async_reg of syncstages_ff : signal is "true";
  attribute xpm_cdc of syncstages_ff : signal is "SINGLE";
  attribute ASYNC_REG_boolean : boolean;
  attribute ASYNC_REG_boolean of \syncstages_ff_reg[0]\ : label is std.standard.true;
  attribute XPM_CDC of \syncstages_ff_reg[0]\ : label is "SINGLE";
  attribute ASYNC_REG_boolean of \syncstages_ff_reg[1]\ : label is std.standard.true;
  attribute XPM_CDC of \syncstages_ff_reg[1]\ : label is "SINGLE";
begin
  dest_out <= syncstages_ff(1);
\syncstages_ff_reg[0]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => '1',
      D => src_in,
      Q => syncstages_ff(0),
      R => '0'
    );
\syncstages_ff_reg[1]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => '1',
      D => syncstages_ff(0),
      Q => syncstages_ff(1),
      R => '0'
    );
end STRUCTURE;
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
entity \axi_clock_converter_oclnew_xpm_cdc_single__6\ is
  port (
    src_clk : in STD_LOGIC;
    src_in : in STD_LOGIC;
    dest_clk : in STD_LOGIC;
    dest_out : out STD_LOGIC
  );
  attribute DEST_SYNC_FF : integer;
  attribute DEST_SYNC_FF of \axi_clock_converter_oclnew_xpm_cdc_single__6\ : entity is 2;
  attribute ORIG_REF_NAME : string;
  attribute ORIG_REF_NAME of \axi_clock_converter_oclnew_xpm_cdc_single__6\ : entity is "xpm_cdc_single";
  attribute SIM_ASSERT_CHK : integer;
  attribute SIM_ASSERT_CHK of \axi_clock_converter_oclnew_xpm_cdc_single__6\ : entity is 0;
  attribute SRC_INPUT_REG : integer;
  attribute SRC_INPUT_REG of \axi_clock_converter_oclnew_xpm_cdc_single__6\ : entity is 0;
  attribute VERSION : integer;
  attribute VERSION of \axi_clock_converter_oclnew_xpm_cdc_single__6\ : entity is 0;
  attribute XPM_MODULE : string;
  attribute XPM_MODULE of \axi_clock_converter_oclnew_xpm_cdc_single__6\ : entity is "TRUE";
  attribute xpm_cdc : string;
  attribute xpm_cdc of \axi_clock_converter_oclnew_xpm_cdc_single__6\ : entity is "SINGLE";
end \axi_clock_converter_oclnew_xpm_cdc_single__6\;

architecture STRUCTURE of \axi_clock_converter_oclnew_xpm_cdc_single__6\ is
  signal syncstages_ff : STD_LOGIC_VECTOR ( 1 downto 0 );
  attribute RTL_KEEP : string;
  attribute RTL_KEEP of syncstages_ff : signal is "true";
  attribute async_reg : string;
  attribute async_reg of syncstages_ff : signal is "true";
  attribute xpm_cdc of syncstages_ff : signal is "SINGLE";
  attribute ASYNC_REG_boolean : boolean;
  attribute ASYNC_REG_boolean of \syncstages_ff_reg[0]\ : label is std.standard.true;
  attribute XPM_CDC of \syncstages_ff_reg[0]\ : label is "SINGLE";
  attribute ASYNC_REG_boolean of \syncstages_ff_reg[1]\ : label is std.standard.true;
  attribute XPM_CDC of \syncstages_ff_reg[1]\ : label is "SINGLE";
begin
  dest_out <= syncstages_ff(1);
\syncstages_ff_reg[0]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => '1',
      D => src_in,
      Q => syncstages_ff(0),
      R => '0'
    );
\syncstages_ff_reg[1]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => '1',
      D => syncstages_ff(0),
      Q => syncstages_ff(1),
      R => '0'
    );
end STRUCTURE;
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
entity \axi_clock_converter_oclnew_xpm_cdc_single__7\ is
  port (
    src_clk : in STD_LOGIC;
    src_in : in STD_LOGIC;
    dest_clk : in STD_LOGIC;
    dest_out : out STD_LOGIC
  );
  attribute DEST_SYNC_FF : integer;
  attribute DEST_SYNC_FF of \axi_clock_converter_oclnew_xpm_cdc_single__7\ : entity is 2;
  attribute ORIG_REF_NAME : string;
  attribute ORIG_REF_NAME of \axi_clock_converter_oclnew_xpm_cdc_single__7\ : entity is "xpm_cdc_single";
  attribute SIM_ASSERT_CHK : integer;
  attribute SIM_ASSERT_CHK of \axi_clock_converter_oclnew_xpm_cdc_single__7\ : entity is 0;
  attribute SRC_INPUT_REG : integer;
  attribute SRC_INPUT_REG of \axi_clock_converter_oclnew_xpm_cdc_single__7\ : entity is 0;
  attribute VERSION : integer;
  attribute VERSION of \axi_clock_converter_oclnew_xpm_cdc_single__7\ : entity is 0;
  attribute XPM_MODULE : string;
  attribute XPM_MODULE of \axi_clock_converter_oclnew_xpm_cdc_single__7\ : entity is "TRUE";
  attribute xpm_cdc : string;
  attribute xpm_cdc of \axi_clock_converter_oclnew_xpm_cdc_single__7\ : entity is "SINGLE";
end \axi_clock_converter_oclnew_xpm_cdc_single__7\;

architecture STRUCTURE of \axi_clock_converter_oclnew_xpm_cdc_single__7\ is
  signal syncstages_ff : STD_LOGIC_VECTOR ( 1 downto 0 );
  attribute RTL_KEEP : string;
  attribute RTL_KEEP of syncstages_ff : signal is "true";
  attribute async_reg : string;
  attribute async_reg of syncstages_ff : signal is "true";
  attribute xpm_cdc of syncstages_ff : signal is "SINGLE";
  attribute ASYNC_REG_boolean : boolean;
  attribute ASYNC_REG_boolean of \syncstages_ff_reg[0]\ : label is std.standard.true;
  attribute XPM_CDC of \syncstages_ff_reg[0]\ : label is "SINGLE";
  attribute ASYNC_REG_boolean of \syncstages_ff_reg[1]\ : label is std.standard.true;
  attribute XPM_CDC of \syncstages_ff_reg[1]\ : label is "SINGLE";
begin
  dest_out <= syncstages_ff(1);
\syncstages_ff_reg[0]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => '1',
      D => src_in,
      Q => syncstages_ff(0),
      R => '0'
    );
\syncstages_ff_reg[1]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => '1',
      D => syncstages_ff(0),
      Q => syncstages_ff(1),
      R => '0'
    );
end STRUCTURE;
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
entity \axi_clock_converter_oclnew_xpm_cdc_single__8\ is
  port (
    src_clk : in STD_LOGIC;
    src_in : in STD_LOGIC;
    dest_clk : in STD_LOGIC;
    dest_out : out STD_LOGIC
  );
  attribute DEST_SYNC_FF : integer;
  attribute DEST_SYNC_FF of \axi_clock_converter_oclnew_xpm_cdc_single__8\ : entity is 2;
  attribute ORIG_REF_NAME : string;
  attribute ORIG_REF_NAME of \axi_clock_converter_oclnew_xpm_cdc_single__8\ : entity is "xpm_cdc_single";
  attribute SIM_ASSERT_CHK : integer;
  attribute SIM_ASSERT_CHK of \axi_clock_converter_oclnew_xpm_cdc_single__8\ : entity is 0;
  attribute SRC_INPUT_REG : integer;
  attribute SRC_INPUT_REG of \axi_clock_converter_oclnew_xpm_cdc_single__8\ : entity is 0;
  attribute VERSION : integer;
  attribute VERSION of \axi_clock_converter_oclnew_xpm_cdc_single__8\ : entity is 0;
  attribute XPM_MODULE : string;
  attribute XPM_MODULE of \axi_clock_converter_oclnew_xpm_cdc_single__8\ : entity is "TRUE";
  attribute xpm_cdc : string;
  attribute xpm_cdc of \axi_clock_converter_oclnew_xpm_cdc_single__8\ : entity is "SINGLE";
end \axi_clock_converter_oclnew_xpm_cdc_single__8\;

architecture STRUCTURE of \axi_clock_converter_oclnew_xpm_cdc_single__8\ is
  signal syncstages_ff : STD_LOGIC_VECTOR ( 1 downto 0 );
  attribute RTL_KEEP : string;
  attribute RTL_KEEP of syncstages_ff : signal is "true";
  attribute async_reg : string;
  attribute async_reg of syncstages_ff : signal is "true";
  attribute xpm_cdc of syncstages_ff : signal is "SINGLE";
  attribute ASYNC_REG_boolean : boolean;
  attribute ASYNC_REG_boolean of \syncstages_ff_reg[0]\ : label is std.standard.true;
  attribute XPM_CDC of \syncstages_ff_reg[0]\ : label is "SINGLE";
  attribute ASYNC_REG_boolean of \syncstages_ff_reg[1]\ : label is std.standard.true;
  attribute XPM_CDC of \syncstages_ff_reg[1]\ : label is "SINGLE";
begin
  dest_out <= syncstages_ff(1);
\syncstages_ff_reg[0]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => '1',
      D => src_in,
      Q => syncstages_ff(0),
      R => '0'
    );
\syncstages_ff_reg[1]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => '1',
      D => syncstages_ff(0),
      Q => syncstages_ff(1),
      R => '0'
    );
end STRUCTURE;
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
entity \axi_clock_converter_oclnew_xpm_cdc_single__9\ is
  port (
    src_clk : in STD_LOGIC;
    src_in : in STD_LOGIC;
    dest_clk : in STD_LOGIC;
    dest_out : out STD_LOGIC
  );
  attribute DEST_SYNC_FF : integer;
  attribute DEST_SYNC_FF of \axi_clock_converter_oclnew_xpm_cdc_single__9\ : entity is 2;
  attribute ORIG_REF_NAME : string;
  attribute ORIG_REF_NAME of \axi_clock_converter_oclnew_xpm_cdc_single__9\ : entity is "xpm_cdc_single";
  attribute SIM_ASSERT_CHK : integer;
  attribute SIM_ASSERT_CHK of \axi_clock_converter_oclnew_xpm_cdc_single__9\ : entity is 0;
  attribute SRC_INPUT_REG : integer;
  attribute SRC_INPUT_REG of \axi_clock_converter_oclnew_xpm_cdc_single__9\ : entity is 0;
  attribute VERSION : integer;
  attribute VERSION of \axi_clock_converter_oclnew_xpm_cdc_single__9\ : entity is 0;
  attribute XPM_MODULE : string;
  attribute XPM_MODULE of \axi_clock_converter_oclnew_xpm_cdc_single__9\ : entity is "TRUE";
  attribute xpm_cdc : string;
  attribute xpm_cdc of \axi_clock_converter_oclnew_xpm_cdc_single__9\ : entity is "SINGLE";
end \axi_clock_converter_oclnew_xpm_cdc_single__9\;

architecture STRUCTURE of \axi_clock_converter_oclnew_xpm_cdc_single__9\ is
  signal syncstages_ff : STD_LOGIC_VECTOR ( 1 downto 0 );
  attribute RTL_KEEP : string;
  attribute RTL_KEEP of syncstages_ff : signal is "true";
  attribute async_reg : string;
  attribute async_reg of syncstages_ff : signal is "true";
  attribute xpm_cdc of syncstages_ff : signal is "SINGLE";
  attribute ASYNC_REG_boolean : boolean;
  attribute ASYNC_REG_boolean of \syncstages_ff_reg[0]\ : label is std.standard.true;
  attribute XPM_CDC of \syncstages_ff_reg[0]\ : label is "SINGLE";
  attribute ASYNC_REG_boolean of \syncstages_ff_reg[1]\ : label is std.standard.true;
  attribute XPM_CDC of \syncstages_ff_reg[1]\ : label is "SINGLE";
begin
  dest_out <= syncstages_ff(1);
\syncstages_ff_reg[0]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => '1',
      D => src_in,
      Q => syncstages_ff(0),
      R => '0'
    );
\syncstages_ff_reg[1]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => '1',
      D => syncstages_ff(0),
      Q => syncstages_ff(1),
      R => '0'
    );
end STRUCTURE;
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
entity axi_clock_converter_oclnew_xpm_cdc_handshake is
  port (
    src_clk : in STD_LOGIC;
    src_in : in STD_LOGIC_VECTOR ( 34 downto 0 );
    src_send : in STD_LOGIC;
    src_rcv : out STD_LOGIC;
    dest_clk : in STD_LOGIC;
    dest_out : out STD_LOGIC_VECTOR ( 34 downto 0 );
    dest_req : out STD_LOGIC;
    dest_ack : in STD_LOGIC
  );
  attribute DEST_EXT_HSK : integer;
  attribute DEST_EXT_HSK of axi_clock_converter_oclnew_xpm_cdc_handshake : entity is 1;
  attribute DEST_SYNC_FF : integer;
  attribute DEST_SYNC_FF of axi_clock_converter_oclnew_xpm_cdc_handshake : entity is 2;
  attribute ORIG_REF_NAME : string;
  attribute ORIG_REF_NAME of axi_clock_converter_oclnew_xpm_cdc_handshake : entity is "xpm_cdc_handshake";
  attribute SIM_ASSERT_CHK : integer;
  attribute SIM_ASSERT_CHK of axi_clock_converter_oclnew_xpm_cdc_handshake : entity is 0;
  attribute SRC_SYNC_FF : integer;
  attribute SRC_SYNC_FF of axi_clock_converter_oclnew_xpm_cdc_handshake : entity is 2;
  attribute VERSION : integer;
  attribute VERSION of axi_clock_converter_oclnew_xpm_cdc_handshake : entity is 0;
  attribute WIDTH : integer;
  attribute WIDTH of axi_clock_converter_oclnew_xpm_cdc_handshake : entity is 35;
  attribute XPM_MODULE : string;
  attribute XPM_MODULE of axi_clock_converter_oclnew_xpm_cdc_handshake : entity is "TRUE";
  attribute xpm_cdc : string;
  attribute xpm_cdc of axi_clock_converter_oclnew_xpm_cdc_handshake : entity is "HANDSHAKE";
end axi_clock_converter_oclnew_xpm_cdc_handshake;

architecture STRUCTURE of axi_clock_converter_oclnew_xpm_cdc_handshake is
  signal dest_hsdata_en : STD_LOGIC;
  attribute DIRECT_ENABLE : boolean;
  attribute DIRECT_ENABLE of dest_hsdata_en : signal is std.standard.true;
  signal dest_hsdata_ff : STD_LOGIC_VECTOR ( 34 downto 0 );
  attribute RTL_KEEP : string;
  attribute RTL_KEEP of dest_hsdata_ff : signal is "true";
  attribute xpm_cdc of dest_hsdata_ff : signal is "HANDSHAKE";
  signal \^dest_req\ : STD_LOGIC;
  signal dest_req_nxt : STD_LOGIC;
  signal p_0_in : STD_LOGIC;
  signal src_hsdata_ff : STD_LOGIC_VECTOR ( 34 downto 0 );
  signal src_sendd_ff : STD_LOGIC;
  attribute KEEP : string;
  attribute KEEP of \dest_hsdata_ff_reg[0]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[0]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[10]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[10]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[11]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[11]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[12]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[12]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[13]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[13]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[14]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[14]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[15]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[15]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[16]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[16]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[17]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[17]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[18]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[18]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[19]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[19]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[1]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[1]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[20]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[20]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[21]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[21]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[22]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[22]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[23]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[23]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[24]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[24]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[25]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[25]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[26]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[26]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[27]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[27]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[28]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[28]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[29]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[29]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[2]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[2]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[30]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[30]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[31]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[31]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[32]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[32]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[33]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[33]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[34]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[34]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[3]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[3]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[4]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[4]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[5]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[5]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[6]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[6]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[7]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[7]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[8]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[8]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[9]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[9]\ : label is "HANDSHAKE";
  attribute DEST_SYNC_FF of xpm_cdc_single_dest2src_inst : label is 2;
  attribute SIM_ASSERT_CHK of xpm_cdc_single_dest2src_inst : label is 0;
  attribute SRC_INPUT_REG : integer;
  attribute SRC_INPUT_REG of xpm_cdc_single_dest2src_inst : label is 0;
  attribute VERSION of xpm_cdc_single_dest2src_inst : label is 0;
  attribute XPM_CDC of xpm_cdc_single_dest2src_inst : label is "SINGLE";
  attribute XPM_MODULE of xpm_cdc_single_dest2src_inst : label is "TRUE";
  attribute DEST_SYNC_FF of xpm_cdc_single_src2dest_inst : label is 2;
  attribute SIM_ASSERT_CHK of xpm_cdc_single_src2dest_inst : label is 0;
  attribute SRC_INPUT_REG of xpm_cdc_single_src2dest_inst : label is 0;
  attribute VERSION of xpm_cdc_single_src2dest_inst : label is 0;
  attribute XPM_CDC of xpm_cdc_single_src2dest_inst : label is "SINGLE";
  attribute XPM_MODULE of xpm_cdc_single_src2dest_inst : label is "TRUE";
begin
  dest_out(34 downto 0) <= dest_hsdata_ff(34 downto 0);
  dest_req <= \^dest_req\;
dest_hsdata_en_inferred_i_1: unisim.vcomponents.LUT2
    generic map(
      INIT => X"2"
    )
        port map (
      I0 => dest_req_nxt,
      I1 => \^dest_req\,
      O => dest_hsdata_en
    );
\dest_hsdata_ff_reg[0]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(0),
      Q => dest_hsdata_ff(0),
      R => '0'
    );
\dest_hsdata_ff_reg[10]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(10),
      Q => dest_hsdata_ff(10),
      R => '0'
    );
\dest_hsdata_ff_reg[11]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(11),
      Q => dest_hsdata_ff(11),
      R => '0'
    );
\dest_hsdata_ff_reg[12]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(12),
      Q => dest_hsdata_ff(12),
      R => '0'
    );
\dest_hsdata_ff_reg[13]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(13),
      Q => dest_hsdata_ff(13),
      R => '0'
    );
\dest_hsdata_ff_reg[14]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(14),
      Q => dest_hsdata_ff(14),
      R => '0'
    );
\dest_hsdata_ff_reg[15]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(15),
      Q => dest_hsdata_ff(15),
      R => '0'
    );
\dest_hsdata_ff_reg[16]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(16),
      Q => dest_hsdata_ff(16),
      R => '0'
    );
\dest_hsdata_ff_reg[17]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(17),
      Q => dest_hsdata_ff(17),
      R => '0'
    );
\dest_hsdata_ff_reg[18]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(18),
      Q => dest_hsdata_ff(18),
      R => '0'
    );
\dest_hsdata_ff_reg[19]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(19),
      Q => dest_hsdata_ff(19),
      R => '0'
    );
\dest_hsdata_ff_reg[1]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(1),
      Q => dest_hsdata_ff(1),
      R => '0'
    );
\dest_hsdata_ff_reg[20]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(20),
      Q => dest_hsdata_ff(20),
      R => '0'
    );
\dest_hsdata_ff_reg[21]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(21),
      Q => dest_hsdata_ff(21),
      R => '0'
    );
\dest_hsdata_ff_reg[22]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(22),
      Q => dest_hsdata_ff(22),
      R => '0'
    );
\dest_hsdata_ff_reg[23]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(23),
      Q => dest_hsdata_ff(23),
      R => '0'
    );
\dest_hsdata_ff_reg[24]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(24),
      Q => dest_hsdata_ff(24),
      R => '0'
    );
\dest_hsdata_ff_reg[25]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(25),
      Q => dest_hsdata_ff(25),
      R => '0'
    );
\dest_hsdata_ff_reg[26]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(26),
      Q => dest_hsdata_ff(26),
      R => '0'
    );
\dest_hsdata_ff_reg[27]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(27),
      Q => dest_hsdata_ff(27),
      R => '0'
    );
\dest_hsdata_ff_reg[28]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(28),
      Q => dest_hsdata_ff(28),
      R => '0'
    );
\dest_hsdata_ff_reg[29]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(29),
      Q => dest_hsdata_ff(29),
      R => '0'
    );
\dest_hsdata_ff_reg[2]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(2),
      Q => dest_hsdata_ff(2),
      R => '0'
    );
\dest_hsdata_ff_reg[30]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(30),
      Q => dest_hsdata_ff(30),
      R => '0'
    );
\dest_hsdata_ff_reg[31]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(31),
      Q => dest_hsdata_ff(31),
      R => '0'
    );
\dest_hsdata_ff_reg[32]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(32),
      Q => dest_hsdata_ff(32),
      R => '0'
    );
\dest_hsdata_ff_reg[33]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(33),
      Q => dest_hsdata_ff(33),
      R => '0'
    );
\dest_hsdata_ff_reg[34]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(34),
      Q => dest_hsdata_ff(34),
      R => '0'
    );
\dest_hsdata_ff_reg[3]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(3),
      Q => dest_hsdata_ff(3),
      R => '0'
    );
\dest_hsdata_ff_reg[4]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(4),
      Q => dest_hsdata_ff(4),
      R => '0'
    );
\dest_hsdata_ff_reg[5]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(5),
      Q => dest_hsdata_ff(5),
      R => '0'
    );
\dest_hsdata_ff_reg[6]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(6),
      Q => dest_hsdata_ff(6),
      R => '0'
    );
\dest_hsdata_ff_reg[7]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(7),
      Q => dest_hsdata_ff(7),
      R => '0'
    );
\dest_hsdata_ff_reg[8]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(8),
      Q => dest_hsdata_ff(8),
      R => '0'
    );
\dest_hsdata_ff_reg[9]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(9),
      Q => dest_hsdata_ff(9),
      R => '0'
    );
dest_req_ff_reg: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => '1',
      D => dest_req_nxt,
      Q => \^dest_req\,
      R => '0'
    );
\src_hsdata_ff[34]_i_1\: unisim.vcomponents.LUT1
    generic map(
      INIT => X"1"
    )
        port map (
      I0 => src_sendd_ff,
      O => p_0_in
    );
\src_hsdata_ff_reg[0]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(0),
      Q => src_hsdata_ff(0),
      R => '0'
    );
\src_hsdata_ff_reg[10]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(10),
      Q => src_hsdata_ff(10),
      R => '0'
    );
\src_hsdata_ff_reg[11]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(11),
      Q => src_hsdata_ff(11),
      R => '0'
    );
\src_hsdata_ff_reg[12]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(12),
      Q => src_hsdata_ff(12),
      R => '0'
    );
\src_hsdata_ff_reg[13]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(13),
      Q => src_hsdata_ff(13),
      R => '0'
    );
\src_hsdata_ff_reg[14]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(14),
      Q => src_hsdata_ff(14),
      R => '0'
    );
\src_hsdata_ff_reg[15]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(15),
      Q => src_hsdata_ff(15),
      R => '0'
    );
\src_hsdata_ff_reg[16]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(16),
      Q => src_hsdata_ff(16),
      R => '0'
    );
\src_hsdata_ff_reg[17]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(17),
      Q => src_hsdata_ff(17),
      R => '0'
    );
\src_hsdata_ff_reg[18]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(18),
      Q => src_hsdata_ff(18),
      R => '0'
    );
\src_hsdata_ff_reg[19]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(19),
      Q => src_hsdata_ff(19),
      R => '0'
    );
\src_hsdata_ff_reg[1]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(1),
      Q => src_hsdata_ff(1),
      R => '0'
    );
\src_hsdata_ff_reg[20]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(20),
      Q => src_hsdata_ff(20),
      R => '0'
    );
\src_hsdata_ff_reg[21]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(21),
      Q => src_hsdata_ff(21),
      R => '0'
    );
\src_hsdata_ff_reg[22]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(22),
      Q => src_hsdata_ff(22),
      R => '0'
    );
\src_hsdata_ff_reg[23]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(23),
      Q => src_hsdata_ff(23),
      R => '0'
    );
\src_hsdata_ff_reg[24]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(24),
      Q => src_hsdata_ff(24),
      R => '0'
    );
\src_hsdata_ff_reg[25]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(25),
      Q => src_hsdata_ff(25),
      R => '0'
    );
\src_hsdata_ff_reg[26]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(26),
      Q => src_hsdata_ff(26),
      R => '0'
    );
\src_hsdata_ff_reg[27]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(27),
      Q => src_hsdata_ff(27),
      R => '0'
    );
\src_hsdata_ff_reg[28]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(28),
      Q => src_hsdata_ff(28),
      R => '0'
    );
\src_hsdata_ff_reg[29]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(29),
      Q => src_hsdata_ff(29),
      R => '0'
    );
\src_hsdata_ff_reg[2]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(2),
      Q => src_hsdata_ff(2),
      R => '0'
    );
\src_hsdata_ff_reg[30]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(30),
      Q => src_hsdata_ff(30),
      R => '0'
    );
\src_hsdata_ff_reg[31]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(31),
      Q => src_hsdata_ff(31),
      R => '0'
    );
\src_hsdata_ff_reg[32]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(32),
      Q => src_hsdata_ff(32),
      R => '0'
    );
\src_hsdata_ff_reg[33]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(33),
      Q => src_hsdata_ff(33),
      R => '0'
    );
\src_hsdata_ff_reg[34]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(34),
      Q => src_hsdata_ff(34),
      R => '0'
    );
\src_hsdata_ff_reg[3]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(3),
      Q => src_hsdata_ff(3),
      R => '0'
    );
\src_hsdata_ff_reg[4]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(4),
      Q => src_hsdata_ff(4),
      R => '0'
    );
\src_hsdata_ff_reg[5]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(5),
      Q => src_hsdata_ff(5),
      R => '0'
    );
\src_hsdata_ff_reg[6]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(6),
      Q => src_hsdata_ff(6),
      R => '0'
    );
\src_hsdata_ff_reg[7]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(7),
      Q => src_hsdata_ff(7),
      R => '0'
    );
\src_hsdata_ff_reg[8]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(8),
      Q => src_hsdata_ff(8),
      R => '0'
    );
\src_hsdata_ff_reg[9]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(9),
      Q => src_hsdata_ff(9),
      R => '0'
    );
src_sendd_ff_reg: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => '1',
      D => src_send,
      Q => src_sendd_ff,
      R => '0'
    );
xpm_cdc_single_dest2src_inst: entity work.\axi_clock_converter_oclnew_xpm_cdc_single__3\
     port map (
      dest_clk => src_clk,
      dest_out => src_rcv,
      src_clk => dest_clk,
      src_in => dest_ack
    );
xpm_cdc_single_src2dest_inst: entity work.\axi_clock_converter_oclnew_xpm_cdc_single__2\
     port map (
      dest_clk => dest_clk,
      dest_out => dest_req_nxt,
      src_clk => src_clk,
      src_in => src_sendd_ff
    );
end STRUCTURE;
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
entity \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized0\ is
  port (
    src_clk : in STD_LOGIC;
    src_in : in STD_LOGIC_VECTOR ( 35 downto 0 );
    src_send : in STD_LOGIC;
    src_rcv : out STD_LOGIC;
    dest_clk : in STD_LOGIC;
    dest_out : out STD_LOGIC_VECTOR ( 35 downto 0 );
    dest_req : out STD_LOGIC;
    dest_ack : in STD_LOGIC
  );
  attribute DEST_EXT_HSK : integer;
  attribute DEST_EXT_HSK of \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized0\ : entity is 1;
  attribute DEST_SYNC_FF : integer;
  attribute DEST_SYNC_FF of \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized0\ : entity is 2;
  attribute ORIG_REF_NAME : string;
  attribute ORIG_REF_NAME of \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized0\ : entity is "xpm_cdc_handshake";
  attribute SIM_ASSERT_CHK : integer;
  attribute SIM_ASSERT_CHK of \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized0\ : entity is 0;
  attribute SRC_SYNC_FF : integer;
  attribute SRC_SYNC_FF of \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized0\ : entity is 2;
  attribute VERSION : integer;
  attribute VERSION of \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized0\ : entity is 0;
  attribute WIDTH : integer;
  attribute WIDTH of \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized0\ : entity is 36;
  attribute XPM_MODULE : string;
  attribute XPM_MODULE of \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized0\ : entity is "TRUE";
  attribute xpm_cdc : string;
  attribute xpm_cdc of \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized0\ : entity is "HANDSHAKE";
end \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized0\;

architecture STRUCTURE of \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized0\ is
  signal dest_hsdata_en : STD_LOGIC;
  attribute DIRECT_ENABLE : boolean;
  attribute DIRECT_ENABLE of dest_hsdata_en : signal is std.standard.true;
  signal dest_hsdata_ff : STD_LOGIC_VECTOR ( 35 downto 0 );
  attribute RTL_KEEP : string;
  attribute RTL_KEEP of dest_hsdata_ff : signal is "true";
  attribute xpm_cdc of dest_hsdata_ff : signal is "HANDSHAKE";
  signal \^dest_req\ : STD_LOGIC;
  signal dest_req_nxt : STD_LOGIC;
  signal p_0_in : STD_LOGIC;
  signal src_hsdata_ff : STD_LOGIC_VECTOR ( 35 downto 0 );
  signal src_sendd_ff : STD_LOGIC;
  attribute KEEP : string;
  attribute KEEP of \dest_hsdata_ff_reg[0]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[0]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[10]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[10]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[11]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[11]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[12]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[12]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[13]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[13]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[14]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[14]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[15]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[15]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[16]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[16]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[17]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[17]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[18]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[18]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[19]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[19]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[1]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[1]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[20]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[20]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[21]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[21]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[22]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[22]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[23]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[23]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[24]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[24]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[25]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[25]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[26]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[26]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[27]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[27]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[28]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[28]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[29]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[29]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[2]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[2]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[30]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[30]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[31]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[31]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[32]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[32]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[33]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[33]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[34]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[34]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[35]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[35]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[3]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[3]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[4]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[4]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[5]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[5]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[6]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[6]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[7]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[7]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[8]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[8]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[9]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[9]\ : label is "HANDSHAKE";
  attribute DEST_SYNC_FF of xpm_cdc_single_dest2src_inst : label is 2;
  attribute SIM_ASSERT_CHK of xpm_cdc_single_dest2src_inst : label is 0;
  attribute SRC_INPUT_REG : integer;
  attribute SRC_INPUT_REG of xpm_cdc_single_dest2src_inst : label is 0;
  attribute VERSION of xpm_cdc_single_dest2src_inst : label is 0;
  attribute XPM_CDC of xpm_cdc_single_dest2src_inst : label is "SINGLE";
  attribute XPM_MODULE of xpm_cdc_single_dest2src_inst : label is "TRUE";
  attribute DEST_SYNC_FF of xpm_cdc_single_src2dest_inst : label is 2;
  attribute SIM_ASSERT_CHK of xpm_cdc_single_src2dest_inst : label is 0;
  attribute SRC_INPUT_REG of xpm_cdc_single_src2dest_inst : label is 0;
  attribute VERSION of xpm_cdc_single_src2dest_inst : label is 0;
  attribute XPM_CDC of xpm_cdc_single_src2dest_inst : label is "SINGLE";
  attribute XPM_MODULE of xpm_cdc_single_src2dest_inst : label is "TRUE";
begin
  dest_out(35 downto 0) <= dest_hsdata_ff(35 downto 0);
  dest_req <= \^dest_req\;
dest_hsdata_en_inferred_i_1: unisim.vcomponents.LUT2
    generic map(
      INIT => X"2"
    )
        port map (
      I0 => dest_req_nxt,
      I1 => \^dest_req\,
      O => dest_hsdata_en
    );
\dest_hsdata_ff_reg[0]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(0),
      Q => dest_hsdata_ff(0),
      R => '0'
    );
\dest_hsdata_ff_reg[10]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(10),
      Q => dest_hsdata_ff(10),
      R => '0'
    );
\dest_hsdata_ff_reg[11]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(11),
      Q => dest_hsdata_ff(11),
      R => '0'
    );
\dest_hsdata_ff_reg[12]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(12),
      Q => dest_hsdata_ff(12),
      R => '0'
    );
\dest_hsdata_ff_reg[13]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(13),
      Q => dest_hsdata_ff(13),
      R => '0'
    );
\dest_hsdata_ff_reg[14]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(14),
      Q => dest_hsdata_ff(14),
      R => '0'
    );
\dest_hsdata_ff_reg[15]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(15),
      Q => dest_hsdata_ff(15),
      R => '0'
    );
\dest_hsdata_ff_reg[16]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(16),
      Q => dest_hsdata_ff(16),
      R => '0'
    );
\dest_hsdata_ff_reg[17]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(17),
      Q => dest_hsdata_ff(17),
      R => '0'
    );
\dest_hsdata_ff_reg[18]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(18),
      Q => dest_hsdata_ff(18),
      R => '0'
    );
\dest_hsdata_ff_reg[19]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(19),
      Q => dest_hsdata_ff(19),
      R => '0'
    );
\dest_hsdata_ff_reg[1]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(1),
      Q => dest_hsdata_ff(1),
      R => '0'
    );
\dest_hsdata_ff_reg[20]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(20),
      Q => dest_hsdata_ff(20),
      R => '0'
    );
\dest_hsdata_ff_reg[21]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(21),
      Q => dest_hsdata_ff(21),
      R => '0'
    );
\dest_hsdata_ff_reg[22]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(22),
      Q => dest_hsdata_ff(22),
      R => '0'
    );
\dest_hsdata_ff_reg[23]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(23),
      Q => dest_hsdata_ff(23),
      R => '0'
    );
\dest_hsdata_ff_reg[24]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(24),
      Q => dest_hsdata_ff(24),
      R => '0'
    );
\dest_hsdata_ff_reg[25]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(25),
      Q => dest_hsdata_ff(25),
      R => '0'
    );
\dest_hsdata_ff_reg[26]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(26),
      Q => dest_hsdata_ff(26),
      R => '0'
    );
\dest_hsdata_ff_reg[27]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(27),
      Q => dest_hsdata_ff(27),
      R => '0'
    );
\dest_hsdata_ff_reg[28]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(28),
      Q => dest_hsdata_ff(28),
      R => '0'
    );
\dest_hsdata_ff_reg[29]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(29),
      Q => dest_hsdata_ff(29),
      R => '0'
    );
\dest_hsdata_ff_reg[2]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(2),
      Q => dest_hsdata_ff(2),
      R => '0'
    );
\dest_hsdata_ff_reg[30]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(30),
      Q => dest_hsdata_ff(30),
      R => '0'
    );
\dest_hsdata_ff_reg[31]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(31),
      Q => dest_hsdata_ff(31),
      R => '0'
    );
\dest_hsdata_ff_reg[32]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(32),
      Q => dest_hsdata_ff(32),
      R => '0'
    );
\dest_hsdata_ff_reg[33]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(33),
      Q => dest_hsdata_ff(33),
      R => '0'
    );
\dest_hsdata_ff_reg[34]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(34),
      Q => dest_hsdata_ff(34),
      R => '0'
    );
\dest_hsdata_ff_reg[35]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(35),
      Q => dest_hsdata_ff(35),
      R => '0'
    );
\dest_hsdata_ff_reg[3]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(3),
      Q => dest_hsdata_ff(3),
      R => '0'
    );
\dest_hsdata_ff_reg[4]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(4),
      Q => dest_hsdata_ff(4),
      R => '0'
    );
\dest_hsdata_ff_reg[5]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(5),
      Q => dest_hsdata_ff(5),
      R => '0'
    );
\dest_hsdata_ff_reg[6]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(6),
      Q => dest_hsdata_ff(6),
      R => '0'
    );
\dest_hsdata_ff_reg[7]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(7),
      Q => dest_hsdata_ff(7),
      R => '0'
    );
\dest_hsdata_ff_reg[8]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(8),
      Q => dest_hsdata_ff(8),
      R => '0'
    );
\dest_hsdata_ff_reg[9]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(9),
      Q => dest_hsdata_ff(9),
      R => '0'
    );
dest_req_ff_reg: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => '1',
      D => dest_req_nxt,
      Q => \^dest_req\,
      R => '0'
    );
\src_hsdata_ff[35]_i_1\: unisim.vcomponents.LUT1
    generic map(
      INIT => X"1"
    )
        port map (
      I0 => src_sendd_ff,
      O => p_0_in
    );
\src_hsdata_ff_reg[0]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(0),
      Q => src_hsdata_ff(0),
      R => '0'
    );
\src_hsdata_ff_reg[10]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(10),
      Q => src_hsdata_ff(10),
      R => '0'
    );
\src_hsdata_ff_reg[11]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(11),
      Q => src_hsdata_ff(11),
      R => '0'
    );
\src_hsdata_ff_reg[12]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(12),
      Q => src_hsdata_ff(12),
      R => '0'
    );
\src_hsdata_ff_reg[13]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(13),
      Q => src_hsdata_ff(13),
      R => '0'
    );
\src_hsdata_ff_reg[14]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(14),
      Q => src_hsdata_ff(14),
      R => '0'
    );
\src_hsdata_ff_reg[15]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(15),
      Q => src_hsdata_ff(15),
      R => '0'
    );
\src_hsdata_ff_reg[16]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(16),
      Q => src_hsdata_ff(16),
      R => '0'
    );
\src_hsdata_ff_reg[17]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(17),
      Q => src_hsdata_ff(17),
      R => '0'
    );
\src_hsdata_ff_reg[18]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(18),
      Q => src_hsdata_ff(18),
      R => '0'
    );
\src_hsdata_ff_reg[19]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(19),
      Q => src_hsdata_ff(19),
      R => '0'
    );
\src_hsdata_ff_reg[1]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(1),
      Q => src_hsdata_ff(1),
      R => '0'
    );
\src_hsdata_ff_reg[20]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(20),
      Q => src_hsdata_ff(20),
      R => '0'
    );
\src_hsdata_ff_reg[21]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(21),
      Q => src_hsdata_ff(21),
      R => '0'
    );
\src_hsdata_ff_reg[22]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(22),
      Q => src_hsdata_ff(22),
      R => '0'
    );
\src_hsdata_ff_reg[23]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(23),
      Q => src_hsdata_ff(23),
      R => '0'
    );
\src_hsdata_ff_reg[24]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(24),
      Q => src_hsdata_ff(24),
      R => '0'
    );
\src_hsdata_ff_reg[25]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(25),
      Q => src_hsdata_ff(25),
      R => '0'
    );
\src_hsdata_ff_reg[26]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(26),
      Q => src_hsdata_ff(26),
      R => '0'
    );
\src_hsdata_ff_reg[27]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(27),
      Q => src_hsdata_ff(27),
      R => '0'
    );
\src_hsdata_ff_reg[28]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(28),
      Q => src_hsdata_ff(28),
      R => '0'
    );
\src_hsdata_ff_reg[29]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(29),
      Q => src_hsdata_ff(29),
      R => '0'
    );
\src_hsdata_ff_reg[2]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(2),
      Q => src_hsdata_ff(2),
      R => '0'
    );
\src_hsdata_ff_reg[30]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(30),
      Q => src_hsdata_ff(30),
      R => '0'
    );
\src_hsdata_ff_reg[31]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(31),
      Q => src_hsdata_ff(31),
      R => '0'
    );
\src_hsdata_ff_reg[32]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(32),
      Q => src_hsdata_ff(32),
      R => '0'
    );
\src_hsdata_ff_reg[33]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(33),
      Q => src_hsdata_ff(33),
      R => '0'
    );
\src_hsdata_ff_reg[34]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(34),
      Q => src_hsdata_ff(34),
      R => '0'
    );
\src_hsdata_ff_reg[35]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(35),
      Q => src_hsdata_ff(35),
      R => '0'
    );
\src_hsdata_ff_reg[3]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(3),
      Q => src_hsdata_ff(3),
      R => '0'
    );
\src_hsdata_ff_reg[4]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(4),
      Q => src_hsdata_ff(4),
      R => '0'
    );
\src_hsdata_ff_reg[5]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(5),
      Q => src_hsdata_ff(5),
      R => '0'
    );
\src_hsdata_ff_reg[6]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(6),
      Q => src_hsdata_ff(6),
      R => '0'
    );
\src_hsdata_ff_reg[7]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(7),
      Q => src_hsdata_ff(7),
      R => '0'
    );
\src_hsdata_ff_reg[8]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(8),
      Q => src_hsdata_ff(8),
      R => '0'
    );
\src_hsdata_ff_reg[9]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(9),
      Q => src_hsdata_ff(9),
      R => '0'
    );
src_sendd_ff_reg: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => '1',
      D => src_send,
      Q => src_sendd_ff,
      R => '0'
    );
xpm_cdc_single_dest2src_inst: entity work.\axi_clock_converter_oclnew_xpm_cdc_single__7\
     port map (
      dest_clk => src_clk,
      dest_out => src_rcv,
      src_clk => dest_clk,
      src_in => dest_ack
    );
xpm_cdc_single_src2dest_inst: entity work.\axi_clock_converter_oclnew_xpm_cdc_single__6\
     port map (
      dest_clk => dest_clk,
      dest_out => dest_req_nxt,
      src_clk => src_clk,
      src_in => src_sendd_ff
    );
end STRUCTURE;
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
entity \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized1\ is
  port (
    src_clk : in STD_LOGIC;
    src_in : in STD_LOGIC_VECTOR ( 1 downto 0 );
    src_send : in STD_LOGIC;
    src_rcv : out STD_LOGIC;
    dest_clk : in STD_LOGIC;
    dest_out : out STD_LOGIC_VECTOR ( 1 downto 0 );
    dest_req : out STD_LOGIC;
    dest_ack : in STD_LOGIC
  );
  attribute DEST_EXT_HSK : integer;
  attribute DEST_EXT_HSK of \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized1\ : entity is 1;
  attribute DEST_SYNC_FF : integer;
  attribute DEST_SYNC_FF of \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized1\ : entity is 2;
  attribute ORIG_REF_NAME : string;
  attribute ORIG_REF_NAME of \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized1\ : entity is "xpm_cdc_handshake";
  attribute SIM_ASSERT_CHK : integer;
  attribute SIM_ASSERT_CHK of \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized1\ : entity is 0;
  attribute SRC_SYNC_FF : integer;
  attribute SRC_SYNC_FF of \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized1\ : entity is 2;
  attribute VERSION : integer;
  attribute VERSION of \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized1\ : entity is 0;
  attribute WIDTH : integer;
  attribute WIDTH of \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized1\ : entity is 2;
  attribute XPM_MODULE : string;
  attribute XPM_MODULE of \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized1\ : entity is "TRUE";
  attribute xpm_cdc : string;
  attribute xpm_cdc of \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized1\ : entity is "HANDSHAKE";
end \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized1\;

architecture STRUCTURE of \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized1\ is
  signal dest_hsdata_en : STD_LOGIC;
  attribute DIRECT_ENABLE : boolean;
  attribute DIRECT_ENABLE of dest_hsdata_en : signal is std.standard.true;
  signal dest_hsdata_ff : STD_LOGIC_VECTOR ( 1 downto 0 );
  attribute RTL_KEEP : string;
  attribute RTL_KEEP of dest_hsdata_ff : signal is "true";
  attribute xpm_cdc of dest_hsdata_ff : signal is "HANDSHAKE";
  signal \^dest_req\ : STD_LOGIC;
  signal dest_req_nxt : STD_LOGIC;
  signal p_0_in : STD_LOGIC;
  signal src_hsdata_ff : STD_LOGIC_VECTOR ( 1 downto 0 );
  signal src_sendd_ff : STD_LOGIC;
  attribute KEEP : string;
  attribute KEEP of \dest_hsdata_ff_reg[0]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[0]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[1]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[1]\ : label is "HANDSHAKE";
  attribute DEST_SYNC_FF of xpm_cdc_single_dest2src_inst : label is 2;
  attribute SIM_ASSERT_CHK of xpm_cdc_single_dest2src_inst : label is 0;
  attribute SRC_INPUT_REG : integer;
  attribute SRC_INPUT_REG of xpm_cdc_single_dest2src_inst : label is 0;
  attribute VERSION of xpm_cdc_single_dest2src_inst : label is 0;
  attribute XPM_CDC of xpm_cdc_single_dest2src_inst : label is "SINGLE";
  attribute XPM_MODULE of xpm_cdc_single_dest2src_inst : label is "TRUE";
  attribute DEST_SYNC_FF of xpm_cdc_single_src2dest_inst : label is 2;
  attribute SIM_ASSERT_CHK of xpm_cdc_single_src2dest_inst : label is 0;
  attribute SRC_INPUT_REG of xpm_cdc_single_src2dest_inst : label is 0;
  attribute VERSION of xpm_cdc_single_src2dest_inst : label is 0;
  attribute XPM_CDC of xpm_cdc_single_src2dest_inst : label is "SINGLE";
  attribute XPM_MODULE of xpm_cdc_single_src2dest_inst : label is "TRUE";
begin
  dest_out(1 downto 0) <= dest_hsdata_ff(1 downto 0);
  dest_req <= \^dest_req\;
dest_hsdata_en_inferred_i_1: unisim.vcomponents.LUT2
    generic map(
      INIT => X"2"
    )
        port map (
      I0 => dest_req_nxt,
      I1 => \^dest_req\,
      O => dest_hsdata_en
    );
\dest_hsdata_ff_reg[0]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(0),
      Q => dest_hsdata_ff(0),
      R => '0'
    );
\dest_hsdata_ff_reg[1]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(1),
      Q => dest_hsdata_ff(1),
      R => '0'
    );
dest_req_ff_reg: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => '1',
      D => dest_req_nxt,
      Q => \^dest_req\,
      R => '0'
    );
\src_hsdata_ff[1]_i_1\: unisim.vcomponents.LUT1
    generic map(
      INIT => X"1"
    )
        port map (
      I0 => src_sendd_ff,
      O => p_0_in
    );
\src_hsdata_ff_reg[0]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(0),
      Q => src_hsdata_ff(0),
      R => '0'
    );
\src_hsdata_ff_reg[1]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(1),
      Q => src_hsdata_ff(1),
      R => '0'
    );
src_sendd_ff_reg: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => '1',
      D => src_send,
      Q => src_sendd_ff,
      R => '0'
    );
xpm_cdc_single_dest2src_inst: entity work.\axi_clock_converter_oclnew_xpm_cdc_single__9\
     port map (
      dest_clk => src_clk,
      dest_out => src_rcv,
      src_clk => dest_clk,
      src_in => dest_ack
    );
xpm_cdc_single_src2dest_inst: entity work.\axi_clock_converter_oclnew_xpm_cdc_single__8\
     port map (
      dest_clk => dest_clk,
      dest_out => dest_req_nxt,
      src_clk => src_clk,
      src_in => src_sendd_ff
    );
end STRUCTURE;
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
entity \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized2\ is
  port (
    src_clk : in STD_LOGIC;
    src_in : in STD_LOGIC_VECTOR ( 33 downto 0 );
    src_send : in STD_LOGIC;
    src_rcv : out STD_LOGIC;
    dest_clk : in STD_LOGIC;
    dest_out : out STD_LOGIC_VECTOR ( 33 downto 0 );
    dest_req : out STD_LOGIC;
    dest_ack : in STD_LOGIC
  );
  attribute DEST_EXT_HSK : integer;
  attribute DEST_EXT_HSK of \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized2\ : entity is 1;
  attribute DEST_SYNC_FF : integer;
  attribute DEST_SYNC_FF of \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized2\ : entity is 2;
  attribute ORIG_REF_NAME : string;
  attribute ORIG_REF_NAME of \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized2\ : entity is "xpm_cdc_handshake";
  attribute SIM_ASSERT_CHK : integer;
  attribute SIM_ASSERT_CHK of \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized2\ : entity is 0;
  attribute SRC_SYNC_FF : integer;
  attribute SRC_SYNC_FF of \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized2\ : entity is 2;
  attribute VERSION : integer;
  attribute VERSION of \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized2\ : entity is 0;
  attribute WIDTH : integer;
  attribute WIDTH of \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized2\ : entity is 34;
  attribute XPM_MODULE : string;
  attribute XPM_MODULE of \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized2\ : entity is "TRUE";
  attribute xpm_cdc : string;
  attribute xpm_cdc of \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized2\ : entity is "HANDSHAKE";
end \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized2\;

architecture STRUCTURE of \axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized2\ is
  signal dest_hsdata_en : STD_LOGIC;
  attribute DIRECT_ENABLE : boolean;
  attribute DIRECT_ENABLE of dest_hsdata_en : signal is std.standard.true;
  signal dest_hsdata_ff : STD_LOGIC_VECTOR ( 33 downto 0 );
  attribute RTL_KEEP : string;
  attribute RTL_KEEP of dest_hsdata_ff : signal is "true";
  attribute xpm_cdc of dest_hsdata_ff : signal is "HANDSHAKE";
  signal \^dest_req\ : STD_LOGIC;
  signal dest_req_nxt : STD_LOGIC;
  signal p_0_in : STD_LOGIC;
  signal src_hsdata_ff : STD_LOGIC_VECTOR ( 33 downto 0 );
  signal src_sendd_ff : STD_LOGIC;
  attribute KEEP : string;
  attribute KEEP of \dest_hsdata_ff_reg[0]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[0]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[10]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[10]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[11]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[11]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[12]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[12]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[13]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[13]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[14]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[14]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[15]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[15]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[16]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[16]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[17]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[17]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[18]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[18]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[19]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[19]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[1]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[1]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[20]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[20]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[21]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[21]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[22]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[22]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[23]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[23]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[24]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[24]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[25]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[25]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[26]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[26]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[27]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[27]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[28]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[28]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[29]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[29]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[2]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[2]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[30]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[30]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[31]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[31]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[32]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[32]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[33]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[33]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[3]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[3]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[4]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[4]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[5]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[5]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[6]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[6]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[7]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[7]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[8]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[8]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[9]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[9]\ : label is "HANDSHAKE";
  attribute DEST_SYNC_FF of xpm_cdc_single_dest2src_inst : label is 2;
  attribute SIM_ASSERT_CHK of xpm_cdc_single_dest2src_inst : label is 0;
  attribute SRC_INPUT_REG : integer;
  attribute SRC_INPUT_REG of xpm_cdc_single_dest2src_inst : label is 0;
  attribute VERSION of xpm_cdc_single_dest2src_inst : label is 0;
  attribute XPM_CDC of xpm_cdc_single_dest2src_inst : label is "SINGLE";
  attribute XPM_MODULE of xpm_cdc_single_dest2src_inst : label is "TRUE";
  attribute DEST_SYNC_FF of xpm_cdc_single_src2dest_inst : label is 2;
  attribute SIM_ASSERT_CHK of xpm_cdc_single_src2dest_inst : label is 0;
  attribute SRC_INPUT_REG of xpm_cdc_single_src2dest_inst : label is 0;
  attribute VERSION of xpm_cdc_single_src2dest_inst : label is 0;
  attribute XPM_CDC of xpm_cdc_single_src2dest_inst : label is "SINGLE";
  attribute XPM_MODULE of xpm_cdc_single_src2dest_inst : label is "TRUE";
begin
  dest_out(33 downto 0) <= dest_hsdata_ff(33 downto 0);
  dest_req <= \^dest_req\;
dest_hsdata_en_inferred_i_1: unisim.vcomponents.LUT2
    generic map(
      INIT => X"2"
    )
        port map (
      I0 => dest_req_nxt,
      I1 => \^dest_req\,
      O => dest_hsdata_en
    );
\dest_hsdata_ff_reg[0]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(0),
      Q => dest_hsdata_ff(0),
      R => '0'
    );
\dest_hsdata_ff_reg[10]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(10),
      Q => dest_hsdata_ff(10),
      R => '0'
    );
\dest_hsdata_ff_reg[11]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(11),
      Q => dest_hsdata_ff(11),
      R => '0'
    );
\dest_hsdata_ff_reg[12]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(12),
      Q => dest_hsdata_ff(12),
      R => '0'
    );
\dest_hsdata_ff_reg[13]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(13),
      Q => dest_hsdata_ff(13),
      R => '0'
    );
\dest_hsdata_ff_reg[14]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(14),
      Q => dest_hsdata_ff(14),
      R => '0'
    );
\dest_hsdata_ff_reg[15]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(15),
      Q => dest_hsdata_ff(15),
      R => '0'
    );
\dest_hsdata_ff_reg[16]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(16),
      Q => dest_hsdata_ff(16),
      R => '0'
    );
\dest_hsdata_ff_reg[17]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(17),
      Q => dest_hsdata_ff(17),
      R => '0'
    );
\dest_hsdata_ff_reg[18]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(18),
      Q => dest_hsdata_ff(18),
      R => '0'
    );
\dest_hsdata_ff_reg[19]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(19),
      Q => dest_hsdata_ff(19),
      R => '0'
    );
\dest_hsdata_ff_reg[1]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(1),
      Q => dest_hsdata_ff(1),
      R => '0'
    );
\dest_hsdata_ff_reg[20]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(20),
      Q => dest_hsdata_ff(20),
      R => '0'
    );
\dest_hsdata_ff_reg[21]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(21),
      Q => dest_hsdata_ff(21),
      R => '0'
    );
\dest_hsdata_ff_reg[22]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(22),
      Q => dest_hsdata_ff(22),
      R => '0'
    );
\dest_hsdata_ff_reg[23]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(23),
      Q => dest_hsdata_ff(23),
      R => '0'
    );
\dest_hsdata_ff_reg[24]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(24),
      Q => dest_hsdata_ff(24),
      R => '0'
    );
\dest_hsdata_ff_reg[25]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(25),
      Q => dest_hsdata_ff(25),
      R => '0'
    );
\dest_hsdata_ff_reg[26]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(26),
      Q => dest_hsdata_ff(26),
      R => '0'
    );
\dest_hsdata_ff_reg[27]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(27),
      Q => dest_hsdata_ff(27),
      R => '0'
    );
\dest_hsdata_ff_reg[28]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(28),
      Q => dest_hsdata_ff(28),
      R => '0'
    );
\dest_hsdata_ff_reg[29]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(29),
      Q => dest_hsdata_ff(29),
      R => '0'
    );
\dest_hsdata_ff_reg[2]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(2),
      Q => dest_hsdata_ff(2),
      R => '0'
    );
\dest_hsdata_ff_reg[30]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(30),
      Q => dest_hsdata_ff(30),
      R => '0'
    );
\dest_hsdata_ff_reg[31]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(31),
      Q => dest_hsdata_ff(31),
      R => '0'
    );
\dest_hsdata_ff_reg[32]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(32),
      Q => dest_hsdata_ff(32),
      R => '0'
    );
\dest_hsdata_ff_reg[33]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(33),
      Q => dest_hsdata_ff(33),
      R => '0'
    );
\dest_hsdata_ff_reg[3]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(3),
      Q => dest_hsdata_ff(3),
      R => '0'
    );
\dest_hsdata_ff_reg[4]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(4),
      Q => dest_hsdata_ff(4),
      R => '0'
    );
\dest_hsdata_ff_reg[5]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(5),
      Q => dest_hsdata_ff(5),
      R => '0'
    );
\dest_hsdata_ff_reg[6]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(6),
      Q => dest_hsdata_ff(6),
      R => '0'
    );
\dest_hsdata_ff_reg[7]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(7),
      Q => dest_hsdata_ff(7),
      R => '0'
    );
\dest_hsdata_ff_reg[8]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(8),
      Q => dest_hsdata_ff(8),
      R => '0'
    );
\dest_hsdata_ff_reg[9]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(9),
      Q => dest_hsdata_ff(9),
      R => '0'
    );
dest_req_ff_reg: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => '1',
      D => dest_req_nxt,
      Q => \^dest_req\,
      R => '0'
    );
\src_hsdata_ff[33]_i_1\: unisim.vcomponents.LUT1
    generic map(
      INIT => X"1"
    )
        port map (
      I0 => src_sendd_ff,
      O => p_0_in
    );
\src_hsdata_ff_reg[0]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(0),
      Q => src_hsdata_ff(0),
      R => '0'
    );
\src_hsdata_ff_reg[10]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(10),
      Q => src_hsdata_ff(10),
      R => '0'
    );
\src_hsdata_ff_reg[11]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(11),
      Q => src_hsdata_ff(11),
      R => '0'
    );
\src_hsdata_ff_reg[12]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(12),
      Q => src_hsdata_ff(12),
      R => '0'
    );
\src_hsdata_ff_reg[13]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(13),
      Q => src_hsdata_ff(13),
      R => '0'
    );
\src_hsdata_ff_reg[14]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(14),
      Q => src_hsdata_ff(14),
      R => '0'
    );
\src_hsdata_ff_reg[15]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(15),
      Q => src_hsdata_ff(15),
      R => '0'
    );
\src_hsdata_ff_reg[16]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(16),
      Q => src_hsdata_ff(16),
      R => '0'
    );
\src_hsdata_ff_reg[17]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(17),
      Q => src_hsdata_ff(17),
      R => '0'
    );
\src_hsdata_ff_reg[18]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(18),
      Q => src_hsdata_ff(18),
      R => '0'
    );
\src_hsdata_ff_reg[19]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(19),
      Q => src_hsdata_ff(19),
      R => '0'
    );
\src_hsdata_ff_reg[1]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(1),
      Q => src_hsdata_ff(1),
      R => '0'
    );
\src_hsdata_ff_reg[20]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(20),
      Q => src_hsdata_ff(20),
      R => '0'
    );
\src_hsdata_ff_reg[21]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(21),
      Q => src_hsdata_ff(21),
      R => '0'
    );
\src_hsdata_ff_reg[22]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(22),
      Q => src_hsdata_ff(22),
      R => '0'
    );
\src_hsdata_ff_reg[23]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(23),
      Q => src_hsdata_ff(23),
      R => '0'
    );
\src_hsdata_ff_reg[24]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(24),
      Q => src_hsdata_ff(24),
      R => '0'
    );
\src_hsdata_ff_reg[25]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(25),
      Q => src_hsdata_ff(25),
      R => '0'
    );
\src_hsdata_ff_reg[26]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(26),
      Q => src_hsdata_ff(26),
      R => '0'
    );
\src_hsdata_ff_reg[27]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(27),
      Q => src_hsdata_ff(27),
      R => '0'
    );
\src_hsdata_ff_reg[28]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(28),
      Q => src_hsdata_ff(28),
      R => '0'
    );
\src_hsdata_ff_reg[29]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(29),
      Q => src_hsdata_ff(29),
      R => '0'
    );
\src_hsdata_ff_reg[2]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(2),
      Q => src_hsdata_ff(2),
      R => '0'
    );
\src_hsdata_ff_reg[30]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(30),
      Q => src_hsdata_ff(30),
      R => '0'
    );
\src_hsdata_ff_reg[31]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(31),
      Q => src_hsdata_ff(31),
      R => '0'
    );
\src_hsdata_ff_reg[32]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(32),
      Q => src_hsdata_ff(32),
      R => '0'
    );
\src_hsdata_ff_reg[33]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(33),
      Q => src_hsdata_ff(33),
      R => '0'
    );
\src_hsdata_ff_reg[3]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(3),
      Q => src_hsdata_ff(3),
      R => '0'
    );
\src_hsdata_ff_reg[4]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(4),
      Q => src_hsdata_ff(4),
      R => '0'
    );
\src_hsdata_ff_reg[5]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(5),
      Q => src_hsdata_ff(5),
      R => '0'
    );
\src_hsdata_ff_reg[6]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(6),
      Q => src_hsdata_ff(6),
      R => '0'
    );
\src_hsdata_ff_reg[7]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(7),
      Q => src_hsdata_ff(7),
      R => '0'
    );
\src_hsdata_ff_reg[8]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(8),
      Q => src_hsdata_ff(8),
      R => '0'
    );
\src_hsdata_ff_reg[9]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(9),
      Q => src_hsdata_ff(9),
      R => '0'
    );
src_sendd_ff_reg: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => '1',
      D => src_send,
      Q => src_sendd_ff,
      R => '0'
    );
xpm_cdc_single_dest2src_inst: entity work.axi_clock_converter_oclnew_xpm_cdc_single
     port map (
      dest_clk => src_clk,
      dest_out => src_rcv,
      src_clk => dest_clk,
      src_in => dest_ack
    );
xpm_cdc_single_src2dest_inst: entity work.\axi_clock_converter_oclnew_xpm_cdc_single__10\
     port map (
      dest_clk => dest_clk,
      dest_out => dest_req_nxt,
      src_clk => src_clk,
      src_in => src_sendd_ff
    );
end STRUCTURE;
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
entity \axi_clock_converter_oclnew_xpm_cdc_handshake__xdcDup__1\ is
  port (
    src_clk : in STD_LOGIC;
    src_in : in STD_LOGIC_VECTOR ( 34 downto 0 );
    src_send : in STD_LOGIC;
    src_rcv : out STD_LOGIC;
    dest_clk : in STD_LOGIC;
    dest_out : out STD_LOGIC_VECTOR ( 34 downto 0 );
    dest_req : out STD_LOGIC;
    dest_ack : in STD_LOGIC
  );
  attribute DEST_EXT_HSK : integer;
  attribute DEST_EXT_HSK of \axi_clock_converter_oclnew_xpm_cdc_handshake__xdcDup__1\ : entity is 1;
  attribute DEST_SYNC_FF : integer;
  attribute DEST_SYNC_FF of \axi_clock_converter_oclnew_xpm_cdc_handshake__xdcDup__1\ : entity is 2;
  attribute ORIG_REF_NAME : string;
  attribute ORIG_REF_NAME of \axi_clock_converter_oclnew_xpm_cdc_handshake__xdcDup__1\ : entity is "xpm_cdc_handshake";
  attribute SIM_ASSERT_CHK : integer;
  attribute SIM_ASSERT_CHK of \axi_clock_converter_oclnew_xpm_cdc_handshake__xdcDup__1\ : entity is 0;
  attribute SRC_SYNC_FF : integer;
  attribute SRC_SYNC_FF of \axi_clock_converter_oclnew_xpm_cdc_handshake__xdcDup__1\ : entity is 2;
  attribute VERSION : integer;
  attribute VERSION of \axi_clock_converter_oclnew_xpm_cdc_handshake__xdcDup__1\ : entity is 0;
  attribute WIDTH : integer;
  attribute WIDTH of \axi_clock_converter_oclnew_xpm_cdc_handshake__xdcDup__1\ : entity is 35;
  attribute XPM_MODULE : string;
  attribute XPM_MODULE of \axi_clock_converter_oclnew_xpm_cdc_handshake__xdcDup__1\ : entity is "TRUE";
  attribute xpm_cdc : string;
  attribute xpm_cdc of \axi_clock_converter_oclnew_xpm_cdc_handshake__xdcDup__1\ : entity is "HANDSHAKE";
end \axi_clock_converter_oclnew_xpm_cdc_handshake__xdcDup__1\;

architecture STRUCTURE of \axi_clock_converter_oclnew_xpm_cdc_handshake__xdcDup__1\ is
  signal dest_hsdata_en : STD_LOGIC;
  attribute DIRECT_ENABLE : boolean;
  attribute DIRECT_ENABLE of dest_hsdata_en : signal is std.standard.true;
  signal dest_hsdata_ff : STD_LOGIC_VECTOR ( 34 downto 0 );
  attribute RTL_KEEP : string;
  attribute RTL_KEEP of dest_hsdata_ff : signal is "true";
  attribute xpm_cdc of dest_hsdata_ff : signal is "HANDSHAKE";
  signal \^dest_req\ : STD_LOGIC;
  signal dest_req_nxt : STD_LOGIC;
  signal p_0_in : STD_LOGIC;
  signal src_hsdata_ff : STD_LOGIC_VECTOR ( 34 downto 0 );
  signal src_sendd_ff : STD_LOGIC;
  attribute KEEP : string;
  attribute KEEP of \dest_hsdata_ff_reg[0]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[0]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[10]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[10]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[11]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[11]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[12]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[12]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[13]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[13]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[14]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[14]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[15]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[15]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[16]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[16]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[17]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[17]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[18]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[18]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[19]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[19]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[1]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[1]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[20]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[20]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[21]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[21]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[22]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[22]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[23]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[23]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[24]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[24]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[25]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[25]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[26]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[26]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[27]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[27]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[28]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[28]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[29]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[29]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[2]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[2]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[30]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[30]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[31]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[31]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[32]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[32]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[33]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[33]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[34]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[34]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[3]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[3]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[4]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[4]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[5]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[5]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[6]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[6]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[7]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[7]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[8]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[8]\ : label is "HANDSHAKE";
  attribute KEEP of \dest_hsdata_ff_reg[9]\ : label is "yes";
  attribute XPM_CDC of \dest_hsdata_ff_reg[9]\ : label is "HANDSHAKE";
  attribute DEST_SYNC_FF of xpm_cdc_single_dest2src_inst : label is 2;
  attribute SIM_ASSERT_CHK of xpm_cdc_single_dest2src_inst : label is 0;
  attribute SRC_INPUT_REG : integer;
  attribute SRC_INPUT_REG of xpm_cdc_single_dest2src_inst : label is 0;
  attribute VERSION of xpm_cdc_single_dest2src_inst : label is 0;
  attribute XPM_CDC of xpm_cdc_single_dest2src_inst : label is "SINGLE";
  attribute XPM_MODULE of xpm_cdc_single_dest2src_inst : label is "TRUE";
  attribute DEST_SYNC_FF of xpm_cdc_single_src2dest_inst : label is 2;
  attribute SIM_ASSERT_CHK of xpm_cdc_single_src2dest_inst : label is 0;
  attribute SRC_INPUT_REG of xpm_cdc_single_src2dest_inst : label is 0;
  attribute VERSION of xpm_cdc_single_src2dest_inst : label is 0;
  attribute XPM_CDC of xpm_cdc_single_src2dest_inst : label is "SINGLE";
  attribute XPM_MODULE of xpm_cdc_single_src2dest_inst : label is "TRUE";
begin
  dest_out(34 downto 0) <= dest_hsdata_ff(34 downto 0);
  dest_req <= \^dest_req\;
dest_hsdata_en_inferred_i_1: unisim.vcomponents.LUT2
    generic map(
      INIT => X"2"
    )
        port map (
      I0 => dest_req_nxt,
      I1 => \^dest_req\,
      O => dest_hsdata_en
    );
\dest_hsdata_ff_reg[0]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(0),
      Q => dest_hsdata_ff(0),
      R => '0'
    );
\dest_hsdata_ff_reg[10]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(10),
      Q => dest_hsdata_ff(10),
      R => '0'
    );
\dest_hsdata_ff_reg[11]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(11),
      Q => dest_hsdata_ff(11),
      R => '0'
    );
\dest_hsdata_ff_reg[12]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(12),
      Q => dest_hsdata_ff(12),
      R => '0'
    );
\dest_hsdata_ff_reg[13]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(13),
      Q => dest_hsdata_ff(13),
      R => '0'
    );
\dest_hsdata_ff_reg[14]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(14),
      Q => dest_hsdata_ff(14),
      R => '0'
    );
\dest_hsdata_ff_reg[15]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(15),
      Q => dest_hsdata_ff(15),
      R => '0'
    );
\dest_hsdata_ff_reg[16]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(16),
      Q => dest_hsdata_ff(16),
      R => '0'
    );
\dest_hsdata_ff_reg[17]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(17),
      Q => dest_hsdata_ff(17),
      R => '0'
    );
\dest_hsdata_ff_reg[18]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(18),
      Q => dest_hsdata_ff(18),
      R => '0'
    );
\dest_hsdata_ff_reg[19]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(19),
      Q => dest_hsdata_ff(19),
      R => '0'
    );
\dest_hsdata_ff_reg[1]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(1),
      Q => dest_hsdata_ff(1),
      R => '0'
    );
\dest_hsdata_ff_reg[20]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(20),
      Q => dest_hsdata_ff(20),
      R => '0'
    );
\dest_hsdata_ff_reg[21]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(21),
      Q => dest_hsdata_ff(21),
      R => '0'
    );
\dest_hsdata_ff_reg[22]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(22),
      Q => dest_hsdata_ff(22),
      R => '0'
    );
\dest_hsdata_ff_reg[23]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(23),
      Q => dest_hsdata_ff(23),
      R => '0'
    );
\dest_hsdata_ff_reg[24]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(24),
      Q => dest_hsdata_ff(24),
      R => '0'
    );
\dest_hsdata_ff_reg[25]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(25),
      Q => dest_hsdata_ff(25),
      R => '0'
    );
\dest_hsdata_ff_reg[26]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(26),
      Q => dest_hsdata_ff(26),
      R => '0'
    );
\dest_hsdata_ff_reg[27]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(27),
      Q => dest_hsdata_ff(27),
      R => '0'
    );
\dest_hsdata_ff_reg[28]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(28),
      Q => dest_hsdata_ff(28),
      R => '0'
    );
\dest_hsdata_ff_reg[29]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(29),
      Q => dest_hsdata_ff(29),
      R => '0'
    );
\dest_hsdata_ff_reg[2]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(2),
      Q => dest_hsdata_ff(2),
      R => '0'
    );
\dest_hsdata_ff_reg[30]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(30),
      Q => dest_hsdata_ff(30),
      R => '0'
    );
\dest_hsdata_ff_reg[31]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(31),
      Q => dest_hsdata_ff(31),
      R => '0'
    );
\dest_hsdata_ff_reg[32]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(32),
      Q => dest_hsdata_ff(32),
      R => '0'
    );
\dest_hsdata_ff_reg[33]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(33),
      Q => dest_hsdata_ff(33),
      R => '0'
    );
\dest_hsdata_ff_reg[34]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(34),
      Q => dest_hsdata_ff(34),
      R => '0'
    );
\dest_hsdata_ff_reg[3]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(3),
      Q => dest_hsdata_ff(3),
      R => '0'
    );
\dest_hsdata_ff_reg[4]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(4),
      Q => dest_hsdata_ff(4),
      R => '0'
    );
\dest_hsdata_ff_reg[5]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(5),
      Q => dest_hsdata_ff(5),
      R => '0'
    );
\dest_hsdata_ff_reg[6]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(6),
      Q => dest_hsdata_ff(6),
      R => '0'
    );
\dest_hsdata_ff_reg[7]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(7),
      Q => dest_hsdata_ff(7),
      R => '0'
    );
\dest_hsdata_ff_reg[8]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(8),
      Q => dest_hsdata_ff(8),
      R => '0'
    );
\dest_hsdata_ff_reg[9]\: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => dest_hsdata_en,
      D => src_hsdata_ff(9),
      Q => dest_hsdata_ff(9),
      R => '0'
    );
dest_req_ff_reg: unisim.vcomponents.FDRE
     port map (
      C => dest_clk,
      CE => '1',
      D => dest_req_nxt,
      Q => \^dest_req\,
      R => '0'
    );
\src_hsdata_ff[34]_i_1\: unisim.vcomponents.LUT1
    generic map(
      INIT => X"1"
    )
        port map (
      I0 => src_sendd_ff,
      O => p_0_in
    );
\src_hsdata_ff_reg[0]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(0),
      Q => src_hsdata_ff(0),
      R => '0'
    );
\src_hsdata_ff_reg[10]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(10),
      Q => src_hsdata_ff(10),
      R => '0'
    );
\src_hsdata_ff_reg[11]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(11),
      Q => src_hsdata_ff(11),
      R => '0'
    );
\src_hsdata_ff_reg[12]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(12),
      Q => src_hsdata_ff(12),
      R => '0'
    );
\src_hsdata_ff_reg[13]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(13),
      Q => src_hsdata_ff(13),
      R => '0'
    );
\src_hsdata_ff_reg[14]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(14),
      Q => src_hsdata_ff(14),
      R => '0'
    );
\src_hsdata_ff_reg[15]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(15),
      Q => src_hsdata_ff(15),
      R => '0'
    );
\src_hsdata_ff_reg[16]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(16),
      Q => src_hsdata_ff(16),
      R => '0'
    );
\src_hsdata_ff_reg[17]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(17),
      Q => src_hsdata_ff(17),
      R => '0'
    );
\src_hsdata_ff_reg[18]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(18),
      Q => src_hsdata_ff(18),
      R => '0'
    );
\src_hsdata_ff_reg[19]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(19),
      Q => src_hsdata_ff(19),
      R => '0'
    );
\src_hsdata_ff_reg[1]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(1),
      Q => src_hsdata_ff(1),
      R => '0'
    );
\src_hsdata_ff_reg[20]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(20),
      Q => src_hsdata_ff(20),
      R => '0'
    );
\src_hsdata_ff_reg[21]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(21),
      Q => src_hsdata_ff(21),
      R => '0'
    );
\src_hsdata_ff_reg[22]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(22),
      Q => src_hsdata_ff(22),
      R => '0'
    );
\src_hsdata_ff_reg[23]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(23),
      Q => src_hsdata_ff(23),
      R => '0'
    );
\src_hsdata_ff_reg[24]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(24),
      Q => src_hsdata_ff(24),
      R => '0'
    );
\src_hsdata_ff_reg[25]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(25),
      Q => src_hsdata_ff(25),
      R => '0'
    );
\src_hsdata_ff_reg[26]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(26),
      Q => src_hsdata_ff(26),
      R => '0'
    );
\src_hsdata_ff_reg[27]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(27),
      Q => src_hsdata_ff(27),
      R => '0'
    );
\src_hsdata_ff_reg[28]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(28),
      Q => src_hsdata_ff(28),
      R => '0'
    );
\src_hsdata_ff_reg[29]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(29),
      Q => src_hsdata_ff(29),
      R => '0'
    );
\src_hsdata_ff_reg[2]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(2),
      Q => src_hsdata_ff(2),
      R => '0'
    );
\src_hsdata_ff_reg[30]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(30),
      Q => src_hsdata_ff(30),
      R => '0'
    );
\src_hsdata_ff_reg[31]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(31),
      Q => src_hsdata_ff(31),
      R => '0'
    );
\src_hsdata_ff_reg[32]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(32),
      Q => src_hsdata_ff(32),
      R => '0'
    );
\src_hsdata_ff_reg[33]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(33),
      Q => src_hsdata_ff(33),
      R => '0'
    );
\src_hsdata_ff_reg[34]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(34),
      Q => src_hsdata_ff(34),
      R => '0'
    );
\src_hsdata_ff_reg[3]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(3),
      Q => src_hsdata_ff(3),
      R => '0'
    );
\src_hsdata_ff_reg[4]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(4),
      Q => src_hsdata_ff(4),
      R => '0'
    );
\src_hsdata_ff_reg[5]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(5),
      Q => src_hsdata_ff(5),
      R => '0'
    );
\src_hsdata_ff_reg[6]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(6),
      Q => src_hsdata_ff(6),
      R => '0'
    );
\src_hsdata_ff_reg[7]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(7),
      Q => src_hsdata_ff(7),
      R => '0'
    );
\src_hsdata_ff_reg[8]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(8),
      Q => src_hsdata_ff(8),
      R => '0'
    );
\src_hsdata_ff_reg[9]\: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => p_0_in,
      D => src_in(9),
      Q => src_hsdata_ff(9),
      R => '0'
    );
src_sendd_ff_reg: unisim.vcomponents.FDRE
     port map (
      C => src_clk,
      CE => '1',
      D => src_send,
      Q => src_sendd_ff,
      R => '0'
    );
xpm_cdc_single_dest2src_inst: entity work.\axi_clock_converter_oclnew_xpm_cdc_single__5\
     port map (
      dest_clk => src_clk,
      dest_out => src_rcv,
      src_clk => dest_clk,
      src_in => dest_ack
    );
xpm_cdc_single_src2dest_inst: entity work.\axi_clock_converter_oclnew_xpm_cdc_single__4\
     port map (
      dest_clk => dest_clk,
      dest_out => dest_req_nxt,
      src_clk => src_clk,
      src_in => src_sendd_ff
    );
end STRUCTURE;
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
entity axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_lite_async is
  port (
    dest_out : out STD_LOGIC_VECTOR ( 34 downto 0 );
    s_axi_awready : out STD_LOGIC;
    m_axi_awvalid : out STD_LOGIC;
    CLK : in STD_LOGIC;
    src_in : in STD_LOGIC_VECTOR ( 34 downto 0 );
    m_axi_aclk : in STD_LOGIC;
    SR : in STD_LOGIC_VECTOR ( 0 to 0 );
    m_axi_aresetn : in STD_LOGIC_VECTOR ( 0 to 0 );
    s_axi_awvalid : in STD_LOGIC;
    m_axi_awready : in STD_LOGIC
  );
  attribute ORIG_REF_NAME : string;
  attribute ORIG_REF_NAME of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_lite_async : entity is "axi_clock_converter_v2_1_11_lite_async";
end axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_lite_async;

architecture STRUCTURE of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_lite_async is
  signal \/FSM_sequential_dest_state[0]_i_1_n_0\ : STD_LOGIC;
  signal \/FSM_sequential_dest_state[1]_i_1_n_0\ : STD_LOGIC;
  signal \/FSM_sequential_src_state[0]_i_1_n_0\ : STD_LOGIC;
  signal \/FSM_sequential_src_state[1]_i_1_n_0\ : STD_LOGIC;
  signal dest_ack_i_1_n_0 : STD_LOGIC;
  signal dest_ack_reg_n_0 : STD_LOGIC;
  signal dest_req : STD_LOGIC;
  signal \dest_state__0\ : STD_LOGIC_VECTOR ( 1 downto 0 );
  attribute RTL_KEEP : string;
  attribute RTL_KEEP of \dest_state__0\ : signal is "yes";
  signal dest_state_n_0 : STD_LOGIC;
  signal \^m_axi_awvalid\ : STD_LOGIC;
  signal m_valid_i_i_2_n_0 : STD_LOGIC;
  signal \^s_axi_awready\ : STD_LOGIC;
  signal s_ready_i_i_2_n_0 : STD_LOGIC;
  signal src_rcv : STD_LOGIC;
  signal src_send_i_1_n_0 : STD_LOGIC;
  signal src_send_reg_n_0 : STD_LOGIC;
  signal \src_state__0\ : STD_LOGIC_VECTOR ( 1 downto 0 );
  attribute RTL_KEEP of \src_state__0\ : signal is "yes";
  signal src_state_n_0 : STD_LOGIC;
  attribute KEEP : string;
  attribute KEEP of \FSM_sequential_dest_state_reg[0]\ : label is "yes";
  attribute KEEP of \FSM_sequential_dest_state_reg[1]\ : label is "yes";
  attribute KEEP of \FSM_sequential_src_state_reg[0]\ : label is "yes";
  attribute KEEP of \FSM_sequential_src_state_reg[1]\ : label is "yes";
  attribute DEST_EXT_HSK : integer;
  attribute DEST_EXT_HSK of handshake : label is 1;
  attribute DEST_SYNC_FF : integer;
  attribute DEST_SYNC_FF of handshake : label is 2;
  attribute SIM_ASSERT_CHK : integer;
  attribute SIM_ASSERT_CHK of handshake : label is 0;
  attribute SRC_SYNC_FF : integer;
  attribute SRC_SYNC_FF of handshake : label is 2;
  attribute VERSION : integer;
  attribute VERSION of handshake : label is 0;
  attribute WIDTH : integer;
  attribute WIDTH of handshake : label is 35;
  attribute XPM_CDC : string;
  attribute XPM_CDC of handshake : label is "HANDSHAKE";
  attribute XPM_MODULE : string;
  attribute XPM_MODULE of handshake : label is "TRUE";
begin
  m_axi_awvalid <= \^m_axi_awvalid\;
  s_axi_awready <= \^s_axi_awready\;
\/FSM_sequential_dest_state[0]_i_1\: unisim.vcomponents.LUT3
    generic map(
      INIT => X"45"
    )
        port map (
      I0 => \dest_state__0\(0),
      I1 => dest_req,
      I2 => \dest_state__0\(1),
      O => \/FSM_sequential_dest_state[0]_i_1_n_0\
    );
\/FSM_sequential_dest_state[1]_i_1\: unisim.vcomponents.LUT3
    generic map(
      INIT => X"4A"
    )
        port map (
      I0 => \dest_state__0\(0),
      I1 => dest_req,
      I2 => \dest_state__0\(1),
      O => \/FSM_sequential_dest_state[1]_i_1_n_0\
    );
\/FSM_sequential_src_state[0]_i_1\: unisim.vcomponents.LUT4
    generic map(
      INIT => X"5455"
    )
        port map (
      I0 => \src_state__0\(0),
      I1 => s_axi_awvalid,
      I2 => src_rcv,
      I3 => \src_state__0\(1),
      O => \/FSM_sequential_src_state[0]_i_1_n_0\
    );
\/FSM_sequential_src_state[1]_i_1\: unisim.vcomponents.LUT3
    generic map(
      INIT => X"4A"
    )
        port map (
      I0 => \src_state__0\(0),
      I1 => src_rcv,
      I2 => \src_state__0\(1),
      O => \/FSM_sequential_src_state[1]_i_1_n_0\
    );
\FSM_sequential_dest_state_reg[0]\: unisim.vcomponents.FDRE
     port map (
      C => m_axi_aclk,
      CE => dest_state_n_0,
      D => \/FSM_sequential_dest_state[0]_i_1_n_0\,
      Q => \dest_state__0\(0),
      R => m_axi_aresetn(0)
    );
\FSM_sequential_dest_state_reg[1]\: unisim.vcomponents.FDRE
     port map (
      C => m_axi_aclk,
      CE => dest_state_n_0,
      D => \/FSM_sequential_dest_state[1]_i_1_n_0\,
      Q => \dest_state__0\(1),
      R => m_axi_aresetn(0)
    );
\FSM_sequential_src_state_reg[0]\: unisim.vcomponents.FDRE
     port map (
      C => CLK,
      CE => src_state_n_0,
      D => \/FSM_sequential_src_state[0]_i_1_n_0\,
      Q => \src_state__0\(0),
      R => SR(0)
    );
\FSM_sequential_src_state_reg[1]\: unisim.vcomponents.FDRE
     port map (
      C => CLK,
      CE => src_state_n_0,
      D => \/FSM_sequential_src_state[1]_i_1_n_0\,
      Q => \src_state__0\(1),
      R => SR(0)
    );
dest_ack_i_1: unisim.vcomponents.LUT6
    generic map(
      INIT => X"55FF550040004000"
    )
        port map (
      I0 => \dest_state__0\(1),
      I1 => \^m_axi_awvalid\,
      I2 => m_axi_awready,
      I3 => \dest_state__0\(0),
      I4 => dest_req,
      I5 => dest_ack_reg_n_0,
      O => dest_ack_i_1_n_0
    );
dest_ack_reg: unisim.vcomponents.FDRE
    generic map(
      INIT => '0'
    )
        port map (
      C => m_axi_aclk,
      CE => '1',
      D => dest_ack_i_1_n_0,
      Q => dest_ack_reg_n_0,
      R => m_axi_aresetn(0)
    );
dest_state: unisim.vcomponents.LUT5
    generic map(
      INIT => X"F6A6A6A6"
    )
        port map (
      I0 => \dest_state__0\(1),
      I1 => dest_req,
      I2 => \dest_state__0\(0),
      I3 => m_axi_awready,
      I4 => \^m_axi_awvalid\,
      O => dest_state_n_0
    );
handshake: entity work.axi_clock_converter_oclnew_xpm_cdc_handshake
     port map (
      dest_ack => dest_ack_reg_n_0,
      dest_clk => m_axi_aclk,
      dest_out(34 downto 0) => dest_out(34 downto 0),
      dest_req => dest_req,
      src_clk => CLK,
      src_in(34 downto 0) => src_in(34 downto 0),
      src_rcv => src_rcv,
      src_send => src_send_reg_n_0
    );
m_valid_i_i_2: unisim.vcomponents.LUT5
    generic map(
      INIT => X"0030F0AA"
    )
        port map (
      I0 => dest_req,
      I1 => m_axi_awready,
      I2 => \^m_axi_awvalid\,
      I3 => \dest_state__0\(1),
      I4 => \dest_state__0\(0),
      O => m_valid_i_i_2_n_0
    );
m_valid_i_reg: unisim.vcomponents.FDRE
    generic map(
      INIT => '0'
    )
        port map (
      C => m_axi_aclk,
      CE => '1',
      D => m_valid_i_i_2_n_0,
      Q => \^m_axi_awvalid\,
      R => m_axi_aresetn(0)
    );
s_ready_i_i_2: unisim.vcomponents.LUT4
    generic map(
      INIT => X"5540"
    )
        port map (
      I0 => \src_state__0\(1),
      I1 => src_rcv,
      I2 => \src_state__0\(0),
      I3 => \^s_axi_awready\,
      O => s_ready_i_i_2_n_0
    );
s_ready_i_reg: unisim.vcomponents.FDRE
    generic map(
      INIT => '0'
    )
        port map (
      C => CLK,
      CE => '1',
      D => s_ready_i_i_2_n_0,
      Q => \^s_axi_awready\,
      R => SR(0)
    );
src_send_i_1: unisim.vcomponents.LUT5
    generic map(
      INIT => X"0F5F040C"
    )
        port map (
      I0 => \src_state__0\(1),
      I1 => s_axi_awvalid,
      I2 => \src_state__0\(0),
      I3 => src_rcv,
      I4 => src_send_reg_n_0,
      O => src_send_i_1_n_0
    );
src_send_reg: unisim.vcomponents.FDRE
    generic map(
      INIT => '0'
    )
        port map (
      C => CLK,
      CE => '1',
      D => src_send_i_1_n_0,
      Q => src_send_reg_n_0,
      R => SR(0)
    );
src_state: unisim.vcomponents.LUT4
    generic map(
      INIT => X"F4AE"
    )
        port map (
      I0 => \src_state__0\(1),
      I1 => s_axi_awvalid,
      I2 => \src_state__0\(0),
      I3 => src_rcv,
      O => src_state_n_0
    );
end STRUCTURE;
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
entity \axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_lite_async__parameterized0\ is
  port (
    dest_out : out STD_LOGIC_VECTOR ( 35 downto 0 );
    s_axi_wready : out STD_LOGIC;
    m_axi_wvalid : out STD_LOGIC;
    \out\ : in STD_LOGIC;
    src_in : in STD_LOGIC_VECTOR ( 35 downto 0 );
    m_axi_aclk : in STD_LOGIC;
    s_axi_aresetn : in STD_LOGIC_VECTOR ( 0 to 0 );
    SR : in STD_LOGIC_VECTOR ( 0 to 0 );
    s_axi_wvalid : in STD_LOGIC;
    m_axi_wready : in STD_LOGIC
  );
  attribute ORIG_REF_NAME : string;
  attribute ORIG_REF_NAME of \axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_lite_async__parameterized0\ : entity is "axi_clock_converter_v2_1_11_lite_async";
end \axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_lite_async__parameterized0\;

architecture STRUCTURE of \axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_lite_async__parameterized0\ is
  signal \/FSM_sequential_dest_state[0]_i_1_n_0\ : STD_LOGIC;
  signal \/FSM_sequential_dest_state[1]_i_1_n_0\ : STD_LOGIC;
  signal \/FSM_sequential_src_state[0]_i_1_n_0\ : STD_LOGIC;
  signal \/FSM_sequential_src_state[1]_i_1_n_0\ : STD_LOGIC;
  signal \dest_ack_i_1__1_n_0\ : STD_LOGIC;
  signal dest_ack_reg_n_0 : STD_LOGIC;
  signal dest_req : STD_LOGIC;
  signal \dest_state__0\ : STD_LOGIC_VECTOR ( 1 downto 0 );
  attribute RTL_KEEP : string;
  attribute RTL_KEEP of \dest_state__0\ : signal is "yes";
  signal dest_state_n_0 : STD_LOGIC;
  signal \^m_axi_wvalid\ : STD_LOGIC;
  signal \m_valid_i_i_1__0_n_0\ : STD_LOGIC;
  signal \^s_axi_wready\ : STD_LOGIC;
  signal \s_ready_i_i_1__0_n_0\ : STD_LOGIC;
  signal src_rcv : STD_LOGIC;
  signal \src_send_i_1__1_n_0\ : STD_LOGIC;
  signal src_send_reg_n_0 : STD_LOGIC;
  signal \src_state__0\ : STD_LOGIC_VECTOR ( 1 downto 0 );
  attribute RTL_KEEP of \src_state__0\ : signal is "yes";
  signal src_state_n_0 : STD_LOGIC;
  attribute KEEP : string;
  attribute KEEP of \FSM_sequential_dest_state_reg[0]\ : label is "yes";
  attribute KEEP of \FSM_sequential_dest_state_reg[1]\ : label is "yes";
  attribute KEEP of \FSM_sequential_src_state_reg[0]\ : label is "yes";
  attribute KEEP of \FSM_sequential_src_state_reg[1]\ : label is "yes";
  attribute DEST_EXT_HSK : integer;
  attribute DEST_EXT_HSK of handshake : label is 1;
  attribute DEST_SYNC_FF : integer;
  attribute DEST_SYNC_FF of handshake : label is 2;
  attribute SIM_ASSERT_CHK : integer;
  attribute SIM_ASSERT_CHK of handshake : label is 0;
  attribute SRC_SYNC_FF : integer;
  attribute SRC_SYNC_FF of handshake : label is 2;
  attribute VERSION : integer;
  attribute VERSION of handshake : label is 0;
  attribute WIDTH : integer;
  attribute WIDTH of handshake : label is 36;
  attribute XPM_CDC : string;
  attribute XPM_CDC of handshake : label is "HANDSHAKE";
  attribute XPM_MODULE : string;
  attribute XPM_MODULE of handshake : label is "TRUE";
begin
  m_axi_wvalid <= \^m_axi_wvalid\;
  s_axi_wready <= \^s_axi_wready\;
\/FSM_sequential_dest_state[0]_i_1\: unisim.vcomponents.LUT3
    generic map(
      INIT => X"45"
    )
        port map (
      I0 => \dest_state__0\(0),
      I1 => dest_req,
      I2 => \dest_state__0\(1),
      O => \/FSM_sequential_dest_state[0]_i_1_n_0\
    );
\/FSM_sequential_dest_state[1]_i_1\: unisim.vcomponents.LUT3
    generic map(
      INIT => X"4A"
    )
        port map (
      I0 => \dest_state__0\(0),
      I1 => dest_req,
      I2 => \dest_state__0\(1),
      O => \/FSM_sequential_dest_state[1]_i_1_n_0\
    );
\/FSM_sequential_src_state[0]_i_1\: unisim.vcomponents.LUT4
    generic map(
      INIT => X"5455"
    )
        port map (
      I0 => \src_state__0\(0),
      I1 => s_axi_wvalid,
      I2 => src_rcv,
      I3 => \src_state__0\(1),
      O => \/FSM_sequential_src_state[0]_i_1_n_0\
    );
\/FSM_sequential_src_state[1]_i_1\: unisim.vcomponents.LUT3
    generic map(
      INIT => X"4A"
    )
        port map (
      I0 => \src_state__0\(0),
      I1 => src_rcv,
      I2 => \src_state__0\(1),
      O => \/FSM_sequential_src_state[1]_i_1_n_0\
    );
\FSM_sequential_dest_state_reg[0]\: unisim.vcomponents.FDRE
     port map (
      C => m_axi_aclk,
      CE => dest_state_n_0,
      D => \/FSM_sequential_dest_state[0]_i_1_n_0\,
      Q => \dest_state__0\(0),
      R => SR(0)
    );
\FSM_sequential_dest_state_reg[1]\: unisim.vcomponents.FDRE
     port map (
      C => m_axi_aclk,
      CE => dest_state_n_0,
      D => \/FSM_sequential_dest_state[1]_i_1_n_0\,
      Q => \dest_state__0\(1),
      R => SR(0)
    );
\FSM_sequential_src_state_reg[0]\: unisim.vcomponents.FDRE
     port map (
      C => \out\,
      CE => src_state_n_0,
      D => \/FSM_sequential_src_state[0]_i_1_n_0\,
      Q => \src_state__0\(0),
      R => s_axi_aresetn(0)
    );
\FSM_sequential_src_state_reg[1]\: unisim.vcomponents.FDRE
     port map (
      C => \out\,
      CE => src_state_n_0,
      D => \/FSM_sequential_src_state[1]_i_1_n_0\,
      Q => \src_state__0\(1),
      R => s_axi_aresetn(0)
    );
\dest_ack_i_1__1\: unisim.vcomponents.LUT6
    generic map(
      INIT => X"55FF550040004000"
    )
        port map (
      I0 => \dest_state__0\(1),
      I1 => \^m_axi_wvalid\,
      I2 => m_axi_wready,
      I3 => \dest_state__0\(0),
      I4 => dest_req,
      I5 => dest_ack_reg_n_0,
      O => \dest_ack_i_1__1_n_0\
    );
dest_ack_reg: unisim.vcomponents.FDRE
    generic map(
      INIT => '0'
    )
        port map (
      C => m_axi_aclk,
      CE => '1',
      D => \dest_ack_i_1__1_n_0\,
      Q => dest_ack_reg_n_0,
      R => SR(0)
    );
dest_state: unisim.vcomponents.LUT5
    generic map(
      INIT => X"F6A6A6A6"
    )
        port map (
      I0 => \dest_state__0\(1),
      I1 => dest_req,
      I2 => \dest_state__0\(0),
      I3 => m_axi_wready,
      I4 => \^m_axi_wvalid\,
      O => dest_state_n_0
    );
handshake: entity work.\axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized0\
     port map (
      dest_ack => dest_ack_reg_n_0,
      dest_clk => m_axi_aclk,
      dest_out(35 downto 0) => dest_out(35 downto 0),
      dest_req => dest_req,
      src_clk => \out\,
      src_in(35 downto 0) => src_in(35 downto 0),
      src_rcv => src_rcv,
      src_send => src_send_reg_n_0
    );
\m_valid_i_i_1__0\: unisim.vcomponents.LUT5
    generic map(
      INIT => X"0030F0AA"
    )
        port map (
      I0 => dest_req,
      I1 => m_axi_wready,
      I2 => \^m_axi_wvalid\,
      I3 => \dest_state__0\(1),
      I4 => \dest_state__0\(0),
      O => \m_valid_i_i_1__0_n_0\
    );
m_valid_i_reg: unisim.vcomponents.FDRE
    generic map(
      INIT => '0'
    )
        port map (
      C => m_axi_aclk,
      CE => '1',
      D => \m_valid_i_i_1__0_n_0\,
      Q => \^m_axi_wvalid\,
      R => SR(0)
    );
\s_ready_i_i_1__0\: unisim.vcomponents.LUT4
    generic map(
      INIT => X"5540"
    )
        port map (
      I0 => \src_state__0\(1),
      I1 => src_rcv,
      I2 => \src_state__0\(0),
      I3 => \^s_axi_wready\,
      O => \s_ready_i_i_1__0_n_0\
    );
s_ready_i_reg: unisim.vcomponents.FDRE
    generic map(
      INIT => '0'
    )
        port map (
      C => \out\,
      CE => '1',
      D => \s_ready_i_i_1__0_n_0\,
      Q => \^s_axi_wready\,
      R => s_axi_aresetn(0)
    );
\src_send_i_1__1\: unisim.vcomponents.LUT5
    generic map(
      INIT => X"0F5F040C"
    )
        port map (
      I0 => \src_state__0\(1),
      I1 => s_axi_wvalid,
      I2 => \src_state__0\(0),
      I3 => src_rcv,
      I4 => src_send_reg_n_0,
      O => \src_send_i_1__1_n_0\
    );
src_send_reg: unisim.vcomponents.FDRE
    generic map(
      INIT => '0'
    )
        port map (
      C => \out\,
      CE => '1',
      D => \src_send_i_1__1_n_0\,
      Q => src_send_reg_n_0,
      R => s_axi_aresetn(0)
    );
src_state: unisim.vcomponents.LUT4
    generic map(
      INIT => X"F4AE"
    )
        port map (
      I0 => \src_state__0\(1),
      I1 => s_axi_wvalid,
      I2 => \src_state__0\(0),
      I3 => src_rcv,
      O => src_state_n_0
    );
end STRUCTURE;
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
entity \axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_lite_async__parameterized1\ is
  port (
    s_axi_bresp : out STD_LOGIC_VECTOR ( 1 downto 0 );
    m_axi_bready : out STD_LOGIC;
    s_axi_bvalid : out STD_LOGIC;
    CLK : in STD_LOGIC;
    m_axi_bresp : in STD_LOGIC_VECTOR ( 1 downto 0 );
    s_axi_aclk : in STD_LOGIC;
    SR : in STD_LOGIC_VECTOR ( 0 to 0 );
    s_axi_aresetn : in STD_LOGIC_VECTOR ( 0 to 0 );
    m_axi_bvalid : in STD_LOGIC;
    s_axi_bready : in STD_LOGIC
  );
  attribute ORIG_REF_NAME : string;
  attribute ORIG_REF_NAME of \axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_lite_async__parameterized1\ : entity is "axi_clock_converter_v2_1_11_lite_async";
end \axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_lite_async__parameterized1\;

architecture STRUCTURE of \axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_lite_async__parameterized1\ is
  signal \/FSM_sequential_dest_state[0]_i_1_n_0\ : STD_LOGIC;
  signal \/FSM_sequential_dest_state[1]_i_1_n_0\ : STD_LOGIC;
  signal \/FSM_sequential_src_state[0]_i_1_n_0\ : STD_LOGIC;
  signal \/FSM_sequential_src_state[1]_i_1_n_0\ : STD_LOGIC;
  signal \dest_ack_i_1__2_n_0\ : STD_LOGIC;
  signal dest_ack_reg_n_0 : STD_LOGIC;
  signal dest_req : STD_LOGIC;
  signal \dest_state__0\ : STD_LOGIC_VECTOR ( 1 downto 0 );
  attribute RTL_KEEP : string;
  attribute RTL_KEEP of \dest_state__0\ : signal is "yes";
  signal dest_state_n_0 : STD_LOGIC;
  signal \^m_axi_bready\ : STD_LOGIC;
  signal \m_valid_i_i_1__1_n_0\ : STD_LOGIC;
  signal \^s_axi_bvalid\ : STD_LOGIC;
  signal \s_ready_i_i_1__1_n_0\ : STD_LOGIC;
  signal src_rcv : STD_LOGIC;
  signal \src_send_i_1__2_n_0\ : STD_LOGIC;
  signal src_send_reg_n_0 : STD_LOGIC;
  signal \src_state__0\ : STD_LOGIC_VECTOR ( 1 downto 0 );
  attribute RTL_KEEP of \src_state__0\ : signal is "yes";
  signal src_state_n_0 : STD_LOGIC;
  attribute KEEP : string;
  attribute KEEP of \FSM_sequential_dest_state_reg[0]\ : label is "yes";
  attribute KEEP of \FSM_sequential_dest_state_reg[1]\ : label is "yes";
  attribute KEEP of \FSM_sequential_src_state_reg[0]\ : label is "yes";
  attribute KEEP of \FSM_sequential_src_state_reg[1]\ : label is "yes";
  attribute DEST_EXT_HSK : integer;
  attribute DEST_EXT_HSK of handshake : label is 1;
  attribute DEST_SYNC_FF : integer;
  attribute DEST_SYNC_FF of handshake : label is 2;
  attribute SIM_ASSERT_CHK : integer;
  attribute SIM_ASSERT_CHK of handshake : label is 0;
  attribute SRC_SYNC_FF : integer;
  attribute SRC_SYNC_FF of handshake : label is 2;
  attribute VERSION : integer;
  attribute VERSION of handshake : label is 0;
  attribute WIDTH : integer;
  attribute WIDTH of handshake : label is 2;
  attribute XPM_CDC : string;
  attribute XPM_CDC of handshake : label is "HANDSHAKE";
  attribute XPM_MODULE : string;
  attribute XPM_MODULE of handshake : label is "TRUE";
begin
  m_axi_bready <= \^m_axi_bready\;
  s_axi_bvalid <= \^s_axi_bvalid\;
\/FSM_sequential_dest_state[0]_i_1\: unisim.vcomponents.LUT3
    generic map(
      INIT => X"45"
    )
        port map (
      I0 => \dest_state__0\(0),
      I1 => dest_req,
      I2 => \dest_state__0\(1),
      O => \/FSM_sequential_dest_state[0]_i_1_n_0\
    );
\/FSM_sequential_dest_state[1]_i_1\: unisim.vcomponents.LUT3
    generic map(
      INIT => X"4A"
    )
        port map (
      I0 => \dest_state__0\(0),
      I1 => dest_req,
      I2 => \dest_state__0\(1),
      O => \/FSM_sequential_dest_state[1]_i_1_n_0\
    );
\/FSM_sequential_src_state[0]_i_1\: unisim.vcomponents.LUT4
    generic map(
      INIT => X"5455"
    )
        port map (
      I0 => \src_state__0\(0),
      I1 => m_axi_bvalid,
      I2 => src_rcv,
      I3 => \src_state__0\(1),
      O => \/FSM_sequential_src_state[0]_i_1_n_0\
    );
\/FSM_sequential_src_state[1]_i_1\: unisim.vcomponents.LUT3
    generic map(
      INIT => X"4A"
    )
        port map (
      I0 => \src_state__0\(0),
      I1 => src_rcv,
      I2 => \src_state__0\(1),
      O => \/FSM_sequential_src_state[1]_i_1_n_0\
    );
\FSM_sequential_dest_state_reg[0]\: unisim.vcomponents.FDRE
     port map (
      C => s_axi_aclk,
      CE => dest_state_n_0,
      D => \/FSM_sequential_dest_state[0]_i_1_n_0\,
      Q => \dest_state__0\(0),
      R => s_axi_aresetn(0)
    );
\FSM_sequential_dest_state_reg[1]\: unisim.vcomponents.FDRE
     port map (
      C => s_axi_aclk,
      CE => dest_state_n_0,
      D => \/FSM_sequential_dest_state[1]_i_1_n_0\,
      Q => \dest_state__0\(1),
      R => s_axi_aresetn(0)
    );
\FSM_sequential_src_state_reg[0]\: unisim.vcomponents.FDRE
     port map (
      C => CLK,
      CE => src_state_n_0,
      D => \/FSM_sequential_src_state[0]_i_1_n_0\,
      Q => \src_state__0\(0),
      R => SR(0)
    );
\FSM_sequential_src_state_reg[1]\: unisim.vcomponents.FDRE
     port map (
      C => CLK,
      CE => src_state_n_0,
      D => \/FSM_sequential_src_state[1]_i_1_n_0\,
      Q => \src_state__0\(1),
      R => SR(0)
    );
\dest_ack_i_1__2\: unisim.vcomponents.LUT6
    generic map(
      INIT => X"55FF550040004000"
    )
        port map (
      I0 => \dest_state__0\(1),
      I1 => \^s_axi_bvalid\,
      I2 => s_axi_bready,
      I3 => \dest_state__0\(0),
      I4 => dest_req,
      I5 => dest_ack_reg_n_0,
      O => \dest_ack_i_1__2_n_0\
    );
dest_ack_reg: unisim.vcomponents.FDRE
    generic map(
      INIT => '0'
    )
        port map (
      C => s_axi_aclk,
      CE => '1',
      D => \dest_ack_i_1__2_n_0\,
      Q => dest_ack_reg_n_0,
      R => s_axi_aresetn(0)
    );
dest_state: unisim.vcomponents.LUT5
    generic map(
      INIT => X"F6A6A6A6"
    )
        port map (
      I0 => \dest_state__0\(1),
      I1 => dest_req,
      I2 => \dest_state__0\(0),
      I3 => s_axi_bready,
      I4 => \^s_axi_bvalid\,
      O => dest_state_n_0
    );
handshake: entity work.\axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized1\
     port map (
      dest_ack => dest_ack_reg_n_0,
      dest_clk => s_axi_aclk,
      dest_out(1 downto 0) => s_axi_bresp(1 downto 0),
      dest_req => dest_req,
      src_clk => CLK,
      src_in(1 downto 0) => m_axi_bresp(1 downto 0),
      src_rcv => src_rcv,
      src_send => src_send_reg_n_0
    );
\m_valid_i_i_1__1\: unisim.vcomponents.LUT5
    generic map(
      INIT => X"0030F0AA"
    )
        port map (
      I0 => dest_req,
      I1 => s_axi_bready,
      I2 => \^s_axi_bvalid\,
      I3 => \dest_state__0\(1),
      I4 => \dest_state__0\(0),
      O => \m_valid_i_i_1__1_n_0\
    );
m_valid_i_reg: unisim.vcomponents.FDRE
    generic map(
      INIT => '0'
    )
        port map (
      C => s_axi_aclk,
      CE => '1',
      D => \m_valid_i_i_1__1_n_0\,
      Q => \^s_axi_bvalid\,
      R => s_axi_aresetn(0)
    );
\s_ready_i_i_1__1\: unisim.vcomponents.LUT4
    generic map(
      INIT => X"5540"
    )
        port map (
      I0 => \src_state__0\(1),
      I1 => src_rcv,
      I2 => \src_state__0\(0),
      I3 => \^m_axi_bready\,
      O => \s_ready_i_i_1__1_n_0\
    );
s_ready_i_reg: unisim.vcomponents.FDRE
    generic map(
      INIT => '0'
    )
        port map (
      C => CLK,
      CE => '1',
      D => \s_ready_i_i_1__1_n_0\,
      Q => \^m_axi_bready\,
      R => SR(0)
    );
\src_send_i_1__2\: unisim.vcomponents.LUT5
    generic map(
      INIT => X"0F5F040C"
    )
        port map (
      I0 => \src_state__0\(1),
      I1 => m_axi_bvalid,
      I2 => \src_state__0\(0),
      I3 => src_rcv,
      I4 => src_send_reg_n_0,
      O => \src_send_i_1__2_n_0\
    );
src_send_reg: unisim.vcomponents.FDRE
    generic map(
      INIT => '0'
    )
        port map (
      C => CLK,
      CE => '1',
      D => \src_send_i_1__2_n_0\,
      Q => src_send_reg_n_0,
      R => SR(0)
    );
src_state: unisim.vcomponents.LUT4
    generic map(
      INIT => X"F4AE"
    )
        port map (
      I0 => \src_state__0\(1),
      I1 => m_axi_bvalid,
      I2 => \src_state__0\(0),
      I3 => src_rcv,
      O => src_state_n_0
    );
end STRUCTURE;
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
entity \axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_lite_async__parameterized2\ is
  port (
    dest_out : out STD_LOGIC_VECTOR ( 33 downto 0 );
    m_axi_rready : out STD_LOGIC;
    SR : out STD_LOGIC_VECTOR ( 0 to 0 );
    s_axi_rvalid : out STD_LOGIC;
    dest_ack_reg_0 : out STD_LOGIC_VECTOR ( 0 to 0 );
    \out\ : in STD_LOGIC;
    src_in : in STD_LOGIC_VECTOR ( 33 downto 0 );
    s_axi_aclk : in STD_LOGIC;
    m_axi_rvalid : in STD_LOGIC;
    s_axi_rready : in STD_LOGIC;
    s_axi_aresetn : in STD_LOGIC;
    m_axi_aresetn : in STD_LOGIC
  );
  attribute ORIG_REF_NAME : string;
  attribute ORIG_REF_NAME of \axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_lite_async__parameterized2\ : entity is "axi_clock_converter_v2_1_11_lite_async";
end \axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_lite_async__parameterized2\;

architecture STRUCTURE of \axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_lite_async__parameterized2\ is
  signal \/FSM_sequential_dest_state[0]_i_1_n_0\ : STD_LOGIC;
  signal \/FSM_sequential_dest_state[1]_i_1_n_0\ : STD_LOGIC;
  signal \/FSM_sequential_src_state[0]_i_1_n_0\ : STD_LOGIC;
  signal \/FSM_sequential_src_state[1]_i_1_n_0\ : STD_LOGIC;
  signal \^sr\ : STD_LOGIC_VECTOR ( 0 to 0 );
  signal \dest_ack_i_1__3_n_0\ : STD_LOGIC;
  signal \^dest_ack_reg_0\ : STD_LOGIC_VECTOR ( 0 to 0 );
  signal dest_ack_reg_n_0 : STD_LOGIC;
  signal dest_req : STD_LOGIC;
  signal \dest_state__0\ : STD_LOGIC_VECTOR ( 1 downto 0 );
  attribute RTL_KEEP : string;
  attribute RTL_KEEP of \dest_state__0\ : signal is "yes";
  signal dest_state_n_0 : STD_LOGIC;
  signal \^m_axi_rready\ : STD_LOGIC;
  signal \m_valid_i_i_1__2_n_0\ : STD_LOGIC;
  signal \^s_axi_rvalid\ : STD_LOGIC;
  signal \s_ready_i_i_1__2_n_0\ : STD_LOGIC;
  signal src_rcv : STD_LOGIC;
  signal \src_send_i_1__3_n_0\ : STD_LOGIC;
  signal src_send_reg_n_0 : STD_LOGIC;
  signal \src_state__0\ : STD_LOGIC_VECTOR ( 1 downto 0 );
  attribute RTL_KEEP of \src_state__0\ : signal is "yes";
  signal src_state_n_0 : STD_LOGIC;
  attribute KEEP : string;
  attribute KEEP of \FSM_sequential_dest_state_reg[0]\ : label is "yes";
  attribute KEEP of \FSM_sequential_dest_state_reg[1]\ : label is "yes";
  attribute KEEP of \FSM_sequential_src_state_reg[0]\ : label is "yes";
  attribute KEEP of \FSM_sequential_src_state_reg[1]\ : label is "yes";
  attribute DEST_EXT_HSK : integer;
  attribute DEST_EXT_HSK of handshake : label is 1;
  attribute DEST_SYNC_FF : integer;
  attribute DEST_SYNC_FF of handshake : label is 2;
  attribute SIM_ASSERT_CHK : integer;
  attribute SIM_ASSERT_CHK of handshake : label is 0;
  attribute SRC_SYNC_FF : integer;
  attribute SRC_SYNC_FF of handshake : label is 2;
  attribute VERSION : integer;
  attribute VERSION of handshake : label is 0;
  attribute WIDTH : integer;
  attribute WIDTH of handshake : label is 34;
  attribute XPM_CDC : string;
  attribute XPM_CDC of handshake : label is "HANDSHAKE";
  attribute XPM_MODULE : string;
  attribute XPM_MODULE of handshake : label is "TRUE";
begin
  SR(0) <= \^sr\(0);
  dest_ack_reg_0(0) <= \^dest_ack_reg_0\(0);
  m_axi_rready <= \^m_axi_rready\;
  s_axi_rvalid <= \^s_axi_rvalid\;
\/FSM_sequential_dest_state[0]_i_1\: unisim.vcomponents.LUT3
    generic map(
      INIT => X"45"
    )
        port map (
      I0 => \dest_state__0\(0),
      I1 => dest_req,
      I2 => \dest_state__0\(1),
      O => \/FSM_sequential_dest_state[0]_i_1_n_0\
    );
\/FSM_sequential_dest_state[1]_i_1\: unisim.vcomponents.LUT3
    generic map(
      INIT => X"4A"
    )
        port map (
      I0 => \dest_state__0\(0),
      I1 => dest_req,
      I2 => \dest_state__0\(1),
      O => \/FSM_sequential_dest_state[1]_i_1_n_0\
    );
\/FSM_sequential_src_state[0]_i_1\: unisim.vcomponents.LUT4
    generic map(
      INIT => X"5455"
    )
        port map (
      I0 => \src_state__0\(0),
      I1 => m_axi_rvalid,
      I2 => src_rcv,
      I3 => \src_state__0\(1),
      O => \/FSM_sequential_src_state[0]_i_1_n_0\
    );
\/FSM_sequential_src_state[1]_i_1\: unisim.vcomponents.LUT3
    generic map(
      INIT => X"4A"
    )
        port map (
      I0 => \src_state__0\(0),
      I1 => src_rcv,
      I2 => \src_state__0\(1),
      O => \/FSM_sequential_src_state[1]_i_1_n_0\
    );
\FSM_sequential_dest_state_reg[0]\: unisim.vcomponents.FDRE
     port map (
      C => s_axi_aclk,
      CE => dest_state_n_0,
      D => \/FSM_sequential_dest_state[0]_i_1_n_0\,
      Q => \dest_state__0\(0),
      R => \^dest_ack_reg_0\(0)
    );
\FSM_sequential_dest_state_reg[1]\: unisim.vcomponents.FDRE
     port map (
      C => s_axi_aclk,
      CE => dest_state_n_0,
      D => \/FSM_sequential_dest_state[1]_i_1_n_0\,
      Q => \dest_state__0\(1),
      R => \^dest_ack_reg_0\(0)
    );
\FSM_sequential_src_state_reg[0]\: unisim.vcomponents.FDRE
     port map (
      C => \out\,
      CE => src_state_n_0,
      D => \/FSM_sequential_src_state[0]_i_1_n_0\,
      Q => \src_state__0\(0),
      R => \^sr\(0)
    );
\FSM_sequential_src_state_reg[1]\: unisim.vcomponents.FDRE
     port map (
      C => \out\,
      CE => src_state_n_0,
      D => \/FSM_sequential_src_state[1]_i_1_n_0\,
      Q => \src_state__0\(1),
      R => \^sr\(0)
    );
\dest_ack_i_1__3\: unisim.vcomponents.LUT6
    generic map(
      INIT => X"55FF550040004000"
    )
        port map (
      I0 => \dest_state__0\(1),
      I1 => \^s_axi_rvalid\,
      I2 => s_axi_rready,
      I3 => \dest_state__0\(0),
      I4 => dest_req,
      I5 => dest_ack_reg_n_0,
      O => \dest_ack_i_1__3_n_0\
    );
dest_ack_reg: unisim.vcomponents.FDRE
    generic map(
      INIT => '0'
    )
        port map (
      C => s_axi_aclk,
      CE => '1',
      D => \dest_ack_i_1__3_n_0\,
      Q => dest_ack_reg_n_0,
      R => \^dest_ack_reg_0\(0)
    );
dest_state: unisim.vcomponents.LUT5
    generic map(
      INIT => X"F6A6A6A6"
    )
        port map (
      I0 => \dest_state__0\(1),
      I1 => dest_req,
      I2 => \dest_state__0\(0),
      I3 => s_axi_rready,
      I4 => \^s_axi_rvalid\,
      O => dest_state_n_0
    );
handshake: entity work.\axi_clock_converter_oclnew_xpm_cdc_handshake__parameterized2\
     port map (
      dest_ack => dest_ack_reg_n_0,
      dest_clk => s_axi_aclk,
      dest_out(33 downto 0) => dest_out(33 downto 0),
      dest_req => dest_req,
      src_clk => \out\,
      src_in(33 downto 0) => src_in(33 downto 0),
      src_rcv => src_rcv,
      src_send => src_send_reg_n_0
    );
\m_valid_i_i_1__2\: unisim.vcomponents.LUT5
    generic map(
      INIT => X"0030F0AA"
    )
        port map (
      I0 => dest_req,
      I1 => s_axi_rready,
      I2 => \^s_axi_rvalid\,
      I3 => \dest_state__0\(1),
      I4 => \dest_state__0\(0),
      O => \m_valid_i_i_1__2_n_0\
    );
\m_valid_i_i_1__3\: unisim.vcomponents.LUT1
    generic map(
      INIT => X"1"
    )
        port map (
      I0 => m_axi_aresetn,
      O => \^sr\(0)
    );
m_valid_i_reg: unisim.vcomponents.FDRE
    generic map(
      INIT => '0'
    )
        port map (
      C => s_axi_aclk,
      CE => '1',
      D => \m_valid_i_i_1__2_n_0\,
      Q => \^s_axi_rvalid\,
      R => \^dest_ack_reg_0\(0)
    );
\s_ready_i_i_1__2\: unisim.vcomponents.LUT4
    generic map(
      INIT => X"5540"
    )
        port map (
      I0 => \src_state__0\(1),
      I1 => src_rcv,
      I2 => \src_state__0\(0),
      I3 => \^m_axi_rready\,
      O => \s_ready_i_i_1__2_n_0\
    );
\s_ready_i_i_1__3\: unisim.vcomponents.LUT1
    generic map(
      INIT => X"1"
    )
        port map (
      I0 => s_axi_aresetn,
      O => \^dest_ack_reg_0\(0)
    );
s_ready_i_reg: unisim.vcomponents.FDRE
    generic map(
      INIT => '0'
    )
        port map (
      C => \out\,
      CE => '1',
      D => \s_ready_i_i_1__2_n_0\,
      Q => \^m_axi_rready\,
      R => \^sr\(0)
    );
\src_send_i_1__3\: unisim.vcomponents.LUT5
    generic map(
      INIT => X"0F5F040C"
    )
        port map (
      I0 => \src_state__0\(1),
      I1 => m_axi_rvalid,
      I2 => \src_state__0\(0),
      I3 => src_rcv,
      I4 => src_send_reg_n_0,
      O => \src_send_i_1__3_n_0\
    );
src_send_reg: unisim.vcomponents.FDRE
    generic map(
      INIT => '0'
    )
        port map (
      C => \out\,
      CE => '1',
      D => \src_send_i_1__3_n_0\,
      Q => src_send_reg_n_0,
      R => \^sr\(0)
    );
src_state: unisim.vcomponents.LUT4
    generic map(
      INIT => X"F4AE"
    )
        port map (
      I0 => \src_state__0\(1),
      I1 => m_axi_rvalid,
      I2 => \src_state__0\(0),
      I3 => src_rcv,
      O => src_state_n_0
    );
end STRUCTURE;
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
entity \axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_lite_async__xdcDup__1\ is
  port (
    dest_out : out STD_LOGIC_VECTOR ( 34 downto 0 );
    s_axi_arready : out STD_LOGIC;
    m_axi_arvalid : out STD_LOGIC;
    CLK : in STD_LOGIC;
    src_in : in STD_LOGIC_VECTOR ( 34 downto 0 );
    m_axi_aclk : in STD_LOGIC;
    SR : in STD_LOGIC_VECTOR ( 0 to 0 );
    m_axi_aresetn : in STD_LOGIC_VECTOR ( 0 to 0 );
    s_axi_arvalid : in STD_LOGIC;
    m_axi_arready : in STD_LOGIC
  );
  attribute ORIG_REF_NAME : string;
  attribute ORIG_REF_NAME of \axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_lite_async__xdcDup__1\ : entity is "axi_clock_converter_v2_1_11_lite_async";
end \axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_lite_async__xdcDup__1\;

architecture STRUCTURE of \axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_lite_async__xdcDup__1\ is
  signal \/FSM_sequential_dest_state[0]_i_1_n_0\ : STD_LOGIC;
  signal \/FSM_sequential_dest_state[1]_i_1_n_0\ : STD_LOGIC;
  signal \/FSM_sequential_src_state[0]_i_1_n_0\ : STD_LOGIC;
  signal \/FSM_sequential_src_state[1]_i_1_n_0\ : STD_LOGIC;
  signal \dest_ack_i_1__0_n_0\ : STD_LOGIC;
  signal dest_ack_reg_n_0 : STD_LOGIC;
  signal dest_req : STD_LOGIC;
  signal \dest_state__0\ : STD_LOGIC_VECTOR ( 1 downto 0 );
  attribute RTL_KEEP : string;
  attribute RTL_KEEP of \dest_state__0\ : signal is "yes";
  signal dest_state_n_0 : STD_LOGIC;
  signal \^m_axi_arvalid\ : STD_LOGIC;
  signal m_valid_i_i_1_n_0 : STD_LOGIC;
  signal \^s_axi_arready\ : STD_LOGIC;
  signal s_ready_i_i_1_n_0 : STD_LOGIC;
  signal src_rcv : STD_LOGIC;
  signal \src_send_i_1__0_n_0\ : STD_LOGIC;
  signal src_send_reg_n_0 : STD_LOGIC;
  signal \src_state__0\ : STD_LOGIC_VECTOR ( 1 downto 0 );
  attribute RTL_KEEP of \src_state__0\ : signal is "yes";
  signal src_state_n_0 : STD_LOGIC;
  attribute KEEP : string;
  attribute KEEP of \FSM_sequential_dest_state_reg[0]\ : label is "yes";
  attribute KEEP of \FSM_sequential_dest_state_reg[1]\ : label is "yes";
  attribute KEEP of \FSM_sequential_src_state_reg[0]\ : label is "yes";
  attribute KEEP of \FSM_sequential_src_state_reg[1]\ : label is "yes";
  attribute DEST_EXT_HSK : integer;
  attribute DEST_EXT_HSK of handshake : label is 1;
  attribute DEST_SYNC_FF : integer;
  attribute DEST_SYNC_FF of handshake : label is 2;
  attribute SIM_ASSERT_CHK : integer;
  attribute SIM_ASSERT_CHK of handshake : label is 0;
  attribute SRC_SYNC_FF : integer;
  attribute SRC_SYNC_FF of handshake : label is 2;
  attribute VERSION : integer;
  attribute VERSION of handshake : label is 0;
  attribute WIDTH : integer;
  attribute WIDTH of handshake : label is 35;
  attribute XPM_CDC : string;
  attribute XPM_CDC of handshake : label is "HANDSHAKE";
  attribute XPM_MODULE : string;
  attribute XPM_MODULE of handshake : label is "TRUE";
begin
  m_axi_arvalid <= \^m_axi_arvalid\;
  s_axi_arready <= \^s_axi_arready\;
\/FSM_sequential_dest_state[0]_i_1\: unisim.vcomponents.LUT3
    generic map(
      INIT => X"45"
    )
        port map (
      I0 => \dest_state__0\(0),
      I1 => dest_req,
      I2 => \dest_state__0\(1),
      O => \/FSM_sequential_dest_state[0]_i_1_n_0\
    );
\/FSM_sequential_dest_state[1]_i_1\: unisim.vcomponents.LUT3
    generic map(
      INIT => X"4A"
    )
        port map (
      I0 => \dest_state__0\(0),
      I1 => dest_req,
      I2 => \dest_state__0\(1),
      O => \/FSM_sequential_dest_state[1]_i_1_n_0\
    );
\/FSM_sequential_src_state[0]_i_1\: unisim.vcomponents.LUT4
    generic map(
      INIT => X"5455"
    )
        port map (
      I0 => \src_state__0\(0),
      I1 => s_axi_arvalid,
      I2 => src_rcv,
      I3 => \src_state__0\(1),
      O => \/FSM_sequential_src_state[0]_i_1_n_0\
    );
\/FSM_sequential_src_state[1]_i_1\: unisim.vcomponents.LUT3
    generic map(
      INIT => X"4A"
    )
        port map (
      I0 => \src_state__0\(0),
      I1 => src_rcv,
      I2 => \src_state__0\(1),
      O => \/FSM_sequential_src_state[1]_i_1_n_0\
    );
\FSM_sequential_dest_state_reg[0]\: unisim.vcomponents.FDRE
     port map (
      C => m_axi_aclk,
      CE => dest_state_n_0,
      D => \/FSM_sequential_dest_state[0]_i_1_n_0\,
      Q => \dest_state__0\(0),
      R => m_axi_aresetn(0)
    );
\FSM_sequential_dest_state_reg[1]\: unisim.vcomponents.FDRE
     port map (
      C => m_axi_aclk,
      CE => dest_state_n_0,
      D => \/FSM_sequential_dest_state[1]_i_1_n_0\,
      Q => \dest_state__0\(1),
      R => m_axi_aresetn(0)
    );
\FSM_sequential_src_state_reg[0]\: unisim.vcomponents.FDRE
     port map (
      C => CLK,
      CE => src_state_n_0,
      D => \/FSM_sequential_src_state[0]_i_1_n_0\,
      Q => \src_state__0\(0),
      R => SR(0)
    );
\FSM_sequential_src_state_reg[1]\: unisim.vcomponents.FDRE
     port map (
      C => CLK,
      CE => src_state_n_0,
      D => \/FSM_sequential_src_state[1]_i_1_n_0\,
      Q => \src_state__0\(1),
      R => SR(0)
    );
\dest_ack_i_1__0\: unisim.vcomponents.LUT6
    generic map(
      INIT => X"55FF550040004000"
    )
        port map (
      I0 => \dest_state__0\(1),
      I1 => \^m_axi_arvalid\,
      I2 => m_axi_arready,
      I3 => \dest_state__0\(0),
      I4 => dest_req,
      I5 => dest_ack_reg_n_0,
      O => \dest_ack_i_1__0_n_0\
    );
dest_ack_reg: unisim.vcomponents.FDRE
    generic map(
      INIT => '0'
    )
        port map (
      C => m_axi_aclk,
      CE => '1',
      D => \dest_ack_i_1__0_n_0\,
      Q => dest_ack_reg_n_0,
      R => m_axi_aresetn(0)
    );
dest_state: unisim.vcomponents.LUT5
    generic map(
      INIT => X"F6A6A6A6"
    )
        port map (
      I0 => \dest_state__0\(1),
      I1 => dest_req,
      I2 => \dest_state__0\(0),
      I3 => m_axi_arready,
      I4 => \^m_axi_arvalid\,
      O => dest_state_n_0
    );
handshake: entity work.\axi_clock_converter_oclnew_xpm_cdc_handshake__xdcDup__1\
     port map (
      dest_ack => dest_ack_reg_n_0,
      dest_clk => m_axi_aclk,
      dest_out(34 downto 0) => dest_out(34 downto 0),
      dest_req => dest_req,
      src_clk => CLK,
      src_in(34 downto 0) => src_in(34 downto 0),
      src_rcv => src_rcv,
      src_send => src_send_reg_n_0
    );
m_valid_i_i_1: unisim.vcomponents.LUT5
    generic map(
      INIT => X"0030F0AA"
    )
        port map (
      I0 => dest_req,
      I1 => m_axi_arready,
      I2 => \^m_axi_arvalid\,
      I3 => \dest_state__0\(1),
      I4 => \dest_state__0\(0),
      O => m_valid_i_i_1_n_0
    );
m_valid_i_reg: unisim.vcomponents.FDRE
    generic map(
      INIT => '0'
    )
        port map (
      C => m_axi_aclk,
      CE => '1',
      D => m_valid_i_i_1_n_0,
      Q => \^m_axi_arvalid\,
      R => m_axi_aresetn(0)
    );
s_ready_i_i_1: unisim.vcomponents.LUT4
    generic map(
      INIT => X"5540"
    )
        port map (
      I0 => \src_state__0\(1),
      I1 => src_rcv,
      I2 => \src_state__0\(0),
      I3 => \^s_axi_arready\,
      O => s_ready_i_i_1_n_0
    );
s_ready_i_reg: unisim.vcomponents.FDRE
    generic map(
      INIT => '0'
    )
        port map (
      C => CLK,
      CE => '1',
      D => s_ready_i_i_1_n_0,
      Q => \^s_axi_arready\,
      R => SR(0)
    );
\src_send_i_1__0\: unisim.vcomponents.LUT5
    generic map(
      INIT => X"0F5F040C"
    )
        port map (
      I0 => \src_state__0\(1),
      I1 => s_axi_arvalid,
      I2 => \src_state__0\(0),
      I3 => src_rcv,
      I4 => src_send_reg_n_0,
      O => \src_send_i_1__0_n_0\
    );
src_send_reg: unisim.vcomponents.FDRE
    generic map(
      INIT => '0'
    )
        port map (
      C => CLK,
      CE => '1',
      D => \src_send_i_1__0_n_0\,
      Q => src_send_reg_n_0,
      R => SR(0)
    );
src_state: unisim.vcomponents.LUT4
    generic map(
      INIT => X"F4AE"
    )
        port map (
      I0 => \src_state__0\(1),
      I1 => s_axi_arvalid,
      I2 => \src_state__0\(0),
      I3 => src_rcv,
      O => src_state_n_0
    );
end STRUCTURE;
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
entity axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter is
  port (
    s_axi_aclk : in STD_LOGIC;
    s_axi_aresetn : in STD_LOGIC;
    s_axi_awid : in STD_LOGIC_VECTOR ( 0 to 0 );
    s_axi_awaddr : in STD_LOGIC_VECTOR ( 31 downto 0 );
    s_axi_awlen : in STD_LOGIC_VECTOR ( 7 downto 0 );
    s_axi_awsize : in STD_LOGIC_VECTOR ( 2 downto 0 );
    s_axi_awburst : in STD_LOGIC_VECTOR ( 1 downto 0 );
    s_axi_awlock : in STD_LOGIC_VECTOR ( 0 to 0 );
    s_axi_awcache : in STD_LOGIC_VECTOR ( 3 downto 0 );
    s_axi_awprot : in STD_LOGIC_VECTOR ( 2 downto 0 );
    s_axi_awregion : in STD_LOGIC_VECTOR ( 3 downto 0 );
    s_axi_awqos : in STD_LOGIC_VECTOR ( 3 downto 0 );
    s_axi_awuser : in STD_LOGIC_VECTOR ( 0 to 0 );
    s_axi_awvalid : in STD_LOGIC;
    s_axi_awready : out STD_LOGIC;
    s_axi_wid : in STD_LOGIC_VECTOR ( 0 to 0 );
    s_axi_wdata : in STD_LOGIC_VECTOR ( 31 downto 0 );
    s_axi_wstrb : in STD_LOGIC_VECTOR ( 3 downto 0 );
    s_axi_wlast : in STD_LOGIC;
    s_axi_wuser : in STD_LOGIC_VECTOR ( 0 to 0 );
    s_axi_wvalid : in STD_LOGIC;
    s_axi_wready : out STD_LOGIC;
    s_axi_bid : out STD_LOGIC_VECTOR ( 0 to 0 );
    s_axi_bresp : out STD_LOGIC_VECTOR ( 1 downto 0 );
    s_axi_buser : out STD_LOGIC_VECTOR ( 0 to 0 );
    s_axi_bvalid : out STD_LOGIC;
    s_axi_bready : in STD_LOGIC;
    s_axi_arid : in STD_LOGIC_VECTOR ( 0 to 0 );
    s_axi_araddr : in STD_LOGIC_VECTOR ( 31 downto 0 );
    s_axi_arlen : in STD_LOGIC_VECTOR ( 7 downto 0 );
    s_axi_arsize : in STD_LOGIC_VECTOR ( 2 downto 0 );
    s_axi_arburst : in STD_LOGIC_VECTOR ( 1 downto 0 );
    s_axi_arlock : in STD_LOGIC_VECTOR ( 0 to 0 );
    s_axi_arcache : in STD_LOGIC_VECTOR ( 3 downto 0 );
    s_axi_arprot : in STD_LOGIC_VECTOR ( 2 downto 0 );
    s_axi_arregion : in STD_LOGIC_VECTOR ( 3 downto 0 );
    s_axi_arqos : in STD_LOGIC_VECTOR ( 3 downto 0 );
    s_axi_aruser : in STD_LOGIC_VECTOR ( 0 to 0 );
    s_axi_arvalid : in STD_LOGIC;
    s_axi_arready : out STD_LOGIC;
    s_axi_rid : out STD_LOGIC_VECTOR ( 0 to 0 );
    s_axi_rdata : out STD_LOGIC_VECTOR ( 31 downto 0 );
    s_axi_rresp : out STD_LOGIC_VECTOR ( 1 downto 0 );
    s_axi_rlast : out STD_LOGIC;
    s_axi_ruser : out STD_LOGIC_VECTOR ( 0 to 0 );
    s_axi_rvalid : out STD_LOGIC;
    s_axi_rready : in STD_LOGIC;
    m_axi_aclk : in STD_LOGIC;
    m_axi_aresetn : in STD_LOGIC;
    m_axi_awid : out STD_LOGIC_VECTOR ( 0 to 0 );
    m_axi_awaddr : out STD_LOGIC_VECTOR ( 31 downto 0 );
    m_axi_awlen : out STD_LOGIC_VECTOR ( 7 downto 0 );
    m_axi_awsize : out STD_LOGIC_VECTOR ( 2 downto 0 );
    m_axi_awburst : out STD_LOGIC_VECTOR ( 1 downto 0 );
    m_axi_awlock : out STD_LOGIC_VECTOR ( 0 to 0 );
    m_axi_awcache : out STD_LOGIC_VECTOR ( 3 downto 0 );
    m_axi_awprot : out STD_LOGIC_VECTOR ( 2 downto 0 );
    m_axi_awregion : out STD_LOGIC_VECTOR ( 3 downto 0 );
    m_axi_awqos : out STD_LOGIC_VECTOR ( 3 downto 0 );
    m_axi_awuser : out STD_LOGIC_VECTOR ( 0 to 0 );
    m_axi_awvalid : out STD_LOGIC;
    m_axi_awready : in STD_LOGIC;
    m_axi_wid : out STD_LOGIC_VECTOR ( 0 to 0 );
    m_axi_wdata : out STD_LOGIC_VECTOR ( 31 downto 0 );
    m_axi_wstrb : out STD_LOGIC_VECTOR ( 3 downto 0 );
    m_axi_wlast : out STD_LOGIC;
    m_axi_wuser : out STD_LOGIC_VECTOR ( 0 to 0 );
    m_axi_wvalid : out STD_LOGIC;
    m_axi_wready : in STD_LOGIC;
    m_axi_bid : in STD_LOGIC_VECTOR ( 0 to 0 );
    m_axi_bresp : in STD_LOGIC_VECTOR ( 1 downto 0 );
    m_axi_buser : in STD_LOGIC_VECTOR ( 0 to 0 );
    m_axi_bvalid : in STD_LOGIC;
    m_axi_bready : out STD_LOGIC;
    m_axi_arid : out STD_LOGIC_VECTOR ( 0 to 0 );
    m_axi_araddr : out STD_LOGIC_VECTOR ( 31 downto 0 );
    m_axi_arlen : out STD_LOGIC_VECTOR ( 7 downto 0 );
    m_axi_arsize : out STD_LOGIC_VECTOR ( 2 downto 0 );
    m_axi_arburst : out STD_LOGIC_VECTOR ( 1 downto 0 );
    m_axi_arlock : out STD_LOGIC_VECTOR ( 0 to 0 );
    m_axi_arcache : out STD_LOGIC_VECTOR ( 3 downto 0 );
    m_axi_arprot : out STD_LOGIC_VECTOR ( 2 downto 0 );
    m_axi_arregion : out STD_LOGIC_VECTOR ( 3 downto 0 );
    m_axi_arqos : out STD_LOGIC_VECTOR ( 3 downto 0 );
    m_axi_aruser : out STD_LOGIC_VECTOR ( 0 to 0 );
    m_axi_arvalid : out STD_LOGIC;
    m_axi_arready : in STD_LOGIC;
    m_axi_rid : in STD_LOGIC_VECTOR ( 0 to 0 );
    m_axi_rdata : in STD_LOGIC_VECTOR ( 31 downto 0 );
    m_axi_rresp : in STD_LOGIC_VECTOR ( 1 downto 0 );
    m_axi_rlast : in STD_LOGIC;
    m_axi_ruser : in STD_LOGIC_VECTOR ( 0 to 0 );
    m_axi_rvalid : in STD_LOGIC;
    m_axi_rready : out STD_LOGIC
  );
  attribute C_ARADDR_RIGHT : integer;
  attribute C_ARADDR_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 3;
  attribute C_ARADDR_WIDTH : integer;
  attribute C_ARADDR_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 32;
  attribute C_ARBURST_RIGHT : integer;
  attribute C_ARBURST_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 3;
  attribute C_ARBURST_WIDTH : integer;
  attribute C_ARBURST_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_ARCACHE_RIGHT : integer;
  attribute C_ARCACHE_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 3;
  attribute C_ARCACHE_WIDTH : integer;
  attribute C_ARCACHE_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_ARID_RIGHT : integer;
  attribute C_ARID_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 35;
  attribute C_ARID_WIDTH : integer;
  attribute C_ARID_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_ARLEN_RIGHT : integer;
  attribute C_ARLEN_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 3;
  attribute C_ARLEN_WIDTH : integer;
  attribute C_ARLEN_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_ARLOCK_RIGHT : integer;
  attribute C_ARLOCK_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 3;
  attribute C_ARLOCK_WIDTH : integer;
  attribute C_ARLOCK_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_ARPROT_RIGHT : integer;
  attribute C_ARPROT_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_ARPROT_WIDTH : integer;
  attribute C_ARPROT_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 3;
  attribute C_ARQOS_RIGHT : integer;
  attribute C_ARQOS_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_ARQOS_WIDTH : integer;
  attribute C_ARQOS_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_ARREGION_RIGHT : integer;
  attribute C_ARREGION_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_ARREGION_WIDTH : integer;
  attribute C_ARREGION_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_ARSIZE_RIGHT : integer;
  attribute C_ARSIZE_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 3;
  attribute C_ARSIZE_WIDTH : integer;
  attribute C_ARSIZE_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_ARUSER_RIGHT : integer;
  attribute C_ARUSER_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_ARUSER_WIDTH : integer;
  attribute C_ARUSER_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_AR_WIDTH : integer;
  attribute C_AR_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 35;
  attribute C_AWADDR_RIGHT : integer;
  attribute C_AWADDR_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 3;
  attribute C_AWADDR_WIDTH : integer;
  attribute C_AWADDR_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 32;
  attribute C_AWBURST_RIGHT : integer;
  attribute C_AWBURST_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 3;
  attribute C_AWBURST_WIDTH : integer;
  attribute C_AWBURST_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_AWCACHE_RIGHT : integer;
  attribute C_AWCACHE_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 3;
  attribute C_AWCACHE_WIDTH : integer;
  attribute C_AWCACHE_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_AWID_RIGHT : integer;
  attribute C_AWID_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 35;
  attribute C_AWID_WIDTH : integer;
  attribute C_AWID_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_AWLEN_RIGHT : integer;
  attribute C_AWLEN_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 3;
  attribute C_AWLEN_WIDTH : integer;
  attribute C_AWLEN_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_AWLOCK_RIGHT : integer;
  attribute C_AWLOCK_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 3;
  attribute C_AWLOCK_WIDTH : integer;
  attribute C_AWLOCK_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_AWPROT_RIGHT : integer;
  attribute C_AWPROT_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_AWPROT_WIDTH : integer;
  attribute C_AWPROT_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 3;
  attribute C_AWQOS_RIGHT : integer;
  attribute C_AWQOS_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_AWQOS_WIDTH : integer;
  attribute C_AWQOS_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_AWREGION_RIGHT : integer;
  attribute C_AWREGION_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_AWREGION_WIDTH : integer;
  attribute C_AWREGION_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_AWSIZE_RIGHT : integer;
  attribute C_AWSIZE_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 3;
  attribute C_AWSIZE_WIDTH : integer;
  attribute C_AWSIZE_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_AWUSER_RIGHT : integer;
  attribute C_AWUSER_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_AWUSER_WIDTH : integer;
  attribute C_AWUSER_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_AW_WIDTH : integer;
  attribute C_AW_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 35;
  attribute C_AXI_ADDR_WIDTH : integer;
  attribute C_AXI_ADDR_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 32;
  attribute C_AXI_ARUSER_WIDTH : integer;
  attribute C_AXI_ARUSER_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 1;
  attribute C_AXI_AWUSER_WIDTH : integer;
  attribute C_AXI_AWUSER_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 1;
  attribute C_AXI_BUSER_WIDTH : integer;
  attribute C_AXI_BUSER_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 1;
  attribute C_AXI_DATA_WIDTH : integer;
  attribute C_AXI_DATA_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 32;
  attribute C_AXI_ID_WIDTH : integer;
  attribute C_AXI_ID_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 1;
  attribute C_AXI_IS_ACLK_ASYNC : integer;
  attribute C_AXI_IS_ACLK_ASYNC of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 1;
  attribute C_AXI_PROTOCOL : integer;
  attribute C_AXI_PROTOCOL of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 2;
  attribute C_AXI_RUSER_WIDTH : integer;
  attribute C_AXI_RUSER_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 1;
  attribute C_AXI_SUPPORTS_READ : integer;
  attribute C_AXI_SUPPORTS_READ of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 1;
  attribute C_AXI_SUPPORTS_USER_SIGNALS : integer;
  attribute C_AXI_SUPPORTS_USER_SIGNALS of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_AXI_SUPPORTS_WRITE : integer;
  attribute C_AXI_SUPPORTS_WRITE of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 1;
  attribute C_AXI_WUSER_WIDTH : integer;
  attribute C_AXI_WUSER_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 1;
  attribute C_BID_RIGHT : integer;
  attribute C_BID_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 2;
  attribute C_BID_WIDTH : integer;
  attribute C_BID_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_BRESP_RIGHT : integer;
  attribute C_BRESP_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_BRESP_WIDTH : integer;
  attribute C_BRESP_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 2;
  attribute C_BUSER_RIGHT : integer;
  attribute C_BUSER_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_BUSER_WIDTH : integer;
  attribute C_BUSER_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_B_WIDTH : integer;
  attribute C_B_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 2;
  attribute C_FAMILY : string;
  attribute C_FAMILY of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is "virtexuplus";
  attribute C_FIFO_AR_WIDTH : integer;
  attribute C_FIFO_AR_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 35;
  attribute C_FIFO_AW_WIDTH : integer;
  attribute C_FIFO_AW_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 35;
  attribute C_FIFO_B_WIDTH : integer;
  attribute C_FIFO_B_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 2;
  attribute C_FIFO_R_WIDTH : integer;
  attribute C_FIFO_R_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 34;
  attribute C_FIFO_W_WIDTH : integer;
  attribute C_FIFO_W_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 36;
  attribute C_M_AXI_ACLK_RATIO : integer;
  attribute C_M_AXI_ACLK_RATIO of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 2;
  attribute C_RDATA_RIGHT : integer;
  attribute C_RDATA_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 2;
  attribute C_RDATA_WIDTH : integer;
  attribute C_RDATA_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 32;
  attribute C_RID_RIGHT : integer;
  attribute C_RID_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 34;
  attribute C_RID_WIDTH : integer;
  attribute C_RID_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_RLAST_RIGHT : integer;
  attribute C_RLAST_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_RLAST_WIDTH : integer;
  attribute C_RLAST_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_RRESP_RIGHT : integer;
  attribute C_RRESP_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_RRESP_WIDTH : integer;
  attribute C_RRESP_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 2;
  attribute C_RUSER_RIGHT : integer;
  attribute C_RUSER_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_RUSER_WIDTH : integer;
  attribute C_RUSER_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_R_WIDTH : integer;
  attribute C_R_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 34;
  attribute C_SYNCHRONIZER_STAGE : integer;
  attribute C_SYNCHRONIZER_STAGE of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 3;
  attribute C_S_AXI_ACLK_RATIO : integer;
  attribute C_S_AXI_ACLK_RATIO of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 1;
  attribute C_WDATA_RIGHT : integer;
  attribute C_WDATA_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 4;
  attribute C_WDATA_WIDTH : integer;
  attribute C_WDATA_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 32;
  attribute C_WID_RIGHT : integer;
  attribute C_WID_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 36;
  attribute C_WID_WIDTH : integer;
  attribute C_WID_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_WLAST_RIGHT : integer;
  attribute C_WLAST_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_WLAST_WIDTH : integer;
  attribute C_WLAST_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_WSTRB_RIGHT : integer;
  attribute C_WSTRB_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_WSTRB_WIDTH : integer;
  attribute C_WSTRB_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 4;
  attribute C_WUSER_RIGHT : integer;
  attribute C_WUSER_RIGHT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_WUSER_WIDTH : integer;
  attribute C_WUSER_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute C_W_WIDTH : integer;
  attribute C_W_WIDTH of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 36;
  attribute DowngradeIPIdentifiedWarnings : string;
  attribute DowngradeIPIdentifiedWarnings of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is "yes";
  attribute ORIG_REF_NAME : string;
  attribute ORIG_REF_NAME of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is "axi_clock_converter_v2_1_11_axi_clock_converter";
  attribute P_ACLK_RATIO : integer;
  attribute P_ACLK_RATIO of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 2;
  attribute P_AXI3 : integer;
  attribute P_AXI3 of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 1;
  attribute P_AXI4 : integer;
  attribute P_AXI4 of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute P_AXILITE : integer;
  attribute P_AXILITE of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 2;
  attribute P_FULLY_REG : integer;
  attribute P_FULLY_REG of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 1;
  attribute P_LIGHT_WT : integer;
  attribute P_LIGHT_WT of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute P_LUTRAM_ASYNC : integer;
  attribute P_LUTRAM_ASYNC of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 12;
  attribute P_ROUNDING_OFFSET : integer;
  attribute P_ROUNDING_OFFSET of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is 0;
  attribute P_SI_LT_MI : string;
  attribute P_SI_LT_MI of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter : entity is "1'b1";
end axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter;

architecture STRUCTURE of axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter is
  signal \<const0>\ : STD_LOGIC;
  signal \gen_clock_conv.gen_async_lite_conv.r_handshake_n_35\ : STD_LOGIC;
  signal \gen_clock_conv.gen_async_lite_conv.r_handshake_n_37\ : STD_LOGIC;
begin
  m_axi_arburst(1) <= \<const0>\;
  m_axi_arburst(0) <= \<const0>\;
  m_axi_arcache(3) <= \<const0>\;
  m_axi_arcache(2) <= \<const0>\;
  m_axi_arcache(1) <= \<const0>\;
  m_axi_arcache(0) <= \<const0>\;
  m_axi_arid(0) <= \<const0>\;
  m_axi_arlen(7) <= \<const0>\;
  m_axi_arlen(6) <= \<const0>\;
  m_axi_arlen(5) <= \<const0>\;
  m_axi_arlen(4) <= \<const0>\;
  m_axi_arlen(3) <= \<const0>\;
  m_axi_arlen(2) <= \<const0>\;
  m_axi_arlen(1) <= \<const0>\;
  m_axi_arlen(0) <= \<const0>\;
  m_axi_arlock(0) <= \<const0>\;
  m_axi_arqos(3) <= \<const0>\;
  m_axi_arqos(2) <= \<const0>\;
  m_axi_arqos(1) <= \<const0>\;
  m_axi_arqos(0) <= \<const0>\;
  m_axi_arregion(3) <= \<const0>\;
  m_axi_arregion(2) <= \<const0>\;
  m_axi_arregion(1) <= \<const0>\;
  m_axi_arregion(0) <= \<const0>\;
  m_axi_arsize(2) <= \<const0>\;
  m_axi_arsize(1) <= \<const0>\;
  m_axi_arsize(0) <= \<const0>\;
  m_axi_aruser(0) <= \<const0>\;
  m_axi_awburst(1) <= \<const0>\;
  m_axi_awburst(0) <= \<const0>\;
  m_axi_awcache(3) <= \<const0>\;
  m_axi_awcache(2) <= \<const0>\;
  m_axi_awcache(1) <= \<const0>\;
  m_axi_awcache(0) <= \<const0>\;
  m_axi_awid(0) <= \<const0>\;
  m_axi_awlen(7) <= \<const0>\;
  m_axi_awlen(6) <= \<const0>\;
  m_axi_awlen(5) <= \<const0>\;
  m_axi_awlen(4) <= \<const0>\;
  m_axi_awlen(3) <= \<const0>\;
  m_axi_awlen(2) <= \<const0>\;
  m_axi_awlen(1) <= \<const0>\;
  m_axi_awlen(0) <= \<const0>\;
  m_axi_awlock(0) <= \<const0>\;
  m_axi_awqos(3) <= \<const0>\;
  m_axi_awqos(2) <= \<const0>\;
  m_axi_awqos(1) <= \<const0>\;
  m_axi_awqos(0) <= \<const0>\;
  m_axi_awregion(3) <= \<const0>\;
  m_axi_awregion(2) <= \<const0>\;
  m_axi_awregion(1) <= \<const0>\;
  m_axi_awregion(0) <= \<const0>\;
  m_axi_awsize(2) <= \<const0>\;
  m_axi_awsize(1) <= \<const0>\;
  m_axi_awsize(0) <= \<const0>\;
  m_axi_awuser(0) <= \<const0>\;
  m_axi_wid(0) <= \<const0>\;
  m_axi_wlast <= \<const0>\;
  m_axi_wuser(0) <= \<const0>\;
  s_axi_bid(0) <= \<const0>\;
  s_axi_buser(0) <= \<const0>\;
  s_axi_rid(0) <= \<const0>\;
  s_axi_rlast <= \<const0>\;
  s_axi_ruser(0) <= \<const0>\;
GND: unisim.vcomponents.GND
     port map (
      G => \<const0>\
    );
\gen_clock_conv.gen_async_lite_conv.ar_handshake\: entity work.\axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_lite_async__xdcDup__1\
     port map (
      CLK => s_axi_aclk,
      SR(0) => \gen_clock_conv.gen_async_lite_conv.r_handshake_n_37\,
      dest_out(34 downto 32) => m_axi_arprot(2 downto 0),
      dest_out(31 downto 0) => m_axi_araddr(31 downto 0),
      m_axi_aclk => m_axi_aclk,
      m_axi_aresetn(0) => \gen_clock_conv.gen_async_lite_conv.r_handshake_n_35\,
      m_axi_arready => m_axi_arready,
      m_axi_arvalid => m_axi_arvalid,
      s_axi_arready => s_axi_arready,
      s_axi_arvalid => s_axi_arvalid,
      src_in(34 downto 32) => s_axi_arprot(2 downto 0),
      src_in(31 downto 0) => s_axi_araddr(31 downto 0)
    );
\gen_clock_conv.gen_async_lite_conv.aw_handshake\: entity work.axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_lite_async
     port map (
      CLK => s_axi_aclk,
      SR(0) => \gen_clock_conv.gen_async_lite_conv.r_handshake_n_37\,
      dest_out(34 downto 32) => m_axi_awprot(2 downto 0),
      dest_out(31 downto 0) => m_axi_awaddr(31 downto 0),
      m_axi_aclk => m_axi_aclk,
      m_axi_aresetn(0) => \gen_clock_conv.gen_async_lite_conv.r_handshake_n_35\,
      m_axi_awready => m_axi_awready,
      m_axi_awvalid => m_axi_awvalid,
      s_axi_awready => s_axi_awready,
      s_axi_awvalid => s_axi_awvalid,
      src_in(34 downto 32) => s_axi_awprot(2 downto 0),
      src_in(31 downto 0) => s_axi_awaddr(31 downto 0)
    );
\gen_clock_conv.gen_async_lite_conv.b_handshake\: entity work.\axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_lite_async__parameterized1\
     port map (
      CLK => m_axi_aclk,
      SR(0) => \gen_clock_conv.gen_async_lite_conv.r_handshake_n_35\,
      m_axi_bready => m_axi_bready,
      m_axi_bresp(1 downto 0) => m_axi_bresp(1 downto 0),
      m_axi_bvalid => m_axi_bvalid,
      s_axi_aclk => s_axi_aclk,
      s_axi_aresetn(0) => \gen_clock_conv.gen_async_lite_conv.r_handshake_n_37\,
      s_axi_bready => s_axi_bready,
      s_axi_bresp(1 downto 0) => s_axi_bresp(1 downto 0),
      s_axi_bvalid => s_axi_bvalid
    );
\gen_clock_conv.gen_async_lite_conv.r_handshake\: entity work.\axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_lite_async__parameterized2\
     port map (
      SR(0) => \gen_clock_conv.gen_async_lite_conv.r_handshake_n_35\,
      dest_ack_reg_0(0) => \gen_clock_conv.gen_async_lite_conv.r_handshake_n_37\,
      dest_out(33 downto 32) => s_axi_rresp(1 downto 0),
      dest_out(31 downto 0) => s_axi_rdata(31 downto 0),
      m_axi_aresetn => m_axi_aresetn,
      m_axi_rready => m_axi_rready,
      m_axi_rvalid => m_axi_rvalid,
      \out\ => m_axi_aclk,
      s_axi_aclk => s_axi_aclk,
      s_axi_aresetn => s_axi_aresetn,
      s_axi_rready => s_axi_rready,
      s_axi_rvalid => s_axi_rvalid,
      src_in(33 downto 32) => m_axi_rresp(1 downto 0),
      src_in(31 downto 0) => m_axi_rdata(31 downto 0)
    );
\gen_clock_conv.gen_async_lite_conv.w_handshake\: entity work.\axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_lite_async__parameterized0\
     port map (
      SR(0) => \gen_clock_conv.gen_async_lite_conv.r_handshake_n_35\,
      dest_out(35 downto 32) => m_axi_wstrb(3 downto 0),
      dest_out(31 downto 0) => m_axi_wdata(31 downto 0),
      m_axi_aclk => m_axi_aclk,
      m_axi_wready => m_axi_wready,
      m_axi_wvalid => m_axi_wvalid,
      \out\ => s_axi_aclk,
      s_axi_aresetn(0) => \gen_clock_conv.gen_async_lite_conv.r_handshake_n_37\,
      s_axi_wready => s_axi_wready,
      s_axi_wvalid => s_axi_wvalid,
      src_in(35 downto 32) => s_axi_wstrb(3 downto 0),
      src_in(31 downto 0) => s_axi_wdata(31 downto 0)
    );
end STRUCTURE;
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
entity axi_clock_converter_oclnew is
  port (
    s_axi_aclk : in STD_LOGIC;
    s_axi_aresetn : in STD_LOGIC;
    s_axi_awaddr : in STD_LOGIC_VECTOR ( 31 downto 0 );
    s_axi_awprot : in STD_LOGIC_VECTOR ( 2 downto 0 );
    s_axi_awvalid : in STD_LOGIC;
    s_axi_awready : out STD_LOGIC;
    s_axi_wdata : in STD_LOGIC_VECTOR ( 31 downto 0 );
    s_axi_wstrb : in STD_LOGIC_VECTOR ( 3 downto 0 );
    s_axi_wvalid : in STD_LOGIC;
    s_axi_wready : out STD_LOGIC;
    s_axi_bresp : out STD_LOGIC_VECTOR ( 1 downto 0 );
    s_axi_bvalid : out STD_LOGIC;
    s_axi_bready : in STD_LOGIC;
    s_axi_araddr : in STD_LOGIC_VECTOR ( 31 downto 0 );
    s_axi_arprot : in STD_LOGIC_VECTOR ( 2 downto 0 );
    s_axi_arvalid : in STD_LOGIC;
    s_axi_arready : out STD_LOGIC;
    s_axi_rdata : out STD_LOGIC_VECTOR ( 31 downto 0 );
    s_axi_rresp : out STD_LOGIC_VECTOR ( 1 downto 0 );
    s_axi_rvalid : out STD_LOGIC;
    s_axi_rready : in STD_LOGIC;
    m_axi_aclk : in STD_LOGIC;
    m_axi_aresetn : in STD_LOGIC;
    m_axi_awaddr : out STD_LOGIC_VECTOR ( 31 downto 0 );
    m_axi_awprot : out STD_LOGIC_VECTOR ( 2 downto 0 );
    m_axi_awvalid : out STD_LOGIC;
    m_axi_awready : in STD_LOGIC;
    m_axi_wdata : out STD_LOGIC_VECTOR ( 31 downto 0 );
    m_axi_wstrb : out STD_LOGIC_VECTOR ( 3 downto 0 );
    m_axi_wvalid : out STD_LOGIC;
    m_axi_wready : in STD_LOGIC;
    m_axi_bresp : in STD_LOGIC_VECTOR ( 1 downto 0 );
    m_axi_bvalid : in STD_LOGIC;
    m_axi_bready : out STD_LOGIC;
    m_axi_araddr : out STD_LOGIC_VECTOR ( 31 downto 0 );
    m_axi_arprot : out STD_LOGIC_VECTOR ( 2 downto 0 );
    m_axi_arvalid : out STD_LOGIC;
    m_axi_arready : in STD_LOGIC;
    m_axi_rdata : in STD_LOGIC_VECTOR ( 31 downto 0 );
    m_axi_rresp : in STD_LOGIC_VECTOR ( 1 downto 0 );
    m_axi_rvalid : in STD_LOGIC;
    m_axi_rready : out STD_LOGIC
  );
  attribute NotValidForBitStream : boolean;
  attribute NotValidForBitStream of axi_clock_converter_oclnew : entity is true;
  attribute CHECK_LICENSE_TYPE : string;
  attribute CHECK_LICENSE_TYPE of axi_clock_converter_oclnew : entity is "axi_clock_converter_oclnew,axi_clock_converter_v2_1_11_axi_clock_converter,{}";
  attribute DowngradeIPIdentifiedWarnings : string;
  attribute DowngradeIPIdentifiedWarnings of axi_clock_converter_oclnew : entity is "yes";
  attribute X_CORE_INFO : string;
  attribute X_CORE_INFO of axi_clock_converter_oclnew : entity is "axi_clock_converter_v2_1_11_axi_clock_converter,Vivado 2017.1";
end axi_clock_converter_oclnew;

architecture STRUCTURE of axi_clock_converter_oclnew is
  signal NLW_inst_m_axi_wlast_UNCONNECTED : STD_LOGIC;
  signal NLW_inst_s_axi_rlast_UNCONNECTED : STD_LOGIC;
  signal NLW_inst_m_axi_arburst_UNCONNECTED : STD_LOGIC_VECTOR ( 1 downto 0 );
  signal NLW_inst_m_axi_arcache_UNCONNECTED : STD_LOGIC_VECTOR ( 3 downto 0 );
  signal NLW_inst_m_axi_arid_UNCONNECTED : STD_LOGIC_VECTOR ( 0 to 0 );
  signal NLW_inst_m_axi_arlen_UNCONNECTED : STD_LOGIC_VECTOR ( 7 downto 0 );
  signal NLW_inst_m_axi_arlock_UNCONNECTED : STD_LOGIC_VECTOR ( 0 to 0 );
  signal NLW_inst_m_axi_arqos_UNCONNECTED : STD_LOGIC_VECTOR ( 3 downto 0 );
  signal NLW_inst_m_axi_arregion_UNCONNECTED : STD_LOGIC_VECTOR ( 3 downto 0 );
  signal NLW_inst_m_axi_arsize_UNCONNECTED : STD_LOGIC_VECTOR ( 2 downto 0 );
  signal NLW_inst_m_axi_aruser_UNCONNECTED : STD_LOGIC_VECTOR ( 0 to 0 );
  signal NLW_inst_m_axi_awburst_UNCONNECTED : STD_LOGIC_VECTOR ( 1 downto 0 );
  signal NLW_inst_m_axi_awcache_UNCONNECTED : STD_LOGIC_VECTOR ( 3 downto 0 );
  signal NLW_inst_m_axi_awid_UNCONNECTED : STD_LOGIC_VECTOR ( 0 to 0 );
  signal NLW_inst_m_axi_awlen_UNCONNECTED : STD_LOGIC_VECTOR ( 7 downto 0 );
  signal NLW_inst_m_axi_awlock_UNCONNECTED : STD_LOGIC_VECTOR ( 0 to 0 );
  signal NLW_inst_m_axi_awqos_UNCONNECTED : STD_LOGIC_VECTOR ( 3 downto 0 );
  signal NLW_inst_m_axi_awregion_UNCONNECTED : STD_LOGIC_VECTOR ( 3 downto 0 );
  signal NLW_inst_m_axi_awsize_UNCONNECTED : STD_LOGIC_VECTOR ( 2 downto 0 );
  signal NLW_inst_m_axi_awuser_UNCONNECTED : STD_LOGIC_VECTOR ( 0 to 0 );
  signal NLW_inst_m_axi_wid_UNCONNECTED : STD_LOGIC_VECTOR ( 0 to 0 );
  signal NLW_inst_m_axi_wuser_UNCONNECTED : STD_LOGIC_VECTOR ( 0 to 0 );
  signal NLW_inst_s_axi_bid_UNCONNECTED : STD_LOGIC_VECTOR ( 0 to 0 );
  signal NLW_inst_s_axi_buser_UNCONNECTED : STD_LOGIC_VECTOR ( 0 to 0 );
  signal NLW_inst_s_axi_rid_UNCONNECTED : STD_LOGIC_VECTOR ( 0 to 0 );
  signal NLW_inst_s_axi_ruser_UNCONNECTED : STD_LOGIC_VECTOR ( 0 to 0 );
  attribute C_ARADDR_RIGHT : integer;
  attribute C_ARADDR_RIGHT of inst : label is 3;
  attribute C_ARADDR_WIDTH : integer;
  attribute C_ARADDR_WIDTH of inst : label is 32;
  attribute C_ARBURST_RIGHT : integer;
  attribute C_ARBURST_RIGHT of inst : label is 3;
  attribute C_ARBURST_WIDTH : integer;
  attribute C_ARBURST_WIDTH of inst : label is 0;
  attribute C_ARCACHE_RIGHT : integer;
  attribute C_ARCACHE_RIGHT of inst : label is 3;
  attribute C_ARCACHE_WIDTH : integer;
  attribute C_ARCACHE_WIDTH of inst : label is 0;
  attribute C_ARID_RIGHT : integer;
  attribute C_ARID_RIGHT of inst : label is 35;
  attribute C_ARID_WIDTH : integer;
  attribute C_ARID_WIDTH of inst : label is 0;
  attribute C_ARLEN_RIGHT : integer;
  attribute C_ARLEN_RIGHT of inst : label is 3;
  attribute C_ARLEN_WIDTH : integer;
  attribute C_ARLEN_WIDTH of inst : label is 0;
  attribute C_ARLOCK_RIGHT : integer;
  attribute C_ARLOCK_RIGHT of inst : label is 3;
  attribute C_ARLOCK_WIDTH : integer;
  attribute C_ARLOCK_WIDTH of inst : label is 0;
  attribute C_ARPROT_RIGHT : integer;
  attribute C_ARPROT_RIGHT of inst : label is 0;
  attribute C_ARPROT_WIDTH : integer;
  attribute C_ARPROT_WIDTH of inst : label is 3;
  attribute C_ARQOS_RIGHT : integer;
  attribute C_ARQOS_RIGHT of inst : label is 0;
  attribute C_ARQOS_WIDTH : integer;
  attribute C_ARQOS_WIDTH of inst : label is 0;
  attribute C_ARREGION_RIGHT : integer;
  attribute C_ARREGION_RIGHT of inst : label is 0;
  attribute C_ARREGION_WIDTH : integer;
  attribute C_ARREGION_WIDTH of inst : label is 0;
  attribute C_ARSIZE_RIGHT : integer;
  attribute C_ARSIZE_RIGHT of inst : label is 3;
  attribute C_ARSIZE_WIDTH : integer;
  attribute C_ARSIZE_WIDTH of inst : label is 0;
  attribute C_ARUSER_RIGHT : integer;
  attribute C_ARUSER_RIGHT of inst : label is 0;
  attribute C_ARUSER_WIDTH : integer;
  attribute C_ARUSER_WIDTH of inst : label is 0;
  attribute C_AR_WIDTH : integer;
  attribute C_AR_WIDTH of inst : label is 35;
  attribute C_AWADDR_RIGHT : integer;
  attribute C_AWADDR_RIGHT of inst : label is 3;
  attribute C_AWADDR_WIDTH : integer;
  attribute C_AWADDR_WIDTH of inst : label is 32;
  attribute C_AWBURST_RIGHT : integer;
  attribute C_AWBURST_RIGHT of inst : label is 3;
  attribute C_AWBURST_WIDTH : integer;
  attribute C_AWBURST_WIDTH of inst : label is 0;
  attribute C_AWCACHE_RIGHT : integer;
  attribute C_AWCACHE_RIGHT of inst : label is 3;
  attribute C_AWCACHE_WIDTH : integer;
  attribute C_AWCACHE_WIDTH of inst : label is 0;
  attribute C_AWID_RIGHT : integer;
  attribute C_AWID_RIGHT of inst : label is 35;
  attribute C_AWID_WIDTH : integer;
  attribute C_AWID_WIDTH of inst : label is 0;
  attribute C_AWLEN_RIGHT : integer;
  attribute C_AWLEN_RIGHT of inst : label is 3;
  attribute C_AWLEN_WIDTH : integer;
  attribute C_AWLEN_WIDTH of inst : label is 0;
  attribute C_AWLOCK_RIGHT : integer;
  attribute C_AWLOCK_RIGHT of inst : label is 3;
  attribute C_AWLOCK_WIDTH : integer;
  attribute C_AWLOCK_WIDTH of inst : label is 0;
  attribute C_AWPROT_RIGHT : integer;
  attribute C_AWPROT_RIGHT of inst : label is 0;
  attribute C_AWPROT_WIDTH : integer;
  attribute C_AWPROT_WIDTH of inst : label is 3;
  attribute C_AWQOS_RIGHT : integer;
  attribute C_AWQOS_RIGHT of inst : label is 0;
  attribute C_AWQOS_WIDTH : integer;
  attribute C_AWQOS_WIDTH of inst : label is 0;
  attribute C_AWREGION_RIGHT : integer;
  attribute C_AWREGION_RIGHT of inst : label is 0;
  attribute C_AWREGION_WIDTH : integer;
  attribute C_AWREGION_WIDTH of inst : label is 0;
  attribute C_AWSIZE_RIGHT : integer;
  attribute C_AWSIZE_RIGHT of inst : label is 3;
  attribute C_AWSIZE_WIDTH : integer;
  attribute C_AWSIZE_WIDTH of inst : label is 0;
  attribute C_AWUSER_RIGHT : integer;
  attribute C_AWUSER_RIGHT of inst : label is 0;
  attribute C_AWUSER_WIDTH : integer;
  attribute C_AWUSER_WIDTH of inst : label is 0;
  attribute C_AW_WIDTH : integer;
  attribute C_AW_WIDTH of inst : label is 35;
  attribute C_AXI_ADDR_WIDTH : integer;
  attribute C_AXI_ADDR_WIDTH of inst : label is 32;
  attribute C_AXI_ARUSER_WIDTH : integer;
  attribute C_AXI_ARUSER_WIDTH of inst : label is 1;
  attribute C_AXI_AWUSER_WIDTH : integer;
  attribute C_AXI_AWUSER_WIDTH of inst : label is 1;
  attribute C_AXI_BUSER_WIDTH : integer;
  attribute C_AXI_BUSER_WIDTH of inst : label is 1;
  attribute C_AXI_DATA_WIDTH : integer;
  attribute C_AXI_DATA_WIDTH of inst : label is 32;
  attribute C_AXI_ID_WIDTH : integer;
  attribute C_AXI_ID_WIDTH of inst : label is 1;
  attribute C_AXI_IS_ACLK_ASYNC : integer;
  attribute C_AXI_IS_ACLK_ASYNC of inst : label is 1;
  attribute C_AXI_PROTOCOL : integer;
  attribute C_AXI_PROTOCOL of inst : label is 2;
  attribute C_AXI_RUSER_WIDTH : integer;
  attribute C_AXI_RUSER_WIDTH of inst : label is 1;
  attribute C_AXI_SUPPORTS_READ : integer;
  attribute C_AXI_SUPPORTS_READ of inst : label is 1;
  attribute C_AXI_SUPPORTS_USER_SIGNALS : integer;
  attribute C_AXI_SUPPORTS_USER_SIGNALS of inst : label is 0;
  attribute C_AXI_SUPPORTS_WRITE : integer;
  attribute C_AXI_SUPPORTS_WRITE of inst : label is 1;
  attribute C_AXI_WUSER_WIDTH : integer;
  attribute C_AXI_WUSER_WIDTH of inst : label is 1;
  attribute C_BID_RIGHT : integer;
  attribute C_BID_RIGHT of inst : label is 2;
  attribute C_BID_WIDTH : integer;
  attribute C_BID_WIDTH of inst : label is 0;
  attribute C_BRESP_RIGHT : integer;
  attribute C_BRESP_RIGHT of inst : label is 0;
  attribute C_BRESP_WIDTH : integer;
  attribute C_BRESP_WIDTH of inst : label is 2;
  attribute C_BUSER_RIGHT : integer;
  attribute C_BUSER_RIGHT of inst : label is 0;
  attribute C_BUSER_WIDTH : integer;
  attribute C_BUSER_WIDTH of inst : label is 0;
  attribute C_B_WIDTH : integer;
  attribute C_B_WIDTH of inst : label is 2;
  attribute C_FAMILY : string;
  attribute C_FAMILY of inst : label is "virtexuplus";
  attribute C_FIFO_AR_WIDTH : integer;
  attribute C_FIFO_AR_WIDTH of inst : label is 35;
  attribute C_FIFO_AW_WIDTH : integer;
  attribute C_FIFO_AW_WIDTH of inst : label is 35;
  attribute C_FIFO_B_WIDTH : integer;
  attribute C_FIFO_B_WIDTH of inst : label is 2;
  attribute C_FIFO_R_WIDTH : integer;
  attribute C_FIFO_R_WIDTH of inst : label is 34;
  attribute C_FIFO_W_WIDTH : integer;
  attribute C_FIFO_W_WIDTH of inst : label is 36;
  attribute C_M_AXI_ACLK_RATIO : integer;
  attribute C_M_AXI_ACLK_RATIO of inst : label is 2;
  attribute C_RDATA_RIGHT : integer;
  attribute C_RDATA_RIGHT of inst : label is 2;
  attribute C_RDATA_WIDTH : integer;
  attribute C_RDATA_WIDTH of inst : label is 32;
  attribute C_RID_RIGHT : integer;
  attribute C_RID_RIGHT of inst : label is 34;
  attribute C_RID_WIDTH : integer;
  attribute C_RID_WIDTH of inst : label is 0;
  attribute C_RLAST_RIGHT : integer;
  attribute C_RLAST_RIGHT of inst : label is 0;
  attribute C_RLAST_WIDTH : integer;
  attribute C_RLAST_WIDTH of inst : label is 0;
  attribute C_RRESP_RIGHT : integer;
  attribute C_RRESP_RIGHT of inst : label is 0;
  attribute C_RRESP_WIDTH : integer;
  attribute C_RRESP_WIDTH of inst : label is 2;
  attribute C_RUSER_RIGHT : integer;
  attribute C_RUSER_RIGHT of inst : label is 0;
  attribute C_RUSER_WIDTH : integer;
  attribute C_RUSER_WIDTH of inst : label is 0;
  attribute C_R_WIDTH : integer;
  attribute C_R_WIDTH of inst : label is 34;
  attribute C_SYNCHRONIZER_STAGE : integer;
  attribute C_SYNCHRONIZER_STAGE of inst : label is 3;
  attribute C_S_AXI_ACLK_RATIO : integer;
  attribute C_S_AXI_ACLK_RATIO of inst : label is 1;
  attribute C_WDATA_RIGHT : integer;
  attribute C_WDATA_RIGHT of inst : label is 4;
  attribute C_WDATA_WIDTH : integer;
  attribute C_WDATA_WIDTH of inst : label is 32;
  attribute C_WID_RIGHT : integer;
  attribute C_WID_RIGHT of inst : label is 36;
  attribute C_WID_WIDTH : integer;
  attribute C_WID_WIDTH of inst : label is 0;
  attribute C_WLAST_RIGHT : integer;
  attribute C_WLAST_RIGHT of inst : label is 0;
  attribute C_WLAST_WIDTH : integer;
  attribute C_WLAST_WIDTH of inst : label is 0;
  attribute C_WSTRB_RIGHT : integer;
  attribute C_WSTRB_RIGHT of inst : label is 0;
  attribute C_WSTRB_WIDTH : integer;
  attribute C_WSTRB_WIDTH of inst : label is 4;
  attribute C_WUSER_RIGHT : integer;
  attribute C_WUSER_RIGHT of inst : label is 0;
  attribute C_WUSER_WIDTH : integer;
  attribute C_WUSER_WIDTH of inst : label is 0;
  attribute C_W_WIDTH : integer;
  attribute C_W_WIDTH of inst : label is 36;
  attribute DowngradeIPIdentifiedWarnings of inst : label is "yes";
  attribute P_ACLK_RATIO : integer;
  attribute P_ACLK_RATIO of inst : label is 2;
  attribute P_AXI3 : integer;
  attribute P_AXI3 of inst : label is 1;
  attribute P_AXI4 : integer;
  attribute P_AXI4 of inst : label is 0;
  attribute P_AXILITE : integer;
  attribute P_AXILITE of inst : label is 2;
  attribute P_FULLY_REG : integer;
  attribute P_FULLY_REG of inst : label is 1;
  attribute P_LIGHT_WT : integer;
  attribute P_LIGHT_WT of inst : label is 0;
  attribute P_LUTRAM_ASYNC : integer;
  attribute P_LUTRAM_ASYNC of inst : label is 12;
  attribute P_ROUNDING_OFFSET : integer;
  attribute P_ROUNDING_OFFSET of inst : label is 0;
  attribute P_SI_LT_MI : string;
  attribute P_SI_LT_MI of inst : label is "1'b1";
begin
inst: entity work.axi_clock_converter_oclnew_axi_clock_converter_v2_1_11_axi_clock_converter
     port map (
      m_axi_aclk => m_axi_aclk,
      m_axi_araddr(31 downto 0) => m_axi_araddr(31 downto 0),
      m_axi_arburst(1 downto 0) => NLW_inst_m_axi_arburst_UNCONNECTED(1 downto 0),
      m_axi_arcache(3 downto 0) => NLW_inst_m_axi_arcache_UNCONNECTED(3 downto 0),
      m_axi_aresetn => m_axi_aresetn,
      m_axi_arid(0) => NLW_inst_m_axi_arid_UNCONNECTED(0),
      m_axi_arlen(7 downto 0) => NLW_inst_m_axi_arlen_UNCONNECTED(7 downto 0),
      m_axi_arlock(0) => NLW_inst_m_axi_arlock_UNCONNECTED(0),
      m_axi_arprot(2 downto 0) => m_axi_arprot(2 downto 0),
      m_axi_arqos(3 downto 0) => NLW_inst_m_axi_arqos_UNCONNECTED(3 downto 0),
      m_axi_arready => m_axi_arready,
      m_axi_arregion(3 downto 0) => NLW_inst_m_axi_arregion_UNCONNECTED(3 downto 0),
      m_axi_arsize(2 downto 0) => NLW_inst_m_axi_arsize_UNCONNECTED(2 downto 0),
      m_axi_aruser(0) => NLW_inst_m_axi_aruser_UNCONNECTED(0),
      m_axi_arvalid => m_axi_arvalid,
      m_axi_awaddr(31 downto 0) => m_axi_awaddr(31 downto 0),
      m_axi_awburst(1 downto 0) => NLW_inst_m_axi_awburst_UNCONNECTED(1 downto 0),
      m_axi_awcache(3 downto 0) => NLW_inst_m_axi_awcache_UNCONNECTED(3 downto 0),
      m_axi_awid(0) => NLW_inst_m_axi_awid_UNCONNECTED(0),
      m_axi_awlen(7 downto 0) => NLW_inst_m_axi_awlen_UNCONNECTED(7 downto 0),
      m_axi_awlock(0) => NLW_inst_m_axi_awlock_UNCONNECTED(0),
      m_axi_awprot(2 downto 0) => m_axi_awprot(2 downto 0),
      m_axi_awqos(3 downto 0) => NLW_inst_m_axi_awqos_UNCONNECTED(3 downto 0),
      m_axi_awready => m_axi_awready,
      m_axi_awregion(3 downto 0) => NLW_inst_m_axi_awregion_UNCONNECTED(3 downto 0),
      m_axi_awsize(2 downto 0) => NLW_inst_m_axi_awsize_UNCONNECTED(2 downto 0),
      m_axi_awuser(0) => NLW_inst_m_axi_awuser_UNCONNECTED(0),
      m_axi_awvalid => m_axi_awvalid,
      m_axi_bid(0) => '0',
      m_axi_bready => m_axi_bready,
      m_axi_bresp(1 downto 0) => m_axi_bresp(1 downto 0),
      m_axi_buser(0) => '0',
      m_axi_bvalid => m_axi_bvalid,
      m_axi_rdata(31 downto 0) => m_axi_rdata(31 downto 0),
      m_axi_rid(0) => '0',
      m_axi_rlast => '1',
      m_axi_rready => m_axi_rready,
      m_axi_rresp(1 downto 0) => m_axi_rresp(1 downto 0),
      m_axi_ruser(0) => '0',
      m_axi_rvalid => m_axi_rvalid,
      m_axi_wdata(31 downto 0) => m_axi_wdata(31 downto 0),
      m_axi_wid(0) => NLW_inst_m_axi_wid_UNCONNECTED(0),
      m_axi_wlast => NLW_inst_m_axi_wlast_UNCONNECTED,
      m_axi_wready => m_axi_wready,
      m_axi_wstrb(3 downto 0) => m_axi_wstrb(3 downto 0),
      m_axi_wuser(0) => NLW_inst_m_axi_wuser_UNCONNECTED(0),
      m_axi_wvalid => m_axi_wvalid,
      s_axi_aclk => s_axi_aclk,
      s_axi_araddr(31 downto 0) => s_axi_araddr(31 downto 0),
      s_axi_arburst(1 downto 0) => B"01",
      s_axi_arcache(3 downto 0) => B"0000",
      s_axi_aresetn => s_axi_aresetn,
      s_axi_arid(0) => '0',
      s_axi_arlen(7 downto 0) => B"00000000",
      s_axi_arlock(0) => '0',
      s_axi_arprot(2 downto 0) => s_axi_arprot(2 downto 0),
      s_axi_arqos(3 downto 0) => B"0000",
      s_axi_arready => s_axi_arready,
      s_axi_arregion(3 downto 0) => B"0000",
      s_axi_arsize(2 downto 0) => B"000",
      s_axi_aruser(0) => '0',
      s_axi_arvalid => s_axi_arvalid,
      s_axi_awaddr(31 downto 0) => s_axi_awaddr(31 downto 0),
      s_axi_awburst(1 downto 0) => B"01",
      s_axi_awcache(3 downto 0) => B"0000",
      s_axi_awid(0) => '0',
      s_axi_awlen(7 downto 0) => B"00000000",
      s_axi_awlock(0) => '0',
      s_axi_awprot(2 downto 0) => s_axi_awprot(2 downto 0),
      s_axi_awqos(3 downto 0) => B"0000",
      s_axi_awready => s_axi_awready,
      s_axi_awregion(3 downto 0) => B"0000",
      s_axi_awsize(2 downto 0) => B"000",
      s_axi_awuser(0) => '0',
      s_axi_awvalid => s_axi_awvalid,
      s_axi_bid(0) => NLW_inst_s_axi_bid_UNCONNECTED(0),
      s_axi_bready => s_axi_bready,
      s_axi_bresp(1 downto 0) => s_axi_bresp(1 downto 0),
      s_axi_buser(0) => NLW_inst_s_axi_buser_UNCONNECTED(0),
      s_axi_bvalid => s_axi_bvalid,
      s_axi_rdata(31 downto 0) => s_axi_rdata(31 downto 0),
      s_axi_rid(0) => NLW_inst_s_axi_rid_UNCONNECTED(0),
      s_axi_rlast => NLW_inst_s_axi_rlast_UNCONNECTED,
      s_axi_rready => s_axi_rready,
      s_axi_rresp(1 downto 0) => s_axi_rresp(1 downto 0),
      s_axi_ruser(0) => NLW_inst_s_axi_ruser_UNCONNECTED(0),
      s_axi_rvalid => s_axi_rvalid,
      s_axi_wdata(31 downto 0) => s_axi_wdata(31 downto 0),
      s_axi_wid(0) => '0',
      s_axi_wlast => '1',
      s_axi_wready => s_axi_wready,
      s_axi_wstrb(3 downto 0) => s_axi_wstrb(3 downto 0),
      s_axi_wuser(0) => '0',
      s_axi_wvalid => s_axi_wvalid
    );
end STRUCTURE;
