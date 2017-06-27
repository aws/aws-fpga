/******************************************************************************
// (c) Copyright 2013 - 2014 Xilinx, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of Xilinx, Inc. and is protected under U.S. and
// international copyright and other intellectual property
// laws.
//
// DISCLAIMER
// This disclaimer is not a license and does not grant any
// rights to the materials distributed herewith. Except as
// otherwise provided in a valid license issued to you by
// Xilinx, and to the maximum extent permitted by applicable
// law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// (2) Xilinx shall not be liable (whether in contract or tort,
// including negligence, or under any other theory of
// liability) for any loss or damage of any kind or nature
// related to, arising under or in connection with these
// materials, including for any direct, or any indirect,
// special, incidental, or consequential loss or damage
// (including loss of data, profits, goodwill, or any type of
// loss or damage suffered as a result of any action brought
// by a third party) even if such damage or loss was
// reasonably foreseeable or Xilinx had been advised of the
// possibility of the same.
//
// CRITICAL APPLICATIONS
// Xilinx products are not designed or intended to be fail-
// safe, or for use in any application requiring fail-safe
// performance, such as life-support or safety devices or
// systems, Class III medical devices, nuclear facilities,
// applications related to the deployment of airbags, or any
// other applications that could lead to death, personal
// injury, or severe property or environmental damage
// (individually and collectively, "Critical
// Applications"). Customer assumes the sole risk and
// liability of any use of Xilinx products in Critical
// Applications, subject only to applicable laws and
// regulations governing limitations on product liability.
//
// THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// PART OF THIS FILE AT ALL TIMES.
******************************************************************************/
//   ____  ____
//  /   /\/   /
// /___/  \  /    Vendor             : Xilinx
// \   \   \/     Version            : 1.0
//  \   \         Application        : MIG
//  /   /         Filename           : ddr4_core_phy_ddr4.sv
// /___/   /\     Date Last Modified : $Date: 2017/02/27 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4_SDRAM
// Purpose          :
//                   Phy module
// Reference        :
// Revision History :
//*****************************************************************************


`timescale 1ps/1ps
`ifdef MODEL_TECH
    `ifndef CALIB_SIM
       `define SIMULATION
     `endif
`elsif INCA
    `ifndef CALIB_SIM
       `define SIMULATION
     `endif
`elsif VCS
    `ifndef CALIB_SIM
       `define SIMULATION
     `endif
`elsif XILINX_SIMULATOR
    `ifndef CALIB_SIM
       `define SIMULATION
     `endif
`endif

module ddr4_core_phy_ddr4 #
  (
    parameter         PING_PONG_PHY        = 1
   ,parameter integer ADDR_WIDTH           = 17
   ,parameter integer BANK_WIDTH           = 2
   ,parameter integer BANK_GROUP_WIDTH     = 2
   ,parameter integer LR_WIDTH             = 1
   ,parameter integer CK_WIDTH             = 1
   ,parameter integer CKE_WIDTH            = 1
   ,parameter integer COL_WIDTH            = 10
   ,parameter integer CS_WIDTH             = 1
   ,parameter integer ODT_WIDTH            = 1
   ,parameter         DRAM_TYPE            = "DDR4"
   ,parameter integer DQ_WIDTH             = 72
   ,parameter integer DQS_WIDTH            = 18
   ,parameter integer DM_WIDTH             = 9
   ,parameter         C_FAMILY             = "virtexuplus"

   ,parameter         tCK                  = 937
   ,parameter real    TCQ                  = 100

   ,parameter         USE_DYNAMIC_DCI      = 1
   ,parameter         RANKS                = 1
   ,parameter         nCK_PER_CLK          = 4

   ,parameter         SYSCLK_TYPE          = "DIFFERENTIAL"
                                // input clock type
   
   ,parameter         BACKBONE_ROUTE       = "TRUE"
   ,parameter         PLL_WIDTH            = 3
   ,parameter         CLKOUTPHY_MODE       = "VCO_2X"

   ,parameter         SIM_DEVICE           = "ULTRASCALE_PLUS"
   ,parameter integer BYTES                = 12
   ,parameter integer DBYTES               = 9
   ,parameter [39*BYTES-1:0] IOBTYPE       = {                                                                                   39'b000_011_011_011_011_111_111_011_011_011_011_111_111,                                                                                  39'b000_011_011_011_011_111_111_011_011_011_011_111_111,                                                                                  39'b000_011_011_011_011_111_111_011_011_011_011_111_111,                                                                                  39'b000_011_011_011_011_111_111_011_011_011_011_111_111,                                                                                  39'b000_011_011_011_011_111_111_011_011_011_011_111_111,                                                                                  39'b000_011_011_011_011_111_111_011_011_011_011_111_111,                                                                                  39'b000_011_011_011_011_111_111_011_011_011_011_111_111,                                                                                  39'b000_011_011_011_011_111_111_011_011_011_011_111_111,                                                                                  39'b000_011_011_011_011_111_111_011_011_011_011_111_111,                                                                                  39'b000_000_000_000_000_000_000_001_000_001_001_001_001,                                                                                  39'b001_001_001_000_000_001_001_001_001_001_001_001_001,                                                                                  39'b000_001_001_001_001_001_001_001_001_001_001_001_001   }
   ,parameter                PLLCLK_SRC         = 1'b0
   ,parameter [1:0]          DIV_MODE           = 2'b00
   ,parameter                DATA_WIDTH         = 8
   ,parameter [1:0]          CTRL_CLK           = 2'b11
    
   ,parameter [15*BYTES-1:0] INIT               = {                            15'b111111111111111,                                                                                15'b111111111111111,                                                                                15'b111111111111111,                                                                                15'b111111111111111,                                                                                15'b111111111111111,                                                                                15'b111111111111111,                                                                                15'b111111111111111,                                                                                15'b111111111111111,                                                                                15'b111111111111111,                                                                                15'b111111111111101,                                                                                15'b111111111111111,                                                                                15'b111111111111111                                                                                }
   ,parameter [BYTES-1:0]    PING_PONG_CH1_BYTES_MAP = 12'b000000000000
   ,parameter [15*BYTES-1:0] RX_DATA_TYPE       = { 15'b011110_11_11110_11,                                                                                15'b011110_11_11110_11,                                                                                15'b011110_11_11110_11,                                                                                15'b011110_11_11110_11,                                                                                15'b011110_11_11110_11,                                                                                15'b011110_11_11110_11,                                                                                15'b011110_11_11110_11,                                                                                15'b011110_11_11110_11,                                                                                15'b011110_11_11110_11,                                                                                15'b000000_00_10111_11,                                                                                15'b111001_11_11111_11,                                                                                15'b011111_11_11111_11                                                                                }
   ,parameter [13*BYTES-1:0] TX_OUTPUT_PHASE_90 = { 13'b0000011000011,                                                                                13'b0000011000011,                                                                                13'b0000011000011,                                                                                13'b0000011000011,                                                                                13'b0000011000011,                                                                                13'b0000011000011,                                                                                13'b0000011000011,                                                                                13'b0000011000011,                                                                                13'b0000011000011,                                                                                13'b0000000101111,                                                                                13'b1110011111111,                                                                                13'b0111111111111                                                                                }
   ,parameter [13*BYTES-1:0] RXTX_BITSLICE_EN   = {13'b0111101111101,                                                                                13'b0111101111101,                                                                                13'b0111101111101,                                                                                13'b0111101111101,                                                                                13'b0111101111101,                                                                                13'b0111101111101,                                                                                13'b0111101111101,                                                                                13'b0111101111101,                                                                                13'b0111101111101,                                                                                13'b0000000101111,                                                                                13'b1110011111111,                                                                                13'b0111111111111                                                                                }
   ,parameter [13*BYTES-1:0] NATIVE_ODELAY_BYPASS = {(13*BYTES){1'b0}}
   ,parameter [2*BYTES-1:0]  EN_OTHER_PCLK      = {12{2'b00}} 
   ,parameter [2*BYTES-1:0]  EN_OTHER_NCLK      = {12{2'b00}} 
   ,parameter [2*BYTES-1:0]  RX_CLK_PHASE_P     = {{9{2'b11}}, {3{2'b00}}} 
   ,parameter [2*BYTES-1:0]  RX_CLK_PHASE_N     = {{9{2'b11}}, {3{2'b00}}} 
   ,parameter [2*BYTES-1:0]  TX_GATING          = {{9{2'b11}}, {3{2'b00}}} 
   ,parameter [2*BYTES-1:0]  RX_GATING          = {{9{2'b11}}, {3{2'b00}}} 
   ,parameter [2*BYTES-1:0]  EN_DYN_ODLY_MODE   = {{9{2'b11}}, {3{2'b00}}} 
   ,parameter                BANK_TYPE          = "HP_IO"
   ,parameter [2*BYTES-1:0] IDLY_VT_TRACK       = (RANKS == 1)?{(2*BYTES){1'b1}}:
                                                                 {(2*BYTES){1'b0}}
   ,parameter [2*BYTES-1:0] ODLY_VT_TRACK       = (RANKS == 1)?{(2*BYTES){1'b1}}:
                                                                 {(2*BYTES){1'b0}}
   ,parameter [2*BYTES-1:0] QDLY_VT_TRACK       = {(2*BYTES){1'b1}}

  `ifdef SIMULATION
   ,parameter                SIM_MODE           = "BFM"
   ,parameter [2*BYTES-1:0]  SELF_CALIBRATE     = {(2*BYTES){1'b0}}
  `else
   ,parameter                SIM_MODE           = "FULL"
   ,parameter [2*BYTES-1:0]  SELF_CALIBRATE     = {12{2'b11}} 
  `endif
  )
  (
    input                                           sys_clk_p
   ,input                                           sys_clk_n
   ,input                                           mmcm_lock
   ,input                                           pllGate
   ,input                                           div_clk
   ,input                                           div_clk_rst
   ,input                                           riu_clk
   ,input                                           riu_clk_rst
   ,output                                          pll_lock
   ,output                                          sys_clk_in
   ,output                                          mmcm_clk_in

   // iob<>DDR4 signals
   ,output                                          ddr4_act_n
   ,output [ADDR_WIDTH-1:0]                         ddr4_adr
   ,output [BANK_WIDTH-1:0]                         ddr4_ba
   ,output [BANK_GROUP_WIDTH-1:0]                   ddr4_bg
   ,output [LR_WIDTH-1:0]                           ddr4_c
   ,output                                          ddr4_parity
   ,output [PING_PONG_PHY*CKE_WIDTH-1:0]            ddr4_cke
   ,output [PING_PONG_PHY*ODT_WIDTH-1:0]            ddr4_odt
   ,output [PING_PONG_PHY*CS_WIDTH-1:0]             ddr4_cs_n
   ,output [CK_WIDTH-1:0]                           ddr4_ck_t
   ,output [CK_WIDTH-1:0]                           ddr4_ck_c
   ,output                                          ddr4_reset_n
   ,inout  [DM_WIDTH-1:0]                           ddr4_dm_dbi_n
   ,inout  [DQ_WIDTH-1:0]                           ddr4_dq
   ,inout  [DQS_WIDTH-1:0]                          ddr4_dqs_c
   ,inout  [DQS_WIDTH-1:0]                          ddr4_dqs_t

   // phy<>cal signals

   ,input     [CK_WIDTH*8-1:0] mcal_CK_t
   ,input     [CK_WIDTH*8-1:0] mcal_CK_c
   ,input                [7:0] mcal_ACT_n
   ,input                [7:0] mcal_CAS_n
   ,input                [7:0] mcal_RAS_n
   ,input                [7:0] mcal_WE_n
   ,input        [ADDR_WIDTH*8-1:0] mcal_ADR
   ,input       [BANK_WIDTH*8-1:0] mcal_BA
   ,input       [BANK_GROUP_WIDTH*8-1:0] mcal_BG
   ,input	[LR_WIDTH*8-1:0] mcal_C
   ,input       [PING_PONG_PHY*CKE_WIDTH*8-1:0] mcal_CKE
   ,input       [PING_PONG_PHY*CS_WIDTH*8-1:0] mcal_CS_n
   ,input      [PING_PONG_PHY*ODT_WIDTH*8-1:0] mcal_ODT
   ,input                [7:0] mcal_PAR

   ,input       [DBYTES*8-1:0] ch0_mcal_DMOut_n
   ,input     [DBYTES*8*8-1:0] ch0_mcal_DQOut
   ,input                [7:0] ch0_mcal_DQSOut
   ,input        [DBYTES*4-1:0] ch0_mcal_clb2phy_rden_upp
   ,input        [DBYTES*4-1:0] ch0_mcal_clb2phy_rden_low
   ,input     [DBYTES*4-1:0] ch0_mcal_clb2phy_wrcs0_upp
   ,input     [DBYTES*4-1:0] ch0_mcal_clb2phy_wrcs1_upp
   ,input     [DBYTES*4-1:0] ch0_mcal_clb2phy_wrcs0_low
   ,input     [DBYTES*4-1:0] ch0_mcal_clb2phy_wrcs1_low
   ,input     [DBYTES*4-1:0] ch0_mcal_clb2phy_rdcs0_upp
   ,input     [DBYTES*4-1:0] ch0_mcal_clb2phy_rdcs1_upp
   ,input     [DBYTES*4-1:0] ch0_mcal_clb2phy_rdcs0_low
   ,input     [DBYTES*4-1:0] ch0_mcal_clb2phy_rdcs1_low
   ,input        [DBYTES*7-1:0] ch0_mcal_clb2phy_odt_upp
   ,input        [DBYTES*7-1:0] ch0_mcal_clb2phy_odt_low
   ,input     [DBYTES*4-1:0] ch0_mcal_clb2phy_t_b_low
   ,input     [DBYTES*4-1:0] ch0_mcal_clb2phy_t_b_upp

   ,input        [DBYTES*7-1:0] mcal_rd_vref_value

   ,input       [DBYTES*8-1:0] ch1_mcal_DMOut_n
   ,input     [DBYTES*8*8-1:0] ch1_mcal_DQOut
   ,input                [7:0] ch1_mcal_DQSOut
   ,input        [DBYTES*4-1:0] ch1_mcal_clb2phy_rden_upp
   ,input        [DBYTES*4-1:0] ch1_mcal_clb2phy_rden_low
   ,input     [DBYTES*4-1:0] ch1_mcal_clb2phy_wrcs0_upp
   ,input     [DBYTES*4-1:0] ch1_mcal_clb2phy_wrcs1_upp
   ,input     [DBYTES*4-1:0] ch1_mcal_clb2phy_wrcs0_low
   ,input     [DBYTES*4-1:0] ch1_mcal_clb2phy_wrcs1_low
   ,input     [DBYTES*4-1:0] ch1_mcal_clb2phy_rdcs0_upp
   ,input     [DBYTES*4-1:0] ch1_mcal_clb2phy_rdcs1_upp
   ,input     [DBYTES*4-1:0] ch1_mcal_clb2phy_rdcs0_low
   ,input     [DBYTES*4-1:0] ch1_mcal_clb2phy_rdcs1_low
   ,input        [DBYTES*7-1:0] ch1_mcal_clb2phy_odt_upp
   ,input        [DBYTES*7-1:0] ch1_mcal_clb2phy_odt_low
   ,input     [DBYTES*4-1:0] ch1_mcal_clb2phy_t_b_low
   ,input     [DBYTES*4-1:0] ch1_mcal_clb2phy_t_b_upp

   ,input  [DBYTES*13-1:0] ch0_mcal_clb2phy_fifo_rden	// MAN - unused input (could be needed for DIABLO)
   ,input  [DBYTES*13-1:0] ch1_mcal_clb2phy_fifo_rden	// MAN - unused input (could be needed for DIABLO)

   ,output   [DBYTES*8-1:0] mcal_DMIn_n
   ,output [DBYTES*8*8-1:0] mcal_DQIn

   ,output reg	phy_ready_riuclk
   ,output reg	bisc_complete_riuclk
   ,output [7:0] phy2clb_rd_dq_bits
   ,input [8:0] bisc_byte

   ,input [7:0] cal_RESET_n
   ,input	en_vtc_riuclk
   ,input	ub_rst_out_riuclk
// PHY <> cal RIU
   ,output reg [15:0] riu2clb_vld_read_data
   ,output [7:0] riu_nibble_8
   ,output reg	[5:0] riu_addr_cal
   ,output [20-1:0] riu2clb_valid_riuclk // max number of bytes possible 
   
   ,input io_addr_strobe_clb2riu_riuclk
   ,input [31:0] io_address_riuclk
   ,input [31:0] io_write_data_riuclk
   ,input io_write_strobe_riuclk

   ,output [19:0] phy2clb_fixdly_rdy_low_riuclk
   ,output [19:0] phy2clb_fixdly_rdy_upp_riuclk
   ,output [19:0] phy2clb_phy_rdy_upp_riuclk
   ,output [19:0] phy2clb_phy_rdy_low_riuclk

   //Debug Port
   ,output wire [511:0]                             dbg_bus
   );

// localparam   RTL_VERSION  = 2;
localparam [BYTES-1:0]  PING_PONG_CH1_BYTES  = {{BYTES-DBYTES{1'b0}},{DBYTES/2{1'b1}},{DBYTES/2{1'b0}}};
localparam [DBYTES-1:0] PING_PONG_CH1_DBYTES = {{(DBYTES-(DBYTES/2))*2{1'b0}},{DBYTES/2{1'b1}},{DBYTES/2{1'b0}}};

localparam   TBYTE_CTL                                                     = "TBYTE_IN";
localparam   DELAY_TYPE                                                    = "FIXED";
localparam   DELAY_FORMAT                                                  = "TIME";
localparam   UPDATE_MODE                                                   = "ASYNC";
localparam  [13*BYTES-1:0] FIFO_SYNC_MODE                                  = {(13*BYTES){1'b0}};
localparam  [1:0] REFCLK_SRC                                               = 2'b00;
localparam  [45*BYTES-1:0] GCLK_SRC                                        = {(45*BYTES){1'b0}};
localparam  [2*BYTES-1:0] TRI_OUTPUT_PHASE_90                              = {(BYTES*2){1'b1}};
localparam  [2*BYTES-1:0] SERIAL_MODE                                      = {BYTES{2'b00}};
localparam  [2*BYTES-1:0] INV_RXCLK                                        = {BYTES{2'b00}};
localparam  [2*BYTES-1:0] EN_CLK_TO_EXT_NORTH                              = {BYTES{2'b00}};
localparam  [2*BYTES-1:0] EN_CLK_TO_EXT_SOUTH                              = {BYTES{2'b00}};
localparam  integer RX_DELAY_VAL             [12:0]                        = '{0,0,0,0,0,0,0,0,0,0,0,0,0};
localparam  integer TX_DELAY_VAL             [12:0]                        = '{0,0,0,0,0,0,0,0,0,0,0,0,0};
localparam  integer TRI_DELAY_VAL             [1:0]                        = '{0, 0};
localparam  integer READ_IDLE_COUNT           [1:0]                        = '{31, 31};
localparam  integer ROUNDING_FACTOR           [1:0]                        = '{16, 16};
localparam  real REFCLK_FREQ                                               = 300.0;
localparam  [13*BYTES-1:0]  DCI_SRC                                        = {(BYTES*13){1'b1}};
localparam  [2*BYTES-1:0] RXGATE_EXTEND                                    = {(2*BYTES){1'b0}};

localparam SYNC_MTBF = 2; // Synchronizer Depth based on MTBF

  function integer clogb2 (input integer size);
    begin
      size = size - 1;
      for (clogb2=1; size>1; clogb2=clogb2+1)
        size = size >> 1;
    end
  endfunction

localparam         DQS_BIAS                        = "FALSE";

  wire sys_clk_i;

// mcCal<>phy signals

wire            [7:0] mcal_nc [249:0];

wire  [DBYTES*13-1:0] phy2clb_fifo_empty; // MAN - currently not used (could be needed for Diablo fine tuning later)
wire          [249:0] phy2clb_fifo_empty_nc;

wire    [BYTES*2-1:0] phy2rclk_ss_divclk;

wire    [BYTES*8-1:0] phy2clb_rd_dq0;
wire    [BYTES*8-1:0] phy2clb_rd_dq1;
wire    [BYTES*8-1:0] phy2clb_rd_dq2;
wire    [BYTES*8-1:0] phy2clb_rd_dq3;
wire    [BYTES*8-1:0] phy2clb_rd_dq4;
wire    [BYTES*8-1:0] phy2clb_rd_dq5;
wire    [BYTES*8-1:0] phy2clb_rd_dq6;
wire    [BYTES*8-1:0] phy2clb_rd_dq7;
wire    [BYTES*8-1:0] phy2clb_rd_dq8;
wire    [BYTES*8-1:0] phy2clb_rd_dq9;
wire    [BYTES*8-1:0] phy2clb_rd_dq10;
wire    [BYTES*8-1:0] phy2clb_rd_dq11;
wire    [BYTES*8-1:0] phy2clb_rd_dq12;

wire  [BYTES*117-1:0] phy2clb_idelay_cntvalueout;
wire  [BYTES*117-1:0] phy2clb_odelay_cntvalueout;
wire   [BYTES*18-1:0] phy2clb_tristate_odelay_cntvalueout;

wire    [BYTES*1-1:0] phy2clb_fixdly_rdy_upp;
wire    [BYTES*1-1:0] phy2clb_fixdly_rdy_upp_in_riuclk;
wire	[BYTES*1-1:0] phy2clb_fixdly_rdy_low;
wire    [BYTES*1-1:0] phy2clb_fixdly_rdy_low_in_riuclk;

reg	[BYTES*1-1:0] phy2clb_fixdly_rdy_low_riuclk_int;
reg	[BYTES*1-1:0] phy2clb_fixdly_rdy_upp_riuclk_int;
reg	[BYTES*1-1:0] phy2clb_phy_rdy_upp_riuclk_int;
reg	[BYTES*1-1:0] phy2clb_phy_rdy_low_riuclk_int;

assign phy2clb_fixdly_rdy_low_riuclk = {{20-BYTES{1'b1}},phy2clb_fixdly_rdy_low_riuclk_int};
assign phy2clb_fixdly_rdy_upp_riuclk = {{20-BYTES{1'b1}},phy2clb_fixdly_rdy_upp_riuclk_int};
assign phy2clb_phy_rdy_low_riuclk = {{20-BYTES{1'b1}},phy2clb_phy_rdy_low_riuclk_int};
assign phy2clb_phy_rdy_upp_riuclk = {{20-BYTES{1'b1}},phy2clb_phy_rdy_upp_riuclk_int};

(* dont_touch = "true" *) reg		clb2phy_t_b_addr_riuclk;
(* dont_touch = "true" *) reg	[3:0]	clb2phy_t_b_addr;
(* keep = "true", ASYNC_REG = "TRUE" *) reg	[1:0]	clb2phy_t_b_addr_i;
wire    [BYTES*1-1:0] clk_to_ext_north_upp;
wire    [BYTES*1-1:0] clk_to_ext_south_upp;
wire    [BYTES*1-1:0] clk_to_ext_north_low;
wire    [BYTES*1-1:0] clk_to_ext_south_low;

wire    [BYTES*1-1:0] phy2clb_phy_rdy_upp;
wire    [BYTES*1-1:0] phy2clb_phy_rdy_upp_in_riuclk;
wire    [BYTES*1-1:0] phy2clb_phy_rdy_low;
wire    [BYTES*1-1:0] phy2clb_phy_rdy_low_in_riuclk;

wire   [BYTES*13-1:0] clb2phy_fifo_clk;
wire    [BYTES*1-1:0] clb2phy_ctrl_clk_upp;
wire    [BYTES*1-1:0] clb2phy_ctrl_clk_low;
wire    [BYTES*1-1:0] clb2phy_ref_clk_upp = { BYTES { 1'b0 } };
wire    [BYTES*1-1:0] clb2phy_ref_clk_low = { BYTES { 1'b0 } };
wire    [BYTES*1-1:0] clb2phy_ctrl_rst_upp_riuclk;
wire    [BYTES*1-1:0] clb2phy_ctrl_rst_low_riuclk;
wire    [BYTES*2-1:0] clb2phy_txbit_tri_rst;
wire   [BYTES*13-1:0] clb2phy_txbit_rst;
wire   [BYTES*13-1:0] clb2phy_rxbit_rst;

(* keep = "TRUE" *) reg riu_clk_rst_r1;

always @(posedge riu_clk)
  riu_clk_rst_r1 <= riu_clk_rst;

assign clb2phy_ctrl_clk_low = {BYTES{riu_clk}};
assign clb2phy_ctrl_clk_upp = {BYTES{riu_clk}};
assign clb2phy_ctrl_rst_low_riuclk = {BYTES{riu_clk_rst_r1}};
assign clb2phy_ctrl_rst_upp_riuclk = {BYTES{riu_clk_rst_r1}};

// ddrMap IO

reg	[BYTES*6-1:0] clb2riu_addr;
reg	[BYTES*16-1:0] clb2riu_wr_data;
reg	[BYTES*1-1:0] clb2riu_wr_en;
reg	[BYTES*1-1:0] clb2riu_nibble_sel_upp;
reg	[BYTES*1-1:0] clb2riu_nibble_sel_low;

wire   [BYTES*13-1:0] clb2phy_idelay_rst;
wire   [BYTES*13-1:0] clb2phy_odelay_rst;
wire   [BYTES*13-1:0] clb2phy_tristate_odelay_rst;

wire    [BYTES*4-1:0] clb2phy_wrcs0_upp;
wire    [BYTES*4-1:0] clb2phy_wrcs1_upp;
wire    [BYTES*4-1:0] clb2phy_wrcs0_low;
wire    [BYTES*4-1:0] clb2phy_wrcs1_low;
wire    [BYTES*4-1:0] clb2phy_rdcs0_upp;
wire    [BYTES*4-1:0] clb2phy_rdcs1_upp;
wire    [BYTES*4-1:0] clb2phy_rdcs0_low;
wire    [BYTES*4-1:0] clb2phy_rdcs1_low;

wire    [BYTES*1-1:0] clk_from_ext_low;
wire    [BYTES*1-1:0] clk_from_ext_upp;

wire    [BYTES*1-1:0] clb2phy_dlyctl_en_vtc_upp_riuclk;
wire    [BYTES*1-1:0] clb2phy_dlyctl_en_vtc_low_riuclk;

wire    [BYTES*7-1:0] clb2phy_odt_upp;
wire    [BYTES*7-1:0] clb2phy_odt_low;

wire [BYTES-1:0] self_calibrate_low;
wire [BYTES-1:0] self_calibrate_upp;

(* keep = "TRUE" *) reg div_clk_rst_r1;

assign clb2phy_idelay_rst = {(BYTES*13){div_clk_rst_r1}};
assign clb2phy_odelay_rst = {(BYTES*13){div_clk_rst_r1}};
assign clb2phy_rxbit_rst = {(BYTES*13){div_clk_rst_r1}};
assign clb2phy_tristate_odelay_rst = {(BYTES*13){div_clk_rst_r1}};
assign clb2phy_txbit_rst = {(BYTES*13){div_clk_rst_r1}};
assign clb2phy_txbit_tri_rst = {(BYTES*2){div_clk_rst_r1}};
assign clb2phy_fifo_clk = {(BYTES*13){div_clk}};

//added for K2 BISC workaround
wire [13*BYTES*8-1:0] phy2clb_rd_dq;
wire    [BYTES*1-1:0] phy2clb_master_pd_out_upp;
wire    [BYTES*1-1:0] phy2clb_master_pd_out_low;

// phy<>iob signals
wire [BYTES*13-1:0] phy2iob_q_out_byte;
wire [BYTES*13-1:0] phy2iob_odt_out_byte;
wire [BYTES*13-1:0] phy2iob_t;
wire [BYTES*13-1:0] iob2phy_d_in_byte;
wire        [249:0] ddr4_nc;

wire        DDR4_AP = ddr4_adr[10];
wire [23:0] DDR4_BURST = ddr4_adr[12] ? "BL8" : "BC4";
wire  [9:0] DDR4_COL = ddr4_adr[9:0];
reg  [31:0] cmdName;

// misc
wire [5:0] gclk_in = 6'b111111;

wire [PLL_WIDTH-1:0] pll_clk;

//*****************************************************************************************
// Removal of Output buffer for ddr4_reset_n when partial reconfiguration enabled through TCL command 
//*****************************************************************************************
  assign ddr4_reset_n = cal_RESET_n[0];

wire fab_rst_sync;

wire   [BYTES*16-1:0] riu2clb_rd_data;
wire    [BYTES*1-1:0] riu2clb_valid;
assign riu2clb_valid_riuclk = {{20-BYTES{1'b1}},riu2clb_valid};

localparam NIBBLE_WIDTH = BYTES*2;
localparam NIBBLE_CNT_WIDTH = clogb2(NIBBLE_WIDTH);                         //nibble count (riu_nibble) width
reg [NIBBLE_CNT_WIDTH+1:0]   riu_nibble;             //mapped_nibble, 2MSBs are set for unknown io_address

// RIU decode logic
reg [BYTES*16-1:0] riu_read_data;
wire [BYTES*1-1:0]           riu_bytes;                      //riu_bytes cal from riu_nibble
  always @ (posedge riu_clk)
  begin
    clb2riu_addr <= #TCQ  {BYTES{riu_addr_cal}};
    clb2riu_wr_data <= #TCQ {BYTES{io_write_data_riuclk[15:0]}};
  end

  //Generate one hot riu_nibble_sel;
integer n;
generate
    always @ (posedge riu_clk)
    begin
      for (n = 0; n < BYTES; n = n + 1) begin: gen_riu_nibble_sel
        if (riu_clk_rst_r1) begin
          clb2riu_nibble_sel_low[n] <= #TCQ 1'b0;
          clb2riu_nibble_sel_upp[n] <= #TCQ 1'b0;
          clb2riu_wr_en[n]          <= #TCQ 1'b0;
        end else begin
          // valid only comes with a write. If wr_en is low then do not wait for valid for nibble_sel
          clb2riu_nibble_sel_low[n] <= #TCQ (2*n == riu_nibble) & io_addr_strobe_clb2riu_riuclk;
          clb2riu_nibble_sel_upp[n] <= #TCQ (2*n+1 == riu_nibble)& io_addr_strobe_clb2riu_riuclk;
          clb2riu_wr_en[n] <= #TCQ ((2*n == riu_nibble) | (2*n+1 == riu_nibble) ) & io_addr_strobe_clb2riu_riuclk & io_write_strobe_riuclk;
        end
      end
    end
endgenerate

  assign riu_bytes = riu_nibble[NIBBLE_CNT_WIDTH-1:1];
  assign riu_nibble_8 = {{riu_nibble[NIBBLE_CNT_WIDTH+1:NIBBLE_CNT_WIDTH]},{{6-NIBBLE_CNT_WIDTH}{1'b0}},riu_nibble[NIBBLE_CNT_WIDTH-1:0]};


  always @ (posedge riu_clk) begin
      riu2clb_vld_read_data <= #TCQ  riu_read_data[riu_bytes*16+:16];
      riu_read_data <= #TCQ  riu2clb_rd_data;
  end

// wait until riu write finished
  always @ (posedge riu_clk) begin
    phy2clb_fixdly_rdy_low_riuclk_int <= #TCQ phy2clb_fixdly_rdy_low_in_riuclk;
    phy2clb_fixdly_rdy_upp_riuclk_int <= #TCQ phy2clb_fixdly_rdy_upp_in_riuclk;
    phy2clb_phy_rdy_low_riuclk_int <= #TCQ phy2clb_phy_rdy_low_in_riuclk;
    phy2clb_phy_rdy_upp_riuclk_int <= #TCQ phy2clb_phy_rdy_upp_in_riuclk;
  end

// Determine which bitslices are running BISC and detect when they all finish
genvar byt;

generate
  for(byt = 0; byt < BYTES; byt = byt + 1) begin : self_calibrate
     assign self_calibrate_low[byt] = SELF_CALIBRATE[byt*2];
     assign self_calibrate_upp[byt] = SELF_CALIBRATE[byt*2+1];
  end
endgenerate

 // Initial BISC is complete, or disabled
  always @ (posedge riu_clk) begin
    bisc_complete_riuclk <= (&(phy2clb_fixdly_rdy_low_riuclk_int | (~self_calibrate_low))) &
                     (&(phy2clb_fixdly_rdy_upp_riuclk_int | (~self_calibrate_upp)));
    phy_ready_riuclk  <=    (&phy2clb_phy_rdy_upp_riuclk_int) && (&phy2clb_phy_rdy_low_riuclk_int);
  end

//added for K2 BISC workaround =================================================
//Put the mapped signals back into a regular bus
//assign phy2clb_rd_dq signals to the mapping generated from MIG
assign phy2clb_rd_dq0 = 'b0;
assign phy2clb_rd_dq1 = 'b0;
assign phy2clb_rd_dq2 = 'b0;
assign phy2clb_rd_dq3 = 'b0;
assign phy2clb_rd_dq4 = 'b0;
assign phy2clb_rd_dq5 = 'b0;
assign phy2clb_rd_dq6 = 'b0;
assign phy2clb_rd_dq7 = 'b0;
assign phy2clb_rd_dq8 = 'b0;
assign phy2clb_rd_dq9 = 'b0;
assign phy2clb_rd_dq10 = 'b0;
assign phy2clb_rd_dq11 = 'b0;
assign phy2clb_rd_dq12 = 'b0;

//We only need to check the results of rise0/fall0 but for now try to keep all
//signals. We remap all the bits so we can reference all values
//for a given bit together (bit0 - [7:0], bit 1 is [15:8], etc).
generate
genvar bisc_map;
  for (bisc_map = 0; bisc_map < BYTES; bisc_map++) begin
    assign phy2clb_rd_dq[13*bisc_map*8+:(13*8)] =
             {phy2clb_rd_dq12[bisc_map*8+:8],
              phy2clb_rd_dq11[bisc_map*8+:8],
              phy2clb_rd_dq10[bisc_map*8+:8],
              phy2clb_rd_dq9[bisc_map*8+:8],
              phy2clb_rd_dq8[bisc_map*8+:8],
              phy2clb_rd_dq7[bisc_map*8+:8],
              phy2clb_rd_dq6[bisc_map*8+:8],
              phy2clb_rd_dq5[bisc_map*8+:8],
              phy2clb_rd_dq4[bisc_map*8+:8],
              phy2clb_rd_dq3[bisc_map*8+:8],
              phy2clb_rd_dq2[bisc_map*8+:8],
              phy2clb_rd_dq1[bisc_map*8+:8],
              phy2clb_rd_dq0[bisc_map*8+:8]};
  end
endgenerate

  assign sys_clk_i = 1'b0;

  ddr4_phy_v2_2_0_pll #
    (
     .SYSCLK_TYPE           (SYSCLK_TYPE),
     .BACKBONE_ROUTE        (BACKBONE_ROUTE),
     .PLL_WIDTH             (PLL_WIDTH),
     .CLKOUTPHY_MODE        (CLKOUTPHY_MODE),
     .CLKIN_PERIOD_PLL      (tCK*nCK_PER_CLK),
     .nCK_PER_CLK           (nCK_PER_CLK),
     .C_FAMILY              (C_FAMILY),
     .TCQ                   (TCQ)
     )
  u_ddr4_phy_pll
    (
     .sys_clk_p       (sys_clk_p),
     .sys_clk_n       (sys_clk_n),
     .sys_clk_i       (sys_clk_i),
     .ub_rst_out      (ub_rst_out_riuclk),
     .mmcm_lock       (mmcm_lock),
     .div_clk         (div_clk),
     .div_clk_rst     (div_clk_rst_r1),
     .pllgate         (pllGate),
     .pll_clk         (pll_clk),
     .pll_lock        (pll_lock),
     .sys_clk_in      (sys_clk_in),
     .mmcm_clk_in     (mmcm_clk_in)
     );

ddr4_phy_v2_2_0_iob # (
    .BYTES          (BYTES)
   ,.IOBTYPE        (IOBTYPE)
   ,.DRAM_TYPE      (DRAM_TYPE)
   ,.DQS_BIAS       (DQS_BIAS)
   ,.BANK_TYPE      (BANK_TYPE)
   ,.USE_DYNAMIC_DCI(USE_DYNAMIC_DCI)
) u_ddr_iob (
    .phy2iob_q_out_byte   (phy2iob_q_out_byte)
   ,.phy2iob_odt_out_byte (phy2iob_odt_out_byte)
   ,.phy2iob_t            (phy2iob_t)
   ,.iob2phy_d_in_byte    (iob2phy_d_in_byte)

   // spyglass disable_block WRN_32
   `include "ddr4_core_phy_iobMapDDR4.vh"
   // spyglass enable_block WRN_32
);

  //*************************************************************************//
  //******************RIU address Map****************************************//
  //*************************************************************************//

  wire [27:0]                  io_address = io_address_riuclk;

  always @(*)
  begin
    casez(io_address)
      //DIRECT ACCESS to RIU
      28'h0001???: begin
        riu_addr_cal = io_address[5:0];
        riu_nibble = { 2'b00, io_address[NIBBLE_CNT_WIDTH+5:6] };
      end

      `include "ddr4_core_phy_riuMap.vh"

      default: begin
        riu_addr_cal = 6'h3f;
        riu_nibble = {2'b11,{NIBBLE_CNT_WIDTH{1'b0}}};
      end
    endcase
  end

//######################## Fabric Clock Domain ########################
  always @(posedge div_clk) begin
    div_clk_rst_r1    <= #TCQ div_clk_rst;
  end

   wire        [DBYTES*4-1:0] mcal_clb2phy_rden_upp;
   wire        [DBYTES*4-1:0] mcal_clb2phy_rden_low;
   wire     [DBYTES*4-1:0] mcal_clb2phy_wrcs0_upp;
   wire     [DBYTES*4-1:0] mcal_clb2phy_wrcs1_upp;
   wire     [DBYTES*4-1:0] mcal_clb2phy_wrcs0_low;
   wire     [DBYTES*4-1:0] mcal_clb2phy_wrcs1_low;
   wire     [DBYTES*4-1:0] mcal_clb2phy_rdcs0_upp;
   wire     [DBYTES*4-1:0] mcal_clb2phy_rdcs1_upp;
   wire     [DBYTES*4-1:0] mcal_clb2phy_rdcs0_low;
   wire     [DBYTES*4-1:0] mcal_clb2phy_rdcs1_low;
   wire        [DBYTES*7-1:0] mcal_clb2phy_odt_upp;
   wire        [DBYTES*7-1:0] mcal_clb2phy_odt_low;
   wire     [DBYTES*4-1:0] mcal_clb2phy_t_b_low;
   wire     [DBYTES*4-1:0] mcal_clb2phy_t_b_upp;

   wire       [DBYTES*8-1:0] mcal_DMOut_n;
   wire     [DBYTES*8*8-1:0] mcal_DQOut;
   wire                [7:0] mcal_DQSOut;

   wire  [DBYTES*13-1:0] mcal_clb2phy_fifo_rden;

generate
genvar ppp_map;
   for (ppp_map=0; ppp_map<DBYTES; ppp_map++) begin
      if ((PING_PONG_PHY > 1) && PING_PONG_CH1_BYTES[ppp_map]) begin
	 assign mcal_clb2phy_t_b_upp[ppp_map*4+:4]     = ch1_mcal_clb2phy_t_b_upp[ppp_map*4+:4];
	 assign mcal_clb2phy_t_b_low[ppp_map*4+:4]     = ch1_mcal_clb2phy_t_b_low[ppp_map*4+:4];
	 assign mcal_clb2phy_rden_upp[ppp_map*4+:4]    = ch1_mcal_clb2phy_rden_upp[ppp_map*4+:4]; 
	 assign mcal_clb2phy_rden_low[ppp_map*4+:4]    = ch1_mcal_clb2phy_rden_low[ppp_map*4+:4]; 
	 assign mcal_clb2phy_wrcs0_upp[ppp_map*4+:4]   = ch1_mcal_clb2phy_wrcs0_upp[ppp_map*4+:4];
	 assign mcal_clb2phy_wrcs1_upp[ppp_map*4+:4]   = ch1_mcal_clb2phy_wrcs1_upp[ppp_map*4+:4];
	 assign mcal_clb2phy_wrcs0_low[ppp_map*4+:4]   = ch1_mcal_clb2phy_wrcs0_low[ppp_map*4+:4];
	 assign mcal_clb2phy_wrcs1_low[ppp_map*4+:4]   = ch1_mcal_clb2phy_wrcs1_low[ppp_map*4+:4];
	 assign mcal_clb2phy_rdcs0_upp[ppp_map*4+:4]   = ch1_mcal_clb2phy_rdcs0_upp[ppp_map*4+:4];
	 assign mcal_clb2phy_rdcs1_upp[ppp_map*4+:4]   = ch1_mcal_clb2phy_rdcs1_upp[ppp_map*4+:4];
	 assign mcal_clb2phy_rdcs0_low[ppp_map*4+:4]   = ch1_mcal_clb2phy_rdcs0_low[ppp_map*4+:4];
	 assign mcal_clb2phy_rdcs1_low[ppp_map*4+:4]   = ch1_mcal_clb2phy_rdcs1_low[ppp_map*4+:4];
	 assign mcal_clb2phy_odt_upp[ppp_map*7+:7]     = ch1_mcal_clb2phy_odt_upp[ppp_map*7+:7];
	 assign mcal_clb2phy_odt_low[ppp_map*7+:7]     = ch1_mcal_clb2phy_odt_low[ppp_map*7+:7];
      end
      else begin
	 assign mcal_clb2phy_t_b_upp[ppp_map*4+:4]     = ch0_mcal_clb2phy_t_b_upp[ppp_map*4+:4];
	 assign mcal_clb2phy_t_b_low[ppp_map*4+:4]     = ch0_mcal_clb2phy_t_b_low[ppp_map*4+:4];
	 assign mcal_clb2phy_rden_upp[ppp_map*4+:4]    = ch0_mcal_clb2phy_rden_upp[ppp_map*4+:4]; 
	 assign mcal_clb2phy_rden_low[ppp_map*4+:4]    = ch0_mcal_clb2phy_rden_low[ppp_map*4+:4]; 
	 assign mcal_clb2phy_wrcs0_upp[ppp_map*4+:4]   = ch0_mcal_clb2phy_wrcs0_upp[ppp_map*4+:4];
	 assign mcal_clb2phy_wrcs1_upp[ppp_map*4+:4]   = ch0_mcal_clb2phy_wrcs1_upp[ppp_map*4+:4];
	 assign mcal_clb2phy_wrcs0_low[ppp_map*4+:4]   = ch0_mcal_clb2phy_wrcs0_low[ppp_map*4+:4];
	 assign mcal_clb2phy_wrcs1_low[ppp_map*4+:4]   = ch0_mcal_clb2phy_wrcs1_low[ppp_map*4+:4];
	 assign mcal_clb2phy_rdcs0_upp[ppp_map*4+:4]   = ch0_mcal_clb2phy_rdcs0_upp[ppp_map*4+:4];
	 assign mcal_clb2phy_rdcs1_upp[ppp_map*4+:4]   = ch0_mcal_clb2phy_rdcs1_upp[ppp_map*4+:4];
	 assign mcal_clb2phy_rdcs0_low[ppp_map*4+:4]   = ch0_mcal_clb2phy_rdcs0_low[ppp_map*4+:4];
	 assign mcal_clb2phy_rdcs1_low[ppp_map*4+:4]   = ch0_mcal_clb2phy_rdcs1_low[ppp_map*4+:4];
	 assign mcal_clb2phy_odt_upp[ppp_map*7+:7]     = ch0_mcal_clb2phy_odt_upp[ppp_map*7+:7];
	 assign mcal_clb2phy_odt_low[ppp_map*7+:7]     = ch0_mcal_clb2phy_odt_low[ppp_map*7+:7];
      end
   end
   for (ppp_map=0; ppp_map<DBYTES; ppp_map++) begin
      if ((PING_PONG_PHY > 1) && PING_PONG_CH1_DBYTES[ppp_map]) begin
	 assign mcal_clb2phy_fifo_rden[ppp_map*13+:13] = ch1_mcal_clb2phy_fifo_rden[ppp_map*13+:13];
	 assign mcal_DMOut_n[ppp_map*8+:8]   = ch1_mcal_DMOut_n[ppp_map*8+:8];
	 assign mcal_DQOut[ppp_map*8*8+:8*8] = ch1_mcal_DQOut[ppp_map*8*8+:8*8];
	 //assign mcal_DQSOut                  = ch1_mcal_DQSOut;
      end
      else begin
	 assign mcal_clb2phy_fifo_rden[ppp_map*13+:13] = ch0_mcal_clb2phy_fifo_rden[ppp_map*13+:13];
	 assign mcal_DMOut_n[ppp_map*8+:8]   = ch0_mcal_DMOut_n[ppp_map*8+:8];
	 assign mcal_DQOut[ppp_map*8*8+:8*8] = ch0_mcal_DQOut[ppp_map*8*8+:8*8];
	 //assign mcal_DQSOut                  = ch0_mcal_DQSOut;
      end      
   end
   // Assign mcal_DQSOut to channel0 only. mcal_DQSOut is not directly used by Xiphy, and hence it would work for PingPong.
   assign mcal_DQSOut                  = ch0_mcal_DQSOut;

endgenerate

generate
if (SIM_MODE == "BFM")  begin : generate_block1
  ddr4_phy_v2_2_0_xiphy_behav # (
    .tCK                 (tCK)
   ,.BYTES               (BYTES)
   ,.DBYTES              (DBYTES)
   ,.IOBTYPE             (IOBTYPE)
   ,.TBYTE_CTL           (TBYTE_CTL)
   ,.DELAY_TYPE          (DELAY_TYPE)
   ,.DELAY_FORMAT        (DELAY_FORMAT)
   ,.UPDATE_MODE         (UPDATE_MODE)
   ,.PLLCLK_SRC          (PLLCLK_SRC)
   ,.GCLK_SRC            (GCLK_SRC)
   ,.INIT                (INIT)
   ,.RX_DATA_TYPE        (RX_DATA_TYPE)
   ,.TX_OUTPUT_PHASE_90  (TX_OUTPUT_PHASE_90)
   ,.RXTX_BITSLICE_EN    (RXTX_BITSLICE_EN)
   ,.NATIVE_ODELAY_BYPASS (NATIVE_ODELAY_BYPASS)
   ,.TRI_OUTPUT_PHASE_90 (TRI_OUTPUT_PHASE_90)
   ,.FIFO_SYNC_MODE      (FIFO_SYNC_MODE)
   ,.EN_OTHER_PCLK       (EN_OTHER_PCLK)
   ,.EN_OTHER_NCLK       (EN_OTHER_NCLK)
   ,.SERIAL_MODE         (SERIAL_MODE)
   ,.RX_CLK_PHASE_P      (RX_CLK_PHASE_P)
   ,.RX_CLK_PHASE_N      (RX_CLK_PHASE_N)
   ,.INV_RXCLK           (INV_RXCLK)
   ,.TX_GATING           (TX_GATING)
   ,.RX_GATING           (RX_GATING)
   ,.DIV_MODE            (DIV_MODE)
   ,.REFCLK_SRC          (REFCLK_SRC)
   ,.CTRL_CLK            (CTRL_CLK)
   ,.EN_CLK_TO_EXT_NORTH (EN_CLK_TO_EXT_NORTH)
   ,.EN_CLK_TO_EXT_SOUTH (EN_CLK_TO_EXT_SOUTH)
   ,.DATA_WIDTH          (DATA_WIDTH)
   ,.RX_DELAY_VAL        (RX_DELAY_VAL)
   ,.TX_DELAY_VAL        (TX_DELAY_VAL)
   ,.TRI_DELAY_VAL       (TRI_DELAY_VAL)
   ,.READ_IDLE_COUNT     (READ_IDLE_COUNT)
   ,.ROUNDING_FACTOR     (ROUNDING_FACTOR)
   ,.REFCLK_FREQ         (REFCLK_FREQ)
   ,.DCI_SRC             (DCI_SRC)
   ,.EN_DYN_ODLY_MODE    (EN_DYN_ODLY_MODE)
   ,.SELF_CALIBRATE      (SELF_CALIBRATE)
   ,.IDLY_VT_TRACK       (IDLY_VT_TRACK)
   ,.ODLY_VT_TRACK       (ODLY_VT_TRACK)
   ,.QDLY_VT_TRACK       (QDLY_VT_TRACK)
   ,.RXGATE_EXTEND       (RXGATE_EXTEND)
   ,.PING_PONG_CH1_BYTES_MAP (PING_PONG_CH1_BYTES_MAP)
   ,.DRAM_TYPE           (DRAM_TYPE)
) u_ddr_xiphy (
   // global clocks
    .gclk_in              (gclk_in)

   // programming static outputs here
   ,.clk_from_ext_low                    ({BYTES{1'b1}})
   ,.clk_from_ext_upp                    ({BYTES{1'b1}})
   ,.clb2phy_idelay_ce                   ({(BYTES*13){1'b0}})
   ,.clb2phy_idelay_inc                  ({(BYTES*13){1'b0}})
   ,.clb2phy_idelay_ld                   ({(BYTES*13){1'b0}})
   ,.clb2phy_idelay_cntvaluein           ({(BYTES*117){1'b0}})
   ,.clb2phy_odelay_ce                   ({(BYTES*13){1'b0}})
   ,.clb2phy_odelay_inc                  ({(BYTES*13){1'b0}})
   ,.clb2phy_odelay_ld                   ({(BYTES*13){1'b0}})
   ,.clb2phy_odelay_cntvaluein           ({(BYTES*117){1'b0}})
   ,.clb2phy_tristate_odelay_ce          ({(BYTES*2){1'b0}})
   ,.clb2phy_tristate_odelay_inc         ({(BYTES*2){1'b0}})
   ,.clb2phy_tristate_odelay_ld          ({(BYTES*2){1'b0}})
   ,.clb2phy_tristate_odelay_cntvaluein  ({(BYTES*18){1'b0}})
   ,.clb2phy_idelay_en_vtc               ({(BYTES*13){1'b1}})
   ,.clb2phy_odelay_en_vtc               ({(BYTES*13){1'b1}})
   ,.clb2phy_odelay_tristate_en_vtc      ({(BYTES*2){1'b1}})
   ,.clb2phy_dlyctl_en_vtc_upp           (clb2phy_dlyctl_en_vtc_upp_riuclk)
   ,.clb2phy_dlyctl_en_vtc_low           (clb2phy_dlyctl_en_vtc_low_riuclk)
   // put all ignored inputs here
   ,.clk_to_ext_north_low                (clk_to_ext_north_low)
   ,.clk_to_ext_north_upp                (clk_to_ext_north_upp)
   ,.clk_to_ext_south_low                (clk_to_ext_south_low)
   ,.clk_to_ext_south_upp                (clk_to_ext_south_upp)
   ,.phy2clb_idelay_cntvalueout          (phy2clb_idelay_cntvalueout)
   ,.phy2clb_odelay_cntvalueout          (phy2clb_odelay_cntvalueout)
   ,.phy2clb_tristate_odelay_cntvalueout (phy2clb_tristate_odelay_cntvalueout)
   ,.phy2rclk_ss_divclk                  (phy2rclk_ss_divclk)


   `include "ddr4_core_phy_ddrMapDDR4.vh"

   // cal stuff
   ,.clb2riu_addr                        (clb2riu_addr)
   ,.clb2riu_nibble_sel_low              (clb2riu_nibble_sel_low)
   ,.clb2riu_nibble_sel_upp              (clb2riu_nibble_sel_upp)
   ,.clb2riu_wr_data                     (clb2riu_wr_data)
   ,.clb2riu_wr_en                       (clb2riu_wr_en)
   ,.phy2clb_fixdly_rdy_upp              (phy2clb_fixdly_rdy_upp_in_riuclk)
   ,.phy2clb_fixdly_rdy_low              (phy2clb_fixdly_rdy_low_in_riuclk)
   ,.phy2clb_phy_rdy_upp                 (phy2clb_phy_rdy_upp_in_riuclk)
   ,.phy2clb_phy_rdy_low                 (phy2clb_phy_rdy_low_in_riuclk)
   //Connect this for K2 BISC workaround
   //,.phy2clb_master_pd_out_low           (phy2clb_master_pd_out_low)
   //,.phy2clb_master_pd_out_upp           (phy2clb_master_pd_out_upp)
   ,.riu2clb_rd_data                     (riu2clb_rd_data)
   ,.riu2clb_valid                       (riu2clb_valid)

   // clocking and reset
   ,.clb2phy_ctrl_clk_upp                (clb2phy_ctrl_clk_upp)
   ,.clb2phy_ctrl_clk_low                (clb2phy_ctrl_clk_low)
   ,.clb2phy_fifo_clk                    (clb2phy_fifo_clk)
   ,.clb2phy_ref_clk_low                 (clb2phy_ref_clk_low)
   ,.clb2phy_ref_clk_upp                 (clb2phy_ref_clk_upp)
   ,.clb2phy_ctrl_rst_low                (clb2phy_ctrl_rst_low_riuclk)
   ,.clb2phy_ctrl_rst_upp                (clb2phy_ctrl_rst_upp_riuclk)
   ,.clb2phy_idelay_rst                  (clb2phy_idelay_rst)
   ,.clb2phy_odelay_rst                  (clb2phy_odelay_rst)
   ,.clb2phy_rxbit_rst                   (clb2phy_rxbit_rst)
   ,.clb2phy_tristate_odelay_rst         (clb2phy_tristate_odelay_rst)
   ,.clb2phy_txbit_rst                   (clb2phy_txbit_rst)
   ,.clb2phy_txbit_tri_rst               (clb2phy_txbit_tri_rst)
   // common to mc and cal stuff

   // special iob stuff
   ,.phy2iob_q_out_byte                  (phy2iob_q_out_byte)
   ,.phy2iob_odt_out_byte                (phy2iob_odt_out_byte)
   ,.phy2iob_t                           (phy2iob_t)

   ,.iob2phy_d_in_byte                   (iob2phy_d_in_byte)
);

end else begin : generate_block1
ddr4_phy_v2_2_0_xiphy # (
    .BYTES               (BYTES)
   ,.DBYTES              (DBYTES)
   ,.TBYTE_CTL           (TBYTE_CTL)
   ,.DELAY_TYPE          (DELAY_TYPE)
   ,.DELAY_FORMAT        (DELAY_FORMAT)
   ,.UPDATE_MODE         (UPDATE_MODE)
   ,.PLLCLK_SRC          (PLLCLK_SRC)
   ,.GCLK_SRC            (GCLK_SRC)
   ,.INIT                (INIT)
   ,.RX_DATA_TYPE        (RX_DATA_TYPE)
   ,.TX_OUTPUT_PHASE_90  (TX_OUTPUT_PHASE_90)
   ,.RXTX_BITSLICE_EN    (RXTX_BITSLICE_EN)
   ,.NATIVE_ODELAY_BYPASS (NATIVE_ODELAY_BYPASS)
   ,.TRI_OUTPUT_PHASE_90 (TRI_OUTPUT_PHASE_90)
   ,.FIFO_SYNC_MODE      (FIFO_SYNC_MODE)
   ,.EN_OTHER_PCLK       (EN_OTHER_PCLK)
   ,.EN_OTHER_NCLK       (EN_OTHER_NCLK)
   ,.SERIAL_MODE         (SERIAL_MODE)
   ,.RX_CLK_PHASE_P      (RX_CLK_PHASE_P)
   ,.RX_CLK_PHASE_N      (RX_CLK_PHASE_N)
   ,.INV_RXCLK           (INV_RXCLK)
   ,.TX_GATING           (TX_GATING)
   ,.RX_GATING           (RX_GATING)
   ,.DIV_MODE            (DIV_MODE)
   ,.REFCLK_SRC          (REFCLK_SRC)
   ,.CTRL_CLK            (CTRL_CLK)
   ,.EN_CLK_TO_EXT_NORTH (EN_CLK_TO_EXT_NORTH)
   ,.EN_CLK_TO_EXT_SOUTH (EN_CLK_TO_EXT_SOUTH)
   ,.DATA_WIDTH          (DATA_WIDTH)
   ,.RX_DELAY_VAL        (RX_DELAY_VAL)
   ,.TX_DELAY_VAL        (TX_DELAY_VAL)
   ,.TRI_DELAY_VAL       (TRI_DELAY_VAL)
   ,.READ_IDLE_COUNT     (READ_IDLE_COUNT)
   ,.ROUNDING_FACTOR     (ROUNDING_FACTOR)
   ,.REFCLK_FREQ         (REFCLK_FREQ)
   ,.DCI_SRC             (DCI_SRC)
   ,.EN_DYN_ODLY_MODE    (EN_DYN_ODLY_MODE)
   ,.SELF_CALIBRATE      (SELF_CALIBRATE)
   ,.IDLY_VT_TRACK       (IDLY_VT_TRACK)
   ,.ODLY_VT_TRACK       (ODLY_VT_TRACK)
   ,.QDLY_VT_TRACK       (QDLY_VT_TRACK)
   ,.RXGATE_EXTEND       (RXGATE_EXTEND)
   ,.DRAM_TYPE           (DRAM_TYPE)
   ,.SIM_DEVICE          (SIM_DEVICE)
) u_ddr_xiphy (
   // global clocks
    .gclk_in              (gclk_in)

   // programming static outputs here
   ,.clk_from_ext_low                    ({BYTES{1'b1}})
   ,.clk_from_ext_upp                    ({BYTES{1'b1}})
   ,.clb2phy_idelay_ce                   ({(BYTES*13){1'b0}})
   ,.clb2phy_idelay_inc                  ({(BYTES*13){1'b0}})
   ,.clb2phy_idelay_ld                   ({(BYTES*13){1'b0}})
   ,.clb2phy_idelay_cntvaluein           ({(BYTES*117){1'b0}})
   ,.clb2phy_odelay_ce                   ({(BYTES*13){1'b0}})
   ,.clb2phy_odelay_inc                  ({(BYTES*13){1'b0}})
   ,.clb2phy_odelay_ld                   ({(BYTES*13){1'b0}})
   ,.clb2phy_odelay_cntvaluein           ({(BYTES*117){1'b0}})
   ,.clb2phy_tristate_odelay_ce          ({(BYTES*2){1'b0}})
   ,.clb2phy_tristate_odelay_inc         ({(BYTES*2){1'b0}})
   ,.clb2phy_tristate_odelay_ld          ({(BYTES*2){1'b0}})
   ,.clb2phy_tristate_odelay_cntvaluein  ({(BYTES*18){1'b0}})
   ,.clb2phy_idelay_en_vtc               ({(BYTES*13){1'b1}})
   ,.clb2phy_odelay_en_vtc               ({(BYTES*13){1'b1}})
   ,.clb2phy_odelay_tristate_en_vtc      ({(BYTES*2){1'b1}})
   ,.clb2phy_dlyctl_en_vtc_upp           (clb2phy_dlyctl_en_vtc_upp_riuclk)
   ,.clb2phy_dlyctl_en_vtc_low           (clb2phy_dlyctl_en_vtc_low_riuclk)
   // put all ignored inputs here
   ,.clk_to_ext_north_low                (clk_to_ext_north_low)
   ,.clk_to_ext_north_upp                (clk_to_ext_north_upp)
   ,.clk_to_ext_south_low                (clk_to_ext_south_low)
   ,.clk_to_ext_south_upp                (clk_to_ext_south_upp)
   ,.phy2clb_idelay_cntvalueout          (phy2clb_idelay_cntvalueout)
   ,.phy2clb_odelay_cntvalueout          (phy2clb_odelay_cntvalueout)
   ,.phy2clb_tristate_odelay_cntvalueout (phy2clb_tristate_odelay_cntvalueout)
   ,.phy2rclk_ss_divclk                  (phy2rclk_ss_divclk)


   `include "ddr4_core_phy_ddrMapDDR4.vh"

   // cal stuff
   ,.clb2riu_addr                        (clb2riu_addr)
   ,.clb2riu_nibble_sel_low              (clb2riu_nibble_sel_low)
   ,.clb2riu_nibble_sel_upp              (clb2riu_nibble_sel_upp)
   ,.clb2riu_wr_data                     (clb2riu_wr_data)
   ,.clb2riu_wr_en                       (clb2riu_wr_en)
   ,.phy2clb_fixdly_rdy_upp              (phy2clb_fixdly_rdy_upp_in_riuclk)
   ,.phy2clb_fixdly_rdy_low              (phy2clb_fixdly_rdy_low_in_riuclk)
   ,.phy2clb_phy_rdy_upp                 (phy2clb_phy_rdy_upp_in_riuclk)
   ,.phy2clb_phy_rdy_low                 (phy2clb_phy_rdy_low_in_riuclk)
   //Connect this for K2 BISC workaround
   //,.phy2clb_master_pd_out_low           (phy2clb_master_pd_out_low)
   //,.phy2clb_master_pd_out_upp           (phy2clb_master_pd_out_upp)
   ,.riu2clb_rd_data                     (riu2clb_rd_data)
   ,.riu2clb_valid                       (riu2clb_valid)

   // clocking and reset
   ,.clb2phy_ctrl_clk_upp                (clb2phy_ctrl_clk_upp)
   ,.clb2phy_ctrl_clk_low                (clb2phy_ctrl_clk_low)
   ,.clb2phy_fifo_clk                    (clb2phy_fifo_clk)
   ,.clb2phy_ref_clk_low                 (clb2phy_ref_clk_low)
   ,.clb2phy_ref_clk_upp                 (clb2phy_ref_clk_upp)
   ,.clb2phy_ctrl_rst_low                (clb2phy_ctrl_rst_low_riuclk)
   ,.clb2phy_ctrl_rst_upp                (clb2phy_ctrl_rst_upp_riuclk)
   ,.clb2phy_idelay_rst                  (clb2phy_idelay_rst)
   ,.clb2phy_odelay_rst                  (clb2phy_odelay_rst)
   ,.clb2phy_rxbit_rst                   (clb2phy_rxbit_rst)
   ,.clb2phy_tristate_odelay_rst         (clb2phy_tristate_odelay_rst)
   ,.clb2phy_txbit_rst                   (clb2phy_txbit_rst)
   ,.clb2phy_txbit_tri_rst               (clb2phy_txbit_tri_rst)
   // common to mc and cal stuff

   // special iob stuff
   ,.phy2iob_q_out_byte                  (phy2iob_q_out_byte)
   ,.phy2iob_odt_out_byte                (phy2iob_odt_out_byte)
   ,.phy2iob_t                           (phy2iob_t)

   ,.iob2phy_d_in_byte                   (iob2phy_d_in_byte)
);
end
endgenerate

// Fan-out en vtc to each nibble
assign clb2phy_dlyctl_en_vtc_low_riuclk = {(BYTES*1){en_vtc_riuclk}};
assign clb2phy_dlyctl_en_vtc_upp_riuclk = {(BYTES*1){en_vtc_riuclk}};

   reg [13*BYTES*8-1:0]     phy2clb_rd_dq_r1;
   reg [13*8-1:0]           phy2clb_rd_dq_r2;
   reg [8-1:0]              phy2clb_rd_dq_r3;

  always @ (posedge div_clk)
  begin
	phy2clb_rd_dq_r1 <= #TCQ phy2clb_rd_dq;
	phy2clb_rd_dq_r2 <= #TCQ phy2clb_rd_dq_r1[bisc_byte[8:4]*13*8 +:13*8];
	phy2clb_rd_dq_r3 <= #TCQ phy2clb_rd_dq_r2[bisc_byte[3:0]*8 +:8];
  end
  
assign phy2clb_rd_dq_bits = phy2clb_rd_dq_r3;


  always @ (posedge riu_clk)
    clb2phy_t_b_addr_riuclk <= (&phy2clb_fixdly_rdy_upp_riuclk_int) && (&phy2clb_fixdly_rdy_low_riuclk_int);

  always @ (posedge div_clk) begin
    clb2phy_t_b_addr_i[0] <= clb2phy_t_b_addr_riuclk;
    clb2phy_t_b_addr_i[1] <= clb2phy_t_b_addr_i[0];
    clb2phy_t_b_addr       <= {4{clb2phy_t_b_addr_i[1]}};
  end
    
endmodule
