
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
//  /   /         Filename           : ddr4_core_mem_intfc.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/05 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4_SDRAM
// Purpose          :
//                   mem_intfc module
// Reference        :
// Revision History :
//*****************************************************************************


`timescale 1ps/1ps

module ddr4_core_ddr4_mem_intfc #
  (
    parameter integer ADDR_WIDTH          = 18
   ,parameter integer ROW_WIDTH           = 15
   ,parameter integer BANK_WIDTH          = 2
   ,parameter integer BANK_GROUP_WIDTH    = 2
   ,parameter integer ADDR_FIFO_WIDTH     = 35
   ,parameter integer S_HEIGHT            = 1
   ,parameter integer LR_WIDTH            = 1
   ,parameter         ALIAS_PAGE          = "OFF"
   ,parameter         ALIAS_P_CNT         = "OFF"
   ,parameter integer CK_WIDTH            = 1
   ,parameter integer CKE_WIDTH           = 1
   ,parameter integer COL_WIDTH           = 10
   ,parameter integer CS_WIDTH            = 1
   ,parameter integer ODT_WIDTH           = 1
   ,parameter         DRAM_TYPE           = "DDR4"
   ,parameter integer DQ_WIDTH            = 16
   ,parameter integer DQS_WIDTH           = 2
   ,parameter integer DM_WIDTH            = 2
   ,parameter         ECC                         = "OFF"
   ,parameter         ECC_WIDTH                   = 8
   ,parameter         PAYLOAD_WIDTH               = 64
   ,parameter         integer DATA_BUF_ADDR_WIDTH = 5
   ,parameter         AUTO_AP_COL_A3              = "OFF"
   ,parameter         MEM_ADDR_ORDER              = "ROW_COLUMN_BANK"
   ,parameter         NUMREF                      = 1
   ,parameter         SELF_REFRESH                = 1'b0
   ,parameter         SAVE_RESTORE                = 1'b0
   ,parameter         NUM_SLOT  = 1
   ,parameter         RANK_SLOT = 1

   ,parameter         REG_CTRL             = "OFF" // RDIMM register control
   ,parameter         LRDIMM_MODE          = "OFF" // LRDIMM Mode
   ,parameter         DDR4_DB_HIF_RTT_NOM     = 4'b0011 
   ,parameter         DDR4_DB_HIF_RTT_WR      = 4'b0000 
   ,parameter         DDR4_DB_HIF_RTT_PARK    = 4'b0000 
   ,parameter         DDR4_DB_HIF_DI          = 4'b0001 
   ,parameter         DDR4_DB_DIF_ODT         = 4'b0011 
   ,parameter         DDR4_DB_DIF_DI          = 4'b0000 
   ,parameter         DDR4_DB_HIF_VREF        = 8'b0001_1101
   ,parameter         DDR4_DB_DIF_VREF        = 8'b0001_1101

   ,parameter         MCS_ECC_ENABLE       = "TRUE"

   ,parameter         tCK                 = 938  // Memory clock period
   ,parameter         tFAW                = 20
   ,parameter         tFAW_dlr            = 16
   ,parameter         tRTW                = 4
   ,parameter         tWTR_L              = 13
   ,parameter         tWTR_S              = 13
   ,parameter         tRFC                = 27
   ,parameter         tRFC_dlr            = 9
   ,parameter         tREFI               = 1300
   ,parameter         ZQINTVL             = 10400
   ,parameter         tZQCS               = 128
   ,parameter         tRP                 = 15
   ,parameter         tRRD_L              = 4
   ,parameter         tRRD_S              = 4
   ,parameter         tRRD_dlr            = 4
   ,parameter         tRAS                = 39
   ,parameter         tRCD                = 15
   ,parameter         tRTP                = 6
   ,parameter         tWR                 = 12
   ,parameter         tCCD_3ds            = 4

   ,parameter         PER_RD_INTVL        = 32'd0

   ,parameter         ODTWR               = 16'h0033
   ,parameter         ODTWRDEL            = 5'd8
   ,parameter         ODTWRDUR            = 4'd6
   ,parameter         ODTWRODEL           = 5'd9
   ,parameter         ODTWRODUR           = 4'd6
   ,parameter         ODTRD               = 16'h0012
   ,parameter         ODTRDDEL            = 5'd11
   ,parameter         ODTRDDUR            = 4'd6
   ,parameter         ODTRDODEL           = 5'd9
   ,parameter         ODTRDODUR           = 4'd6
   ,parameter         ODTNOP              = 16'h0000

   ,parameter real    TCQ                 = 100

   ,parameter         DM_DBI              = "DM_NODBI"
   ,parameter         USE_CS_PORT         = 1
   ,parameter         DRAM_WIDTH          = 8
   ,parameter         RANKS               = 1
   ,parameter         RANK_WIDTH          = 1
   ,parameter         ORDERING            = "NORM"
   ,parameter         RTL_VERSION         = 0
   ,parameter         TXN_FIFO_BYPASS     = "ON"
   ,parameter         TXN_FIFO_PIPE       = "OFF"
   ,parameter         PER_RD_PERF         = 1'b1
   ,parameter         CAS_FIFO_BYPASS     = "ON"
   ,parameter         NOP_ADD_LOW         = 1'b0
   ,parameter         STARVATION_EN       = 1'b1 
   ,parameter         STARVE_COUNT_WIDTH  = 9
   ,parameter	      EXTRA_CMD_DELAY	  = 0
   ,parameter         nCK_PER_CLK         = 4
   ,parameter         APP_ADDR_WIDTH      = 32
   ,parameter         APP_DATA_WIDTH      = 64
   ,parameter         APP_MASK_WIDTH      = 8

   // Migration parameters
   ,parameter                          MIGRATION = "OFF"
   ,parameter [8*CK_WIDTH-1:0]         CK_SKEW   = {CK_WIDTH{8'b0}}
   ,parameter [8*ADDR_WIDTH-1:0]       ADDR_SKEW = {ADDR_WIDTH{8'b0}}
   ,parameter [8*BANK_WIDTH-1:0]       BA_SKEW   = {BANK_WIDTH{8'b0}}
   ,parameter [8*BANK_GROUP_WIDTH-1:0] BG_SKEW   = {BANK_GROUP_WIDTH{8'b0}}
   ,parameter [8*1-1:0]                ACT_SKEW  = 8'b0
   ,parameter [8*1-1:0]                PAR_SKEW  = 8'b0
   ,parameter [8*CS_WIDTH-1:0]         CS_SKEW   = {CS_WIDTH{8'b0}}
   ,parameter [8*CKE_WIDTH-1:0]        CKE_SKEW  = {CKE_WIDTH{8'b0}}
   ,parameter [8*ODT_WIDTH-1:0]        ODT_SKEW  = {ODT_WIDTH{8'b0}}
   ,parameter [8*LR_WIDTH-1:0]         C_SKEW    = {LR_WIDTH{8'b0}}

   //Assertion Check
   ,parameter         MIG_PARAM_CHECKS        ="TRUE"
   ,parameter         INTERFACE               ="NATIVE"
   ,parameter         C_S_AXI_ADDR_WIDTH      = 28
   ,parameter         ADV_USER_REQ            ="NONE"
   // Memory part parameters
   ,parameter         DEVICE                  ="xcku060-es2"
   ,parameter         MEMORY_DENSITY          = "2Gb"
   ,parameter         MEMORY_SPEED_GRADE      = "083E"
   ,parameter         MEMORY_WIDTH            = "8"
   ,parameter         MEMORY_CONFIGURATION    = "COMPONENT"
   ,parameter         CALIB_HIGH_SPEED        = "FALSE"
   ,parameter         DDR4_CLAMSHELL          = "OFF" // Clamshell architecture of DRAM parts on PCB
   ,parameter         CA_MIRROR               = "OFF" // Address mirroring enable, RDIMM register RC0D DA[3]
   ,parameter         DDR4_REG_PARITY_ENABLE  = "OFF"
   // CAL Parameters
   ,parameter integer DBYTES               = 2
   ,parameter         MR0                     = 13'b0011100110000
   ,parameter         MR1                     = 13'b0000100000001
   ,parameter         MR2                     = 13'b0000000010000
   ,parameter         MR3                     = 13'b0000000000000
   ,parameter         MR4                     = 13'b0000000000000
   ,parameter         MR5                     = 13'b0010000000000
   ,parameter         MR6                     = 13'b0100000000000
   ,parameter         RD_VREF_VAL             = 7'h2E
   ,parameter         SLOT0_CONFIG         = {{(8-CS_WIDTH){1'b0}},{CS_WIDTH{1'b1}}} // Slot0 Physical configuration
   ,parameter         SLOT1_CONFIG         = 8'b0000_0000 // Slot1 Physical configuration
   ,parameter         SLOT0_FUNC_CS        = {{(8-CS_WIDTH){1'b0}},{CS_WIDTH{1'b1}}} // Slot0 Functional chipselect
   ,parameter         SLOT1_FUNC_CS        = 8'b0000_0000 // Slot1 Functional chipselect
   ,parameter         SLOT0_ODD_CS         = 8'b0000_1010 // Slot0 Odd chipselect
   ,parameter         SLOT1_ODD_CS         = 8'b0000_1010 // Slot1 Odd chipselect
   ,parameter         DDR4_REG_RC03        = {9'b0_0000_0011, 4'b0000} // RDIMM register RC03
   ,parameter         DDR4_REG_RC04        = {9'b0_0000_0100, 4'b0000} // RDIMM register RC04
   ,parameter         DDR4_REG_RC05        = {9'b0_0000_0101, 4'b0000} // RDIMM register RC05
   ,parameter         tXPR                 = 72 // assertion check
   ,parameter         tMOD                 = 6 // assertion check
   ,parameter         tMRD                 = 2 // assertion check
   ,parameter         tZQINIT              = 256 // assertion check
   ,parameter         MEM_CODE             = 0
   ,parameter         C_FAMILY             = "kintexu"
   ,parameter         C_DEBUG_ENABLED      = 0
   ,parameter         CPLX_PAT_LENGTH      = "LONG"
   ,parameter         BACKBONE_ROUTE       = "FALSE"
   ,parameter         CLKIN_PERIOD_MMCM    = 3750
   ,parameter         CLKFBOUT_MULT_MMCM   = 4        // write MMCM VCO multiplier
   ,parameter         DIVCLK_DIVIDE_MMCM   = 1        // write MMCM VCO divisor
   ,parameter         CLKOUT0_DIVIDE_MMCM  = 4        // VCO output divisor for MMCM clkout0
   ,parameter         CLKOUT1_DIVIDE_MMCM  = 4
   ,parameter         CLKOUT2_DIVIDE_MMCM  = 4
   ,parameter         CLKOUT3_DIVIDE_MMCM  = 4
   ,parameter         CLKOUT4_DIVIDE_MMCM  = 4
   ,parameter         PLL_WIDTH            = 1     // Number of PLLs
   ,parameter         CLKOUTPHY_MODE       = "VCO_2X" // PHY Mode
   ,parameter         EARLY_WR_DATA        = "OFF"
   ,parameter         SIM_MODE             = "FULL"
   ,parameter         BISC_EN              = 1
   ,parameter         BYPASS_CAL           = "FALSE"
   ,parameter         CAL_DQS_GATE         = "FULL"
   ,parameter         CAL_WRLVL            = "FULL"
   ,parameter         CAL_RDLVL            = "FULL"
   ,parameter         CAL_RDLVL_DBI        = "SKIP"
   ,parameter         CAL_WR_DQS_DQ        = "FULL"
   ,parameter         CAL_WR_DQS_DM_DBI    = "FULL"
   ,parameter         CAL_WRITE_LAT        = "FULL"
   ,parameter         CAL_RDLVL_COMPLEX    = "FULL"
   ,parameter         CAL_WR_DQS_COMPLEX   = "FULL"
   ,parameter         CAL_RD_VREF          = "SKIP"
   ,parameter         CAL_RD_VREF_PATTERN  = "SIMPLE"
   ,parameter         CAL_WR_VREF          = "SKIP"
   ,parameter         CAL_WR_VREF_PATTERN  = "SIMPLE"
   ,parameter         CAL_DQS_TRACKING     = "FULL"
   ,parameter         CAL_JITTER           = "FULL"
   ,parameter         t200us               = 53305
   ,parameter         t500us               = 133263
)
  (
    input                           sys_clk_p
   ,input                           sys_clk_n
   ,input                           mmcm_lock
   ,input                           reset_ub
   ,input                           pllGate
   ,input                           div_clk
   ,input                           div_clk_rst
   ,input                           riu_clk
   ,input                           riu_clk_rst
   ,output                          pll_lock
   ,output                          sys_clk_in
   ,output                          mmcm_clk_in

   ,output                          calDone

   // iob<>DDR4 signals
   ,output                          ddr4_act_n
   ,output [ADDR_WIDTH-1:0]         ddr4_adr
   ,output [BANK_WIDTH-1:0]         ddr4_ba
   ,output [BANK_GROUP_WIDTH-1:0]   ddr4_bg
   ,output [LR_WIDTH-1:0]           ddr4_c
   ,output [CKE_WIDTH-1:0]          ddr4_cke
   ,output [ODT_WIDTH-1:0]          ddr4_odt
   ,output [CS_WIDTH-1:0]           ddr4_cs_n
   ,output [CK_WIDTH-1:0]           ddr4_ck_t
   ,output [CK_WIDTH-1:0]           ddr4_ck_c
   ,output                          ddr4_reset_n
   ,output                          ddr4_parity
   ,inout  [DM_WIDTH-1:0]           ddr4_dm_dbi_n
   ,inout  [DQ_WIDTH-1:0]           ddr4_dq
   ,inout  [DQS_WIDTH-1:0]          ddr4_dqs_c
   ,inout  [DQS_WIDTH-1:0]          ddr4_dqs_t

   // user interface ports
   ,input [APP_ADDR_WIDTH-1:0]      app_addr
   ,input [2:0]                     app_cmd
   ,input                           app_en
   ,input                           app_hi_pri
   ,input                           app_autoprecharge
   ,input [APP_DATA_WIDTH-1:0]      app_wdf_data
   ,input                           app_wdf_end
   ,input [APP_MASK_WIDTH-1:0]      app_wdf_mask
   ,input                           app_wdf_wren
   ,input                           app_correct_en_i
   ,input [2*nCK_PER_CLK-1:0]       app_raw_not_ecc
   ,output [2*nCK_PER_CLK-1:0]      app_ecc_multiple_err
   ,output [APP_DATA_WIDTH-1:0]     app_rd_data
   ,output                          app_rd_data_end
   ,output                          app_rd_data_valid
   ,output                          app_rdy
   ,output                          app_wdf_rdy
   ,input                           app_sr_req
   ,output                          app_sr_active
   ,input                           app_ref_req
   ,output                          app_ref_ack
   ,input                           app_zq_req
   ,output                          app_zq_ack

   , output                         ALT_ddr4_reset_n                       //AK Added

   ,input [36:0]                    sl_iport0
   ,output [16:0]                   sl_oport0

   //Status and Debug outputs
   ,output wire [8:0]               cal_pre_status
   ,output wire [127:0]             cal_r0_status
   ,output wire [127:0]             cal_r1_status
   ,output wire [127:0]             cal_r2_status
   ,output wire [127:0]             cal_r3_status
   ,output wire [8:0]               cal_post_status
   ,output wire                     cal_error
   ,output wire [7:0]               cal_error_bit
   ,output wire [7:0]               cal_error_nibble
   ,output wire [3:0]               cal_error_code


   // Self-Refresh and Save/Restore
   ,input                           app_save_req
   ,output                          app_save_ack
   ,input                           app_mem_init_skip
   ,input                           app_restore_en
   ,input                           app_restore_complete
   ,input                           xsdb_select
   ,input                           xsdb_rd_en
   ,input                           xsdb_wr_en
   ,input [15:0]                    xsdb_addr
   ,input [8:0]                     xsdb_wr_data
   ,output [8:0]                    xsdb_rd_data
   ,output                          xsdb_rdy
   ,output [31:0]                   dbg_out

   ,input                            traffic_wr_done
   ,input                            traffic_status_err_bit_valid
   ,input                            traffic_status_err_type_valid
   ,input                            traffic_status_err_type
   ,input                            traffic_status_done
   ,input                            traffic_status_watch_dog_hang
   ,input [APP_DATA_WIDTH-1:0]       traffic_error
   ,input [3:0]                      win_start

   ,output wire                      traffic_clr_error
   ,output wire                      traffic_start
   ,output wire                      traffic_rst
   ,output wire                      traffic_err_chk_en
   ,output wire [3:0]                traffic_instr_addr_mode
   ,output wire [3:0]                traffic_instr_data_mode
   ,output wire [3:0]                traffic_instr_rw_mode
   ,output wire [1:0]                traffic_instr_rw_submode
   ,output wire [31:0]               traffic_instr_num_of_iter
   ,output wire [5:0]                traffic_instr_nxt_instr
   ,output wire [31:0]               win_status

   ,output [ADDR_FIFO_WIDTH-1:0]    ecc_err_addr
   ,output [2*nCK_PER_CLK-1:0]      eccSingle
   ,output [2*nCK_PER_CLK-1:0]      eccMultiple
   ,input  [DQ_WIDTH/8-1:0]         fi_xor_we
   ,input  [DQ_WIDTH-1:0]           fi_xor_wrdata
   ,output [DQ_WIDTH*8-1:0]         rd_data_phy2mc
   ,output                          ddr4_mcs_lmb_ue
   ,output                          ddr4_mcs_lmb_ce

   //Debug Port
   ,output wire [511:0]             dbg_bus
   ,output wire [2:0]               dbg_cal_seq
   ,output wire [31:0]              dbg_cal_seq_cnt
   ,output wire [7:0]               dbg_cal_seq_rd_cnt
   ,output wire                     dbg_rd_valid
   ,output wire [5:0]               dbg_cmp_byte
   ,output wire [63:0]              dbg_rd_data
   ,output wire [63:0]              dbg_rd_data_cmp
   ,output wire [63:0]              dbg_expected_data
   ,output wire [15:0]              dbg_cplx_config
   ,output wire [1:0]               dbg_cplx_status
   ,output wire [27:0]              dbg_io_address
   ,output wire                     dbg_pllGate
   ,output wire [19:0]              dbg_phy2clb_fixdly_rdy_low
   ,output wire [19:0]              dbg_phy2clb_fixdly_rdy_upp
   ,output wire [19:0]              dbg_phy2clb_phy_rdy_low
   ,output wire [19:0]              dbg_phy2clb_phy_rdy_upp
);

  localparam PAYLOAD_DM_WIDTH = PAYLOAD_WIDTH/8;

  localparam ADDR_FIFO_WIDTH_INT = (S_HEIGHT > 1) ? 52 : ADDR_FIFO_WIDTH;
   wire [31:0] io_address;

   wire [DBYTES*8*8-1:0] wrData;
   wire                [7:0] mcal_ACT_n;
   wire                [7:0] mcal_CAS_n;
   wire                [7:0] mcal_RAS_n;
   wire                [7:0] mcal_WE_n;
   wire        [ADDR_WIDTH*8-1:0] mcal_ADR;
   wire       [BANK_WIDTH*8-1:0] mcal_BA;
   wire       [BANK_GROUP_WIDTH*8-1:0] mcal_BG;
   wire      [CKE_WIDTH*8-1:0] mcal_CKE;
   wire       [CS_WIDTH*8-1:0] mcal_CS_n;
   wire           [LR_WIDTH*8-1:0] mc_C, mcal_C;

   wire       [DBYTES*8-1:0] ch0_mcal_DMOut_n;
   wire     [DBYTES*8*8-1:0] ch0_mcal_DQOut;
   wire                [7:0] ch0_mcal_DQSOut;

   wire       [DBYTES*8-1:0] ch1_mcal_DMOut_n;
   wire     [DBYTES*8*8-1:0] ch1_mcal_DQOut;
   wire                [7:0] ch1_mcal_DQSOut;

   wire      [ODT_WIDTH*8-1:0] mcal_ODT;
   wire                [7:0] mcal_PAR;

   wire     [DBYTES*13-1:0] ch0_mcal_clb2phy_fifo_rden;
   wire        [DBYTES*4-1:0] ch0_mcal_clb2phy_t_b_upp;
   wire        [DBYTES*4-1:0] ch0_mcal_clb2phy_t_b_low;
   wire        [DBYTES*4-1:0] ch0_mcal_clb2phy_rden_upp;
   wire        [DBYTES*4-1:0] ch0_mcal_clb2phy_rden_low;
   wire     [DBYTES*4-1:0] ch0_mcal_clb2phy_wrcs0_upp;
   wire     [DBYTES*4-1:0] ch0_mcal_clb2phy_wrcs1_upp;
   wire     [DBYTES*4-1:0] ch0_mcal_clb2phy_wrcs0_low;
   wire     [DBYTES*4-1:0] ch0_mcal_clb2phy_wrcs1_low;
   wire     [DBYTES*4-1:0] ch0_mcal_clb2phy_rdcs0_upp;
   wire     [DBYTES*4-1:0] ch0_mcal_clb2phy_rdcs1_upp;
   wire     [DBYTES*4-1:0] ch0_mcal_clb2phy_rdcs0_low;
   wire     [DBYTES*4-1:0] ch0_mcal_clb2phy_rdcs1_low;
   wire        [DBYTES*7-1:0] ch0_mcal_clb2phy_odt_upp;
   wire        [DBYTES*7-1:0] ch0_mcal_clb2phy_odt_low;

   wire [DBYTES*13-1:0] ch1_mcal_clb2phy_fifo_rden;
   wire        [DBYTES*4-1:0] ch1_mcal_clb2phy_t_b_upp;
   wire        [DBYTES*4-1:0] ch1_mcal_clb2phy_t_b_low;
   wire        [DBYTES*4-1:0] ch1_mcal_clb2phy_rden_upp;
   wire        [DBYTES*4-1:0] ch1_mcal_clb2phy_rden_low;
   wire     [DBYTES*4-1:0] ch1_mcal_clb2phy_wrcs0_upp;
   wire     [DBYTES*4-1:0] ch1_mcal_clb2phy_wrcs1_upp;
   wire     [DBYTES*4-1:0] ch1_mcal_clb2phy_wrcs0_low;
   wire     [DBYTES*4-1:0] ch1_mcal_clb2phy_wrcs1_low;
   wire     [DBYTES*4-1:0] ch1_mcal_clb2phy_rdcs0_upp;
   wire     [DBYTES*4-1:0] ch1_mcal_clb2phy_rdcs1_upp;
   wire     [DBYTES*4-1:0] ch1_mcal_clb2phy_rdcs0_low;
   wire     [DBYTES*4-1:0] ch1_mcal_clb2phy_rdcs1_low;
   wire        [DBYTES*7-1:0] ch1_mcal_clb2phy_odt_upp;
   wire        [DBYTES*7-1:0] ch1_mcal_clb2phy_odt_low;

   wire       [DBYTES*7-1:0] mcal_rd_vref_value;


   wire     [DBYTES*8-1:0] mcal_DMIn_n;
   wire     [DBYTES*8*8-1:0] mcal_DQIn;
 
//  localparam LR_WIDTH = (S_HEIGHT > 1) ? clogb2(S_HEIGHT) : 1;
  //Debug Signals
  reg [31:0] io_address_r1; // MAN change debug address from 28 to 32 bits 
  reg [31:0] io_address_r2;
  reg        pllGate_r1;
  reg        pllGate_r2;
  wire  [20*1-1:0] phy2clb_fixdly_rdy_low;
  wire  [20*1-1:0] phy2clb_fixdly_rdy_upp;
  wire  [20*1-1:0] phy2clb_phy_rdy_low;
  wire  [20*1-1:0] phy2clb_phy_rdy_upp;

  wire  [20*1-1:0] phy2clb_fixdly_rdy_low_riuclk;
  wire  [20*1-1:0] phy2clb_fixdly_rdy_upp_riuclk;
  wire  [20*1-1:0] phy2clb_phy_rdy_low_riuclk;
  wire  [20*1-1:0] phy2clb_phy_rdy_upp_riuclk;

  reg [20*1-1:0] dbg_phy2clb_fixdly_rdy_low_r1;
  reg [20*1-1:0] dbg_phy2clb_fixdly_rdy_low_r2;
  reg [20*1-1:0] dbg_phy2clb_fixdly_rdy_upp_r1;
  reg [20*1-1:0] dbg_phy2clb_fixdly_rdy_upp_r2;
  reg [20*1-1:0] dbg_phy2clb_phy_rdy_low_r1;
  reg [20*1-1:0] dbg_phy2clb_phy_rdy_low_r2;
  reg [20*1-1:0] dbg_phy2clb_phy_rdy_upp_r1;
  reg [20*1-1:0] dbg_phy2clb_phy_rdy_upp_r2;

  always @ (posedge div_clk)
  begin
    io_address_r1                 <= #TCQ io_address;
    pllGate_r1                    <= #TCQ pllGate;
    dbg_phy2clb_fixdly_rdy_low_r1 <= #TCQ phy2clb_fixdly_rdy_low;
    dbg_phy2clb_fixdly_rdy_upp_r1 <= #TCQ phy2clb_fixdly_rdy_upp;
    dbg_phy2clb_phy_rdy_low_r1    <= #TCQ phy2clb_phy_rdy_low;
    dbg_phy2clb_phy_rdy_upp_r1    <= #TCQ phy2clb_phy_rdy_upp;

    io_address_r2                 <= #TCQ io_address_r1;
    pllGate_r2                    <= #TCQ pllGate_r1;
    dbg_phy2clb_fixdly_rdy_low_r2 <= #TCQ dbg_phy2clb_fixdly_rdy_low_r1;
    dbg_phy2clb_fixdly_rdy_upp_r2 <= #TCQ dbg_phy2clb_fixdly_rdy_upp_r1;
    dbg_phy2clb_phy_rdy_low_r2    <= #TCQ dbg_phy2clb_phy_rdy_low_r1;
    dbg_phy2clb_phy_rdy_upp_r2    <= #TCQ dbg_phy2clb_phy_rdy_upp_r1;
  end

  assign dbg_io_address             = io_address_r2[27:0];
  assign dbg_pllGate                = pllGate_r2;
  assign dbg_phy2clb_fixdly_rdy_low = dbg_phy2clb_fixdly_rdy_low_r2;
  assign dbg_phy2clb_fixdly_rdy_upp = dbg_phy2clb_fixdly_rdy_upp_r2;
  assign dbg_phy2clb_phy_rdy_low    = dbg_phy2clb_phy_rdy_low_r2;
  assign dbg_phy2clb_phy_rdy_upp    = dbg_phy2clb_phy_rdy_upp_r2;

// MB IO bus signals
wire [31:0] io_read_data_riuclk, io_read_data;
wire    io_ready_lvl_riuclk, io_ready_lvl;
wire io_addr_strobe_lvl_riuclk, io_addr_strobe_lvl;
wire [31:0] io_address_riuclk;
wire [31:0] io_write_data_riuclk, io_write_data;
wire        io_write_strobe_riuclk, io_write_strobe;

wire                      [7:0] mc_ACT_n;
wire         [ADDR_WIDTH*8-1:0] mc_ADR;
wire         [BANK_WIDTH*8-1:0] mc_BA;
wire   [BANK_GROUP_WIDTH*8-1:0] mc_BG;
wire          [CKE_WIDTH*8-1:0] mc_CKE;
wire           [CS_WIDTH*8-1:0] mc_CS_n;
wire           [DM_WIDTH*8-1:0] mc_DMOut_n;
wire           [DQ_WIDTH*8-1:0] mc_DQOut;
wire                      [7:0] mc_DQSOut;
wire          [ODT_WIDTH*8-1:0] mc_ODT;
wire                      [1:0] mcCasSlot;
wire                            mcCasSlot2;
wire                            mcRdCAS;
wire                            mcWrCAS;
wire                      [5:0] tCWL;
wire                            winInjTxn;
wire                            winRmw;
wire                            gt_data_ready;
wire  [DATA_BUF_ADDR_WIDTH-1:0] winBuf;
wire                      [1:0] winRank;
reg                      [1:0] winRank_phy;

  // native<emcCal signals
  wire                      [1:0] bank;
  wire                      [2:0] cmd; // 3'b001-Read, 3'b000-Write
  wire                      [9:0] col;
  wire  [DATA_BUF_ADDR_WIDTH-1:0] dBufAdr;
  wire                      [1:0] group;
  wire                            hiPri;
  wire                            autoprecharge;
  wire                      [1:0] rank;
  wire                      [1:0] rank_int;
  wire            [ROW_WIDTH-1:0] row;
  wire                     [17:0] row_mc_phy;
  wire                            size; // 0 BC4, 1 BL8
  wire                            useAdr;
  wire           [PAYLOAD_WIDTH*8-1:0]    wr_data_ni2mc;
  wire           [PAYLOAD_DM_WIDTH*8-1:0] wr_data_mask_ni2mc;
  wire           [DQ_WIDTH*8-1:0]         wr_data_mc2phy;
  wire           [DM_WIDTH*8-1:0]         wr_data_mask_mc2phy;

  wire                            accept;
  wire                            accept_ns;
  wire      [PAYLOAD_WIDTH*8-1:0] rd_data_mc2ni;
  wire  [DATA_BUF_ADDR_WIDTH-1:0] rd_data_addr_mc2ni;
  wire                            rd_data_en_mc2ni;
  wire                            rd_data_end_mc2ni;
  wire           [DQ_WIDTH*8-1:0] rd_data_phy2mc_xif;  // Xiphy format read data
  wire  [DATA_BUF_ADDR_WIDTH-1:0] rd_data_addr_phy2mc;
  wire                            rd_data_en_phy2mc;
  wire                            rd_data_end_phy2mc;
  wire                            per_rd_done;
  wire                            rmw_rd_done;
  wire  [DATA_BUF_ADDR_WIDTH-1:0] wrDataAddr;
  wire                            wrDataEn;
  wire                            correct_en;
  wire                            wrDataOffset;
  wire                      [7:0] raw_not_ecc;
//  wire                            eccErrAddr;
  wire                            rdDataOffset;
  wire                            ref_req;
  wire                            zq_req;
  wire                            ref_ack;
  wire                            zq_ack;

  wire  [7:0]                     phy2clb_rd_dq_bits; // selected raw read data from phy (includes all bytes)
  wire  [8:0]                     bisc_byte;      // bit select from Microblaze to ready rd_dq_bits
  wire [15:0]                     riu2clb_vld_read_data; // riu read data selected by bisc_byte
  wire                            io_addr_strobe_clb2riu_riuclk;


    
  wire [7:0]              riu_nibble_8;    // selected physical nibble in PHY - status to MB
  wire [5:0]              riu_addr_cal;
  wire [20-1:0]           riu2clb_valid_r1_riuclk, riu2clb_valid_riuclk, riu2clb_valid; 
                                           // max number of bytes possible
  wire [7:0]              cal_RESET_n;
  (* dont_touch = "true" *) reg rst_r1;
  (* dont_touch = "true" *) reg en_vtc_in;

  wire 			  ui_busy;
  wire 			  mc_block_req;
  wire 			  stop_gate_tracking_req;
  wire 			  stop_gate_tracking_ack;
  wire 			  srx_cke0_release;
  wire 			  srx_req;
  wire [31:0]             dbg_out_phy;
  wire [31:0]             dbg_out_mc;
  wire 			  cmd_complete;

  wire                    en_vtc_riuclk;
  wire                    ub_rst_out_riuclk;
  wire                    phy_ready_riuclk;
  wire                    bisc_complete_riuclk;
  wire                    phy_ready;
  wire                    bisc_complete;
  wire                    en_vtc;
  wire                    fab_rst_sync;


  assign app_save_ack      = stop_gate_tracking_ack & cmd_complete;
  assign srx_cke0_release  = 1'b0;
  assign srx_req           = 1'b0;
  assign dbg_out           = dbg_out_phy | dbg_out_mc;

  assign rank = (RANKS == 1) ? 2'b00 : (RANKS == 2) ? {1'b0,rank_int[0]} : rank_int;
  wire [LR_WIDTH-1:0] lr_int;
  wire [2:0]          lr = {{(3-LR_WIDTH){1'b0}}, lr_int};
  assign row_mc_phy = {{(18-ROW_WIDTH){1'b0}}, row};

  assign ALT_ddr4_reset_n = cal_RESET_n[0]; //AK Added: __SRAI (added for PR compitibility)
   
ddr4_core_phy u_mig_ddr4_phy
    (
      .sys_clk_p           (sys_clk_p)
     ,.sys_clk_n           (sys_clk_n)
     ,.mmcm_lock           (mmcm_lock)
     ,.pllGate             (pllGate)
     ,.div_clk             (div_clk)
     ,.div_clk_rst         (div_clk_rst)
     ,.riu_clk             (riu_clk)
     ,.riu_clk_rst         (riu_clk_rst)
     ,.pll_lock            (pll_lock)
     ,.sys_clk_in          (sys_clk_in)
     ,.mmcm_clk_in         (mmcm_clk_in)

     ,.ddr4_act_n          (ddr4_act_n)
     ,.ddr4_adr            (ddr4_adr)
     ,.ddr4_ba             (ddr4_ba)
     ,.ddr4_bg             (ddr4_bg)
     ,.ddr4_c              (ddr4_c)
     ,.ddr4_parity        (ddr4_parity)
     ,.ddr4_cke            (ddr4_cke)
     ,.ddr4_odt            (ddr4_odt)
     ,.ddr4_cs_n           (ddr4_cs_n)
     ,.ddr4_ck_t           (ddr4_ck_t)
     ,.ddr4_ck_c           (ddr4_ck_c)
     ,.ddr4_reset_n        (ddr4_reset_n)
     ,.ddr4_dm_dbi_n       (ddr4_dm_dbi_n)
     ,.ddr4_dq             (ddr4_dq)
     ,.ddr4_dqs_c          (ddr4_dqs_c)
     ,.ddr4_dqs_t          (ddr4_dqs_t)


     ,.en_vtc_riuclk        (en_vtc_riuclk)
     ,.ub_rst_out_riuclk    (ub_rst_out_riuclk)
     ,.cal_RESET_n          (cal_RESET_n)
     
     ,.riu_nibble_8         (riu_nibble_8)
     ,.riu_addr_cal         (riu_addr_cal)
     
     ,.phy_ready_riuclk     (phy_ready_riuclk)
     ,.bisc_complete_riuclk (bisc_complete_riuclk)
     ,.phy2clb_rd_dq_bits   (phy2clb_rd_dq_bits)
     ,.bisc_byte            (bisc_byte)

     ,.io_addr_strobe_clb2riu_riuclk   (io_addr_strobe_clb2riu_riuclk)
     ,.io_address_riuclk               (io_address_riuclk)
     ,.io_write_data_riuclk            (io_write_data_riuclk)
     ,.io_write_strobe_riuclk          (io_write_strobe_riuclk)
     ,.riu2clb_vld_read_data           (riu2clb_vld_read_data)
     ,.riu2clb_valid_riuclk            (riu2clb_valid_riuclk)
     ,.mcal_C                          (mcal_C) 
     ,.mcal_ODT                        (mcal_ODT)
     ,.mcal_PAR                        (mcal_PAR)
     ,.mcal_ADR                        (mcal_ADR)
     ,.mcal_BA                         (mcal_BA)
     ,.mcal_BG                         (mcal_BG)
     ,.mcal_CKE                        (mcal_CKE)
     ,.mcal_CS_n                       (mcal_CS_n)
     ,.mcal_ACT_n                      (mcal_ACT_n) // MAN - fix
     ,.ch0_mcal_DMOut_n                (ch0_mcal_DMOut_n)
     ,.ch0_mcal_DQOut                  (ch0_mcal_DQOut)
     ,.ch0_mcal_DQSOut                 (ch0_mcal_DQSOut)
     ,.ch0_mcal_clb2phy_fifo_rden      (ch0_mcal_clb2phy_fifo_rden)
     ,.ch0_mcal_clb2phy_t_b_upp        (ch0_mcal_clb2phy_t_b_upp)
     ,.ch0_mcal_clb2phy_t_b_low        (ch0_mcal_clb2phy_t_b_low)
     ,.ch0_mcal_clb2phy_rden_upp       (ch0_mcal_clb2phy_rden_upp)
     ,.ch0_mcal_clb2phy_rden_low       (ch0_mcal_clb2phy_rden_low)
     ,.ch0_mcal_clb2phy_wrcs0_upp      (ch0_mcal_clb2phy_wrcs0_upp)
     ,.ch0_mcal_clb2phy_wrcs1_upp      (ch0_mcal_clb2phy_wrcs1_upp)
     ,.ch0_mcal_clb2phy_wrcs0_low      (ch0_mcal_clb2phy_wrcs0_low)
     ,.ch0_mcal_clb2phy_wrcs1_low      (ch0_mcal_clb2phy_wrcs1_low)
     ,.ch0_mcal_clb2phy_rdcs0_upp      (ch0_mcal_clb2phy_rdcs0_upp)
     ,.ch0_mcal_clb2phy_rdcs1_upp      (ch0_mcal_clb2phy_rdcs1_upp)
     ,.ch0_mcal_clb2phy_rdcs0_low      (ch0_mcal_clb2phy_rdcs0_low)
     ,.ch0_mcal_clb2phy_rdcs1_low      (ch0_mcal_clb2phy_rdcs1_low)
     ,.ch0_mcal_clb2phy_odt_upp        (ch0_mcal_clb2phy_odt_upp)
     ,.ch0_mcal_clb2phy_odt_low        (ch0_mcal_clb2phy_odt_low)

     ,.mcal_rd_vref_value              (mcal_rd_vref_value)
     ,.mcal_DMIn_n                     (mcal_DMIn_n)
     ,.mcal_DQIn                       (mcal_DQIn)

     ,.ch1_mcal_DMOut_n                (ch1_mcal_DMOut_n)
     ,.ch1_mcal_DQOut                  (ch1_mcal_DQOut)
     ,.ch1_mcal_DQSOut                 (ch1_mcal_DQSOut)
     ,.ch1_mcal_clb2phy_fifo_rden      (ch1_mcal_clb2phy_fifo_rden)
     ,.ch1_mcal_clb2phy_t_b_upp        (ch1_mcal_clb2phy_t_b_upp)
     ,.ch1_mcal_clb2phy_t_b_low        (ch1_mcal_clb2phy_t_b_low)
     ,.ch1_mcal_clb2phy_rden_upp       (ch1_mcal_clb2phy_rden_upp)
     ,.ch1_mcal_clb2phy_rden_low       (ch1_mcal_clb2phy_rden_low)
     ,.ch1_mcal_clb2phy_wrcs0_upp      (ch1_mcal_clb2phy_wrcs0_upp)
     ,.ch1_mcal_clb2phy_wrcs1_upp      (ch1_mcal_clb2phy_wrcs1_upp)
     ,.ch1_mcal_clb2phy_wrcs0_low      (ch1_mcal_clb2phy_wrcs0_low)
     ,.ch1_mcal_clb2phy_wrcs1_low      (ch1_mcal_clb2phy_wrcs1_low)
     ,.ch1_mcal_clb2phy_rdcs0_upp      (ch1_mcal_clb2phy_rdcs0_upp)
     ,.ch1_mcal_clb2phy_rdcs1_upp      (ch1_mcal_clb2phy_rdcs1_upp)
     ,.ch1_mcal_clb2phy_rdcs0_low      (ch1_mcal_clb2phy_rdcs0_low)
     ,.ch1_mcal_clb2phy_rdcs1_low      (ch1_mcal_clb2phy_rdcs1_low)
     ,.ch1_mcal_clb2phy_odt_upp        (ch1_mcal_clb2phy_odt_upp)
     ,.ch1_mcal_clb2phy_odt_low        (ch1_mcal_clb2phy_odt_low)

     ,.phy2clb_fixdly_rdy_low_riuclk   (phy2clb_fixdly_rdy_low_riuclk)
     ,.phy2clb_fixdly_rdy_upp_riuclk   (phy2clb_fixdly_rdy_upp_riuclk)
     ,.phy2clb_phy_rdy_low_riuclk      (phy2clb_phy_rdy_low_riuclk)
     ,.phy2clb_phy_rdy_upp_riuclk      (phy2clb_phy_rdy_upp_riuclk)
// DDR3 signals
     ,.mcal_RAS_n                      (8'b0)
     ,.mcal_CAS_n                      (8'b0)
     ,.mcal_WE_n                       (8'b0)
     ,.dbg_bus                         (dbg_bus)
);

   // unused mc outputs in DDR4 mode
   wire                  [7:0] mc_RAS_n;
   wire                  [7:0] mc_CAS_n;
   wire                  [7:0] mc_WE_n;

localparam LRDIMM_DELAY = 6; // This is to consider the tPDM delays through Data buffers and the Trace delays on the LRDIMM

localparam tWTR_S_HOST = (LRDIMM_MODE=="ON") ? tWTR_S + LRDIMM_DELAY : tWTR_S;
localparam tWTR_L_HOST = (LRDIMM_MODE=="ON") ? tWTR_L + LRDIMM_DELAY : tWTR_L;
localparam tRTW_HOST   = (LRDIMM_MODE=="ON") ? tRTW + LRDIMM_DELAY : tRTW;

ddr4_v2_1_1_mc # (
    .ABITS            (ADDR_WIDTH)
   ,.COLBITS          (COL_WIDTH)
   ,.BABITS           (BANK_WIDTH)
   ,.BGBITS           (BANK_GROUP_WIDTH)
   ,.CKEBITS          (CKE_WIDTH)
   ,.S_HEIGHT         (S_HEIGHT)
   ,.LR_WIDTH         (LR_WIDTH)
   ,.ALIAS_PAGE       (ALIAS_PAGE)
   ,.ALIAS_P_CNT      (ALIAS_P_CNT)
   ,.CSBITS           (CS_WIDTH)
   ,.ODTBITS          (ODT_WIDTH)
   ,.MEM              (DRAM_TYPE)
   ,.ECC              (ECC)
   ,.PAYLOAD_WIDTH    (PAYLOAD_WIDTH)
   ,.PAYLOAD_DM_WIDTH (PAYLOAD_DM_WIDTH)
   ,.ECC_WIDTH        (ECC_WIDTH)
   ,.ADDR_FIFO_WIDTH  (ADDR_FIFO_WIDTH_INT)
   ,.DQ_WIDTH         (DQ_WIDTH)
   ,.DM_WIDTH         (DM_WIDTH)
   ,.DQS_WIDTH        (DQS_WIDTH)
   ,.DBAW             (DATA_BUF_ADDR_WIDTH)
   ,.NUMREF           (NUMREF)
   ,.RANKS            (RANKS)
   ,.ORDERING         (ORDERING)
   ,.TXN_FIFO_BYPASS  (TXN_FIFO_BYPASS)
   ,.TXN_FIFO_PIPE    (TXN_FIFO_PIPE)
   ,.PER_RD_PERF      (PER_RD_PERF)
   ,.CAS_FIFO_BYPASS  (CAS_FIFO_BYPASS)
   ,.NOP_ADD_LOW        (NOP_ADD_LOW)
   ,.STARVATION_EN      (STARVATION_EN)
   ,.STARVE_COUNT_WIDTH (STARVE_COUNT_WIDTH)   
   ,.DDR4_CLAMSHELL     (DDR4_CLAMSHELL)
   ,.MEM_CONFIG       (MEMORY_CONFIGURATION)
   ,.tFAW             (tFAW)
   ,.tFAW_dlr         (tFAW_dlr)
   ,.tRTW             (tRTW_HOST)
   ,.tWTR_L           (tWTR_L_HOST)
   ,.tWTR_S           (tWTR_S_HOST)
   ,.tRFC             (tRFC)
   ,.tRFC_dlr         (tRFC_dlr)
   ,.tREFI            (tREFI)
   ,.ZQINTVL          (ZQINTVL)
   ,.tZQCS            (tZQCS)
   ,.tRP              (tRP)
   ,.tRRD_L           (tRRD_L)
   ,.tRRD_S           (tRRD_S)
   ,.tRRD_dlr         (tRRD_dlr)
   ,.tRAS             (tRAS)
   ,.tRCD             (tRCD)
   ,.tRTP             (tRTP)
   ,.tWR              (tWR)
   ,.tCCD_3ds         (tCCD_3ds)
   ,.MR6              (MR6)
   ,.PER_RD_INTVL     (PER_RD_INTVL)
   ,.ODTWR            (ODTWR)
   ,.ODTWRDEL         (ODTWRDEL)
   ,.ODTWRDUR         (ODTWRDUR)
   ,.ODTWRODEL        (ODTWRODEL)
   ,.ODTWRODUR        (ODTWRODUR)
   ,.ODTRD            (ODTRD)
   ,.ODTRDDEL         (ODTRDDEL)
   ,.ODTRDDUR         (ODTRDDUR)
   ,.ODTRDODEL        (ODTRDODEL)
   ,.ODTRDODUR        (ODTRDODUR)
   ,.ODTNOP           (ODTNOP)
   ,.TCQ              (TCQ/1000)
) u_ddr_mc (
    .clk      (div_clk)
   ,.rst      (div_clk_rst)
   ,.calDone  (calDone)
   ,.tCWL     (tCWL)

   // Outputs to PHY
   ,.mc_ACT_n (mc_ACT_n)
   ,.mc_RAS_n (mc_RAS_n)
   ,.mc_CAS_n (mc_CAS_n)
   ,.mc_WE_n  (mc_WE_n)
   ,.mc_ADR   (mc_ADR)
   ,.mc_BA    (mc_BA)
   ,.mc_BG    (mc_BG)
   ,.mc_C     (mc_C)
   ,.mc_CKE   (mc_CKE)
   ,.mc_CS_n  (mc_CS_n)
   ,.mc_ODT   (mc_ODT)
   ,.wr_data_mc2phy      (wr_data_mc2phy)
   ,.wr_data_mask_mc2phy (wr_data_mask_mc2phy)
   ,.wr_data_addr_phy2mc (wrDataAddr)

   // control outputs
   ,.casSlot       (mcCasSlot)
   ,.casSlot2      (mcCasSlot2)
   ,.rdCAS         (mcRdCAS)
   ,.wrCAS         (mcWrCAS)
   ,.winInjTxn     (winInjTxn)
   ,.winRmw        (winRmw)
   ,.gt_data_ready (gt_data_ready)
   ,.winBuf        (winBuf)
   ,.win_rank_cas  (winRank)

   // user interface
   ,.rank     (rank)
   ,.bank     (bank)
   ,.group    (group[BANK_GROUP_WIDTH-1:0])
   ,.lr       (lr)
   ,.row      (row_mc_phy[ADDR_WIDTH-1:0])
   ,.col      (col)
   ,.cmd      (cmd)
   ,.ap       (autoprecharge)
   ,.hiPri    (hiPri)
   ,.size     (size)
   ,.accept   (accept)
   ,.accept_ns(accept_ns)
   ,.useAdr   (useAdr)
   ,.dBufAdr  (dBufAdr)
   ,.ref_req  (ref_req)
   ,.zq_req   (zq_req)
   ,.ref_ack  (ref_ack)
   ,.zq_ack   (zq_ack)
   ,.raw_not_ecc         (raw_not_ecc)
   ,.correct_en          (correct_en)
   ,.wr_data_ni2mc       (wr_data_ni2mc)
   ,.wr_data_mask_ni2mc  (wr_data_mask_ni2mc)
   ,.rd_data_mc2ni       (rd_data_mc2ni)
   ,.rd_data_addr_mc2ni  (rd_data_addr_mc2ni)
   ,.rd_data_en_mc2ni    (rd_data_en_mc2ni)
   ,.rd_data_end_mc2ni   (rd_data_end_mc2ni)
   ,.ecc_err_addr        (ecc_err_addr)
   ,.eccSingle           (eccSingle)
   ,.eccMultiple         (eccMultiple)
   ,.rd_data_phy2mc      (rd_data_phy2mc)
   ,.fi_xor_we           (fi_xor_we)
   ,.fi_xor_wrdata       (fi_xor_wrdata)
   ,.fi_xor_wrdata_en    (wrDataEn)

   // Inputs from Phy
   ,.per_rd_done         (per_rd_done)
   ,.rmw_rd_done         (rmw_rd_done)
   ,.rd_data_phy2mc_xif  (rd_data_phy2mc_xif)
   ,.rd_data_addr_phy2mc (rd_data_addr_phy2mc)
   ,.rd_data_en_phy2mc   (rd_data_en_phy2mc)
   ,.rd_data_end_phy2mc  (rd_data_end_phy2mc)

   ,.sre_req                 (app_sr_req)
   ,.sre_ack                 (app_sr_active)
   ,.ui_busy                 (ui_busy) 
   ,.mc_block_req            (mc_block_req)
   ,.stop_gate_tracking_req  (stop_gate_tracking_req)
   ,.stop_gate_tracking_ack  (stop_gate_tracking_ack)
   ,.cmd_complete            (cmd_complete)
   ,.srx_cke0_release        (srx_cke0_release)
   ,.srx_req                 (srx_req)
   ,.dbg_out                 (dbg_out_mc)
);

  assign rdDataOffset = 1'b0;
  assign wrDataOffset = 1'b0;
  wire sr_req; // unused ui output port

  ddr4_v2_1_1_ui #
    (
     .MEM                                (DRAM_TYPE),
     .TCQ                                (TCQ),
     .ADDR_WIDTH                         (APP_ADDR_WIDTH),
     .APP_DATA_WIDTH                     (APP_DATA_WIDTH),
     .APP_MASK_WIDTH                     (APP_MASK_WIDTH),
     .BANK_WIDTH                         (BANK_WIDTH),
     .BANK_GROUP_WIDTH                   (BANK_GROUP_WIDTH),
     .COL_WIDTH                          (COL_WIDTH),
     .ROW_WIDTH                          (ROW_WIDTH),
     .DATA_BUF_ADDR_WIDTH                (DATA_BUF_ADDR_WIDTH),
     .EARLY_WR_DATA                      (EARLY_WR_DATA),
     .ECC                                (ECC),
     .ECC_TEST                           ("OFF"),
     .ORDERING                           (ORDERING),
     .nCK_PER_CLK                        (4),
     .RANKS                              (RANKS),
     .REG_CTRL                           (REG_CTRL),
     .RANK_WIDTH                         (RANK_WIDTH),
     .AUTO_AP_COL_A3                     (AUTO_AP_COL_A3),
     .S_HEIGHT                           (S_HEIGHT),
     .LR_WIDTH                           (LR_WIDTH),
     .MEM_ADDR_ORDER                     (MEM_ADDR_ORDER)
    ) u_ddr_ui
    (
  // Outputs
    .wr_data_mask                        (wr_data_mask_ni2mc),
    .wr_data                             (wr_data_ni2mc),
    .use_addr                            (useAdr),
    .size                                (size),
    .row                                 (row),
    .rank                                (rank_int[RANK_WIDTH-1:0]),
    .lr                                  (lr_int),
    .hi_priority                         (hiPri),
    .autoprecharge                       (autoprecharge),
    .data_buf_addr                       (dBufAdr),
    .col                                 (col),
    .cmd                                 (cmd),
    .bank                                (bank),
    .group                               (group[BANK_GROUP_WIDTH-1:0]),
    .app_wdf_rdy                         (app_wdf_rdy),
    .app_rdy                             (app_rdy),
    .app_rd_data_valid                   (app_rd_data_valid),
    .app_rd_data_end                     (app_rd_data_end),
    .app_rd_data                         (app_rd_data),
    .app_ecc_multiple_err                (app_ecc_multiple_err),
    .app_ref_ack                         (app_ref_ack),
    .app_zq_ack                          (app_zq_ack),
    .raw_not_ecc                         (raw_not_ecc),
    .correct_en                          (correct_en),
    .sr_req                              (sr_req),
    .ref_req                             (ref_req),
    .zq_req                              (zq_req),

  // Inputs
    .clk                                 (div_clk),
    .rst                                 (div_clk_rst),
    .app_en                              (app_en),
    .app_cmd                             (app_cmd),
    .app_addr                            (app_addr),
    .app_wdf_wren                        (app_wdf_wren),
    .app_wdf_mask                        (app_wdf_mask),
    .app_wdf_end                         (app_wdf_end),
    .app_wdf_data                        (app_wdf_data),
    .app_sz                              (1'b1),
    .app_raw_not_ecc                     (app_raw_not_ecc),
    .app_hi_pri                          (1'b0),
    .app_autoprecharge                   (app_autoprecharge),
    .app_correct_en                      (app_correct_en_i),
    .app_ref_req                         (app_ref_req),
    .app_sr_req                          (app_sr_req),
    .app_zq_req                          (app_zq_req),
    .wr_data_offset                      (wrDataOffset),
    .wr_data_en                          (wrDataEn),
    .wr_data_addr                        (wrDataAddr),
    .rd_data_offset                      (rdDataOffset),
    .rd_data_end                         (rd_data_end_mc2ni),
    .rd_data_en                          (rd_data_en_mc2ni),
    .rd_data_addr                        (rd_data_addr_mc2ni),
    .rd_data                             (rd_data_mc2ni),
    .ecc_multiple                        (eccMultiple),
    .accept_ns                           (accept_ns),
    .accept                              (accept),
    .ref_ack                             (ref_ack),
    .zq_ack                              (zq_ack),
    .ui_busy                             (ui_busy),
    .mc_block_req                        (mc_block_req)
    );

  // RDIMM register RC3X
  localparam mts_min = 1240;
  localparam mts_max = 3200;
  localparam mts_gap = 20;
  localparam mts = 2000000/tCK;
  localparam mts_final = (mts>mts_max) ? mts_max :
             (mts<mts_min) ? mts_min :
             mts;
  localparam [7:0] ddr4_reg_rc3x = ((mts_final-mts_min)>=1) ? (mts_final-mts_min-1)/mts_gap : 0;
  localparam         DDR4_REG_RC3X = {5'b0_0011, ddr4_reg_rc3x[7:0]};

  // In LRDIMM configuration, all the Ranks of the card/slot are mapped to the same XiPHY Rank.
  // Map the controller logical rank number to the XiPHY physical rank number based on the number of slots and dual_rank/quad_rank configuration.
  always @(*) begin
    if(LRDIMM_MODE=="ON") begin
      if(SLOT1_CONFIG==8'h00) begin // Single Slot
        winRank_phy = 'b0;
      end else begin // Dual Slot
        if(RANKS==4) // Total number of Ranks
          winRank_phy = (winRank >> 1);
        else if(RANKS==8)
          winRank_phy = (winRank >> 2);
        else // if(RANKS==2)
          winRank_phy = winRank;
      end
    end else begin
      winRank_phy = winRank;
    end
  end

  // PLL Multiply and Divide values
  // write PLL VCO multiplier
  localparam CLKFBOUT_MULT_PLL  = (CLKOUTPHY_MODE == "VCO_2X") ?
                                    ((nCK_PER_CLK == 4) ? 4 : 2) : 
                                  (CLKOUTPHY_MODE == "VCO") ? 
                                    ((nCK_PER_CLK == 4) ? 8 : 4)
                                  : ((nCK_PER_CLK == 4) ? 16 : 8);
  // VCO output divisor for PLL clkout0
  localparam CLKOUT0_DIVIDE_PLL = (CLKOUTPHY_MODE == "VCO_2X") ? 1 : 
                                  (CLKOUTPHY_MODE == "VCO") ? 2 : 4;

// Calibration Logic 

ddr4_v2_1_1_cal_top # (
    .ABITS          (ADDR_WIDTH)
   ,.BABITS         (BANK_WIDTH)
   ,.BGBITS         (BANK_GROUP_WIDTH)
   ,.S_HEIGHT       (S_HEIGHT)
   ,.LR_WIDTH       (LR_WIDTH)
   ,.CKEBITS        (CKE_WIDTH)
   ,.CKBITS         (CK_WIDTH)
   ,.COLBITS        (COL_WIDTH)
   ,.CSBITS         (CS_WIDTH)
   ,.ODTBITS        (ODT_WIDTH)
   ,.ODTWR          (ODTWR)
   ,.ODTWRDEL       (ODTWRDEL)
   ,.ODTWRDUR       (ODTWRDUR)
   ,.ODTWRODEL      (ODTWRODEL)
   ,.ODTWRODUR      (ODTWRODUR)
   ,.ODTRD          (ODTRD)
   ,.ODTRDDEL       (ODTRDDEL)
   ,.ODTRDDUR       (ODTRDDUR)
   ,.ODTRDODEL      (ODTRDODEL)
   ,.ODTRDODUR      (ODTRDODUR)
   ,.ODTNOP         (ODTNOP)
   ,.MEM            (DRAM_TYPE)
   ,.DQ_WIDTH       (DQ_WIDTH)
   ,.DBYTES         (DBYTES)
   ,.DBAW           (DATA_BUF_ADDR_WIDTH)
   ,.SAVE_RESTORE   (SAVE_RESTORE)
   ,.SELF_REFRESH   (SELF_REFRESH)

   ,.MR0            (MR0)
   ,.MR1            (MR1)
   ,.MR2            (MR2)
   ,.MR3            (MR3)
   ,.MR4            (MR4)
   ,.MR5            (MR5)
   ,.MR6            (MR6)

   ,.RD_VREF_VAL    (RD_VREF_VAL)
   ,.SLOT0_CONFIG   (SLOT0_CONFIG)
   ,.SLOT1_CONFIG   (SLOT1_CONFIG)
   ,.SLOT0_FUNC_CS  (SLOT0_FUNC_CS)
   ,.SLOT1_FUNC_CS  (SLOT1_FUNC_CS)
   ,.SLOT0_ODD_CS   (SLOT0_ODD_CS)
   ,.SLOT1_ODD_CS   (SLOT1_ODD_CS)

   ,.REG_CTRL       (REG_CTRL)
   ,.LRDIMM_MODE    (LRDIMM_MODE)
   ,.DDR4_DB_HIF_RTT_NOM   (DDR4_DB_HIF_RTT_NOM)
   ,.DDR4_DB_HIF_RTT_WR    (DDR4_DB_HIF_RTT_WR)
   ,.DDR4_DB_HIF_RTT_PARK  (DDR4_DB_HIF_RTT_PARK)
   ,.DDR4_DB_HIF_DI        (DDR4_DB_HIF_DI)
   ,.DDR4_DB_DIF_ODT       (DDR4_DB_DIF_ODT)
   ,.DDR4_DB_DIF_DI        (DDR4_DB_DIF_DI)
   ,.DDR4_DB_HIF_VREF      (DDR4_DB_HIF_VREF)
   ,.DDR4_DB_DIF_VREF      (DDR4_DB_DIF_VREF)
   ,.DDR4_CLAMSHELL (DDR4_CLAMSHELL)
   ,.CA_MIRROR      (CA_MIRROR)
   ,.DDR4_REG_PARITY_ENABLE (DDR4_REG_PARITY_ENABLE)
   ,.DDR4_REG_RC03  (DDR4_REG_RC03)
   ,.DDR4_REG_RC04  (DDR4_REG_RC04)
   ,.DDR4_REG_RC05  (DDR4_REG_RC05)
   ,.DDR4_REG_RC3X  (DDR4_REG_RC3X)

   ,.tCK            (tCK)
   ,.t200us         (t200us)
   ,.t500us         (t500us)
   ,.tXPR           (tXPR)
   ,.tMOD           (tMOD)
   ,.tMRD           (tMRD)
   ,.tZQINIT        (tZQINIT)
   ,.tRFC           (tRFC)
   ,.TCQ            (TCQ/1000)

   ,.MEMORY_CONFIGURATION (MEMORY_CONFIGURATION)
   ,.EARLY_WR_DATA   (EARLY_WR_DATA)
   ,.ECC             (ECC)
   ,.DRAM_WIDTH      (DRAM_WIDTH)
   ,.RANKS           (RANKS)
   ,.nCK_PER_CLK     (nCK_PER_CLK)
   ,.MEM_CODE        (MEM_CODE)

   ,.MIGRATION          (MIGRATION)
   ,.CK_SKEW            (CK_SKEW)
   ,.ADDR_SKEW          (ADDR_SKEW)
   ,.ACT_SKEW           (ACT_SKEW)
   ,.PAR_SKEW           (PAR_SKEW)
   ,.BA_SKEW            (BA_SKEW)
   ,.BG_SKEW            (BG_SKEW)
   ,.CKE_SKEW           (CKE_SKEW)
   ,.CS_SKEW            (CS_SKEW)
   ,.ODT_SKEW           (ODT_SKEW)
   ,.C_SKEW             (C_SKEW)

   ,.BYPASS_CAL         (BYPASS_CAL)
   ,.CAL_DQS_GATE       (CAL_DQS_GATE)
   ,.CAL_WRLVL          (CAL_WRLVL)
   ,.CAL_RDLVL          (CAL_RDLVL)
   ,.CAL_RDLVL_DBI      (CAL_RDLVL_DBI)
   ,.CAL_WR_DQS_DQ      (CAL_WR_DQS_DQ)
   ,.CAL_WR_DQS_DM_DBI  (CAL_WR_DQS_DM_DBI)
   ,.CAL_WRITE_LAT      (CAL_WRITE_LAT)
   ,.CAL_RDLVL_COMPLEX  (CAL_RDLVL_COMPLEX)
   ,.CAL_WR_DQS_COMPLEX (CAL_WR_DQS_COMPLEX)
   ,.CAL_RD_VREF        (CAL_RD_VREF)
   ,.CAL_RD_VREF_PATTERN  (CAL_RD_VREF_PATTERN)
   ,.CAL_WR_VREF        (CAL_WR_VREF)
   ,.CAL_WR_VREF_PATTERN  (CAL_WR_VREF_PATTERN)
   ,.CAL_DQS_TRACKING   (CAL_DQS_TRACKING)
   ,.CAL_JITTER         (CAL_JITTER)
   ,.DM_DBI             (DM_DBI)
   ,.USE_CS_PORT        (USE_CS_PORT)
   ,.CPLX_PAT_LENGTH    (CPLX_PAT_LENGTH)
   ,.C_FAMILY           (C_FAMILY)

   ,.CLKFBOUT_MULT_PLL    (CLKFBOUT_MULT_PLL)
   ,.CLKOUT0_DIVIDE_PLL   (CLKOUT0_DIVIDE_PLL)
   ,.CLKFBOUT_MULT_MMCM   (CLKFBOUT_MULT_MMCM)
   ,.DIVCLK_DIVIDE_MMCM   (DIVCLK_DIVIDE_MMCM)
   ,.CLKOUT0_DIVIDE_MMCM  (CLKOUT0_DIVIDE_MMCM)
   ,.EXTRA_CMD_DELAY	  (EXTRA_CMD_DELAY)
   ,.BISC_EN              (BISC_EN)
) u_ddr_cal_top (
    .clk                         (div_clk)
   ,.rst                         (div_clk_rst)

   ,.calDone_gated               (calDone)   // calibration calDone gated with phy_ready
   ,.pllGate                     (pllGate)

   ,.io_address                  (io_address)
   ,.io_addr_strobe_lvl          (io_addr_strobe_lvl)
   ,.io_write_data               (io_write_data)
   ,.io_write_strobe             (io_write_strobe)
   ,.io_read_data                (io_read_data)
   ,.io_ready_lvl                (io_ready_lvl)
   ,.phy_ready                   (phy_ready)
   ,.bisc_complete               (bisc_complete)
   ,.en_vtc                      (en_vtc)
  //  ,.clb2phy_t_b_addr_en      (clb2phy_t_b_addr_en)

   // native
   ,.rdData                      (rd_data_phy2mc_xif)
   ,.rdDataAddr                  (rd_data_addr_phy2mc)
   ,.rdDataEn                    (rd_data_en_phy2mc)
   ,.rdDataEnd                   (rd_data_end_phy2mc)
   ,.per_rd_done                 (per_rd_done)
   ,.rmw_rd_done                 (rmw_rd_done)
   ,.wrData                      (wr_data_mc2phy)
   ,.wrDataMask                  (wr_data_mask_mc2phy)
   ,.wrDataAddr                  (wrDataAddr)   // to MC and UI
   ,.wrDataEn                    (wrDataEn) // to MC and UI

   // mc
   ,.mc_ACT_n                    (mc_ACT_n)
   ,.mc_RAS_n                    (8'b0)
   ,.mc_CAS_n                    (8'b0)
   ,.mc_WE_n                     (8'b0)
   ,.mc_ADR                      (mc_ADR)
   ,.mc_BA                       (mc_BA)
   ,.mc_BG                       (mc_BG)
   ,.mc_C                        (mc_C)
   ,.mc_CKE                      (mc_CKE)
   ,.mc_CS_n                     (mc_CS_n)
   ,.mc_ODT                      (mc_ODT)
   ,.mcCasSlot                   (mcCasSlot)
   ,.mcCasSlot2                  (mcCasSlot2)
   ,.mcRdCAS                     (mcRdCAS)
   ,.mcWrCAS                     (mcWrCAS)
   ,.winInjTxn                   (winInjTxn)
   ,.winRmw                      (winRmw)
   ,.gt_data_ready               (gt_data_ready)
   ,.winBuf                      (winBuf)
   ,.winRank                     (winRank_phy)

   ,.mcal_ACT_n                  (mcal_ACT_n)
   ,.mcal_CAS_n                  (mcal_CAS_n)
   ,.mcal_RAS_n                  (mcal_RAS_n)
   ,.mcal_WE_n                   (mcal_WE_n)
   ,.mcal_ADR                    (mcal_ADR)
   ,.mcal_BA                     (mcal_BA)
   ,.mcal_BG                     (mcal_BG)
   ,.mcal_C                      (mcal_C)
   ,.mcal_CKE                    (mcal_CKE)
   ,.mcal_CS_n                   (mcal_CS_n)

   ,.mcal_DMOut_n                (ch0_mcal_DMOut_n)
   ,.mcal_DQOut                  (ch0_mcal_DQOut)
   ,.mcal_DQSOut                 (ch0_mcal_DQSOut)
   ,.mcal_ODT                    (mcal_ODT)
   ,.mcal_PAR                    (mcal_PAR)
   ,.mcal_clb2phy_fifo_rden      (ch0_mcal_clb2phy_fifo_rden)
   ,.mcal_clb2phy_t_b_upp        (ch0_mcal_clb2phy_t_b_upp)
   ,.mcal_clb2phy_t_b_low        (ch0_mcal_clb2phy_t_b_low)
   ,.mcal_clb2phy_rden_upp       (ch0_mcal_clb2phy_rden_upp)
   ,.mcal_clb2phy_rden_low       (ch0_mcal_clb2phy_rden_low)
   ,.mcal_clb2phy_wrcs0_upp      (ch0_mcal_clb2phy_wrcs0_upp)
   ,.mcal_clb2phy_wrcs1_upp      (ch0_mcal_clb2phy_wrcs1_upp)
   ,.mcal_clb2phy_wrcs0_low      (ch0_mcal_clb2phy_wrcs0_low)
   ,.mcal_clb2phy_wrcs1_low      (ch0_mcal_clb2phy_wrcs1_low)
   ,.mcal_clb2phy_rdcs0_upp      (ch0_mcal_clb2phy_rdcs0_upp)
   ,.mcal_clb2phy_rdcs1_upp      (ch0_mcal_clb2phy_rdcs1_upp)
   ,.mcal_clb2phy_rdcs0_low      (ch0_mcal_clb2phy_rdcs0_low)
   ,.mcal_clb2phy_rdcs1_low      (ch0_mcal_clb2phy_rdcs1_low)
   ,.mcal_clb2phy_odt_upp        (ch0_mcal_clb2phy_odt_upp)
   ,.mcal_clb2phy_odt_low        (ch0_mcal_clb2phy_odt_low)

   ,.mcal_rd_vref_value          (mcal_rd_vref_value)

   ,.ch1_mcal_DMOut_n                (ch1_mcal_DMOut_n)
   ,.ch1_mcal_DQOut                  (ch1_mcal_DQOut)
   ,.ch1_mcal_DQSOut                 (ch1_mcal_DQSOut)
   ,.ch1_mcal_clb2phy_fifo_rden      (ch1_mcal_clb2phy_fifo_rden)
   ,.ch1_mcal_clb2phy_t_b_upp        (ch1_mcal_clb2phy_t_b_upp)
   ,.ch1_mcal_clb2phy_t_b_low        (ch1_mcal_clb2phy_t_b_low)
   ,.ch1_mcal_clb2phy_rden_upp       (ch1_mcal_clb2phy_rden_upp)
   ,.ch1_mcal_clb2phy_rden_low       (ch1_mcal_clb2phy_rden_low)
   ,.ch1_mcal_clb2phy_wrcs0_upp      (ch1_mcal_clb2phy_wrcs0_upp)
   ,.ch1_mcal_clb2phy_wrcs1_upp      (ch1_mcal_clb2phy_wrcs1_upp)
   ,.ch1_mcal_clb2phy_wrcs0_low      (ch1_mcal_clb2phy_wrcs0_low)
   ,.ch1_mcal_clb2phy_wrcs1_low      (ch1_mcal_clb2phy_wrcs1_low)
   ,.ch1_mcal_clb2phy_rdcs0_upp      (ch1_mcal_clb2phy_rdcs0_upp)
   ,.ch1_mcal_clb2phy_rdcs1_upp      (ch1_mcal_clb2phy_rdcs1_upp)
   ,.ch1_mcal_clb2phy_rdcs0_low      (ch1_mcal_clb2phy_rdcs0_low)
   ,.ch1_mcal_clb2phy_rdcs1_low      (ch1_mcal_clb2phy_rdcs1_low)
   ,.ch1_mcal_clb2phy_odt_upp        (ch1_mcal_clb2phy_odt_upp)
   ,.ch1_mcal_clb2phy_odt_low        (ch1_mcal_clb2phy_odt_low)

   ,.mcal_DMIn_n                     (mcal_DMIn_n)
   ,.mcal_DQIn                       (mcal_DQIn)

   ,.phy2clb_rd_dq_bits              (phy2clb_rd_dq_bits)
   ,.bisc_byte                       (bisc_byte)

   ,.cal_RESET_n                 (cal_RESET_n)

   ,.riu2clb_valid               (riu2clb_valid)
   ,.dBufAdr                     (dBufAdr)
   ,.tCWL                        (tCWL[5:0])
   ,.cal_pre_status              (cal_pre_status)
   ,.cal_r0_status               (cal_r0_status)
   ,.cal_r1_status               (cal_r1_status)
   ,.cal_r2_status               (cal_r2_status)
   ,.cal_r3_status               (cal_r3_status)
   ,.cal_post_status             (cal_post_status)
   ,.cal_error                   (cal_error)
   ,.cal_error_bit               (cal_error_bit)
   ,.cal_error_nibble            (cal_error_nibble)
   ,.cal_error_code              (cal_error_code)

   ,.traffic_wr_done                (traffic_wr_done)
   ,.traffic_error                  ({{(8*(DQ_WIDTH/9)){1'b0}},traffic_error})
   ,.traffic_clr_error              (traffic_clr_error)
   ,.traffic_status_err_bit_valid   (traffic_status_err_bit_valid)
   ,.traffic_status_err_type_valid  (traffic_status_err_type_valid)
   ,.traffic_status_err_type        (traffic_status_err_type)
   ,.traffic_status_done            (traffic_status_done)
   ,.traffic_status_watch_dog_hang  (traffic_status_watch_dog_hang)
   ,.traffic_start                  (traffic_start)
   ,.traffic_rst                    (traffic_rst)
   ,.traffic_err_chk_en             (traffic_err_chk_en)
   ,.traffic_instr_addr_mode        (traffic_instr_addr_mode)
   ,.traffic_instr_data_mode        (traffic_instr_data_mode)
   ,.traffic_instr_rw_mode          (traffic_instr_rw_mode)
   ,.traffic_instr_rw_submode       (traffic_instr_rw_submode)
   ,.traffic_instr_num_of_iter      (traffic_instr_num_of_iter)
   ,.traffic_instr_nxt_instr        (traffic_instr_nxt_instr)
   ,.win_start                      (win_start)
   ,.win_status                     (win_status)

   ,.sl_iport0                   (sl_iport0)
   ,.sl_oport0                   (sl_oport0)
   ,.dbg_cal_seq                 (dbg_cal_seq)
   ,.dbg_cal_seq_cnt             (dbg_cal_seq_cnt)
   ,.dbg_cal_seq_rd_cnt          (dbg_cal_seq_rd_cnt)
   ,.dbg_rd_valid                (dbg_rd_valid)
   ,.dbg_cmp_byte                (dbg_cmp_byte)
   ,.dbg_rd_data                 (dbg_rd_data)
   ,.dbg_rd_data_cmp             (dbg_rd_data_cmp)
   ,.dbg_expected_data           (dbg_expected_data)
   ,.dbg_cplx_config             (dbg_cplx_config)
   ,.dbg_cplx_status             (dbg_cplx_status)

   // Self-Refresh and Save/Restore
   ,.stop_gate_tracking_req      (app_save_req | stop_gate_tracking_req)
   ,.stop_gate_tracking_ack      (stop_gate_tracking_ack)
   ,.app_mem_init_skip           (app_mem_init_skip)
   ,.app_restore_en              (app_restore_en)
   ,.app_restore_complete        (app_restore_complete)
   ,.xsdb_select                 (xsdb_select)
   ,.xsdb_rd_en                  (xsdb_rd_en)
   ,.xsdb_wr_en                  (xsdb_wr_en)
   ,.xsdb_addr                   (xsdb_addr)
   ,.xsdb_wr_data                (xsdb_wr_data)
   ,.xsdb_rd_data                (xsdb_rd_data)
   ,.xsdb_rdy                    (xsdb_rdy)
   ,.dbg_out                     (dbg_out_phy)
);

//######################## Fabric Clock Domain ########################
  always @(posedge div_clk) begin
    en_vtc_in    <= #TCQ en_vtc;
  end

  always @(posedge div_clk) begin
    rst_r1    <= #TCQ div_clk_rst;
  end

ddr4_core_ddr4_cal_riu #
  (
    .MCS_ECC_ENABLE   (MCS_ECC_ENABLE)
  )  u_ddr_cal_riu (
    .riu_clk                            (riu_clk)
    ,.riu_clk_rst                       (riu_clk_rst)
    ,.riu2clb_valid_riuclk              (riu2clb_valid_riuclk)
    ,.riu2clb_vld_read_data             (riu2clb_vld_read_data)
    ,.io_read_data_riuclk               (io_read_data_riuclk)
    ,.io_ready_lvl_riuclk               (io_ready_lvl_riuclk)
    ,.fab_rst_sync                      (fab_rst_sync)
    ,.reset_ub_riuclk                   (reset_ub)
    ,.riu_addr_cal                      (riu_addr_cal)
    ,.riu_nibble_8                      (riu_nibble_8)

    ,.riu2clb_valid_r1_riuclk           (riu2clb_valid_r1_riuclk)
    ,.io_addr_strobe_lvl_riuclk         (io_addr_strobe_lvl_riuclk)
    ,.io_addr_strobe_clb2riu_riuclk     (io_addr_strobe_clb2riu_riuclk)
    ,.io_address_riuclk                 (io_address_riuclk)
    ,.io_write_data_riuclk              (io_write_data_riuclk)
    ,.LMB_UE             (ddr4_mcs_lmb_ue)
    ,.LMB_CE             (ddr4_mcs_lmb_ce)
    ,.io_write_strobe_riuclk            (io_write_strobe_riuclk)
    ,.ub_rst_out_riuclk                 (ub_rst_out_riuclk)
);



  localparam INSERT_DELAY = 0; // Insert delay for simulations
  localparam HANDSHAKE_MAX_DELAYf2r = 5000; // RIU Clock Max frequency 200MHz
  localparam STATIC_MAX_DELAY = 10000; // Max delay for static signals
  localparam SYNC_MTBF = 2; // Synchronizer Depth based on MTBF

  ddr4_v2_1_1_cal_sync #(SYNC_MTBF, 1, INSERT_DELAY, STATIC_MAX_DELAY, TCQ)  u_en_vtc_sync       (riu_clk, en_vtc_in, en_vtc_riuclk);
  ddr4_v2_1_1_cal_sync #(SYNC_MTBF, 1, INSERT_DELAY, STATIC_MAX_DELAY, TCQ)  u_fab_rst_sync      (riu_clk, rst_r1, fab_rst_sync);

  ddr4_v2_1_1_cal_sync #(SYNC_MTBF, 32, INSERT_DELAY, HANDSHAKE_MAX_DELAYf2r, TCQ) u_io_read_data_sync (riu_clk, io_read_data, io_read_data_riuclk); // MAN - can we remove this sync

  ddr4_v2_1_1_cal_sync #(SYNC_MTBF, 1, INSERT_DELAY, HANDSHAKE_MAX_DELAYf2r, TCQ)  u_io_ready_lvl_sync (riu_clk, io_ready_lvl, io_ready_lvl_riuclk);

  localparam HANDSHAKE_MAX_DELAYr2f = 3000; // Fabric Clock Max frequency 333MHz

  ddr4_v2_1_1_cal_sync #(SYNC_MTBF, 1, INSERT_DELAY, STATIC_MAX_DELAY, TCQ) u_phy2clb_phy_ready_sync     (div_clk, phy_ready_riuclk, phy_ready);
  ddr4_v2_1_1_cal_sync #(SYNC_MTBF, 1, INSERT_DELAY, STATIC_MAX_DELAY, TCQ) u_phy2clb_bisc_complete_sync  (div_clk, bisc_complete_riuclk, bisc_complete);
  ddr4_v2_1_1_cal_sync #(SYNC_MTBF, 20, INSERT_DELAY, STATIC_MAX_DELAY, TCQ) u_riu2clb_valid_sync     (div_clk, riu2clb_valid_r1_riuclk, riu2clb_valid);

  ddr4_v2_1_1_cal_sync #(SYNC_MTBF, 20, INSERT_DELAY, STATIC_MAX_DELAY, TCQ) u_phy2clb_fixdly_rdy_low (div_clk, phy2clb_fixdly_rdy_low_riuclk, phy2clb_fixdly_rdy_low); // DEBUG only
  ddr4_v2_1_1_cal_sync #(SYNC_MTBF, 20, INSERT_DELAY, STATIC_MAX_DELAY, TCQ) u_phy2clb_fixdly_rdy_upp (div_clk, phy2clb_fixdly_rdy_upp_riuclk, phy2clb_fixdly_rdy_upp); // DEBUG only
  ddr4_v2_1_1_cal_sync #(SYNC_MTBF, 20, INSERT_DELAY, STATIC_MAX_DELAY, TCQ) u_phy2clb_phy_rdy_low    (div_clk, phy2clb_phy_rdy_low_riuclk, phy2clb_phy_rdy_low); // DEBUG only
  ddr4_v2_1_1_cal_sync #(SYNC_MTBF, 20, INSERT_DELAY, STATIC_MAX_DELAY, TCQ) u_phy2clb_phy_rdy_upp    (div_clk, phy2clb_phy_rdy_upp_riuclk, phy2clb_phy_rdy_upp); // DEBUG only

  ddr4_v2_1_1_cal_sync #(SYNC_MTBF, 32, INSERT_DELAY, HANDSHAKE_MAX_DELAYr2f, TCQ) u_io_addr_sync         (div_clk, io_address_riuclk, io_address); // MAN - can we remove this sync
  ddr4_v2_1_1_cal_sync #(SYNC_MTBF, 1, INSERT_DELAY, HANDSHAKE_MAX_DELAYr2f, TCQ)  u_io_write_strobe_sync (div_clk, io_write_strobe_riuclk, io_write_strobe);
  ddr4_v2_1_1_cal_sync #(SYNC_MTBF, 32, INSERT_DELAY, HANDSHAKE_MAX_DELAYr2f, TCQ) u_io_write_data_sync   (div_clk, io_write_data_riuclk, io_write_data);
  ddr4_v2_1_1_cal_sync #(SYNC_MTBF, 1, INSERT_DELAY, HANDSHAKE_MAX_DELAYr2f, TCQ) u_io_addr_strobe_lvl_sync (div_clk, io_addr_strobe_lvl_riuclk, io_addr_strobe_lvl);


//synthesis translate_off
  generate
    if (MIG_PARAM_CHECKS  == "TRUE") begin
       `include "ddr4_v2_1_1_ddr4_assert.vh"
    end
  endgenerate   
//synthesis translate_on

endmodule
