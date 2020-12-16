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
// \   \   \/     Version            : 1.1
//  \   \         Application        : MIG
//  /   /         Filename           : ddr4_v2_2_10_cal.sv
// /___/   /\     Date Last Modified : $Date: 2015/05/01 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                  ddr4_v2_2_10_cal module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ps/1ps
`define RESTORE
`define RECONFIG_INIT_RESET_1

module ddr4_v2_2_10_cal #
(
    parameter       ABITS                      = 18
   ,parameter       BABITS                     = 2
   ,parameter       BGBITS                     = 2
   ,parameter       S_HEIGHT                   = 1
   ,parameter       LR_WIDTH                   = 1
   ,parameter       CKEBITS                    = 4
   ,parameter       CKBITS                     = 1
   ,parameter       CSBITS                     = 4
   ,parameter       ODTBITS                    = 4
   ,parameter       ODTWR                      = 16'h0033
   ,parameter       ODTWRDEL                   = 5'd8
   ,parameter       ODTWRDUR                   = 4'd6
   ,parameter       ODTWRODEL                  = 5'd9
   ,parameter       ODTWRODUR                  = 4'd6
   ,parameter       ODTRD                      = 16'h0012
   ,parameter       ODTRDDEL                   = 5'd11
   ,parameter       ODTRDDUR                   = 4'd6
   ,parameter       ODTRDODEL                  = 5'd9
   ,parameter       ODTRDODUR                  = 4'd6
   ,parameter       ODTNOP                     = 16'h0000
   ,parameter       MEM                        = "DDR4"
   ,parameter       DQ_WIDTH                   = 16
   ,parameter       DBYTES                     = 4
   ,parameter       SELF_REFRESH               = 1'b0
   ,parameter       SAVE_RESTORE               = 1'b0
   ,parameter       tCK                        = 2000
   ,parameter       t200us                     = 100
   ,parameter       t500us                     = 100
   ,parameter       tXPR                       = 20
   ,parameter       tMOD                       = 24
   ,parameter       tMRD                       = 2
   ,parameter       tZQINIT                    = 65
   ,parameter       tRFC                       = 27
   ,parameter       MR0                        = 13'b000000000000
   ,parameter       MR1                        = 13'b000000000000
   ,parameter       MR1_0                      = MR1
   ,parameter       MR1_1                      = MEM == "DDR4" ? ((MR1 & ~(13'b1<<10| 13'b1<<9 | 13'b1<<8)) | (13'b0<<10| 13'b0<<9 | 13'b0<<8)) :
                                                                 ((MR1 & ~(13'b1<<9 | 13'b1<<6 | 13'b1<<2)) | (13'b0<<9 | 13'b0<<6 | 13'b0<<2))
   ,parameter       MR1_2                      = MR1
   ,parameter       MR1_3                      = MEM == "DDR4" ? ((MR1 & ~(13'b1<<10| 13'b1<<9 | 13'b1<<8)) | (13'b0<<10| 13'b0<<9 | 13'b0<<8)) :
                                                                 ((MR1 & ~(13'b1<<9 | 13'b1<<6 | 13'b1<<2)) | (13'b0<<9 | 13'b0<<6 | 13'b0<<2))
   ,parameter       MR2                        = 13'b000000000000
   ,parameter       MR3                        = 13'b000000000000
   ,parameter       MR4                        = 13'b000000000000
   ,parameter       MR5                        = 13'b000000000000
   ,parameter       MR6                        = 13'b000000000000
   ,parameter       RD_VREF_VAL                = 7'h2E
   ,parameter       SLOT0_CONFIG               = {{(8-CSBITS){1'b0}},{CSBITS{1'b1}}} // Slot0 Physical configuration
   ,parameter       SLOT1_CONFIG               = 8'b0000_0000 // Slot1 Physical configuration
   ,parameter       SLOT0_FUNC_CS              = {{(8-CSBITS){1'b0}},{CSBITS{1'b1}}} // Slot0 Functional chipselect
   ,parameter       SLOT1_FUNC_CS              = 8'b0000_0000 // Slot1 Functional chipselect
   ,parameter       SLOT0_ODD_CS               = 8'b0000_1010 // Slot0 Odd chipselect
   ,parameter       SLOT1_ODD_CS               = 8'b0000_1010 // Slot1 Odd chipselect
   
   ,parameter       REG_CTRL                   = "OFF" // RDIMM register control
   ,parameter       LRDIMM_MODE                = "OFF" // LRDIMM Mode
   ,parameter       DDR4_DB_HIF_RTT_NOM        = 4'b0000 // DDR4 Data Buffer Host I/F DQ RTT_NOM
   ,parameter       DDR4_DB_HIF_RTT_WR         = 4'b0000 // DDR4 Data Buffer Host I/F DQ RTT_WR
   ,parameter       DDR4_DB_HIF_RTT_PARK       = 4'b0000 // DDR4 Data Buffer Host I/F DQ RTT_PARK
   ,parameter       DDR4_DB_HIF_DI             = 4'b0000 // DDR4 Data Buffer Host I/F DQ Driver Impedance
   ,parameter       DDR4_DB_DIF_ODT            = 4'b0000 // DDR4 Data Buffer DRAM I/F MDQ ODT
   ,parameter       DDR4_DB_DIF_DI             = 4'b0000 // DDR4 Data Buffer DRAM I/F MDQ Driver Impedance
   ,parameter       DDR4_DB_HIF_VREF           = 8'b0000_0000 // DDR4 Data Buffer Host I/F VRef
   ,parameter       DDR4_DB_DIF_VREF           = 8'b0000_0000 // DDR4 Data Buffer DRAM I/F VRef

   ,parameter       DDR4_CLAMSHELL             = "OFF" // Clamshell architecture of DRAM parts on PCB
   ,parameter       CA_MIRROR                  = "OFF" // Address mirroring enable, RDIMM register RC0D DA[3] 
   ,parameter       DDR4_REG_PARITY_ENABLE     = "OFF"
   ,parameter       DDR4_REG_RC03              = {9'b0_0000_0011, 4'b0101} // RDIMM register RC03
   ,parameter       DDR4_REG_RC04              = {9'b0_0000_0100, 4'b0101} // RDIMM register RC04
   ,parameter       DDR4_REG_RC05              = {9'b0_0000_0101, 4'b0101} // RDIMM register RC05
   ,parameter       DDR4_REG_RC3X              = {5'b0_0011, 8'b00101100} // RDIMM register RC3X

   ,parameter       PL                         = 0
   ,parameter       RL                         = 11
   ,parameter       EXTRA_CMD_DELAY            = 0
   ,parameter       WL                         = 9
   ,parameter       BYPASS_CAL                 = "TRUE" //set to "FALSE" for calibration sim

   ,parameter       EN_PP_4R_MIR               = 0
   ,parameter       MEMORY_CONFIGURATION       = "COMPONENT"
   ,parameter       DRAM_WIDTH                 = 8      // # of DQ per DQS
   ,parameter       RANKS                      = 1      //1, 2, 3, or 4
   ,parameter       RNK_BITS                   = 1
   ,parameter       nCK_PER_CLK                = 4      // # of memory CKs per fabric CLK
   ,parameter       RTL_VERSION                = 0
   ,parameter       MEM_CODE                   = 0

   ,parameter       CAL_DQS_GATE               = "FAST"   //"SKIP", "FULL"
   ,parameter       CAL_WRLVL                  = "SKIP"   //"SKIP", "FULL"
   ,parameter       CAL_RDLVL                  = "SKIP"   //"SKIP", "FULL"
   ,parameter       CAL_RDLVL_DBI              = "SKIP"   //"SKIP", "FULL"
   ,parameter       CAL_WR_DQS_DQ              = "SKIP"   //"SKIP", "FULL"
   ,parameter       CAL_WR_DQS_DM_DBI          = "SKIP"   //"SKIP", "FULL"
   ,parameter       CAL_WRITE_LAT              = "SKIP"   //"SKIP", "FULL"
   ,parameter       CAL_RDLVL_COMPLEX          = "SKIP"   //"SKIP", "FULL"
   ,parameter       CAL_WR_DQS_COMPLEX         = "SKIP"   //"SKIP", "FULL"
   ,parameter       CAL_RD_VREF                = "SKIP"   //"SKIP", "FULL"
   ,parameter       CAL_RD_VREF_PATTERN        = "SIMPLE" //"SIMPLE", "COMPLEX"
   ,parameter       CAL_WR_VREF                = "SKIP"   //"SKIP", "FULL"
   ,parameter       CAL_WR_VREF_PATTERN        = "SIMPLE" //"SIMPLE", "COMPLEX"
   ,parameter       CAL_DQS_TRACKING           = "SKIP"   //"SKIP", "FULL"
   ,parameter       CAL_JITTER                 = "NONE"   //"NONE", "LOW", "HIGH"
   ,parameter       CLK_2TO1                   = "TRUE"
   ,parameter       TCQ                        = 100
   ,parameter       NIBBLE_CNT_WIDTH           = 2
   ,parameter       CPLX_PAT_LENGTH            = "LONG"
   ,parameter       DM_DBI                     = "DM_NODBI"
   ,parameter       USE_CS_PORT                = 1

   // Migration parameters
   ,parameter                  MIGRATION       = "OFF"
   ,parameter [8*CKBITS-1:0]   CK_SKEW         = {CKBITS{8'b0}}
   ,parameter [8*ABITS-1:0]    ADDR_SKEW       = {{8'b0}}
   ,parameter [7:0]            ACT_SKEW        = 8'b0
   ,parameter [7:0]            PAR_SKEW        = 8'b0
   ,parameter [8*BABITS-1:0]   BA_SKEW         = {BABITS{8'b0}}
   ,parameter [8*BGBITS-1:0]   BG_SKEW         = {BGBITS{8'b0}}
   ,parameter [8*CSBITS-1:0]   CS_SKEW         = {CSBITS{8'b0}}
   ,parameter [8*CKEBITS-1:0]  CKE_SKEW        = {CKEBITS{8'b0}}
   ,parameter [8*ODTBITS-1:0]  ODT_SKEW        = {ODTBITS{8'b0}}
   ,parameter [8*LR_WIDTH-1:0] C_SKEW          = {LR_WIDTH{8'b0}}

   // for XSDB
   ,parameter       MEMORY_VOLTAGE             = "1.2V"
   ,parameter       CLKFBOUT_MULT_PLL          = 4
   ,parameter       DIVCLK_DIVIDE_PLL          = 1
   ,parameter       CLKOUT0_DIVIDE_PLL         = 1
   ,parameter       CLKFBOUT_MULT_MMCM         = 4
   ,parameter       DIVCLK_DIVIDE_MMCM         = 1
   ,parameter       CLKOUT0_DIVIDE_MMCM        = 4

   ,parameter       C_FAMILY                   = "kintexu"
   ,parameter       C_MAJOR_VERSION            = 2017
   ,parameter       C_MINOR_VERSION            = 1
   ,parameter       C_CORE_MAJOR_VER           = 3
   ,parameter       C_CORE_MINOR_VER           = 0
   ,parameter       C_NEXT_SLAVE               = 1'b0
   ,parameter       C_CSE_DRV_VER              = 16'h0002
   ,parameter       C_USE_TEST_REG             = 1
   ,parameter       C_PIPE_IFACE               = 1
   ,parameter       C_CORE_INFO1               = 0
   ,parameter       C_CORE_INFO2               = 0
   ,parameter       BISC_EN		       = 1
   ,parameter       RESTORE_CRC                = 0
)
(
    input                          pllGate

   ,input                          clk
   ,input                          rst

   ,input [31:0] io_address
   ,input        io_addr_strobe
   ,input [31:0] io_write_data
   ,input        io_write_strobe
   ,output [31:0] io_read_data
   ,output        io_ready_lvl

   ,input   [20-1:0] riu2clb_valid

   ,input [7:0] phy2clb_rd_dq_bits
   ,output [8:0] bisc_byte

   ,input bisc_complete
   ,input phy_ready
   ,output en_vtc

  ,output   [DBYTES*4-1:0] clb2phy_rdcs0_upp
  ,output   [DBYTES*4-1:0] clb2phy_rdcs1_upp
  ,output   [DBYTES*4-1:0] clb2phy_rdcs0_low
  ,output   [DBYTES*4-1:0] clb2phy_rdcs1_low

  ,output       [DBYTES*13-1:0] clb2phy_fifo_rden
  ,output       [DBYTES*4-1:0] clb2phy_wrcs0_upp
  ,output       [DBYTES*4-1:0] clb2phy_wrcs1_upp
  ,output       [DBYTES*4-1:0] clb2phy_wrcs0_low
  ,output       [DBYTES*4-1:0] clb2phy_wrcs1_low
  
   ,output       [DBYTES*7-1:0]  rd_vref_value

   ,output reg                  calDone
   ,output                [7:0] cal_CAS_n
   ,output                [7:0] cal_RAS_n
   ,output                [7:0] cal_WE_n
   ,output                [7:0] cal_RESET_n
   ,output        [ABITS*8-1:0] cal_ADR
   ,output                [7:0] cal_ACT_n
   ,output       [BABITS*8-1:0] cal_BA
   ,output       [BGBITS*8-1:0] cal_BG
   ,output     [LR_WIDTH*8-1:0] cal_C
   ,output      [CKEBITS*8-1:0] cal_CKE
   ,output       [CSBITS*8-1:0] cal_CS_n
   ,output       [DBYTES*8-1:0] cal_DMOut_n
   ,output     [DBYTES*8*8-1:0] cal_DQOut
   ,output      [ODTBITS*8-1:0] cal_ODT
   ,output                [7:0] cal_PAR
   ,input [DBYTES*8*8-1:0] mcal_DQIn
   ,input   [DBYTES*8-1:0] mcal_DMIn_n
   ,input                  mc_clb2phy_fifo_rden_nxt

   ,output                    cal_dbi_wr
   ,output                    cal_dbi_rd
   ,output [1:0]              calCasSlot
   ,output [1:0]              calRank
   ,output                    calRdCAS
   ,output                    cal_clear_fifo_rden
   ,output                    calWrCAS
   ,input                     wrDataEn

   ,output reg [DBYTES*6-1:0]  lowCL0
   ,output reg [DBYTES*6-1:0]  lowCL1
   ,output reg [DBYTES*6-1:0]  lowCL2
   ,output reg [DBYTES*6-1:0]  lowCL3
   ,output reg [DBYTES*6-1:0]  uppCL0
   ,output reg [DBYTES*6-1:0]  uppCL1
   ,output reg [DBYTES*6-1:0]  uppCL2
   ,output reg [DBYTES*6-1:0]  uppCL3
   ,output reg [6:0]          max_rd_lat
   
   ,output [DBYTES-1:0] cal_oe_dis_low
   ,output [DBYTES-1:0] cal_oe_dis_upp
   
   // Self-Refresh and Save/Restore
   ,input                     stop_gate_tracking_req
   ,output                    stop_gate_tracking_ack
   ,input                     app_mem_init_skip
   ,input                     app_restore_en
   ,input                     app_restore_complete
   ,input                     usr_xsdb_select
   ,input                     usr_xsdb_rd_en
   ,input                     usr_xsdb_wr_en
   ,input [15:0]              usr_xsdb_addr
   ,input [8:0]               usr_xsdb_wr_data
   ,output [8:0]              usr_xsdb_rd_data
   ,output                    usr_xsdb_rdy

   ,input                     traffic_wr_done
   ,input                     traffic_status_err_bit_valid
   ,input                     traffic_status_err_type_valid
   ,input                     traffic_status_err_type
   ,input                     traffic_status_done
   ,input                     traffic_status_watch_dog_hang
   ,input [DBYTES*8*8-1:0]    traffic_error
   ,output wire               traffic_clr_error
   ,output wire               traffic_start
   ,output wire               traffic_rst
   ,output wire               traffic_err_chk_en
   ,output wire [3:0]         traffic_instr_addr_mode
   ,output wire [3:0] 		  traffic_instr_data_mode
   ,output wire [3:0] 	      traffic_instr_rw_mode
   ,output wire [1:0]         traffic_instr_rw_submode
   ,output wire [31:0] 	      traffic_instr_num_of_iter
   ,output wire [5:0]         traffic_instr_nxt_instr

   ,input [3:0]               win_start
   ,input                     gt_data_ready

   //Status and Debug outputs
   ,output wire [8:0]  cal_pre_status
   ,output wire [127:0] cal_r0_status
   ,output wire [127:0] cal_r1_status
   ,output wire [127:0] cal_r2_status
   ,output wire [127:0] cal_r3_status
   ,output wire [8:0]  cal_post_status
   ,output wire        cal_error
   ,output wire [7:0]  cal_error_bit
   ,output wire [7:0]  cal_error_nibble
   ,output wire [3:0]  cal_error_code
   ,output wire        cal_warning
   ,output wire [8:0]  cal_warning_nibble
   ,output wire [8:0]  cal_warning_code
   ,output             cal_crc_error
   
   ,input  wire [36:0] sl_iport0
   ,output wire [16:0] sl_oport0
   
   //Debug Port
   ,output wire [2:0]  dbg_cal_seq
   ,output wire [31:0] dbg_cal_seq_cnt
   ,output wire [7:0]  dbg_cal_seq_rd_cnt
   ,output wire        dbg_rd_valid
   ,output wire [5:0]  dbg_cmp_byte
   ,output wire [63:0] dbg_rd_data
   ,output wire [63:0] dbg_rd_data_cmp
   ,output wire [63:0] dbg_expected_data
   ,output wire [15:0] dbg_cplx_config
   ,output wire [1:0]  dbg_cplx_status
   ,output [31:0] win_status
);



localparam RTL_DDR_INIT = 1; // Use RTL FSM for DDR initialization

localparam LRDIMM_EN = (LRDIMM_MODE=="ON") ? 1:0;

// Assume each slot has same DIMM configuration
localparam DUAL_SLOT      = (SLOT0_CONFIG != 8'b0) && (SLOT1_CONFIG != 8'b0);
localparam RANKS_PER_SLOT = DUAL_SLOT ? RANKS/2 : RANKS;
localparam SLOTS = DUAL_SLOT ? 2 : 1;

localparam LRDIMM_DUAL_RANK = LRDIMM_EN & (RANKS_PER_SLOT == 2);
localparam LRDIMM_QUAD_RANK = LRDIMM_EN & (RANKS_PER_SLOT == 4);

localparam MR5_0 = MR5;
localparam MR5_1 = MR5;
localparam MR5_2 = LRDIMM_QUAD_RANK ? (MR5 & 13'b1_1110_0011_1111) : MR5;
localparam MR5_3 = LRDIMM_QUAD_RANK ? (MR5 & 13'b1_1110_0011_1111) : MR5;

localparam XSDB_SLAVE_TYPE = LRDIMM_EN ? (LRDIMM_QUAD_RANK ? 16'h0089 : 16'h0088) : 16'h0082;

localparam PARAM_MAP_VERSION = LRDIMM_EN ? 16'h0001 : 16'h0002;

localparam XSDB_SLOTS = LRDIMM_EN ? SLOTS : 0;

localparam XSDB_RANKS = LRDIMM_EN ? RANKS_PER_SLOT : RANKS;		

localparam XSDB_MEMORY_TYPE = (LRDIMM_QUAD_RANK ? 9 : (LRDIMM_DUAL_RANK ? 8 : ((MEM == "DDR4") ? 2 : 1)));	//9==LRDIMM_RANK4, 8==LRDIMM_RANK2, 2==DDR4 and 1==DDR3

localparam LRDIMM_CAL_SIZE = LRDIMM_QUAD_RANK ? 48 : (LRDIMM_DUAL_RANK ? 24 : 0);

// Non-LRDIMM - 7 status registers: 27 Stages, 54 Status bits, 6 registers, 1 spare register.
// LRDIMM-Dual Rank - 9 status registers: 39 Stages, 78 Status bits, 9 (=ceil of 78/9)registers
// LRDIMM-Quad Rank - 12 status registers: 51 Stages, 102 Status bits, 12 (=ceil of 102/9) registers
localparam CAL_STATUS_REG_SIZE    = LRDIMM_QUAD_RANK ? 12 : (LRDIMM_DUAL_RANK ? 9 : 7); //Space reserved for State register per rank

localparam PRE_STATUS_ADDR    = 28'h090004E;
localparam POST_STATUS_ADDR   = PRE_STATUS_ADDR + 1;
localparam RANK0_STATUS0_ADDR = POST_STATUS_ADDR + 4;
localparam RANK1_STATUS0_ADDR = RANK0_STATUS0_ADDR + CAL_STATUS_REG_SIZE;
localparam RANK2_STATUS0_ADDR = RANK1_STATUS0_ADDR + CAL_STATUS_REG_SIZE;
localparam RANK3_STATUS0_ADDR = RANK2_STATUS0_ADDR + CAL_STATUS_REG_SIZE;
localparam ERROR0_ADDR        = RANK3_STATUS0_ADDR + CAL_STATUS_REG_SIZE;
localparam ERROR1_ADDR        = ERROR0_ADDR + 1;
localparam ERROR_CODE_ADDR    = ERROR1_ADDR + 1;

localparam CAL_SKIP     = 0;
localparam CAL_FULL     = CAL_SKIP + 1;
localparam CAL_FAST     = CAL_SKIP + 2;
localparam CAL_FAST_ALL = CAL_SKIP + 3;

localparam DEBUG           = 32'hFFFF_FFFF;
localparam SKIP_DEBUG      = 32'h0;
localparam EN_DEBUG        = SKIP_DEBUG;

localparam DQS_GATE  = (CAL_DQS_GATE == "SKIP") ? CAL_SKIP :
                       (CAL_DQS_GATE == "FULL") ? CAL_FULL :
                       (CAL_DQS_GATE == "FAST") ? CAL_FAST : CAL_FAST_ALL;
localparam WRLVL     = (CAL_WRLVL == "SKIP") ? CAL_SKIP :
                       (CAL_WRLVL == "FULL") ? CAL_FULL :
                       (CAL_WRLVL == "FAST") ? CAL_FAST : CAL_FAST_ALL;
localparam RDLVL     = (CAL_RDLVL == "SKIP") ? CAL_SKIP :
                       (CAL_RDLVL == "FULL") ? CAL_FULL :
                       (CAL_RDLVL == "FAST") ? CAL_FAST : CAL_FAST_ALL;
localparam RDLVL_DBI = (CAL_RDLVL_DBI == "SKIP") ? CAL_SKIP :
                       (CAL_RDLVL_DBI == "FULL") ? CAL_FULL :
                       (CAL_RDLVL_DBI == "FAST") ? CAL_FAST : CAL_FAST_ALL;
localparam WR_DQS_DQ = (CAL_WR_DQS_DQ == "SKIP") ? CAL_SKIP :
                       (CAL_WR_DQS_DQ == "FULL") ? CAL_FULL :
                       (CAL_WR_DQS_DQ == "FAST") ? CAL_FAST : CAL_FAST_ALL;
localparam WR_DQS_DM_DBI = (CAL_WR_DQS_DM_DBI == "SKIP") ? CAL_SKIP :
                           (CAL_WR_DQS_DM_DBI == "FULL") ? CAL_FULL :
                           (CAL_WR_DQS_DM_DBI == "FAST") ? CAL_FAST : CAL_FAST_ALL;
localparam WRITE_LAT = (CAL_WRITE_LAT == "SKIP") ? CAL_SKIP :
                       (CAL_WRITE_LAT == "FULL") ? CAL_FULL :
                       (CAL_WRITE_LAT == "FAST") ? CAL_FAST : CAL_FAST_ALL;
localparam RDLVL_COMPLEX  = (CAL_RDLVL_COMPLEX == "SKIP") ? CAL_SKIP :
                            (CAL_RDLVL_COMPLEX == "FULL") ? ((tCK >= 1250) ? CAL_SKIP : CAL_FULL) :
                            (CAL_RDLVL_COMPLEX == "FAST") ? CAL_FAST : CAL_FAST_ALL;
localparam WR_DQS_COMPLEX = (CAL_WR_DQS_COMPLEX == "SKIP") ? CAL_SKIP :
                            (CAL_WR_DQS_COMPLEX == "FULL") ? ((tCK >= 1250) ? CAL_SKIP : CAL_FULL) :
                            (CAL_WR_DQS_COMPLEX == "FAST") ? CAL_FAST : CAL_FAST_ALL;
localparam RD_VREF   = (MEM == "DDR3") ? CAL_SKIP :
                       (CAL_RD_VREF == "SKIP") ? CAL_SKIP :
                       (CAL_RD_VREF == "FULL") ? CAL_FULL :
                       (CAL_RD_VREF == "FAST") ? CAL_FAST : CAL_FAST_ALL;
localparam RD_VREF_PATTERN   = (CAL_RD_VREF_PATTERN == "SIMPLE") ? CAL_FAST : 
                                                                   CAL_FULL;
localparam WR_VREF   = (MEM == "DDR3") ? CAL_SKIP :
		       (CAL_WR_VREF == "SKIP") ? CAL_SKIP :
                       (CAL_WR_VREF == "FULL") ? CAL_FULL :
                       (CAL_WR_VREF == "FAST") ? CAL_FAST : CAL_FAST_ALL;
localparam WR_VREF_PATTERN   = (CAL_WR_VREF_PATTERN == "SIMPLE") ? CAL_FAST : 
                                                                   CAL_FULL;
localparam DQS_TRACKING = (CAL_DQS_TRACKING == "SKIP") ? CAL_SKIP :
                          (CAL_DQS_TRACKING == "FULL") ? CAL_FULL : CAL_FAST;

localparam CAL_TIME_1S_SAMPLE_CNT = (tCK >= 2500) ? 2 :  // < 800MT/s
				    (tCK >= 1876) ? 2 :  // < 1066MT/s 
				    (tCK >= 1500) ? 16 : // < 1333MT/s 
				    (tCK >= 1250) ? 16 : // < 1600MT/s 
				    (tCK >= 1072) ? 4 :  // < 1866MT/s 
				    (tCK >= 938 ) ? 4 :  // < 2133MT/s 
				    (tCK >= 833)  ? 4 :  // < 2400MT/s 
				    (tCK >= 749)  ? 4 :  // < 2666MT/s
				    64;
     
localparam CAL_SIM          = (CAL_JITTER == "NONE" || 
                               CAL_JITTER == "LOW") ? 1'b1 : 1'b0;
localparam DQS_SAMPLE_CNT   = (CAL_JITTER == "NONE") ? 1 :
                              (CAL_JITTER == "LOW") ?  5 : 20;
localparam WRLVL_SAMPLE_CNT = (CAL_JITTER == "NONE") ? 1 :
                              (CAL_JITTER == "LOW") ?  16: CAL_TIME_1S_SAMPLE_CNT; // 64
localparam RDLVL_SAMPLE_CNT = (CAL_JITTER == "NONE") ? 5 :
                              (CAL_JITTER == "LOW") ?  16: CAL_TIME_1S_SAMPLE_CNT; // 64
localparam CMPLX_LOOP_CNT   = (CAL_JITTER == "NONE") ? 1 :
                              (CAL_JITTER == "LOW") ?  5 : CAL_TIME_1S_SAMPLE_CNT; // 127
					
localparam DM_USED = ((DM_DBI == "DM_NODBI") || 
					  (DM_DBI == "DM_DBIRD")) ? 1'b1 : 1'b0;
					  
localparam DBI_RD     = (MEM == "DDR3") ? 1'b0 : 
                        ((DM_DBI == "DM_DBIRD") || 
                         (DM_DBI == "NODM_DBIRD") ||
						 (DM_DBI == "NODM_DBIWRRD")) ? 1'b1 : 1'b0;
						 
localparam DBI_WR     = (MEM == "DDR3") ? 1'b0 : 
                        ((DM_DBI == "NODM_DBIWR") ||
						 (DM_DBI == "NODM_DBIWRRD")) ? 1'b1 : 1'b0;

localparam DM_DBI_SETTING = {DBI_RD, DBI_WR, DM_USED};
							  
// Quarter cycle estimation when BISC is disabled
localparam IODELAY_SIM_TAP_VAL = 5;
localparam IODELAY_QTR_CK_TAP_CNT = tCK / 4 / IODELAY_SIM_TAP_VAL;


localparam
    MRS   = 3'b000
   ,REF   = 3'b001
   ,PRE   = 3'b010
   ,ACT   = 3'b011
   ,WR    = 3'b100
   ,RD    = 3'b101
   ,ZQC   = 3'b110
   ,NOP   = 3'b111
;

   // Define Odd Rank Chip select
   localparam SLOTX_CS_ODD = SLOT0_ODD_CS | SLOT1_ODD_CS;

   localparam SIDE_A = 1'b0;
   localparam SIDE_B = 1'b1;   
   localparam REG_CTRL_ON = (REG_CTRL=="ON") ? 1:0;

   localparam DDR4_DB_BC0A_FREQ_CODE = (tCK < 751)  ? 3'b101 :
					(tCK < 834)  ? 3'b100 :
					(tCK < 938)  ? 3'b011 :
					(tCK < 1072) ? 3'b010 :
					(tCK < 1250) ? 3'b001 : 3'b000;

   localparam DDR4_DB_F0BC0A = (13'b1_0000_1010_0000 | DDR4_DB_BC0A_FREQ_CODE); // LRDIMM Operating speed

   localparam DDR4_DB_F0BC6X = (13'b1_0110_0000_0000 | (DDR4_REG_RC3X & 8'hFF)); // LRDIMM Fine Granularity Operating speed

   localparam DDR4_DB_F0BC00 = (13'b1_0000_0000_0000 | DDR4_DB_HIF_RTT_NOM); // DDR4 Data Buffer Host I/F DQ RTT_NOM
   localparam DDR4_DB_F0BC01 = (13'b1_0000_0001_0000 | DDR4_DB_HIF_RTT_WR); // DDR4 Data Buffer Host I/F DQ RTT_WR
   localparam DDR4_DB_F0BC02 = (13'b1_0000_0010_0000 | DDR4_DB_HIF_RTT_PARK); // DDR4 Data Buffer Host I/F DQ RTT_PARK
   localparam DDR4_DB_F0BC03 = (13'b1_0000_0011_0000 | DDR4_DB_HIF_DI); // DDR4 Data Buffer Host I/F DQ Driver Impedance
   localparam DDR4_DB_F0BC04 = (13'b1_0000_0100_0000 | DDR4_DB_DIF_ODT); // DDR4 Data Buffer DRAM I/F MDQ ODT
   localparam DDR4_DB_F0BC05 = (13'b1_0000_0101_0000 | DDR4_DB_DIF_DI); // DDR4 Data Buffer DRAM I/F MDQ Driver Impedance

   localparam DDR4_DB_F5BC5X = (13'b1_0101_0000_0000 | DDR4_DB_HIF_VREF); // DDR4 Data Buffer Host I/F VRef

   localparam DDR4_DB_F5BC6X = (13'b1_0110_0000_0000 | DDR4_DB_DIF_VREF); // DDR4 Data Buffer DRAM I/F VRef

   localparam DDR4_DB_FXBC7X_F5 = (13'b1_0111_0000_0000 | 4'b0101); // Function space 5 selection

   localparam DDR4_DB_FXBC7X_F0 = (13'b1_0111_0000_0000 | 4'b0000); // Function space 0 selection

  // Register chip programmable values for DDR3
  // The register chip for the registered DIMM needs to be programmed
  // before the initialization of the registered DIMM.
  // Address for the control word is in : DBA2, DA2, DA1, DA0
  // Data for the control word is in: DBA1 DBA0, DA4, DA3
  // The values will be stored in the local param in the following format
  // {DBA[2:0], DA[4:0]}
  
  // RC0 is global features control word. Address == 000
  localparam  REG_RC0 = 8'b00000000;
  
  // RC1 Clock driver enable control word. Enables or disables the four
  // output clocks in the register chip. For single rank and dual rank
  // two clocks will be enabled and for quad rank all the four clocks
  // will be enabled. Address == 000. Data = 0110 for single and dual rank.
  // = 0000 for quad rank 
  localparam REG_RC1 = 8'b00000001;

  // RC2 timing control word. Set in 1T timing mode
  // Address = 010. Data = 0000
  localparam REG_RC2 = 8'b00000010;
   
  // RC3 timing control word. Setting the data based on number of RANKS (inturn the number of loads)
  // This setting is specific to RDIMMs from Micron Technology
  localparam REG_RC3 = ((RANKS_PER_SLOT == 1) && (DRAM_WIDTH == 8)) ? 8'b0_0000_011 : 8'b0_0101_011;
   
  // RC4 timing control work. Setting the data based on number of RANKS (inturn the number of loads)
  // This setting is specific to RDIMMs from Micron Technology
  localparam REG_RC4 = ((RANKS_PER_SLOT == 1) && (DRAM_WIDTH == 4)) ? 8'b0_0101_100 : // R/C C 0x5
		       ((RANKS_PER_SLOT == 1) && (DRAM_WIDTH == 8)) ? 8'b0_0000_100 : // R/C A 0x0
		       ((RANKS_PER_SLOT == 2) && (DRAM_WIDTH == 4)) ? 8'b0_0101_100 : // R/C D,E,J 0x5
		       ((RANKS_PER_SLOT == 2) && (DRAM_WIDTH == 8)) ? 8'b0_0000_100 : // R/C B 0x0
		       ((RANKS_PER_SLOT == 4) && (DRAM_WIDTH == 4)) ? 8'b0_0000_100 : // R/C F,W,AB 0x0
		       ((RANKS_PER_SLOT == 4) && (DRAM_WIDTH == 8)) ? 8'b0_0101_100 : // R/C G,H,Y 0x5
		       8'b0_0101_100;
    
  // RC5 timing control work. Setting the data based on number of RANKS (inturn the number of loads)
  // This setting is specific to RDIMMs from Micron Technology
  localparam REG_RC5 = ((RANKS_PER_SLOT == 1) && (DRAM_WIDTH == 4)) ? 8'b0_0101_101 : // R/C C 0x5
		       ((RANKS_PER_SLOT == 1) && (DRAM_WIDTH == 8)) ? 8'b0_0000_101 : // R/C A 0x0
		       ((RANKS_PER_SLOT == 2) && (DRAM_WIDTH == 4)) ? 8'b0_1010_101 : // R/C D 0xA  E,J 0x5
		       ((RANKS_PER_SLOT == 2) && (DRAM_WIDTH == 8)) ? 8'b0_0000_101 : // R/C B 0x0
		       ((RANKS_PER_SLOT == 4) && (DRAM_WIDTH == 4)) ? 8'b0_0101_101 : // R/C F,W,AB 0x5
		       ((RANKS_PER_SLOT == 4) && (DRAM_WIDTH == 8)) ? 8'b0_0101_101 : // R/C G,H,Y 0x5
		       8'b0_1010_101;   
  
  // RC10 timing control work. Setting the data to 0000 
  localparam [3:0] FREQUENCY_ENCODING = (/*tCK >= 1072 &&*/ tCK < 1250) ? 4'b0100 : 
                                        (tCK >= 1250 && tCK < 1500) ? 4'b0011 :
                                        (tCK >= 1500 && tCK < 1875) ? 4'b0010 :
                                        (tCK >= 1875 && tCK < 2500) ? 4'b0001 : 4'b0000;

  localparam REG_RC10 = {1'b1,FREQUENCY_ENCODING,3'b010};   

  localparam VREF = "EXTERNAL";
  localparam VREF_ENCODING = (VREF == "INTERNAL") ? 1'b1 : 1'b0;

  localparam [3:0] DDR3_VOLTAGE_ENCODING = (MEMORY_VOLTAGE == "1.25V") ? {1'b0,VREF_ENCODING,2'b10} : // 1.25V
                                           (MEMORY_VOLTAGE == "1.35V") ? {1'b0,VREF_ENCODING,2'b01} : // 1.35V
                                                                         {1'b0,VREF_ENCODING,2'b00} ; // 1.5V

  localparam REG_RC11 = {1'b1,DDR3_VOLTAGE_ENCODING,3'b011};
   
  // Register chip programmable values for DDR4
  // Programming refers to DDR4RCD01_Spec
  // DDR4_REG_RCX registers below are defined as ADDR[12:0]
  // For RC00 to RC0F,  4-bit controls. ADDR[12:0] = {addr[12:4], value[3:0]}
  // For RC1x to RC1Bx, 8-bit controls. ADDR[12:0] = {addr[12:8], value[7:0]}
  // RC00 Global Features Control word.   
  localparam  DDR4_REG_RC00 = 13'b0_0000_0000_0000;
  // RC01 Clock Driver Enable Control word. 
  localparam  DDR4_REG_RC01 = 13'b0_0000_0001_0000;   
  // RC02 Timing and IBT Control word.
  localparam  DDR4_REG_RC02 = 13'b0_0000_0010_0000;
  // RC03 CA and CS Signals Driver Characterisitcs Control word.
  //localparam  DDR4_REG_RC03 = (RANKS >= 2)? 13'b0_0000_0011_0101 : 13'b0_0000_0011_0000;
  // RC04 ODT and CKE Signals Driver Characteristics Control word.
  //localparam  DDR4_REG_RC04 = (RANKS >= 2)? 13'b0_0000_0100_0101 : 13'b0_0000_0100_0000;
  // RC05 Clock Driver Characteristics Control word.
  //localparam  DDR4_REG_RC05 = (RANKS >= 2)? 13'b0_0000_0101_0101 : 13'b0_0000_0101_0000;
  // RC06 Command Space Control word. (skipped)
  //localparam  DDR4_REG_RC6 = 13'b0_0000_0110_0000;
  // RC07 Reserved. (skipped)   
  // RC08 Input/Output Configuration Control word.
  
  function [1:0] func_get_rc08;
      input integer stack_height;
  begin
      case (stack_height)
          1 : func_get_rc08 = 2'b11;
          2 : func_get_rc08 = 2'b10;
          4 : func_get_rc08 = 2'b01;
          8 : func_get_rc08 = 2'b00;
          default :  func_get_rc08 = 2'b11;
      endcase
  end    
  endfunction

  localparam  DA17_DIS = (ABITS == 17) ? 1'b1: 1'b0;
  localparam  DC2_0_DIS = (RANKS_PER_SLOT <= 2) ? func_get_rc08(S_HEIGHT) : 2'b01 ;    //  For Quad Rank Case the Stack Height is considered as 1 always

  localparam  DDR4_REG_RC08 = {9'b0_0000_1000, DA17_DIS, 1'b0, DC2_0_DIS};

  // RC09 Power Saving Settings Control word.
  //localparam  DDR4_REG_RC09 = 13'b0_0000_1001_0000;
  // RC0A RDIMM Operating Speed
  localparam  DDR4_REG_RC0A_CONTEXT = 1'b0;
  localparam  DDR4_REG_RC0A_FREQ_CODE = (/*tCK >= 625  &&*/ tCK < 751)  ? 3'b101 :
					(tCK >= 751  && tCK < 834)  ? 3'b100 :
					(tCK >= 834  && tCK < 938)  ? 3'b011 :
					(tCK >= 938  && tCK < 1072) ? 3'b010 :
					(tCK >= 1072 && tCK < 1250) ? 3'b001 : 3'b000;
					
  localparam  DDR4_REG_RC0A = {9'b0_0000_1010, DDR4_REG_RC0A_CONTEXT, DDR4_REG_RC0A_FREQ_CODE};
   
  // RC0B Operating Voltage VDD and VrefCA Source Control word.
  // Use external Vref
  localparam  DDR4_REG_RC0B = 13'b0_0000_1011_1000;

  // RC0C Training Control word.
  // Normal Operation mode
  //localparam  DDR4_REG_RC0C = 13'b0_0000_1100_0000;

  // RC0D DIMM Configuration Control Word.
  // Direct DualCS mode, RDIMM for now
  // RCD mirroring is disabled. Mirroring will be done in this block since mirroring is needed for Non-RDIMM cases as well.
  localparam  DDR4_REG_CS_MODE = (RANKS==8) ? 2'b01 : (((RANKS>2) && ((SLOT0_CONFIG == 8'b0)||(SLOT1_CONFIG == 8'b0))) ? 2'b01 : 2'b00); // CS Mode, RDIMM register RC0D DA[1:0], 00 - Direct Dual CS mode, 01 - Direct Quad CS mode
  localparam  DDR4_REG_RC0D = {9'b0_0000_1101, CA_MIRROR == "ON" ? 1'b1 : 1'b0, (LRDIMM_EN ? 1'b0 : 1'b1), DDR4_REG_CS_MODE};

  // RC0E Parity Control word.
  // Disabled
  localparam  DDR4_REG_RC0E = {12'b0_0000_1110_000, DDR4_REG_PARITY_ENABLE == "ON" ? 1'b1 : 1'b0};
  
  // RC0F Command Latency Adder Control word.
  localparam  DDR4_REG_RC0F = 13'b0_0000_1111_0000;
   
  // RC1X Internal VrefCA Control word. (skipped)
  //localparam  DDR4_REG_RC1X = 13'b0_0001_0000_0000;

  // RC2X I2C Bus Control word.
  // Disabled
  localparam  DDR4_REG_RC2X = 13'b0_0010_0000_0001;

  // RC3X Fine Granularity RDIMM Operating Speed.
  // Need to bring to MIG top
//  localparam  DDR4_REG_RC3X_FINE_FREQ_CODE = (tCK >= 625  && tCK < 751)  ? 8'b01100001 :
//					     (tCK >= 751  && tCK < 834)  ? 8'b01000110 :
//					     (tCK >= 834  && tCK < 938)  ? 8'b00111001 :
//					     (tCK >= 938  && tCK < 1072) ? 8'b00101011 :
//					     (tCK >= 1072 && tCK < 1250) ? 8'b00011110 : 3'b00010001;
   
  //localparam  DDR4_REG_RC3X = {5'b0_0011, DDR4_REG_RC3X_FINE_FREQ_CODE};
  
  // RC4X CW Source Selection Control word. ??
  //localparam  DDR4_REG_RC4X = 13'b0_0100_0000_0000;

  // RC5X CW Destination Selection & Write/Read Additional QxODT[1:0] Signal high ??
  //localparam  DDR4_REG_RC5X = 13'b0_0101_0000_0000;

  // RC6X CW Data Control word. ??
  //localparam  DDR4_REG_RC6X = 13'b0_0110_0000_0000;

  // RC7X IBT Control word. ??
  //localparam  DDR4_REG_RC7X = 13'b0_0111_0000_0000;

  // RC8X ODT Input Buffer/IBT, QxODT Output Buffer and Timing Control word. ??
  //localparam  DDR4_REG_RC8X = 13'b0_1000_0000_0000;
   
  // RC9X QxODT[1:0] Write Pattern Control word. ??
  //localparam  DDR4_REG_RC9X = 13'b0_1001_0000_0000;
   
  // RCAX QxODT[1:0] Read Pattern Control word. ??
  //localparam  DDR4_REG_RCAX = 13'b0_1010_0000_0000;
   
  // RCBX IBT and MRS Snoop Control word. ??
  //localparam  DDR4_REG_RCBX = 13'b0_1011_0000_0000;   

  // RCCx..RCFFx Error Log Register (skipped)
  localparam DDR4_CMR_MAX_CNT = LRDIMM_EN ? 25 : 13;
  
// For DDR4 RDIMM, Each slot needs to have RCD Register programming
   localparam SLOT0_RDIMM_REG_CS = SLOT0_CONFIG[0] ? 8'b00000001 :
				   SLOT0_CONFIG[1] ? 8'b00000010 :
				   SLOT0_CONFIG[2] ? 8'b00000100 :
				   SLOT0_CONFIG[3] ? 8'b00001000 :
				   SLOT0_CONFIG[4] ? 8'b00010000 :
				   SLOT0_CONFIG[5] ? 8'b00100000 :
				   SLOT0_CONFIG[6] ? 8'b01000000 :
				   SLOT0_CONFIG[7] ? 8'b10000000 :
				   8'b00000000;
   localparam SLOT1_RDIMM_REG_CS = SLOT1_CONFIG[0] ? 8'b00000001 :
				   SLOT1_CONFIG[1] ? 8'b00000010 :
				   SLOT1_CONFIG[2] ? 8'b00000100 :
				   SLOT1_CONFIG[3] ? 8'b00001000 :
				   SLOT1_CONFIG[4] ? 8'b00010000 :
				   SLOT1_CONFIG[5] ? 8'b00100000 :
				   SLOT1_CONFIG[6] ? 8'b01000000 :
				   SLOT1_CONFIG[7] ? 8'b10000000 :
				   8'b00000000;   

  localparam BYPASS_LAT_PAD = 2;
  
  // Determine Number of BRAM infer by Vivado based on RANKS, DBYTES, and 
  // BITS_PER_BYTE parameters
  localparam BITS_PER_BYTE = (DRAM_WIDTH ==16) ? 8 : DRAM_WIDTH;
  //If these ......... then set NUM_BRAMS = 3
  localparam J0= (RANKS == 4 && DBYTES >13 && BITS_PER_BYTE == 8) ? 1:0;
  localparam J1= (RANKS == 4 && DBYTES >10 && BITS_PER_BYTE == 4) ? 1:0;
  localparam J2= (RANKS == 3 && DBYTES >16 && BITS_PER_BYTE == 8) ? 1:0;
  localparam J3= (RANKS == 3 && DBYTES >12 && BITS_PER_BYTE == 4) ? 1:0;
  //else if these .... then set NUM_BRAMS = 2
  localparam K0= (RANKS == 4 && DBYTES >6  && BITS_PER_BYTE ==8)  ? 1:0;
  localparam K1= (RANKS == 4 && DBYTES >5  && BITS_PER_BYTE ==4)  ? 1:0;
  localparam K2= (RANKS == 3 && DBYTES >8  && BITS_PER_BYTE ==8)  ? 1:0;
  localparam K3= (RANKS == 3 && DBYTES >6  && BITS_PER_BYTE ==4)  ? 1:0;
  //else if these .... then set NUM_BRAMS = 2
  localparam L0= (RANKS == 2 && DBYTES >11 && BITS_PER_BYTE ==8) ? 1:0;
  localparam L1= (RANKS == 2 && DBYTES >8  && BITS_PER_BYTE ==4) ? 1:0;
  localparam L2= (RANKS == 1 && DBYTES >17 && BITS_PER_BYTE ==8) ? 1:0;
  localparam L3= (RANKS == 1 && DBYTES >13 && BITS_PER_BYTE ==4) ? 1:0;
  //else ............ .... set NUM_BRAMS = 1

  localparam NUM_BRAMS=(J0+J1+J2+J3) >= 1 ? 3 :
                       (K0+K1+K2+K3) >= 1 ? 2 :
		       (L0+L1+L2+L3) >= 1 ? 2 : 
                       (RANKS == 8)       ? 3 : 1;
  localparam BRAM_SIZE= 36 * 1024 * NUM_BRAMS;
  
  // Number of fabric cycles to create tRFC time
  // the tRFC value is in memory clocks
  localparam TRFC_CYCLES = tRFC/nCK_PER_CLK + 1;

  // Passing the migration enable status to config rom
  localparam MIGRATION_EN = (MIGRATION == "ON") ? 1 : 0 ;

  //localparam PRE_RECONFIG_IN_STOP_GATE_TRACKING_REQ = 0;
  //localparam PRE_RECONFIG_OUT_STOP_GATE_TRACKING_ACK = 0;         
  //localparam POST_RECONFIG_IN_HW_INIT_SKIP    = 0;
  //localparam POST_RECONFIG_IN_XSDB_RESTORE_EN = 1;
  //localparam POST_RECONFIG_IN_XSDB_RESTORE_COMPLETE = 2;

  // Num of ranks required for MRS initialization
  localparam MRS_INIT_4RANKS = ((RANKS <= 4) && (EN_PP_4R_MIR == 0)) || ((RANKS <= 2) && (EN_PP_4R_MIR == 1)) ;
   
//Select the rank based on the lowest byte lane
assign calRank = {clb2phy_rdcs1_low[0], clb2phy_rdcs0_low[0]};

// code for sending modified CL for DQS read gate generation.
// values modified after calibration
wire [5:0] tempCL = RL + ((REG_CTRL == "ON") ? 1 : 0);

wire [DBYTES*6-1:0] ub_lowCL0;
wire [DBYTES*6-1:0] ub_lowCL1;
wire [DBYTES*6-1:0] ub_lowCL2;
wire [DBYTES*6-1:0] ub_lowCL3;
wire [DBYTES*6-1:0] ub_uppCL0;
wire [DBYTES*6-1:0] ub_uppCL1;
wire [DBYTES*6-1:0] ub_uppCL2;
wire [DBYTES*6-1:0] ub_uppCL3;
wire [5:0]         ub_max_rd_lat;

(* keep = "TRUE" *) reg rst_r1;

always @(posedge clk)
  rst_r1 <= rst;

always @(posedge clk) if (rst_r1) begin
   lowCL0 <= #TCQ {DBYTES{tempCL}};
   lowCL1 <= #TCQ {DBYTES{tempCL}};
   lowCL2 <= #TCQ {DBYTES{tempCL}};
   lowCL3 <= #TCQ {DBYTES{tempCL}};
   uppCL0 <= #TCQ {DBYTES{tempCL}};
   uppCL1 <= #TCQ {DBYTES{tempCL}};
   uppCL2 <= #TCQ {DBYTES{tempCL}};
   uppCL3 <= #TCQ {DBYTES{tempCL}};
   
   max_rd_lat <= #TCQ tempCL + BYPASS_LAT_PAD;
end else begin
   lowCL0 <= #TCQ (BYPASS_CAL == "TRUE")?{DBYTES{tempCL}}:ub_lowCL0;
   lowCL1 <= #TCQ (BYPASS_CAL == "TRUE")?{DBYTES{tempCL}}:ub_lowCL1;
   lowCL2 <= #TCQ (BYPASS_CAL == "TRUE")?{DBYTES{tempCL}}:ub_lowCL2;
   lowCL3 <= #TCQ (BYPASS_CAL == "TRUE")?{DBYTES{tempCL}}:ub_lowCL3;
   uppCL0 <= #TCQ (BYPASS_CAL == "TRUE")?{DBYTES{tempCL}}:ub_uppCL0;
   uppCL1 <= #TCQ (BYPASS_CAL == "TRUE")?{DBYTES{tempCL}}:ub_uppCL1;
   uppCL2 <= #TCQ (BYPASS_CAL == "TRUE")?{DBYTES{tempCL}}:ub_uppCL2;
   uppCL3 <= #TCQ (BYPASS_CAL == "TRUE")?{DBYTES{tempCL}}:ub_uppCL3;
   
   max_rd_lat <= #TCQ (BYPASS_CAL == "TRUE")?
                      (tempCL + BYPASS_LAT_PAD) : {1'b0, ub_max_rd_lat};

end

// Initialization

wire [7:0]               ub_cal_RESET_n;
wire [ABITS*8-1:0]       ub_cal_ADR;
wire [7:0]               ub_cal_ACT_n;
wire [BABITS*8-1:0]      ub_cal_BA;
wire [BGBITS*8-1:0]      ub_cal_BG;
wire [LR_WIDTH*8-1:0]    ub_cal_C;
wire [CKEBITS*8-1:0]     ub_cal_CKE;
wire [CSBITS*8-1:0]      ub_cal_CS_n;
wire [DBYTES*8-1:0]      ub_cal_DMOut_n;
wire [DBYTES*8*8-1:0]    ub_cal_DQOut;
wire [ODTBITS*8-1:0]     ub_cal_ODT;
wire [7:0]               ub_cal_PAR;
wire [7:0]               ub_cal_WE;
wire [7:0]               ub_cal_RAS;
wire [7:0]               ub_cal_CAS;
wire 			 ub_cal_inv; // inversion enable
wire 			 ub_cal_mrs; // inversion enable

wire        ub_ready;           // cmd initialzation done
wire        ub_calDone;        // calibration is done
wire        ub_en_vtc;         // Enable VTC
wire        rtl_initDone;       // initialization done
wire        ub_initDone;       // initialization done

//Debug RAM
wire xsdb_rd_en;              //Debug Ram rd enable
wire xsdb_wr_en;              //Debug Ram wr enable
wire [8:0]  xsdb_wr_data;     //Debug Ram write data
wire [15:0] xsdb_addr;
wire [8:0]  xsdb_rd_data;     //Debug Ram read data
reg  usr_xsdb_rd_en_r;        //Debug Ram rd enable
wire usr_xsdb_en;             //Debug Ram rd enable

wire ub_xsdb_rd_en;              //Debug Ram rd enable
wire ub_xsdb_wr_en;              //Debug Ram wr enable
wire [8:0]  ub_xsdb_wr_data;     //Debug Ram write data
wire [15:0] ub_xsdb_addr;
wire [8:0]  ub_xsdb_rd_data;     //Debug Ram read data

//ROM configuration
wire [7:0]  config_rd_addr;
wire [31:0] config_rd_data;     //ROM data

wire [31:0] cal_debug;
wire        bramB_en_stch;
wire        bramB_clk;
wire        bramB_en;
wire        bramB_we;
wire [15:0] bramB_addr;
wire [8:0]  bramB_di;
wire [8:0]  bramB_do;
reg         bramB_rdy;

wire        bramA_en;
wire        bramA_we;
wire [15:0] bramA_addr;
wire [8:0]  bramA_di;
wire [8:0]  bramA_do;

`ifndef RESTORE

// strech the xsdb_en pulse for one more cycle
assign usr_xsdb_en = usr_xsdb_rd_en_r | usr_xsdb_rd_en;
always @(posedge clk)
  usr_xsdb_rd_en_r <= #TCQ usr_xsdb_rd_en;

assign bramA_en   = usr_xsdb_select ? usr_xsdb_en : ub_xsdb_rd_en;
assign bramA_we   = usr_xsdb_select ? usr_xsdb_wr_en : ub_xsdb_wr_en;
assign bramA_addr = usr_xsdb_select ? usr_xsdb_addr  : ub_xsdb_addr;
assign bramA_di   = usr_xsdb_select ? usr_xsdb_wr_data : ub_xsdb_wr_data;
assign ub_xsdb_rd_data  = bramA_do;
assign usr_xsdb_rd_data = bramA_do;
`else

assign bramA_en   = ub_xsdb_rd_en;
assign bramA_we   = ub_xsdb_wr_en;
assign bramA_addr = ub_xsdb_addr;
assign bramA_di   = ub_xsdb_wr_data;
assign ub_xsdb_rd_data  = bramA_do;

`endif
// ==================================================
// Instantiate block used only in simulations
//synthesis translate_off

ddr4_v2_2_10_cal_debug_microblaze #
  (
   .CAL_STATUS_REG_SIZE(CAL_STATUS_REG_SIZE),
   .LRDIMM_CAL_SIZE    (LRDIMM_CAL_SIZE),
   .RANKS_PER_SLOT     (RANKS_PER_SLOT),
   .RANK0_STATUS0_ADDR (RANK0_STATUS0_ADDR),
   .RANK1_STATUS0_ADDR (RANK1_STATUS0_ADDR),
   .RANK2_STATUS0_ADDR (RANK2_STATUS0_ADDR),
   .RANK3_STATUS0_ADDR (RANK3_STATUS0_ADDR),
   .ERROR0_ADDR        (ERROR0_ADDR),
   .ERROR1_ADDR        (ERROR1_ADDR),
   .ERROR_CODE_ADDR    (ERROR_CODE_ADDR),
   .TCQ                (TCQ)
  ) u_ddr_debug_microblaze (
   .clk                (clk),
   .rst                (rst_r1),
   .IO_Addr_Strobe     (io_addr_strobe),
   .IO_Address         (io_address[27:0]),
   .IO_Write_Strobe    (io_write_strobe),
   .IO_Write_Data      (io_write_data),
   .cal_dbi_wr         (cal_dbi_wr),
   .cal_dbi_rd         (cal_dbi_rd),
   .cal_pre_status     (cal_pre_status),
   .cal_r0_status      (cal_r0_status),
   .cal_r1_status      (cal_r1_status),
   .cal_r2_status      (cal_r2_status),
   .cal_r3_status      (cal_r3_status),
   .cal_post_status    (cal_post_status),
   .cal_error          (cal_error), 
   .cal_error_bit      (cal_error_bit),
   .cal_error_nibble   (cal_error_nibble),
   .cal_error_code     (cal_error_code),
   .cal_warning        (cal_warning),
   .cal_warning_nibble (cal_warning_nibble),
   .cal_warning_code   (cal_warning_code)
   );

// ==================================================
// Block used only in simulations
//synthesis translate_on


// Address Decoder - Shift to change from byte address to word address

ddr4_v2_2_10_cal_addr_decode # (
    .MEMORY_CONFIGURATION (MEMORY_CONFIGURATION),
    .DRAM_WIDTH           (DRAM_WIDTH),
    .DBYTES               (DBYTES),
    .ABITS                (ABITS),
    .BABITS               (BABITS),
    .BGBITS               (BGBITS),
    .CKEBITS              (CKEBITS),
    .CKBITS               (CKBITS),
    .CSBITS               (CSBITS),
    .RANKS                (RANKS),
    .RNK_BITS             (RNK_BITS),
    .S_HEIGHT             (S_HEIGHT),
    .LR_WIDTH             (LR_WIDTH),
    .ODTBITS              (ODTBITS),
    .ODTWR                (ODTWR),
    .ODTWRDEL             (ODTWRDEL),
    .ODTWRDUR             (ODTWRDUR),
    .ODTWRODEL            (ODTWRODEL),
    .ODTWRODUR            (ODTWRODUR),
    .ODTRD                (ODTRD),
    .ODTRDDEL             (ODTRDDEL),
    .ODTRDDUR             (ODTRDDUR),
    .ODTRDODEL            (ODTRDODEL),
    .ODTRDODUR            (ODTRDODUR),
    .ODTNOP               (ODTNOP),
    .USE_CS_PORT          (USE_CS_PORT),
    .TCQ                  (TCQ),
    .MEM                  (MEM),
    .CLK_2TO1             (CLK_2TO1),
    .LRDIMM_EN            (LRDIMM_EN),
    .NIBBLE_CNT_WIDTH     (NIBBLE_CNT_WIDTH),
    .CPLX_PAT_LENGTH      (CPLX_PAT_LENGTH),
    .EXTRA_CMD_DELAY      (EXTRA_CMD_DELAY),
    .WL                   (WL),
    .INITIAL_DBI_WR       ((MEM == "DDR4") ? MR5[11] : 1'b0),
    .INITIAL_DBI_RD       ((MEM == "DDR4") ? MR5[12] : 1'b0),
    .RD_VREF_VAL          (RD_VREF_VAL),
    .CAL_STATUS_REG_SIZE  (CAL_STATUS_REG_SIZE),
    .PRE_STATUS_ADDR      (PRE_STATUS_ADDR),
    .POST_STATUS_ADDR     (POST_STATUS_ADDR),
    .RANK0_STATUS0_ADDR   (RANK0_STATUS0_ADDR),
    .RANK1_STATUS0_ADDR   (RANK1_STATUS0_ADDR),
    .RANK2_STATUS0_ADDR   (RANK2_STATUS0_ADDR),
    .RANK3_STATUS0_ADDR   (RANK3_STATUS0_ADDR),
    .ERROR0_ADDR          (ERROR0_ADDR),
    .ERROR1_ADDR          (ERROR1_ADDR),
    .ERROR_CODE_ADDR      (ERROR_CODE_ADDR),
    .CLAMSHELL            (DDR4_CLAMSHELL),

    .MIGRATION            (MIGRATION),
    .CK_SKEW              (CK_SKEW),
    .ADDR_SKEW            (ADDR_SKEW),
    .ACT_SKEW             (ACT_SKEW),
    .BA_SKEW              (BA_SKEW),
    .BG_SKEW              (BG_SKEW),
    .CKE_SKEW             (CKE_SKEW),
    .CS_SKEW              (CS_SKEW),
    .ODT_SKEW             (ODT_SKEW),
    .C_SKEW               (C_SKEW),
    .PAR_SKEW             (PAR_SKEW)

) u_ddr_cal_addr_decode (
    .clk                    (clk),
    .rst                    (rst),
    .io_address             (io_address[27:0]),
    .io_addr_strobe         (io_addr_strobe),
    .io_write_strobe        (io_write_strobe),
    .mb_to_addr_dec_data    (io_write_data),
    .io_read_data           (io_read_data),
    .io_ready_lvl             (io_ready_lvl),
    .ub_ready               (ub_ready),
    .bisc_complete          ( (BYPASS_CAL == "TRUE") ? 1'b0 : bisc_complete),
    .phy_ready              (phy_ready),
    .rtl_initDone           (rtl_initDone),
    .ub_initDone            (ub_initDone),
    .calDone                (ub_calDone),
    .en_vtc                 (ub_en_vtc),

    // Self-Refresh and Save/Restore
    .stop_gate_tracking_req (stop_gate_tracking_req),
    .stop_gate_tracking_ack (stop_gate_tracking_ack),
    .app_mem_init_skip      (app_mem_init_skip),
    .app_restore_en         (app_restore_en),
    .app_restore_complete   (app_restore_complete),
    
    .traffic_wr_done              (traffic_wr_done),
	  .traffic_status_err_bit_valid (traffic_status_err_bit_valid),
    .traffic_status_err_type_valid(traffic_status_err_type_valid),
    .traffic_status_err_type      (traffic_status_err_type),
    .traffic_status_done          (traffic_status_done),
    .traffic_status_watch_dog_hang(traffic_status_watch_dog_hang),
    .traffic_error                (traffic_error),
    .traffic_clr_error            (traffic_clr_error),
	  .traffic_start                (traffic_start),
    .traffic_rst                  (traffic_rst),
    .traffic_err_chk_en           (traffic_err_chk_en),
    .traffic_instr_addr_mode      (traffic_instr_addr_mode),
    .traffic_instr_data_mode      (traffic_instr_data_mode),
    .traffic_instr_rw_mode        (traffic_instr_rw_mode),
    .traffic_instr_rw_submode     (traffic_instr_rw_submode),
    .traffic_instr_num_of_iter    (traffic_instr_num_of_iter),
	.traffic_instr_nxt_instr      (traffic_instr_nxt_instr),
	
    .win_start              (win_start),
    .gt_data_ready          (gt_data_ready),
    .riu2clb_valid          (riu2clb_valid),

    .clb2phy_fifo_rden      (clb2phy_fifo_rden),
	
    .phy2clb_rd_dq_bits    (phy2clb_rd_dq_bits),
    .bisc_byte		(bisc_byte),
	
    .rd_vref_value          (rd_vref_value),
    .cal_dbi_wr             (cal_dbi_wr),
    .cal_dbi_rd             (cal_dbi_rd),

    .config_rd_data         (config_rd_data),
    .config_rd_addr         (config_rd_addr),

    .xsdb_rd_en             (ub_xsdb_rd_en),
    .xsdb_wr_en             (ub_xsdb_wr_en),
    .xsdb_wr_data           (ub_xsdb_wr_data),
    .xsdb_addr              (ub_xsdb_addr),
    .xsdb_rd_data           (ub_xsdb_rd_data),
    .mcal_DQIn                (mcal_DQIn),
    .mcal_DMIn_n              (mcal_DMIn_n),
    .mc_clb2phy_fifo_rden_nxt (mc_clb2phy_fifo_rden_nxt),
    .cal_DQOut              (ub_cal_DQOut),
    .cal_DMOut_n            (ub_cal_DMOut_n),
    .cal_ADR                (ub_cal_ADR),
    .cal_WE                 (ub_cal_WE),
    .cal_RAS                (ub_cal_RAS),
    .cal_CAS                (ub_cal_CAS),

    .cal_RESET_n            (ub_cal_RESET_n),
    .cal_ACT_n              (ub_cal_ACT_n),
    .cal_BA                 (ub_cal_BA),
    .cal_BG                 (ub_cal_BG),
    .cal_C                  (ub_cal_C),
    .cal_CKE                (ub_cal_CKE),
    .cal_CS_n               (ub_cal_CS_n),
    .cal_ODT                (ub_cal_ODT),
    .cal_PAR                (ub_cal_PAR),
    .cal_mrs                (ub_cal_mrs),
    .cal_inv                (ub_cal_inv),
    .clb2phy_wrcs0_upp      (clb2phy_wrcs0_upp),
    .clb2phy_wrcs1_upp      (clb2phy_wrcs1_upp),
    .clb2phy_wrcs0_low      (clb2phy_wrcs0_low),
    .clb2phy_wrcs1_low      (clb2phy_wrcs1_low),
    .clb2phy_rdcs0_upp      (clb2phy_rdcs0_upp),
    .clb2phy_rdcs1_upp      (clb2phy_rdcs1_upp),
    .clb2phy_rdcs0_low      (clb2phy_rdcs0_low),
    .clb2phy_rdcs1_low      (clb2phy_rdcs1_low),

    .casSlot                (calCasSlot),
    .calRank                (calRank),
    .rdCAS                  (calRdCAS),
    .clear_fifo_rden        (cal_clear_fifo_rden),
    .wrCAS                  (calWrCAS),
    .wrDataEn               (wrDataEn),
    .lowCL0                 (ub_lowCL0),
    .lowCL1                 (ub_lowCL1),
    .lowCL2                 (ub_lowCL2),
    .lowCL3                 (ub_lowCL3),
    .uppCL0                 (ub_uppCL0),
    .uppCL1                 (ub_uppCL1),
    .uppCL2                 (ub_uppCL2),
    .uppCL3                 (ub_uppCL3),
	.max_rd_lat             (ub_max_rd_lat),
	.cal_oe_dis_low         (cal_oe_dis_low),
	.cal_oe_dis_upp         (cal_oe_dis_upp),

    .cal_debug              (cal_debug),
	.cal_pre_status         (cal_pre_status),
	.cal_r0_status          (cal_r0_status),
    .cal_r1_status          (cal_r1_status),
    .cal_r2_status          (cal_r2_status),
    .cal_r3_status          (cal_r3_status),
	.cal_post_status        (cal_post_status),
    .cal_error              (cal_error),
    .cal_error_bit          (cal_error_bit),
    .cal_error_nibble       (cal_error_nibble),
    .cal_error_code         (cal_error_code),
    .cal_warning            (cal_warning),
    .cal_warning_nibble     (cal_warning_nibble),
    .cal_warning_code       (cal_warning_code),
    .cal_crc_error          (cal_crc_error)
	,.dbg_cal_seq           (dbg_cal_seq)
	,.dbg_cal_seq_cnt       (dbg_cal_seq_cnt)
	,.dbg_cal_seq_rd_cnt    (dbg_cal_seq_rd_cnt)
    ,.dbg_rd_valid          (dbg_rd_valid)
	,.dbg_cmp_byte          (dbg_cmp_byte)
    ,.dbg_rd_data           (dbg_rd_data)
    ,.dbg_rd_data_cmp       (dbg_rd_data_cmp)
	,.dbg_expected_data     (dbg_expected_data)
    ,.dbg_cplx_config       (dbg_cplx_config)
    ,.dbg_cplx_status       (dbg_cplx_status)
    ,.win_status (win_status)
);

//rom configuration
ddr4_v2_2_10_cal_config_rom  #
(
 .MEM0    ( (MEM == "DDR4") ? 1 : 0),
 .MEM1    (ABITS),
 .MEM2    (BABITS),
 .MEM3    (BGBITS),
 .MEM4    (CKEBITS),
 .MEM5    ((USE_CS_PORT==1) ? CSBITS : 0),
 .MEM6    (ODTBITS),
 .MEM7    (DBYTES),
 .MEM8    (DRAM_WIDTH),
 .MEM9    (nCK_PER_CLK),
 .MEM10   (RANKS),
 .MEM11   (RTL_VERSION),
 .MEM12   (NUM_BRAMS), /* XSDB_BRAMS */
 .MEM13   (BISC_EN),
 .MEM14   (REG_CTRL_ON), /* RDIMM enable */
 .MEM15   (MEM_CODE),
 .MEM16   (MR0),
 .MEM17   (MR1),
 .MEM18   (MR2),
 .MEM19   (MR3),
 .MEM20   (MR4),
 .MEM21   (MR5),
 .MEM22   (MR6),
 .MEM23   (CAL_SIM),
 .MEM24   (DM_DBI_SETTING),
 .MEM25   (DQS_GATE),
 .MEM26   (WRLVL),
 .MEM27   (RDLVL),
 .MEM28   (RDLVL_DBI),
 .MEM29   (WR_DQS_DQ),
 .MEM30   (WR_DQS_DM_DBI),
 .MEM31   (WRITE_LAT),
 .MEM32   (RDLVL_COMPLEX),
 .MEM33   (WR_DQS_COMPLEX),
 .MEM34   (RD_VREF),
 .MEM35   (RD_VREF_PATTERN),
 .MEM36   (WR_VREF),
 .MEM37   (WR_VREF_PATTERN),
 .MEM38   (DQS_TRACKING),
 .MEM39   (DQS_SAMPLE_CNT),
 .MEM40   (WRLVL_SAMPLE_CNT),
 .MEM41   (RDLVL_SAMPLE_CNT),
 .MEM42   (CMPLX_LOOP_CNT),
 .MEM43   (IODELAY_QTR_CK_TAP_CNT),  /* Quarter tCK tap count */
 .MEM44   (EN_DEBUG), /* Debug */
 .MEM45   (S_HEIGHT), 
 .MEM46   (LRDIMM_EN),
 .MEM47   (SLOTS),
 .MEM48   (TRFC_CYCLES),
 .MEM49   (MIGRATION_EN),
 .MEM50   (CKBITS),
 .MEM51   (RESTORE_CRC),
 .MEM52   (PL)
 //.MEM52      (),
 //.MEM53      (),
 //.MEM54      (),
 //.MEM55      (),
 //.MEM56      (),
 //.MEM57      (),
 //.MEM58      (),
 //.MEM59      (),
 //.MEM60      (),
 //.MEM61      (),
 //.MEM62      (),
 //.MEM63      ()
 ) u_ddr_config_rom
 (
   .clk_i   (clk),
   .rd_addr (config_rd_addr[5:0]),
   .dout_o  (config_rd_data)
 );

//-------------------------------------------------------------------
// XSDB slave 
//-------------------------------------------------------------------
  wire s_rst;
  wire s_dclk;
  wire s_den; 
  wire s_dwe;
  wire [16:0] s_daddr;
  wire [15:0] s_di;
  wire [15:0] s_do;
  wire s_drdy;

`ifndef XSDB_SLV_DIS
(* DONT_TOUCH = "true" *) ddr4_v2_2_10_chipscope_xsdb_slave 
#(
    .C_XDEVICEFAMILY		(C_FAMILY),
    .C_MAJOR_VERSION		(C_MAJOR_VERSION),//		 = 11,  // ise major version
    .C_MINOR_VERSION		(C_MINOR_VERSION),//        = 1,   // ise minor version
    .C_BUILD_REVISION		(),//        = 0,   // ise service pack
    .C_CORE_TYPE			(16'h0008),//        = 1,   // root coregen type 
    .C_CORE_MAJOR_VER		(C_CORE_MAJOR_VER),//        = 1,   // root coregen core major version
    .C_CORE_MINOR_VER		(C_CORE_MINOR_VER),//        = 0,   // root corgen core minor version
    .C_XSDB_SLAVE_TYPE		(XSDB_SLAVE_TYPE),//    = 1,   // XSDB Slave Type
    .C_NEXT_SLAVE			(C_NEXT_SLAVE),//        = 0,   // Next slave Relative reference neighbor which is part of the core.
    .C_CSE_DRV_VER			(C_CSE_DRV_VER),//    = 1,   // CSE Slave driver version
    .C_USE_TEST_REG			(C_USE_TEST_REG),//    = 1,   // Set to 1 to use test reg
    .C_PIPE_IFACE			(C_PIPE_IFACE),//        = 1,   // Set to 1 to add pipe delay to XSDB interface signals
    .C_CORE_INFO1			(C_CORE_INFO1),//        = 0,
    .C_CORE_INFO2			(C_CORE_INFO2) //        = 0)
) U_XSDB_SLAVE (
    .s_rst_o(s_rst),
    .s_dclk_o(s_dclk),
    .s_den_o(s_den),
    .s_dwe_o(s_dwe),
    .s_daddr_o(s_daddr),
    .s_di_o(s_di),
    .sl_iport_i(sl_iport0), // ports, need to route up to core wrapper
    .sl_oport_o(sl_oport0), // ports, need to route up to core wrapper
    .s_do_i(s_do),
    .s_drdy_i(s_drdy)
  );
`else
assign s_rst = 1'b0;
assign s_dclk = 1'b0;
assign s_den = 1'b0;
assign s_dwe = 1'b0;
assign s_daddr = 17'b0;
assign s_di = 16'b0;
assign sl_oport0 = 16'b0;
`endif

reg t1, t2 = 0;

`ifdef RESTORE
ddr4_v2_2_10_cal_xsdb_arbiter #(
  .TCQ        (TCQ)
) 
u_xsdb_arbiter 
(
  .slave_clk  (s_dclk),
  .slave_en   (s_den), 
  .slave_we   (s_dwe),
  .slave_addr (s_daddr[15:0]),
  .slave_di   (s_di),
  .slave_do   (s_do),
  .slave_rdy  (s_drdy),
 
  .fabric_clk (clk),
  .fabric_rst (rst_r1),
  .user_en    (usr_xsdb_rd_en),
  .user_we    (usr_xsdb_wr_en),
  .user_addr  (usr_xsdb_addr),
  .user_di    (usr_xsdb_wr_data),
  .user_do    (usr_xsdb_rd_data),
  .user_rdy   (usr_xsdb_rdy),
          
  .bram_clk   (bramB_clk),
  .bram_en    (bramB_en),
  .bram_we    (bramB_we),
  .bram_addr  (bramB_addr),
  .bram_di    (bramB_di),
  .bram_do    (bramB_do),
  .bram_rdy   (bramB_rdy)
);

`else

//strech s_den pulse for 2 clocks to enable b side of dpBRAM
assign bramB_clk = s_dclk;
assign bramB_en = s_den;
assign bramB_we = s_dwe;
assign bramB_addr = s_daddr[15:0];
assign bramB_di = s_di;
assign s_do = {7'b0, bramB_do};
assign s_drdy = bramB_rdy;

`endif

//stretch bram_en for two cycles
always@(posedge bramB_clk)
begin
t1 <= bramB_en;
t2 <= t1;
bramB_rdy <= #TCQ t2;
end
assign bramB_en_stch = (bramB_en | t1);

//-------------------------------------------------------------------
//Bram for XSDB and uB wr/rd
//-------------------------------------------------------------------
(* DONT_TOUCH = "true" *) ddr4_v2_2_10_cal_xsdb_bram
#(
		.START_ADDRESS                   (18),
		.SPREAD_SHEET_VERSION            (PARAM_MAP_VERSION),
		.RTL_VERSION                     (RTL_VERSION),
		.MEM_CODE                        (MEM_CODE),
		.MEMORY_TYPE                     (XSDB_MEMORY_TYPE),
		.MEMORY_CONFIGURATION            ((MEMORY_CONFIGURATION == "COMPONENT") ? 1 : 
		                                  (MEMORY_CONFIGURATION == "UDIMM")     ? 2 : 
										  (MEMORY_CONFIGURATION == "SODIMM")    ? 3 : 
										  (MEMORY_CONFIGURATION == "RDIMM")     ? 4 : 0),
		.MEMORY_VOLTAGE                  ((MEMORY_VOLTAGE == "1.2V")  ? 1 : 
		                                  (MEMORY_VOLTAGE == "1.35V") ? 2 : 
										  (MEMORY_VOLTAGE == "1.5V")  ? 3 : 0),
		.CLKFBOUT_MULT_PLL               (CLKFBOUT_MULT_PLL),
        .DIVCLK_DIVIDE_PLL               (DIVCLK_DIVIDE_PLL),
        .CLKOUT0_DIVIDE_PLL              (CLKOUT0_DIVIDE_PLL),
        .CLKFBOUT_MULT_MMCM              (CLKFBOUT_MULT_MMCM),
        .DIVCLK_DIVIDE_MMCM              (DIVCLK_DIVIDE_MMCM),
        .CLKOUT0_DIVIDE_MMCM             (CLKOUT0_DIVIDE_MMCM),
		.NIBBLE                          (DQ_WIDTH/4),							///number of nibbles
		.DQBITS                          (DQ_WIDTH),
		.BITS_PER_BYTE                   (BITS_PER_BYTE),
		.SLOTS                           (XSDB_SLOTS),
		.ABITS                           (ABITS),
		.BABITS                          (BABITS),
		.BGBITS                     	 (BGBITS),
		.CKEBITS                    	 (CKEBITS),
		.CSBITS                     	 (CSBITS),
		.ODTBITS                    	 (ODTBITS),
		.MEM                        	 (MEM),
		.DBYTES                     	 (DBYTES),
		.DRAM_WIDTH                 	 (DRAM_WIDTH),      					// # of DQ per DQS
		.RANKS                      	 (XSDB_RANKS),
		.S_HEIGHT                        (S_HEIGHT),
		.nCK_PER_CLK                	 (nCK_PER_CLK),      					// # of memory CKs per fabric CLK 
        .tCK                             (tCK),		
		.DM_DBI_SETTING             	 (DM_DBI_SETTING),     					//// 3bits required all 7
		.BISC_EN                         (BISC_EN),
		.USE_CS_PORT                     (USE_CS_PORT),
		.EXTRA_CMD_DELAY                 (EXTRA_CMD_DELAY),
		.REG_CTRL_ON                     (REG_CTRL_ON),
		.CA_MIRROR                       ((CA_MIRROR == "ON")? 1 : 0),
		.DQS_GATE                   	 (DQS_GATE),
		.WRLVL                      	 (WRLVL),
		.RDLVL                      	 (RDLVL),
		.RDLVL_DBI                       (RDLVL_DBI),
		.WR_DQS_DQ                  	 (WR_DQS_DQ),
		.WR_DQS_DM_DBI                   (WR_DQS_DM_DBI),
		.WRITE_LAT                       (WRITE_LAT),
		.RDLVL_COMPLEX                   (RDLVL_COMPLEX),     				    ///2 bits required all 3
		.WR_DQS_COMPLEX                  (WR_DQS_COMPLEX),     				    ///2 bits required all 3
		.DQS_TRACKING               	 (DQS_TRACKING),
		.RD_VREF                    	 (RD_VREF),
		.RD_VREF_PATTERN                 (RD_VREF_PATTERN),
		.WR_VREF                    	 (WR_VREF),
		.WR_VREF_PATTERN                 (WR_VREF_PATTERN),
		.DQS_SAMPLE_CNT             	 (DQS_SAMPLE_CNT),
		.WRLVL_SAMPLE_CNT           	 (WRLVL_SAMPLE_CNT),
		.RDLVL_SAMPLE_CNT           	 (RDLVL_SAMPLE_CNT),
		.COMPLEX_LOOP_CNT           	 (CMPLX_LOOP_CNT),
		.IODELAY_QTR_CK_TAP_CNT     	 (IODELAY_QTR_CK_TAP_CNT),
		.DEBUG_MESSAGES                  (EN_DEBUG[0]),
		.MR0                     		 (MR0),
		.MR1                     		 (MR1), 								//RTT_NOM=RZQ/4 (60 Ohm)
		.MR2                     		 (MR2),
		.MR3                     		 (MR3),
		.MR4                     		 (MR4),
		.MR5                     		 (MR5),
		.MR6                     		 (MR6),
		.ODTWR                           (ODTWR),
		.ODTRD                           (ODTRD),
		.SLOT0_CONFIG                    (SLOT0_CONFIG),
		.SLOT1_CONFIG                    (SLOT1_CONFIG),
		.SLOT0_FUNC_CS                   (SLOT0_FUNC_CS),
		.SLOT1_FUNC_CS                   (SLOT1_FUNC_CS),
		.SLOT0_ODD_CS                    (SLOT0_ODD_CS),
		.SLOT1_ODD_CS                    (SLOT1_ODD_CS),
		.DDR4_REG_RC03                   (DDR4_REG_RC03),
		.DDR4_REG_RC04                   (DDR4_REG_RC04),
		.DDR4_REG_RC05                   (DDR4_REG_RC05),
		.DDR4_REG_RC3X                   (DDR4_REG_RC3X),
		.NUM_BRAMS                       (NUM_BRAMS),
		.SIZE                            (BRAM_SIZE)
	)
DDR_XSDB_BRAM
    (
		.addra(bramA_addr[15:0]), //MB writes on side a, using 12 bits from Addr decoder 
		.clka(clk), //Side a uses same clock as RIU
		.dina(bramA_di[8:0]),
		.douta(bramA_do[8:0]),
		.ena(bramA_en),
		.wea(bramA_we),
		.rsta(1'b0), // portA reset. Tied to '0' (not asserted)
		.rstb(1'b0), // portB reset. Tied to '0' (not asserted)
		.addrb(bramB_addr[15:0]),// XSDB reads on side b using sl_iport_i[11:0] for addr input;max 16bits supoorted
		.clkb(bramB_clk),//Side b uses the same clock that XSDB master generated
		.dinb(bramB_di[8:0]),//XSDB writes with user's data 
		.doutb(bramB_do[8:0]),//Output of Bram to XSDB, using sl_oport_o[8:0];XSDB reads 9bits of BRAM data
		.enb(bramB_en_stch),/// stretched pulse to latch output BRAM data
		.web(bramB_we) ///XSDB write enable for BRAM
   );		
//----------------------------------------------------------------------------------


reg  [5:0] calSt;
reg [17:0] cntr;
reg  [5:0] retSt;

reg [4:0] cmr_cnt;
reg [7:0] cs_mask_int; // functional chipselect mask
reg [7:0] cs_mask_int_nxt;
reg [7:0] cs_mask;     // walking functional chipselect mask
reg       mrs_done;    // For RDIMM, mrs_done tracks if MRS is written for each rank and SideA/B

reg                     initDone;
`ifdef RECONFIG_INIT_RESET_1
// Initialize to zero at bit stream download
reg [7:0]               init_cal_RESET_n = {8{SELF_REFRESH}};
`else
reg [7:0]               init_cal_RESET_n = 8'h00;
`endif
reg [18*8-1:0]          init_cal_ADR;            // Max width to avoid index out of range warnings
reg [7:0]               init_cal_ACT_n;
reg [BABITS*8-1:0]      init_cal_BA;
reg [BGBITS*8-1:0]      init_cal_BG;
reg [CKEBITS*8-1:0]     init_cal_CKE = {CKEBITS{8'b0}};
reg [CSBITS*8-1:0]      init_cal_CS_n;
reg [DBYTES*8-1:0]      init_cal_DMOut_n;
reg [DBYTES*8*8-1:0]    init_cal_DQOut;
reg [ODTBITS*8-1:0]     init_cal_ODT;
reg [7:0]               init_cal_PAR;
reg                     init_cal_PAR_r7;
reg [DBYTES*8-1:0]       init_cal_RANKSEL_0;
reg [DBYTES*8-1:0]       init_cal_RANKSEL_1;
reg [7:0]               init_cal_CAS_n;
reg [7:0]               init_cal_RAS_n;
reg [7:0]               init_cal_WE_n;
reg 			init_cal_inv;
reg 			init_cal_mrs;
   
wire caldone;
reg caldone_r;
assign caldone = (BYPASS_CAL == "TRUE")? ((RTL_DDR_INIT == 1) ? initDone : ub_initDone) : ub_calDone;
always @ (posedge clk)
begin
caldone_r <= #TCQ caldone;
calDone <= #TCQ caldone_r;
end 

// DDR4      inversion
// DDR3/DDR4 mirroring for odd rank
   wire [7:0] slotx_cs_odd;
   wire [BGBITS*8-1:0] 	     cal_BG_int; // intermediate signal after uB, init mux
   wire [BABITS*8-1:0] 	     cal_BA_int;
   wire [ABITS*8-1:0] 	     cal_ADR_int;
   wire 		     cal_inv_int;
   wire 		     cal_mrs_int;
   reg [BGBITS*8-1:0] 	     cal_BG_inv; // intermediate signal after uB, init mux
   reg [BABITS*8-1:0] 	     cal_BA_inv;
   reg [ABITS*8-1:0] 	     cal_ADR_inv;
   reg [BGBITS*8-1:0] 	     cal_BG_mirror; // mirrored signal
   reg [BABITS*8-1:0] 	     cal_BA_mirror;
   reg [ABITS*8-1:0] 	     cal_ADR_mirror;
   genvar 		     i,j;
   integer 		     k,l;
   
assign slotx_cs_odd = SLOTX_CS_ODD;
assign cal_BG_int   = ub_ready || (RTL_DDR_INIT == 0) ? ub_cal_BG : init_cal_BG; 
assign cal_BA_int   = ub_ready || (RTL_DDR_INIT == 0) ? ub_cal_BA : init_cal_BA;
assign cal_ADR_int  = ub_ready || (RTL_DDR_INIT == 0) ? ub_cal_ADR : init_cal_ADR[ABITS*8-1:0];
assign cal_inv_int  = ub_ready || (RTL_DDR_INIT == 0) ? ub_cal_inv : init_cal_inv;
assign cal_mrs_int  = ub_ready || (RTL_DDR_INIT == 0) ? ub_cal_mrs : init_cal_mrs;
   
   // DDR4 inversion
   generate
      for (i=0; i<ABITS; i=i+1) begin
	 always@(*) begin
	    cal_ADR_inv[i*8+:8]  = cal_ADR_int[i*8+:8];
	    if (REG_CTRL == "ON" && MEM != "DDR3") begin
	       if (cal_mrs_int && cal_inv_int &&
		   (i==3 || i==4 || i==5 || i==6 || i==7 || i==8 || i==9 || i==11 ||
		    i== 13 || i==17))
		 cal_ADR_inv[i*8+:8] = ~cal_ADR_int[i*8+:8]; // 3,4,5,6,7,8,9,11,13,17
	       
	    end
	 end
      end
      
      for (i=0; i<BABITS; i=i+1) begin
	 always@(*) begin
	    cal_BA_inv[i*8+:8]   = cal_BA_int[i*8+:8];
	    if (REG_CTRL == "ON" && MEM != "DDR3") begin
	       if (cal_mrs_int && cal_inv_int)
		 cal_BA_inv[i*8+:8]  = ~cal_BA_int[i*8+:8]; // 0,1
	    end
	 end
      end

      for (i=0; i<BGBITS; i=i+1) begin
	 always@(*) begin
	    cal_BG_inv[i*8+:8]   = cal_BG_int[i*8+:8];
	    if (REG_CTRL == "ON" && MEM != "DDR3") begin
	       if (cal_mrs_int && cal_inv_int)
		 cal_BG_inv[i*8+:8]  = ~cal_BG_int[i*8+:8]; // 0,1
	    end
	 end
      end
   endgenerate
  
   localparam RANK_SLAB = (MRS_INIT_4RANKS == 1) ? 4 : 8 ;
   // DDR3/4 mirroring for Odd Ranks
   reg  [7:0] cs_odd_vec[RANK_SLAB-1:0];
   wire [7:0] cs_odd;

   generate
   if (RANK_SLAB == 4) begin: Ranks_421
     assign cs_odd = cs_odd_vec[0] | cs_odd_vec[1] | cs_odd_vec[2] | cs_odd_vec[3];
   end else begin: Ranks_8
     assign cs_odd = cs_odd_vec[0] | cs_odd_vec[1] | cs_odd_vec[2] | cs_odd_vec[3] | cs_odd_vec[4] | cs_odd_vec[5] | cs_odd_vec[6] | cs_odd_vec[7];
   end
   endgenerate

   generate      
      if (CA_MIRROR == "ON") begin
	 for (j=0; j<CSBITS; j=j+1) begin
	    always@(*) begin
	       if (slotx_cs_odd[j]) begin
		  cs_odd_vec[j] = ~cal_CS_n[j*8+:8];
	       end
	       else begin
		  cs_odd_vec[j] = 8'b0;
	       end
	    end
	 end
	 for (j=CSBITS; j<4; j=j+1) begin
	    assign cs_odd_vec[j] = 8'b0;
	 end
      end
      else begin
	 for (j=0; j<4; j=j+1) begin
	    assign cs_odd_vec[j] = 8'b0;
	 end
      end
   endgenerate

//   generate      
always@(*) begin
      if (CA_MIRROR == "ON") begin
	 for (k=0; k<ABITS; k=k+1) begin
	    for (l=0; l<8; l=l+1) begin
	       //always@(*) begin
		  cal_ADR_mirror[k*8+l] = cal_ADR_inv[k*8+l];
		  if (cs_odd[l]) begin
		     // DDR3 + DDR4 common mirroring bits
		     if (k==4 || k==6 || k==8) begin
			cal_ADR_mirror[k*8+l]     = cal_ADR_inv[(k-1)*8+l]; // 3->4, 5->6, 7->8
			cal_ADR_mirror[(k-1)*8+l] = cal_ADR_inv[k*8+l];     // 4->3, 6->5, 8->7
		     end
		     else if (MEM != "DDR3") begin
			// DDR4 Only mirroring bits
			if (k == 13) begin
			   cal_ADR_mirror[k*8+l]     = cal_ADR_inv[(k-2)*8+l]; // 11->13
			   cal_ADR_mirror[(k-2)*8+l] = cal_ADR_inv[k*8+l];     // 13->11
			end		     
		     end
		  end
	       //end
	    end
	 end

	 for (k=0; k<BABITS; k=k+1) begin
	    for (l=0; l<8; l=l+1) begin
	       //always@(*) begin
		  cal_BA_mirror[k*8+l]  = cal_BA_inv[k*8+l];
		  if (cs_odd[l]) begin
		     // DDR3 + DDR4 common mirroring bits
		     if (k==1) begin
			cal_BA_mirror[k*8+l]     = cal_BA_inv[(k-1)*8+l]; // 0->1
			cal_BA_mirror[(k-1)*8+l] = cal_BA_inv[k*8+l];     // 1->0
		     end
		  end
	       //end
	    end
	 end

	 for (k=0; k<BGBITS; k=k+1) begin
	    for (l=0; l<8; l=l+1) begin
	       //always@(*) begin
		  // DDR4 Only mirroring bits
		  cal_BG_mirror[k*8+l]  = cal_BG_inv[k*8+l];
		  if ((MEM != "DDR3") && cs_odd[l]) begin
		     if (k==1) begin
			cal_BG_mirror[k*8+l]      = cal_BG_inv[(k-1)*8+l]; // 0->1
			cal_BG_mirror[(k-1)*8+l]  = cal_BG_inv[k*8+l];     // 1->0	
		     end
		  end
	       //end
	    end
	 end
      end
      else begin
	 cal_BG_mirror   = cal_BG_inv;
	 cal_BA_mirror   = cal_BA_inv;
	 cal_ADR_mirror  = cal_ADR_inv;
      end
end
//   endgenerate
   
assign en_vtc  = (BYPASS_CAL == "TRUE")? calDone : ub_en_vtc;
assign rtl_initDone = (RTL_DDR_INIT == 1) ? initDone : 1'b0;
// Mux between rtl initialization driven and MicroBlaze driven signals
assign cal_RESET_n = ub_ready || (RTL_DDR_INIT == 0) ? ub_cal_RESET_n : init_cal_RESET_n;
assign cal_ADR     = cal_ADR_mirror;
assign cal_ACT_n   = ub_ready || (RTL_DDR_INIT == 0) ? ub_cal_ACT_n : init_cal_ACT_n;
assign cal_BA      = cal_BA_mirror;
assign cal_BG      = cal_BG_mirror;
assign cal_C       = ub_ready || (RTL_DDR_INIT == 0) ? ub_cal_C : '0;
assign cal_CKE     = ub_ready || (RTL_DDR_INIT == 0) ? ub_cal_CKE : init_cal_CKE;
assign cal_CS_n    = ub_ready || (RTL_DDR_INIT == 0) ? ub_cal_CS_n : init_cal_CS_n;
assign cal_DMOut_n = ub_cal_DMOut_n;
assign cal_DQOut   = ub_cal_DQOut;
assign cal_ODT     = ub_ready || (RTL_DDR_INIT == 0) ? ub_cal_ODT : init_cal_ODT;
assign cal_PAR     = ub_ready || (RTL_DDR_INIT == 0) ? ub_cal_PAR : init_cal_PAR;
assign cal_WE_n    = ub_ready || (RTL_DDR_INIT == 0) ? ub_cal_WE : init_cal_WE_n;
assign cal_CAS_n   = ub_ready || (RTL_DDR_INIT == 0) ? ub_cal_CAS : init_cal_CAS_n;
assign cal_RAS_n   = ub_ready || (RTL_DDR_INIT == 0) ? ub_cal_RAS : init_cal_RAS_n;


//*************************************************************************//
//****************** DDR Memory Initialization ****************************//
//*************************************************************************// 
localparam
    calStRECONFIG = 6'h00
   ,calStBISC  = 6'h01
   ,calStRESET = 6'h02
   ,calStWAIT  = 6'h03
   ,calStERROR = 6'h04
   ,calStCKEON = 6'h05
   ,calStMR3   = 6'h06
   ,calStMR6   = 6'h07
   ,calStMR5   = 6'h08
   ,calStMR4   = 6'h09
   ,calStMR2   = 6'h0A
   ,calStMR1   = 6'h0B
   ,calStMR0   = 6'h0C
   ,calStZQCL  = 6'h0D
   ,calStGOGO  = 6'h0E
   ,calStMR7   = 6'h0F // RDIMM Control Word Register Programming State for DDR3 or DDR4
;

task setDDROP;
   input [2:0] op;
begin
   case (MEM)
      "DDR3": begin
         init_cal_WE_n  <= #TCQ {3'b111, op[0], op[0], 3'b111};
         init_cal_CAS_n <= #TCQ {3'b111, op[1], op[1], 3'b111};
         init_cal_RAS_n <= #TCQ {3'b111, op[2], op[2], 3'b111};
      end
      default: begin
         init_cal_ADR[119:112] <= #TCQ {3'b111, op[0], op[0], 3'b111};
         init_cal_ADR[127:120] <= #TCQ {3'b111, op[1], op[1], 3'b111};
         init_cal_ADR[135:128] <= #TCQ {3'b111, op[2], op[2], 3'b111};
      end
   endcase
end
endtask

task twiddle;
   input [17:0] del;
   input  [5:0] st;
begin
   cntr  <= #TCQ del;
   retSt <= #TCQ st;
   calSt <= #TCQ calStWAIT;
end
endtask

task setCOL;
   input [9:0] col;
   integer i;
   for (i = 0; i <= 9; i = i + 1) init_cal_ADR[i*8+:8] <= #TCQ {8{col[i]}};
endtask

task setROW;
   input [16:0] row;
   integer i;
   for (i = 0; i <= 9; i = i + 1) init_cal_ADR[i*8+:8] <= #TCQ {8{row[i]}};
endtask

task setMR;
   input [12:0] mr;
   integer i;
   begin
     for (i = 0; i <= 12; i = i + 1) init_cal_ADR[i*8+:8] <= #TCQ {8{mr[i]}};
     case (MEM)
       "DDR3": begin
	 for(i = 2;  i < BABITS; i = i + 1) init_cal_BA[i*8+:8] <= #TCQ 8'b0;
         for(i = 13; i < ABITS; i = i + 1) init_cal_ADR[i*8+:8] <= #TCQ 8'b0;
       end
       default: begin
         init_cal_ADR[((ABITS-1)*8)+:8] <= #TCQ (ABITS == 18)? 8'b0:
		                                        init_cal_ADR[((ABITS-1)*8)+:8];
         init_cal_ADR[111:104] <= #TCQ 8'b0;
         //if (DRAM_WIDTH <= 8)
         if (BGBITS == 2)
           init_cal_BG[15:8]    <= #TCQ 8'b0;
       end
     endcase
   end
 endtask

			     
// RDIMM support for DDR3 and DDR4
// RDIMM Control Word Register Select
// CMRs are mapped to a linear counter (cmr_cnt)
   localparam tSTAB_f = 6000000/tCK/4; // CMR (02, 0A, 3X) in Fabric clock unit
   localparam tMRDx4_f = tMRD*4;      // CMR except 02, 0A, 3X in Fabric clock unit
   
 reg [12:0] cmr;
 reg [2:0] bank_w;
 reg [4:0] addr_w;
   reg [17:0]  tCMR_MRD_f;
   assign tCMR_MRD_f = (cmr_cnt == 5'd2 || cmr_cnt == 5'd7 || cmr_cnt == 5'd13) ? tSTAB_f : tMRDx4_f;
   
 // Each cmr_cnt Linear address generated is mapped to RDIMM CMR register.
 // calSt will loop through calStMR7 states N times where N is number of CMR to write.
 // Each time, a RDIMM CMR is written.
always @ (posedge clk) begin
   if (calSt == calStRESET) begin
	cmr_cnt <= #TCQ 'h0;
   end
   else if (calSt == calStMR7) begin
	cmr_cnt <= #TCQ (cmr_cnt == DDR4_CMR_MAX_CNT) ? 'h0 : cmr_cnt + 'h1;
   end
end   

generate      
   always@(*) begin
	 if (MEM == "DDR3") begin
	   casez (cmr_cnt)
	     // Selecting DDR3 RDIMM registers by cmr_cnt
	     5'd0: cmr = {5'b0, REG_RC0};
	     5'd1: cmr = {5'b0, REG_RC1};
	     5'd2: cmr = {5'b0, REG_RC2};
	     5'd3: cmr = {5'b0, REG_RC3};
	     5'd4: cmr = {5'b0, REG_RC4};
	     5'd5: cmr = {5'b0, REG_RC5};
	     5'd6: cmr = {5'b0, REG_RC10};
	     5'd7: cmr = {5'b0, REG_RC11};
	     default: cmr = {5'b0, REG_RC0};
	   endcase
	 end
	 else begin
	   casez (cmr_cnt)
	     // Selecting DDR4 RDIMM registers by cmr_cnt
	     5'd0: cmr = DDR4_REG_RC00;
	     5'd1: cmr = DDR4_REG_RC01;
	     5'd2: cmr = DDR4_REG_RC02;
	     5'd3: cmr = DDR4_REG_RC03;
	     5'd4: cmr = DDR4_REG_RC04;
	     5'd5: cmr = DDR4_REG_RC05;
	     5'd6: cmr = DDR4_REG_RC08;
	     5'd7: cmr = DDR4_REG_RC0A;
	     5'd8: cmr = DDR4_REG_RC0B;
	     5'd9: cmr = DDR4_REG_RC0D;
	     5'd10: cmr = DDR4_REG_RC0E;
	     5'd11: cmr = DDR4_REG_RC0F;
	     5'd12: cmr = DDR4_REG_RC2X;
	     5'd13: cmr = DDR4_REG_RC3X;
	     5'd14: cmr = DDR4_DB_F0BC00;
	     5'd15: cmr = DDR4_DB_F0BC01;
	     5'd16: cmr = DDR4_DB_F0BC02;
	     5'd17: cmr = DDR4_DB_F0BC03;
	     5'd18: cmr = DDR4_DB_F0BC04;
	     5'd19: cmr = DDR4_DB_F0BC05;
	     5'd20: cmr = DDR4_DB_F0BC0A;
	     5'd21: cmr = DDR4_DB_F0BC6X;
	     5'd22: cmr = DDR4_DB_FXBC7X_F5;
	     5'd23: cmr = DDR4_DB_F5BC5X;
	     5'd24: cmr = DDR4_DB_F5BC6X;
	     5'd25: cmr = DDR4_DB_FXBC7X_F0;
	     default: cmr = REG_RC0;
	   endcase
	 end
   end
endgenerate
   
// RDIMM CMR write for DDR3
// init_cal_ADR and init_cal_BA population
task setCMR;
   integer i;
   begin
      bank_w = cmr[7:5];
      addr_w = cmr[4:0];      
      for(i = 0; i < 5;     i = i + 1) init_cal_ADR[i*8+:8] <= #TCQ {8{addr_w[i]}};
      for(i = 5; i < ABITS; i = i + 1) init_cal_ADR[i*8+:8] <= #TCQ 8'b0;
      for(i = 0; i < 3;     i = i + 1) init_cal_BA[i*8+:8] <= #TCQ {8{bank_w[i]}};
      for(i = 3; i < BABITS;i = i + 1) init_cal_BA[i*8+:8] <= #TCQ 8'b0;
      // For CMR programming, all CS_n are pulled down
      init_cal_CS_n  <= #TCQ {CSBITS{8'b11100111}};
      // RAS/CAS/WE pull downs are optional
      init_cal_CAS_n <= #TCQ 8'b11100111;
      init_cal_RAS_n <= #TCQ 8'b11100111;
      init_cal_WE_n  <= #TCQ 8'b11100111;
   end
 endtask

 // Each MRS 
 // calSt will loop through calStMR7 states 2*N times where N is number of CMR to write.
 // Side A will be written without inversion(N MRS), follow by Side B with inversion(N MRS).
 // Each time, a RDIMM CMR is written.   
always @ (posedge clk) begin
   if (calSt == calStRESET) begin
      cs_mask_int  <= #TCQ (SLOT0_FUNC_CS | SLOT1_FUNC_CS);
      init_cal_inv <= #TCQ SIDE_B;
   end
   else if (calSt == calStMR3) begin
      init_cal_inv <= #TCQ ~init_cal_inv;
   end
   else if (calSt == calStZQCL) begin
      cs_mask_int  <= #TCQ cs_mask_int_nxt;
   end
end   

always @ (posedge clk) begin
   if (calSt == calStRESET) begin
      init_cal_mrs <= #TCQ 1'b0;
   end
   else begin
      init_cal_mrs <= #TCQ (calSt == calStMR3) || (calSt == calStMR6) ||
		           (calSt == calStMR5) || (calSt == calStMR4) ||
		           (calSt == calStMR2) || (calSt == calStMR1) ||
		           (calSt == calStMR0);
   end
end
   
generate
if (MRS_INIT_4RANKS == 1) begin: cs_mask_norm
  // Although there are 8-bit in slot0_config, slot1_config, 
  // Only 4 CS_n are supported in decoding now (to help timing)
  always@(*) begin
     casez(cs_mask_int)
       8'b???1 :
         begin
  	  cs_mask         = 8'b0001;
  	  cs_mask_int_nxt = cs_mask_int & 8'b1110;
         end
       8'b??10 :
         begin
  	  cs_mask         = 8'b0010;
  	  cs_mask_int_nxt = cs_mask_int & 8'b1100;
         end
       8'b?100 :
         begin
  	  cs_mask         = 8'b0100;
  	  cs_mask_int_nxt = cs_mask_int & 8'b1000;
         end
       8'b1000 :     
         begin
  	  cs_mask         = 8'b1000;
  	  cs_mask_int_nxt = cs_mask_int & 8'b0000;
         end
       default:
         begin
  	  cs_mask         = 8'b0000;
  	  cs_mask_int_nxt = cs_mask_int & 8'b0000;
         end
     endcase
  end
end else begin: cs_mask_8ranks
  // Dual slot Quad Rank config can support 8 ranks
  always@(*) begin
     casez(cs_mask_int)
       8'b???????1 :
         begin
  	  cs_mask         = 8'b00000001;
  	  cs_mask_int_nxt = cs_mask_int & 8'b11111110;
         end
       8'b??????10 :
         begin
  	  cs_mask         = 8'b00000010;
  	  cs_mask_int_nxt = cs_mask_int & 8'b11111100;
         end
       8'b?????100 :
         begin
  	  cs_mask         = 8'b00000100;
  	  cs_mask_int_nxt = cs_mask_int & 8'b11111000;
         end
       8'b????1000 :     
         begin
  	  cs_mask         = 8'b00001000;
  	  cs_mask_int_nxt = cs_mask_int & 8'b11110000;
         end
       8'b???10000 :     
         begin
  	  cs_mask         = 8'b00010000;
  	  cs_mask_int_nxt = cs_mask_int & 8'b11100000;
         end
       8'b??100000 :     
         begin
  	  cs_mask         = 8'b00100000;
  	  cs_mask_int_nxt = cs_mask_int & 8'b11000000;
         end
       8'b?1000000 :     
         begin
  	  cs_mask         = 8'b01000000;
  	  cs_mask_int_nxt = cs_mask_int & 8'b10000000;
         end
       8'b10000000 :     
         begin
  	  cs_mask         = 8'b10000000;
  	  cs_mask_int_nxt = cs_mask_int & 8'b00000000;
         end
       default:
         begin
  	  cs_mask         = 8'b00000000;
  	  cs_mask_int_nxt = cs_mask_int & 8'b00000000;
         end
     endcase
  end
end
endgenerate

// Done writing MRS when
// DDR3: all functional CS have been gone through
// DDR4: all functional CS (and SideA/B have been gone through for RDIMM)
assign mrs_done = ~(|cs_mask_int_nxt);
   
// For DIMM and RDIMM, each CS_n is pulled down at different time for MRS access (write one by one)
// Activate one bit of the CS_n[3:0] based on mask_num
task setCSn;
   input [7:0] cs_mask;
   integer i;
   begin
      for(i=0; i<CSBITS; i=i+1) begin
	 if (cs_mask[i])
	   init_cal_CS_n[8*i +:8] <= #TCQ 8'b11100111;
	 else
	   init_cal_CS_n[8*i +:8] <= #TCQ 8'b11111111;
      end
   end
endtask

wire init_start = (BYPASS_CAL == "TRUE") ? bisc_complete : ub_initDone;   
// DRAM Initialization FSM: Default is DDR4
generate
if(RTL_DDR_INIT == 1)
begin
always @(posedge clk) if (rst_r1) begin
   init_cal_CAS_n <= 8'b0;
   init_cal_RAS_n <= 8'b0;
   init_cal_WE_n <= 8'b0;
   init_cal_ACT_n <= 8'b11111111;
   init_cal_ADR <= {ABITS{8'b00000000}};
   init_cal_BA <= {BABITS{8'b00000000}};
   init_cal_BG <= {BGBITS{8'b00000000}};
   init_cal_CKE <= {CKEBITS{8'b0}};
   init_cal_CS_n <= {CSBITS{8'b11111111}};
   init_cal_DMOut_n <= {DBYTES*8{1'b0}};
   init_cal_DQOut <= {DBYTES*8*8{1'b0}};
   init_cal_ODT <= {ODTBITS{8'b0}};
   init_cal_PAR <= 8'b0;
`ifdef RECONFIG_INIT_RESET_1
   init_cal_RESET_n <= {8{SELF_REFRESH}};
`else
   init_cal_RESET_n <= 8'h00;
`endif   
   cntr <= 18'bx;
   initDone <= 1'b0;
   retSt <= calStRECONFIG;
   calSt <= calStRECONFIG;
end else begin
   init_cal_CS_n <= #TCQ {CSBITS{8'b11111111}};
   setDDROP(NOP);
   casez (calSt)
     calStRECONFIG: begin twiddle(t200us, calStBISC); end // Wait for post_reconfig getting stable
     calStBISC: begin
	if (pllGate && init_start /*bisc_complete*/) begin
	   if (app_mem_init_skip) begin
	      init_cal_RESET_n <= #TCQ 8'hFF;
	      twiddle(t200us, calStGOGO); // 5us of tSTAB for RDIMM RCD will be covered by this 200us
	   end
	   else begin
	      init_cal_RESET_n <= #TCQ 8'h00;
	      twiddle(t200us, calStRESET);
	   end
	end
     end
     calStRESET: begin
        init_cal_RESET_n <= #TCQ 8'hFF;
        twiddle(t500us, calStCKEON);
     end
     calStCKEON: begin
        init_cal_CKE <= #TCQ {CKEBITS{8'b11111111}};
	// If register control is on, write CMRs; else, write MRs
	if (REG_CTRL == "ON") begin
           twiddle(tXPR, calStMR7);
	end
	else begin
	   case (MEM)
             "DDR3": twiddle(tXPR, calStMR2);
             default: twiddle(tXPR, calStMR3);
	   endcase
	end
     end

     // Start of RDIMM Register programming for DDR3 or DDR4
     // CMRs written into register chip
     calStMR7: begin
	case (MEM)
          "DDR3": 
	    begin
	       setCMR();
	       if (cmr_cnt == 5'd7) begin // 7 RDIMM CMR written for DDR3
		  twiddle(tCMR_MRD_f, calStMR2);
	       end
	       else begin
		  twiddle(tCMR_MRD_f, calStMR7);
	       end
	    end
          default:
	    begin
               init_cal_BG[7:0] <= #TCQ 8'b11111111;
	       init_cal_BA[15:8] <= #TCQ 8'b11111111;
	       init_cal_BA[7:0] <= #TCQ 8'b11111111;
	       setMR(cmr);
	       setDDROP(MRS);
	       //init_cal_CS_n[7:0] <= #TCQ 8'b11100111; // Only CS0_n goes low when CMR is written for DDR4
	       setCSn(SLOT0_RDIMM_REG_CS|SLOT1_RDIMM_REG_CS);
	       if (cmr_cnt == DDR4_CMR_MAX_CNT) begin // 16 RDIMM CMR written for DDR3
		  twiddle(tCMR_MRD_f, calStMR3);
	       end
	       else begin
		  twiddle(tCMR_MRD_f, calStMR7);
	       end
	    end
	endcase
     end     
      // End of RDIMM Register programming

      calStMR3: begin
         init_cal_BG[7:0] <= #TCQ 8'b00000000;
         init_cal_BA[15:8] <= #TCQ 8'b11111111;
         init_cal_BA[7:0] <= #TCQ 8'b11111111;
         setMR(MR3);
         setDDROP(MRS);
	 setCSn(cs_mask);
case (MEM)
         "DDR3": twiddle(tMRD, calStMR1);
         default: twiddle(tMRD, calStMR6);
endcase
      end
      calStMR6: begin
         init_cal_BG[7:0] <= #TCQ 8'b11111111;
         init_cal_BA[15:8] <= #TCQ 8'b11111111;
         init_cal_BA[7:0] <= #TCQ 8'b00000000;
         setMR(MR6);
         setDDROP(MRS);
	 setCSn(cs_mask);
         twiddle(tMRD, calStMR5);
      end
      calStMR5: begin
         init_cal_BG[7:0] <= #TCQ 8'b11111111;
         init_cal_BA[15:8] <= #TCQ 8'b00000000;
         init_cal_BA[7:0] <= #TCQ 8'b11111111;
	 if (LRDIMM_QUAD_RANK) begin
	    if      (cs_mask == 8'h01) setMR(MR5_0);
	    else if (cs_mask == 8'h02) setMR(MR5_1);
	    else if (cs_mask == 8'h04) setMR(MR5_2);
	    else if (cs_mask == 8'h08) setMR(MR5_3);
	    else if (cs_mask == 8'h10) setMR(MR5_0);
	    else if (cs_mask == 8'h20) setMR(MR5_1);
	    else if (cs_mask == 8'h40) setMR(MR5_2);
	    else                       setMR(MR5_3);
	 end
	 else begin
           setMR(MR5);
	 end
         setDDROP(MRS);
	 setCSn(cs_mask);
         twiddle(tMRD, calStMR4);
      end
      calStMR4: begin
         init_cal_BG[7:0] <= #TCQ 8'b11111111;
         init_cal_BA[15:8] <= #TCQ 8'b00000000;
         init_cal_BA[7:0] <= #TCQ 8'b00000000;
         setMR(MR4);
         setDDROP(MRS);
	 setCSn(cs_mask);
         twiddle(tMRD, calStMR2);
      end
      calStMR2: begin
         init_cal_BG[7:0] <= #TCQ 8'b00000000;
         init_cal_BA[15:8] <= #TCQ 8'b11111111;
         init_cal_BA[7:0] <= #TCQ 8'b00000000;
         setMR(MR2);
         setDDROP(MRS);
	 setCSn(cs_mask);
case (MEM)
         "DDR3": twiddle(tMRD, calStMR3);
         default: twiddle(tMRD, calStMR1);
endcase
      end
      calStMR1: begin
         init_cal_BG[7:0] <= #TCQ 8'b00000000;
         init_cal_BA[15:8] <= #TCQ 8'b00000000;
         init_cal_BA[7:0] <= #TCQ 8'b11111111;
	 if ((LRDIMM_EN == 0) && (SLOT0_CONFIG == 8'b1111 || SLOT1_CONFIG == 8'b1111)) begin // If Single slot Quad Rank
	    if      (cs_mask == 8'b0001) setMR(MR1_0);
	    else if (cs_mask == 8'b0010) setMR(MR1_1);
	    else if (cs_mask == 8'b0100) setMR(MR1_2);
	    else                         setMR(MR1_3);
	 end
	 else begin
            setMR(MR1);
	 end
         setDDROP(MRS);
	 setCSn(cs_mask);
         twiddle(tMRD, calStMR0);
      end
      calStMR0: begin
         init_cal_BG[7:0] <= #TCQ 8'b00000000;
         init_cal_BA[15:8] <= #TCQ 8'b00000000;
         init_cal_BA[7:0] <= #TCQ 8'b00000000;
         setMR(MR0);
         setDDROP(MRS);
	 setCSn(cs_mask);
case (MEM)
         "DDR3": twiddle(tMOD, calStZQCL);
         default: begin
	    if (REG_CTRL == "OFF" || init_cal_inv == SIDE_B) begin
	       twiddle(tMOD, calStZQCL);
	    end
	    else begin
	       twiddle(tMOD, calStMR3);
	    end
	 end
endcase
      end
      calStZQCL: begin
         init_cal_ADR[87:80] <= #TCQ 8'b11111111; // set A10 for ZQCL
         setDDROP(ZQC);
	 setCSn(cs_mask);
	 if (mrs_done)
           twiddle(tZQINIT, calStGOGO);
	 else begin
case (MEM)
         "DDR3": twiddle(tZQINIT, calStMR2);
         default: twiddle(tZQINIT, calStMR3);
endcase
	 end
      end
      calStGOGO: initDone <= 1'b1; // Now we are ready for operations
      calStWAIT: begin
         cntr <= #TCQ cntr - 1'b1;
         if (cntr == 0) calSt <= #TCQ retSt;
      end
      calStERROR: ;
   endcase
end
end
endgenerate
endmodule


