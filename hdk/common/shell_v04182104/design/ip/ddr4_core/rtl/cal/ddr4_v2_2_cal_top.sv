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
//  /   /         Filename           : ddr4_v2_2_10_cal_top.sv
// /___/   /\     Date Last Modified : $Date: 2015/04/21 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                    ddr4_v2_2_10_cal_top module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ns/100ps
`define RECONFIG_INIT_RESET_1

module ddr4_v2_2_10_cal_top #
 (
    parameter         PING_PONG_PHY  = 1
   ,parameter integer ABITS          = 14
   ,parameter integer BABITS         = 2
   ,parameter integer BGBITS         = 2
   ,parameter integer S_HEIGHT       = 1
   ,parameter integer LR_WIDTH       = 1
   ,parameter integer CKEBITS        = 1
   ,parameter integer CKBITS         = 1
   ,parameter integer COLBITS        = 9
   ,parameter integer CSBITS         = 1
   ,parameter integer ODTBITS        = 1
   ,parameter         MEM            = "DDR4"
   ,parameter integer DQ_WIDTH       = 16
   ,parameter integer DBYTES         = 1
   ,parameter integer CH0_DBYTES     = DBYTES
   ,parameter integer CH1_DBYTES     = DBYTES
   ,parameter integer NUM_CHANNELS   = PING_PONG_PHY
   ,parameter integer DBAW           = 5
   ,parameter         ODTWR          = 16'h0033
   ,parameter         ODTWRDEL       = 5'd8
   ,parameter         ODTWRDUR       = 4'd6
   ,parameter         ODTWRODEL      = 5'd9
   ,parameter         ODTWRODUR      = 4'd6
   ,parameter         ODTRD          = 16'h0012
   ,parameter         ODTRDDEL       = 5'd11
   ,parameter         ODTRDDUR       = 4'd6
   ,parameter         ODTRDODEL      = 5'd9
   ,parameter         ODTRDODUR      = 4'd6
   ,parameter         ODTNOP         = 16'h0000
   ,parameter         SELF_REFRESH   = 1'b0
   ,parameter         SAVE_RESTORE   = 1'b0
   ,parameter         RESTORE_CRC    = 1'b0

   ,parameter         MR0            = 13'bxxxxxxxxxxxx
   ,parameter         MR1            = 13'bxxxxxxxxxxxx
   ,parameter         MR2            = 13'bxxxxxxxxxxxx
   ,parameter         MR3            = 13'bxxxxxxxxxxxx
   ,parameter         MR4            = 13'bxxxxxxxxxxxx
   ,parameter         MR5            = 13'bxxxxxxxxxxxx
   ,parameter         MR6            = 13'bxxxxxxxxxxxx
   ,parameter         RD_VREF_VAL    = 7'h2E

   ,parameter         SLOT0_CONFIG   = 8'b0000_0001 // Slot0 Physical configuration
   ,parameter         SLOT1_CONFIG   = 8'b0000_0000 // Slot1 Physical configuration
   ,parameter         SLOT0_FUNC_CS  = 8'b0000_0001 // Slot0 Functional chipselect
   ,parameter         SLOT1_FUNC_CS  = 8'b0000_0000 // Slot1 Functional chipselect
   ,parameter         SLOT0_ODD_CS   = 8'b0000_1010 // Slot0 Odd chipselect
   ,parameter         SLOT1_ODD_CS   = 8'b0000_1010 // Slot1 Odd chipselect
   
   ,parameter         REG_CTRL       = "OFF" // RDIMM register control
   ,parameter         LRDIMM_MODE    = "OFF" // LRDIMM Enable
   ,parameter         DDR4_DB_HIF_RTT_NOM  = 4'b0000 // DDR4 Data Buffer Host I/F DQ RTT_NOM
   ,parameter         DDR4_DB_HIF_RTT_WR   = 4'b0000 // DDR4 Data Buffer Host I/F DQ RTT_WR
   ,parameter         DDR4_DB_HIF_RTT_PARK = 4'b0000 // DDR4 Data Buffer Host I/F DQ RTT_PARK
   ,parameter         DDR4_DB_HIF_DI       = 4'b0000 // DDR4 Data Buffer Host I/F DQ Driver Impedance
   ,parameter         DDR4_DB_DIF_ODT      = 4'b0000 // DDR4 Data Buffer DRAM I/F MDQ ODT
   ,parameter         DDR4_DB_DIF_DI       = 4'b0000 // DDR4 Data Buffer DRAM I/F MDQ Driver Impedance
   ,parameter         DDR4_DB_HIF_VREF     = 8'b0000_0000 // DDR4 Data Buffer Host I/F VRef
   ,parameter         DDR4_DB_DIF_VREF     = 8'b0000_0000 // DDR4 Data Buffer DRAM I/F VRef

   ,parameter         EN_PP_4R_MIR   = 0
   ,parameter         DDR4_CLAMSHELL = "OFF" // Clamshell architecture of DRAM parts on PCB
   ,parameter         CA_MIRROR      = "OFF" // Address mirroring enable
   ,parameter         DDR4_REG_PARITY_ENABLE = "OFF"
   ,parameter         DDR4_REG_RC03  = {9'b0_0000_0011, 4'b0000} // RDIMM register RC03
   ,parameter         DDR4_REG_RC04  = {9'b0_0000_0100, 4'b0000} // RDIMM register RC04
   ,parameter         DDR4_REG_RC05  = {9'b0_0000_0101, 4'b0000} // RDIMM register RC05
   ,parameter         DDR4_REG_RC3X  = {5'b0_0011, 8'b00101011} // RDIMM register RC3X
			     
   ,parameter         tCK            = 2000
   ,parameter         t200us         = 100
   ,parameter         t500us         = 100
   ,parameter         tXPR           = 20
   ,parameter         tMRD           = 2
   ,parameter         tMOD           = 24
   ,parameter         tZQINIT        = 65
   ,parameter         tRFC           = 27
   ,parameter         TCQ            = 0.1

   // Migration parameters
   ,parameter                  MIGRATION = "OFF"
   ,parameter [8*CKBITS-1:0]   CK_SKEW   = {CKBITS{8'b0}}
   ,parameter [8*ABITS-1:0]    ADDR_SKEW = {{8'b0}}
   ,parameter [7:0]            ACT_SKEW  = 8'b0
   ,parameter [7:0]            PAR_SKEW  = 8'b0
   ,parameter [8*BABITS-1:0]   BA_SKEW   = {BABITS{8'b0}}
   ,parameter [8*BGBITS-1:0]   BG_SKEW   = {BGBITS{8'b0}}
   ,parameter [8*CSBITS-1:0]   CS_SKEW   = {CSBITS{8'b0}}
   ,parameter [8*CKEBITS-1:0]  CKE_SKEW  = {CKEBITS{8'b0}}
   ,parameter [8*ODTBITS-1:0]  ODT_SKEW  = {ODTBITS{8'b0}}
   ,parameter [8*LR_WIDTH-1:0] C_SKEW    = {LR_WIDTH{8'b0}}

//for Vivado simulation this param is disabled,for HW always enabled? for verif, can be overwritten from top
`ifdef SIMULATION
   ,parameter BISC_EN = 1'b0
`else
   ,parameter BISC_EN = 1'b1
`endif
   ,parameter         MEMORY_CONFIGURATION = "COMPONENT"
   ,parameter         EARLY_WR_DATA  = "OFF"
   ,parameter         DRAM_WIDTH     = 8
   ,parameter         RANKS          = 1
   ,parameter         RNK_BITS       = (RANKS <= 4) ? 2 : 3
   ,parameter         nCK_PER_CLK    = 4
   ,parameter         RTL_VERSION    = 7
   ,parameter         MEM_CODE       = 0
   ,parameter         BYPASS_CAL     = "TRUE"
   ,parameter         CAL_DQS_GATE       = "FAST_ALL"
   ,parameter         CAL_WRLVL          = "SKIP"
   ,parameter         CAL_RDLVL          = "SKIP"
   ,parameter         CAL_RDLVL_DBI      = "SKIP"
   ,parameter         CAL_WR_DQS_DQ      = "SKIP"
   ,parameter         CAL_WR_DQS_DM_DBI  = "SKIP"
   ,parameter         CAL_WRITE_LAT      = "SKIP"
   ,parameter         CAL_RDLVL_COMPLEX  = "SKIP"
   ,parameter         CAL_WR_DQS_COMPLEX = "SKIP"
   ,parameter         CAL_RD_VREF        = "SKIP"
   ,parameter         CAL_RD_VREF_PATTERN= "SIMPLE"
   ,parameter         CAL_WR_VREF        = "SKIP"
   ,parameter         CAL_WR_VREF_PATTERN= "SIMPLE"
   ,parameter         CAL_DQS_TRACKING   = "FULL"
   ,parameter         CAL_JITTER     = "NONE"
   ,parameter         CLK_2TO1       = "FALSE"
   ,parameter         EXTRA_CMD_DELAY      = 0
   ,parameter         ECC                  = "OFF"

   ,parameter         DM_DBI         = "DM_NODBI"
   ,parameter         USE_CS_PORT    = 1
   ,parameter         RDSTAGES       = 0
   ,parameter         NIBBLE_CNT_WIDTH = 2
   ,parameter         CPLX_PAT_LENGTH  = "LONG"
   ,parameter         C_FAMILY         = "kintexu"
   ,parameter         C_DEBUG_ENABLED  = 0

   // for XSDB
   ,parameter         MEMORY_VOLTAGE       = "1.2V"
   ,parameter         CLKFBOUT_MULT_PLL    = 4
   ,parameter         DIVCLK_DIVIDE_PLL    = 1
   ,parameter         CLKOUT0_DIVIDE_PLL   = 1
   ,parameter         CLKFBOUT_MULT_MMCM   = 4
   ,parameter         DIVCLK_DIVIDE_MMCM   = 1
   ,parameter         CLKOUT0_DIVIDE_MMCM  = 4
)
(
    input clk
   ,input rst

   ,output reg       calDone_gated
   ,input        pllGate
   ,output [5:0] tCWL

   ,input            [7:0] mcCKt
   ,input            [7:0] mcCKc
   ,input            [7:0] mc_ACT_n
   ,input            [7:0] mc_RAS_n
   ,input            [7:0] mc_CAS_n
   ,input            [7:0] mc_WE_n
   ,input    [ABITS*8-1:0] mc_ADR
   ,input   [BABITS*8-1:0] mc_BA
   ,input   [BGBITS*8-1:0] mc_BG
   ,input [LR_WIDTH*8-1:0] mc_C
   ,input  [PING_PONG_PHY*CKEBITS*8-1:0] mc_CKE
   ,input   [PING_PONG_PHY*CSBITS*8-1:0] mc_CS_n
   ,input  [PING_PONG_PHY*ODTBITS*8-1:0] mc_ODT
   ,input            [PING_PONG_PHY*2-1:0] mcCasSlot 
   ,input            [PING_PONG_PHY-1:0]      mcCasSlot2 
   ,input            [PING_PONG_PHY-1:0]      mcRdCAS 
   ,input            [PING_PONG_PHY-1:0]      mcWrCAS 
   ,input            [PING_PONG_PHY-1:0]      winInjTxn 
   ,input            [PING_PONG_PHY-1:0]      winRmw 
   ,input                  gt_data_ready 
   ,input       [PING_PONG_PHY*DBAW-1:0] winBuf 
   ,input            [PING_PONG_PHY*RNK_BITS-1:0] winRank 

   ,output reg [DBYTES*8*8-1:0] rdData
   ,output           [PING_PONG_PHY*DBAW-1:0] rdDataAddr 
   ,output           [PING_PONG_PHY-1:0]           rdDataEn 
   ,output           [PING_PONG_PHY-1:0 ]          rdDataEnd 
   ,output           [PING_PONG_PHY-1:0]           per_rd_done 
   ,output           [PING_PONG_PHY-1:0]           rmw_rd_done 
   ,output           [PING_PONG_PHY*DBAW-1:0] wrDataAddr 
   ,output           [PING_PONG_PHY-1:0]           wrDataEn 

   ,input       [PING_PONG_PHY*DBAW-1:0] dBufAdr 
   ,input [DBYTES*8*8-1:0] wrData
   ,input   [DBYTES*8-1:0] wrDataMask

   ,output reg   [CKBITS*8-1:0] mcal_CK_t
   ,output reg   [CKBITS*8-1:0] mcal_CK_c
   ,output                [7:0] mcal_ACT_n
   ,output                [7:0] mcal_CAS_n
   ,output                [7:0] mcal_RAS_n
   ,output                [7:0] mcal_WE_n
   ,output        [ABITS*8-1:0] mcal_ADR
   ,output       [BABITS*8-1:0] mcal_BA
   ,output       [BGBITS*8-1:0] mcal_BG
   ,output     [LR_WIDTH*8-1:0] mcal_C
   ,output      [PING_PONG_PHY*CKEBITS*8-1:0] mcal_CKE
   ,output       [PING_PONG_PHY*CSBITS*8-1:0] mcal_CS_n
   ,output       [DBYTES*8-1:0] mcal_DMOut_n
   ,output     [DBYTES*8*8-1:0] mcal_DQOut
   ,output                [7:0] mcal_DQSOut

   ,output       [DBYTES*8-1:0] ch1_mcal_DMOut_n
   ,output     [DBYTES*8*8-1:0] ch1_mcal_DQOut
   ,output                [7:0] ch1_mcal_DQSOut

   ,output      [PING_PONG_PHY*ODTBITS*8-1:0] mcal_ODT
   ,output                [7:0] mcal_PAR
   ,(* keep = "true" *) output reg  [DBYTES*13-1:0] mcal_clb2phy_fifo_rden
   ,output        [DBYTES*4-1:0] mcal_clb2phy_t_b_upp
   ,output        [DBYTES*4-1:0] mcal_clb2phy_t_b_low
   ,output        [DBYTES*4-1:0] mcal_clb2phy_rden_upp
   ,output        [DBYTES*4-1:0] mcal_clb2phy_rden_low
   ,output reg    [DBYTES*4-1:0] mcal_clb2phy_wrcs0_upp
   ,output reg    [DBYTES*4-1:0] mcal_clb2phy_wrcs1_upp
   ,output reg    [DBYTES*4-1:0] mcal_clb2phy_wrcs0_low
   ,output reg    [DBYTES*4-1:0] mcal_clb2phy_wrcs1_low
   ,output reg    [DBYTES*4-1:0] mcal_clb2phy_rdcs0_upp
   ,output reg    [DBYTES*4-1:0] mcal_clb2phy_rdcs1_upp
   ,output reg    [DBYTES*4-1:0] mcal_clb2phy_rdcs0_low
   ,output reg    [DBYTES*4-1:0] mcal_clb2phy_rdcs1_low
   ,output        [DBYTES*7-1:0] mcal_clb2phy_odt_upp
   ,output        [DBYTES*7-1:0] mcal_clb2phy_odt_low

   ,(* keep = "true" *) output reg  [DBYTES*13-1:0] ch1_mcal_clb2phy_fifo_rden
   ,output        [DBYTES*4-1:0] ch1_mcal_clb2phy_t_b_upp
   ,output        [DBYTES*4-1:0] ch1_mcal_clb2phy_t_b_low
   ,output        [DBYTES*4-1:0] ch1_mcal_clb2phy_rden_upp
   ,output        [DBYTES*4-1:0] ch1_mcal_clb2phy_rden_low
   ,output reg    [DBYTES*4-1:0] ch1_mcal_clb2phy_wrcs0_upp
   ,output reg    [DBYTES*4-1:0] ch1_mcal_clb2phy_wrcs1_upp
   ,output reg    [DBYTES*4-1:0] ch1_mcal_clb2phy_wrcs0_low
   ,output reg    [DBYTES*4-1:0] ch1_mcal_clb2phy_wrcs1_low
   ,output reg    [DBYTES*4-1:0] ch1_mcal_clb2phy_rdcs0_upp
   ,output reg    [DBYTES*4-1:0] ch1_mcal_clb2phy_rdcs1_upp
   ,output reg    [DBYTES*4-1:0] ch1_mcal_clb2phy_rdcs0_low
   ,output reg    [DBYTES*4-1:0] ch1_mcal_clb2phy_rdcs1_low
   ,output        [DBYTES*7-1:0] ch1_mcal_clb2phy_odt_upp
   ,output        [DBYTES*7-1:0] ch1_mcal_clb2phy_odt_low

   ,output        [DBYTES*7-1:0] mcal_rd_vref_value
   ,output reg    sample_gts

   ,input   [DBYTES*8-1:0] mcal_DMIn_n
   ,input [DBYTES*8*8-1:0] mcal_DQIn

   ,input [7:0] phy2clb_rd_dq_bits
   ,output [8:0] bisc_byte

`ifdef RECONFIG_INIT_RESET_1
   // initial hardware state after bit stream download
   ,output reg      [7:0] cal_RESET_n = {8{SELF_REFRESH}}
`else
   ,output reg      [7:0] cal_RESET_n = 8'h00
`endif

   ,input [31:0] io_address
   ,input        io_addr_strobe_lvl
   ,input [31:0] io_write_data
   ,input        io_write_strobe
   ,output [31:0] io_read_data
   ,output        io_ready_lvl


   ,input phy_ready
   ,input bisc_complete
   ,output en_vtc
   ,input  [20-1:0] riu2clb_valid
   
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
   ,output             cal_crc_error
   
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
   
   ,input  wire [36:0] 	      sl_iport0
   ,output wire [16:0] 	      sl_oport0
   
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

   // Self-Refresh and Save/Restore
   ,input         stop_gate_tracking_req
   ,output        stop_gate_tracking_ack
   ,input         app_mem_init_skip
   ,input         app_restore_en
   ,input         app_restore_complete
   ,input         xsdb_select
   ,input         xsdb_rd_en
   ,input         xsdb_wr_en
   ,input  [15:0] xsdb_addr
   ,input  [8:0]  xsdb_wr_data
   ,output [8:0]  xsdb_rd_data
   ,output        xsdb_rdy
   ,output [31:0] dbg_out
);

assign dbg_out = {8'b0, mcal_CKE[7:0], 16'b0};

function [63:0] swizzle; // spyglass disable W499
   input [63:0] d;
   reg [6:0] b;
   for (b = 0; b <= 63; b = b + 1) swizzle[b] = d[{b[2:0], b[5:3]}];
endfunction

function [4:0] mr2totcwl3;
    input [2:0] mr2;
case (mr2)
   3'b000:  mr2totcwl3  = (BYPASS_CAL=="TRUE") ?  5 :  4; //AL disabled : 9
   3'b001:  mr2totcwl3  = (BYPASS_CAL=="TRUE") ?  6 :  5; //10
   3'b010:  mr2totcwl3  = (BYPASS_CAL=="TRUE") ?  7 :  6; //11
   3'b011:  mr2totcwl3  = (BYPASS_CAL=="TRUE") ?  8 :  7; //12
   3'b100:  mr2totcwl3  = (BYPASS_CAL=="TRUE") ?  9 :  8; //14
   3'b101:  mr2totcwl3  = (BYPASS_CAL=="TRUE") ? 10 :  9;
   3'b110:  mr2totcwl3  = (BYPASS_CAL=="TRUE") ? 11 : 10;
   3'b111:  mr2totcwl3  = (BYPASS_CAL=="TRUE") ? 12 : 11;
   default: mr2totcwl3  = 'bx;
endcase
endfunction

function [4:0] mr2totcwl4;
    input [2:0] mr2;
case (mr2)
   3'b000:  mr2totcwl4  = (BYPASS_CAL=="TRUE")?  9 : 8; //AL disabled : 9
   3'b001:  mr2totcwl4  = (BYPASS_CAL=="TRUE")? 10:  9; //10
   3'b010:  mr2totcwl4  = (BYPASS_CAL=="TRUE")? 11: 10; //11
   3'b011:  mr2totcwl4  = (BYPASS_CAL=="TRUE")? 12: 11; //12
   3'b100:  mr2totcwl4  = (BYPASS_CAL=="TRUE")? 14: 13; //14
   3'b101:  mr2totcwl4  = (BYPASS_CAL=="TRUE")? 16: 15; //16
   3'b110:  mr2totcwl4  = (BYPASS_CAL=="TRUE")? 18: 17; //18
   default: mr2totcwl4  = 'bx;
endcase
endfunction

function [4:0] cl2tcl4;
   input [3:0] cl;
casez (cl)
   4'b0000: cl2tcl4 = 9;
   4'b0001: cl2tcl4 = 10;
   4'b0010: cl2tcl4 = 11;
   4'b0011: cl2tcl4 = 12;
   4'b0100: cl2tcl4 = 13;
   4'b0101: cl2tcl4 = 14;
   4'b0110: cl2tcl4 = 15;
   4'b0111: cl2tcl4 = 16;
   4'b1000: cl2tcl4 = 18;
   4'b1001: cl2tcl4 = 20;
   4'b1010: cl2tcl4 = 22;
   4'b1011: cl2tcl4 = 24;
   default: cl2tcl4 = 5'bx;
endcase
endfunction

function [5:0] cl2tcl4_3ds;
   input [4:0] cl;
casez (cl)
   5'b00000: cl2tcl4_3ds = 9;
   5'b00001: cl2tcl4_3ds = 10;
   5'b00010: cl2tcl4_3ds = 11;
   5'b00011: cl2tcl4_3ds = 12;
   5'b00100: cl2tcl4_3ds = 13;
   5'b00101: cl2tcl4_3ds = 14;
   5'b00110: cl2tcl4_3ds = 15;
   5'b00111: cl2tcl4_3ds = 16;
   5'b01000: cl2tcl4_3ds = 18;
   5'b01001: cl2tcl4_3ds = 20;
   5'b01010: cl2tcl4_3ds = 22;
   5'b01011: cl2tcl4_3ds = 24;
   5'b01100: cl2tcl4_3ds = 23;
   5'b01101: cl2tcl4_3ds = 17;
   5'b01110: cl2tcl4_3ds = 19;
   5'b01111: cl2tcl4_3ds = 21;
   5'b10000: cl2tcl4_3ds = 25;
   5'b10001: cl2tcl4_3ds = 26;
   5'b10010: cl2tcl4_3ds = 27;
   5'b10011: cl2tcl4_3ds = 28;
// 5'b10100: cl2tcl4_3ds = 29; // Reserved for 29
   5'b10101: cl2tcl4_3ds = 30;
// 5'b10110: cl2tcl4_3ds = 31; // Reserved for 31
   5'b10111: cl2tcl4_3ds = 32;
   default: cl2tcl4_3ds = 6'bx;
endcase
endfunction

function [4:0] cl2tcl3;
   input [3:0] cl;
casez (cl)
   4'b0010: cl2tcl3 = 5;
   4'b0100: cl2tcl3 = 6;
   4'b0110: cl2tcl3 = 7;
   4'b1000: cl2tcl3 = 8;
   4'b1010: cl2tcl3 = 9;
   4'b1100: cl2tcl3 = 10;
   4'b1110: cl2tcl3 = 11;
   4'b0001: cl2tcl3 = 12;
   4'b0011: cl2tcl3 = 13;
   4'b0101: cl2tcl3 = 14;
   default: cl2tcl3 = 5'bx;
endcase
endfunction

function [4:0] mr5topl4;
    input [2:0] mr5;
case (mr5)
   3'b000:  mr5topl4  = 0;
   3'b001:  mr5topl4  = 4;
   3'b010:  mr5topl4  = 5;
   3'b011:  mr5topl4  = 6;
   3'b100:  mr5topl4  = 8;
   default: mr5topl4  = 0;
endcase
endfunction

localparam AL = MR1[4:3];
localparam CLSELECT = ( MEM == "DDR4" ) ? { MR0[12], MR0[6:4], MR0[2] } : { MR0[6:4], MR0[2] };

localparam PL   = mr5topl4(MR5[2:0]);
localparam TCL3 = cl2tcl3(CLSELECT);
localparam TCL4 = cl2tcl4_3ds(CLSELECT);
localparam TCL  = (MEM == "DDR4") ? TCL4 : TCL3;
localparam RL_DDR   = (AL==2'b01 & S_HEIGHT < 2) ? TCL  + TCL - 1 :
                  (AL==2'b10)                ? TCL  + TCL - 2 : 
                  (AL==2'b11 & S_HEIGHT > 1) ? TCL  + TCL - 3 : 
                                               TCL;

localparam RL = ((LRDIMM_MODE == "ON") ? (RL_DDR + 1) : RL_DDR) + ((MEM == "DDR4") ? PL : 0); // To compensate the propagation delay through Data buffer

localparam TCWL3 = mr2totcwl3(MR2[5:3]);
localparam TCWL4 = mr2totcwl4(MR2[5:3]);
// CWL increase by 1 for RDIMMs at or below DDR2133, and by 2 for RDIMMs above DDR2133
localparam TCWL  = ((MEM == "DDR4") ? TCWL4 : TCWL3) + ((REG_CTRL == "ON") ? 1 : 0) + ((( REG_CTRL == "ON" ) & ( tCK < 937 ) & (BYPASS_CAL=="FALSE")) ? 1 : 0 );
localparam WL_DDR    = (AL==2'b01 & S_HEIGHT < 2) ? TCWL + TCL - 1 :
                   (AL==2'b10)                ? TCWL + TCL - 2 : 
                   (AL==2'b11 & S_HEIGHT > 1) ? TCWL + TCL - 3 :
                                                TCWL;

localparam WL = ((LRDIMM_MODE == "ON") ? (WL_DDR - 1) : WL_DDR) + ((MEM == "DDR4") ? PL : 0); // To compensate the propagation delay through Data buffer

// Assign output
assign      tCWL = (BYPASS_CAL=="TRUE") ? WL : WL + 1;

localparam CH0_DBYTES_PI = (NUM_CHANNELS == 1) ? DBYTES : CH0_DBYTES;
localparam CH1_DBYTES_PI = CH1_DBYTES;

localparam EN_PP_4R_MIR_WID = 1 + EN_PP_4R_MIR;

wire       cal_dbi_wr;
wire       cal_dbi_rd;
reg  [1:0] cal_dbi_wr_r;
reg  [1:0] cal_dbi_rd_r;

wire [1:0] calCasSlot;
wire       calRdCAS;
wire       cal_clear_fifo_rden;
wire       calWrCAS;
wire [1:0] calRank;
wire [DBYTES-1:0] cal_oe_dis_low;
wire [DBYTES-1:0] cal_oe_dis_upp;

reg [PING_PONG_PHY*RNK_BITS-1:0] mcalRank;
reg [PING_PONG_PHY-1:0]      mcalRdCAS;
reg [PING_PONG_PHY-1:0]      mcalWrCAS;
reg [PING_PONG_PHY*2-1:0] mcalCasSlot;

wire [DBYTES*4-1:0] cal_clb2phy_wrcs0_upp;
wire [DBYTES*4-1:0] cal_clb2phy_wrcs1_upp;
wire [DBYTES*4-1:0] cal_clb2phy_wrcs0_low;
wire [DBYTES*4-1:0] cal_clb2phy_wrcs1_low;
wire [DBYTES*4-1:0] cal_clb2phy_rdcs0_upp;
wire [DBYTES*4-1:0] cal_clb2phy_rdcs1_upp;
wire [DBYTES*4-1:0] cal_clb2phy_rdcs0_low;
wire [DBYTES*4-1:0] cal_clb2phy_rdcs1_low;

wire            [7:0] cal_ACT_n;
wire            [7:0] cal_CAS_n;
wire            [7:0] cal_RAS_n;
wire            [7:0] cal_WE_n;
wire    [ABITS*8-1:0] cal_ADR;
wire   [BABITS*8-1:0] cal_BA;
wire   [BGBITS*8-1:0] cal_BG;
wire [LR_WIDTH*8-1:0] cal_C;
wire  [CKEBITS*8-1:0] cal_CKE;
wire   [EN_PP_4R_MIR_WID*CSBITS*8-1:0] cal_CS_n;
wire   [DBYTES*8-1:0] cal_DMOut_n;
wire [DBYTES*8*8-1:0] cal_DQOut;
wire  [ODTBITS*8-1:0] cal_ODT;
wire            [7:0] cal_PAR;
wire            [7:0] cal_RESET_n_int;
wire  [DBYTES*13-1:0] cal_clb2phy_fifo_rden;

reg [DBYTES*8*8-1:0] cal_mcal_DQIn;
reg [DBYTES*8-1:0]   cal_mcal_DMIn_n;
reg                  mc_clb2phy_fifo_rden_nxt_r;

reg           [7:0] mc_ACT_nMod;
reg           [7:0] mc_CAS_nMod;
reg           [7:0] mc_RAS_nMod;
reg           [7:0] mc_WE_nMod;
reg   [ABITS*8-1:0] mc_ADRMod;
reg  [BABITS*8-1:0] mc_BAMod;
reg  [BGBITS*8-1:0] mc_BGMod;
reg [LR_WIDTH*8-1:0] mc_CMod;
reg [PING_PONG_PHY*CKEBITS*8-1:0] mc_CKEMod;
reg  [PING_PONG_PHY*CSBITS*8-1:0] mc_CS_nMod;
reg [PING_PONG_PHY*ODTBITS*8-1:0] mc_ODTMod;

reg               mc_ACT_n7;
reg               mc_RAS_n7;
reg               mc_CAS_n7;
reg               mc_WE_n7;
reg   [ABITS-1:0] mc_ADR7;
reg  [BABITS-1:0] mc_BA7;
reg  [BGBITS-1:0] mc_BG7;
reg [LR_WIDTH-1:0] mc_C7;
reg [PING_PONG_PHY*CKEBITS-1:0] mc_CKE7;
reg  [PING_PONG_PHY*CSBITS-1:0] mc_CS_n7;
reg [PING_PONG_PHY*ODTBITS-1:0] mc_ODT7;

// Shift register for adding command delay
reg            [7:0] mcal_ACT_n_dly[EXTRA_CMD_DELAY:0];
reg            [7:0] mcal_CAS_n_dly[EXTRA_CMD_DELAY:0];
reg            [7:0] mcal_RAS_n_dly[EXTRA_CMD_DELAY:0];
reg            [7:0] mcal_WE_n_dly[EXTRA_CMD_DELAY:0];
reg    [ABITS*8-1:0] mcal_ADR_dly[EXTRA_CMD_DELAY:0];
reg   [BABITS*8-1:0] mcal_BA_dly[EXTRA_CMD_DELAY:0];
reg   [BGBITS*8-1:0] mcal_BG_dly[EXTRA_CMD_DELAY:0];
reg [LR_WIDTH*8-1:0] mcal_C_dly[EXTRA_CMD_DELAY:0];
reg  [PING_PONG_PHY*CKEBITS*8-1:0] mcal_CKE_dly[EXTRA_CMD_DELAY:0];
reg   [PING_PONG_PHY*CSBITS*8-1:0] mcal_CS_n_dly[EXTRA_CMD_DELAY:0];
reg  [PING_PONG_PHY*ODTBITS*8-1:0] mcal_ODT_dly[EXTRA_CMD_DELAY:0];
reg            [7:0] mcal_PAR_dly[EXTRA_CMD_DELAY:0];

wire [DBYTES*13-1:0] mc_clb2phy_fifo_rden_nxt;
wire   [DBYTES*6-1:0] lowCL0;
wire   [DBYTES*6-1:0] lowCL1;
wire   [DBYTES*6-1:0] lowCL2;
wire   [DBYTES*6-1:0] lowCL3;
wire   [DBYTES*6-1:0] uppCL0;
wire   [DBYTES*6-1:0] uppCL1;
wire   [DBYTES*6-1:0] uppCL2;
wire   [DBYTES*6-1:0] uppCL3;
wire   [6:0]         max_rd_lat;
wire  [PING_PONG_PHY-1:0]               rdDataEn_pi; 
wire  [PING_PONG_PHY-1:0]               wrDataEn_pi; 
wire  [PING_PONG_PHY-1:0]               rdInj;
wire  [PING_PONG_PHY-1:0]               rdRmw;
wire                  stop_gate_tracking_ack_lcl;

wire	calDone, calDone_i;
assign calDone_i = calDone && (!BISC_EN || ((BYPASS_CAL == "FALSE") ? phy_ready : bisc_complete));

  always @ (posedge clk) begin
    calDone_gated <= #TCQ calDone_i; // top level version
  end
reg [DBYTES*8*8-1:0] traffic_error_sw;

wire [DBYTES*13-1:0] ch1_mc_clb2phy_fifo_rden_nxt;

(* keep = "TRUE" *) reg rst_r1;

always @(posedge clk)
  rst_r1 <= rst;

// If the rdDataEn_pi is from an injected periodic read or is an underfill read for rmw, do not send it to the native interface
assign rmw_rd_done      = rdDataEn_pi & rdRmw;
assign per_rd_done      = rdDataEn_pi & {2{calDone}} & rdInj; 
assign rdDataEn         = rdDataEn_pi & {2{calDone}} & ~( rdInj | rdRmw ); 
assign wrDataEn         = wrDataEn_pi & {2{calDone}}; 

integer i,j;

function [63:0] rdDBI;
   input [63:0] d;
   input  [7:0] m;
begin
   rdDBI[07:00] = d[07:00] ^ {8{m[0]}};
   rdDBI[15:08] = d[15:08] ^ {8{m[1]}};
   rdDBI[23:16] = d[23:16] ^ {8{m[2]}};
   rdDBI[31:24] = d[31:24] ^ {8{m[3]}};
   rdDBI[39:32] = d[39:32] ^ {8{m[4]}};
   rdDBI[47:40] = d[47:40] ^ {8{m[5]}};
   rdDBI[55:48] = d[55:48] ^ {8{m[6]}};
   rdDBI[63:56] = d[63:56] ^ {8{m[7]}};
end
endfunction

always @ (posedge clk) begin
  cal_dbi_rd_r[0] <= #TCQ cal_dbi_rd;
  cal_dbi_rd_r[1] <= #TCQ cal_dbi_rd_r[0];
  
  cal_dbi_wr_r[0] <= #TCQ cal_dbi_wr;
  cal_dbi_wr_r[1] <= #TCQ cal_dbi_wr_r[0];
end

generate
  always @(posedge clk)
    for (i = 0; i < DBYTES; i = i + 1) begin
      if (DM_DBI == "DM_NODBI" || DM_DBI == "NONE" || DM_DBI == "NODM_DBIWR")
        rdData[i*64+:64] <= #TCQ swizzle(mcal_DQIn[i*64+:64]);
      else
        rdData[i*64+:64] <= #TCQ (cal_dbi_rd_r[1] == 1'b1) ? 
                  rdDBI(swizzle(mcal_DQIn[i*64+:64]), ~(mcal_DMIn_n >> (i * 8))) : 
  				swizzle(mcal_DQIn[i*64+:64]);	  
    end
endgenerate

generate
  always @(posedge clk) begin
    for (i = 0; i < DBYTES; i = i + 1) begin
      if (DM_DBI == "DM_NODBI" || DM_DBI == "NONE" || DM_DBI == "NODM_DBIWR")
        cal_mcal_DQIn[i*64+:64] <= #TCQ mcal_DQIn[i*64+:64];
      else
        cal_mcal_DQIn[i*64+:64] <= #TCQ (cal_dbi_rd_r[1] == 1'b1) ? 
                  swizzle(rdDBI(swizzle(mcal_DQIn[i*64+:64]), ~(mcal_DMIn_n >> (i * 8)))) : 
  				mcal_DQIn[i*64+:64];
	end
  end
endgenerate

//Register the "valid" signal and DM for calibration since we flopped the data
always @(posedge clk) begin
  cal_mcal_DMIn_n            <= #TCQ mcal_DMIn_n;
  mc_clb2phy_fifo_rden_nxt_r <= #TCQ mc_clb2phy_fifo_rden_nxt[0];
end

//Need to re-swizzle the error signal from the traffic gen
always @(posedge clk) begin
   for (i = 0; i < DBYTES; i = i + 1)
     traffic_error_sw[i*64+:64] <= #TCQ swizzle(traffic_error[i*64+:64]);
end

always @(*) begin
   mc_ACT_nMod = {mc_ACT_n[6:0], mc_ACT_n7};
   mc_CAS_nMod = {mc_CAS_n[6:0], mc_CAS_n7};
   mc_RAS_nMod = {mc_RAS_n[6:0], mc_RAS_n7};
   mc_WE_nMod = {mc_WE_n[6:0], mc_WE_n7};
   for (i = 0; i < ABITS; i=i+1) mc_ADRMod[i*8+:8] =  {mc_ADR[i*8+:7], mc_ADR7[i]};
   for (i = 0; i < BABITS; i=i+1) mc_BAMod[i*8+:8] =  {mc_BA[i*8+:7], mc_BA7[i]};
   for (i = 0; i < BGBITS; i=i+1) mc_BGMod[i*8+:8] =  {mc_BG[i*8+:7], mc_BG7[i]};
   for (i = 0; i < LR_WIDTH; i=i+1) mc_CMod[i*8+:8] = {mc_C[i*8+:7], mc_C7[i]};
   for (i = 0; i < CKEBITS*PING_PONG_PHY; i=i+1) mc_CKEMod[i*8+:8] =  {mc_CKE[i*8+:7], mc_CKE7[i]};
   for (i = 0; i < CSBITS*PING_PONG_PHY; i=i+1) mc_CS_nMod[i*8+:8] =  {mc_CS_n[i*8+:7], mc_CS_n7[i]};
   for (i = 0; i < ODTBITS*PING_PONG_PHY; i=i+1) mc_ODTMod[i*8+:8] =  {mc_ODT[i*8+:7], mc_ODT7[i]};
end

always @(posedge clk) begin
   mc_ACT_n7 <= #TCQ mc_ACT_n[7];
   mc_CAS_n7 <= #TCQ mc_CAS_n[7];
   mc_RAS_n7 <= #TCQ mc_RAS_n[7];
   mc_WE_n7 <= #TCQ mc_WE_n[7];
   for (i = 0; i < ABITS; i=i+1) mc_ADR7[i] <= #TCQ mc_ADR[i*8+7];
   for (i = 0; i < BABITS; i=i+1) mc_BA7[i] <= #TCQ mc_BA[i*8+7];
   for (i = 0; i < BGBITS; i=i+1) mc_BG7[i] <= #TCQ mc_BG[i*8+7];
   for (i = 0; i < LR_WIDTH; i=i+1) mc_C7[i] <= #TCQ mc_C[i*8+7];
   for (i = 0; i < CKEBITS*PING_PONG_PHY; i=i+1) mc_CKE7[i] <= #TCQ mc_CKE[i*8+7];
   for (i = 0; i < CSBITS*PING_PONG_PHY; i=i+1) mc_CS_n7[i] <= #TCQ mc_CS_n[i*8+7];
   for (i = 0; i < ODTBITS*PING_PONG_PHY; i=i+1) mc_ODT7[i] <= #TCQ mc_ODT[i*8+7];
end

always @(*) if (calDone) begin
   mcalCasSlot = mcCasSlot;
   mcalRdCAS = mcRdCAS;
   mcalWrCAS = mcWrCAS;
   mcalRank = winRank;
end else begin
   mcalCasSlot = {calCasSlot, calCasSlot};
   mcalRdCAS = {calRdCAS, calRdCAS};
   mcalWrCAS = {calWrCAS, calWrCAS};
   mcalRank = {calRank, calRank};
end

// Flop fifo_rden before routing to XiPhy
wire  [DBYTES*13-1:0]     mcal_clb2phy_fifo_rden_nxt =     mc_clb2phy_fifo_rden_nxt | cal_clb2phy_fifo_rden;
wire  [DBYTES*13-1:0] ch1_mcal_clb2phy_fifo_rden_nxt = ch1_mc_clb2phy_fifo_rden_nxt | cal_clb2phy_fifo_rden;
always @(posedge clk) begin
       mcal_clb2phy_fifo_rden <= #TCQ     mcal_clb2phy_fifo_rden_nxt;
      ch1_mcal_clb2phy_fifo_rden <= #TCQ ch1_mcal_clb2phy_fifo_rden_nxt;
end

// Delay parity result by 1 cycle according to JEDEC SSTE32882 Spec   
reg mc_PARMod_int7;
reg mc_PARMod_int6;
reg mc_PARMod_int5;
reg cal_PAR_int7;
reg cal_PAR_int6;
reg cal_PAR_int5;
reg [7:0]        mc_PARMod_int;
reg [7:0]        cal_PAR_int;
reg [ABITS-1:0]  cal_par_ADR[7:0];
reg [BABITS-1:0] cal_par_BA[7:0];
reg [BGBITS-1:0] cal_par_BG[7:0];
reg              cal_par_ACT[7:0];
reg [LR_WIDTH-1:0] cal_par_C[7:0];
reg [ABITS-1:0]  mc_par_ADR[7:0];
reg [BABITS-1:0] mc_par_BA[7:0];
reg [BGBITS-1:0] mc_par_BG[7:0];
reg              mc_par_ACT[7:0];
reg [LR_WIDTH-1:0] mc_par_C[7:0];

   
generate
   always@(*) begin
      for (i=0; i<8; i=i+1) begin
	 for (j=0; j<ABITS; j=j+1) begin
	    mc_par_ADR[i][j]  = mc_ADRMod[j*8+i];
	    cal_par_ADR[i][j] = cal_ADR[j*8+i];
	 end
	 for (j=0; j<BABITS; j=j+1) begin
	    mc_par_BA[i][j]  = mc_BAMod[j*8+i];
	    cal_par_BA[i][j] = cal_BA[j*8+i];
	 end	 
	 for (j=0; j<BGBITS; j=j+1) begin
	    mc_par_BG[i][j]  = mc_BGMod[j*8+i];
	    cal_par_BG[i][j] = cal_BG[j*8+i];
	 end	 
         mc_par_ACT[i] = mc_ACT_nMod[i];
	 cal_par_ACT[i] = cal_ACT_n[i];
	 if (MEM == "DDR4" & S_HEIGHT > 1) begin
            for (j=0; j<LR_WIDTH; j=j+1) begin
               mc_par_C[i][j] = mc_CMod[j*8+i];
               cal_par_C[i][j] = cal_C[j*8+i];
            end
	    cal_PAR_int[i]    = (^cal_par_ADR[i])^(^cal_par_BA[i])^(^cal_par_BG[i])^(^cal_par_C[i])^cal_par_ACT[i];
	    mc_PARMod_int[i]  = (^ mc_par_ADR[i])^(^ mc_par_BA[i])^(^ mc_par_BG[i])^(^ mc_par_C[i])^ mc_par_ACT[i];
	 end
	 else if (MEM == "DDR4") begin
	    cal_PAR_int[i]    = (^cal_par_ADR[i])^(^cal_par_BA[i])^(^cal_par_BG[i])^cal_par_ACT[i];
	    mc_PARMod_int[i]  = (^ mc_par_ADR[i])^(^ mc_par_BA[i])^(^ mc_par_BG[i])^ mc_par_ACT[i];
	 end
	 else begin
	    cal_PAR_int[i]    = (^cal_par_ADR[i])^(^cal_par_BA[i])^cal_CAS_n[i]   ^cal_RAS_n[i]   ^cal_WE_n[i];
	    mc_PARMod_int[i]  = (^ mc_par_ADR[i])^(^ mc_par_BA[i])^ mc_CAS_nMod[i]^ mc_RAS_nMod[i]^ mc_WE_nMod[i];
	 end
      end
   end
endgenerate
   
always @(posedge clk) if (rst_r1) begin
   mc_PARMod_int7 <= #TCQ 'h0;
   mc_PARMod_int6 <= #TCQ 'h0;
   mc_PARMod_int5 <= #TCQ 'h0;
   cal_PAR_int7   <= #TCQ 'h0;
   cal_PAR_int6   <= #TCQ 'h0;
   cal_PAR_int5   <= #TCQ 'h0;
end else begin
   mc_PARMod_int7 <= #TCQ mc_PARMod_int[7];
   mc_PARMod_int6 <= #TCQ mc_PARMod_int[6];
   mc_PARMod_int5 <= #TCQ mc_PARMod_int[5];
   cal_PAR_int7   <= #TCQ cal_PAR_int[7];
   cal_PAR_int6   <= #TCQ cal_PAR_int[6];
   cal_PAR_int5   <= #TCQ cal_PAR_int[5];
end

// Flop command from MC or Cal into first stage of command delay shift register
reg  [PING_PONG_PHY*CKEBITS*8-1:0] ppp_cal_CKE;
reg   [PING_PONG_PHY*CSBITS*8-1:0] ppp_cal_CS_n;
reg  [PING_PONG_PHY*ODTBITS*8-1:0] ppp_cal_ODT;

generate
   always@(*) begin
      for (i=0; i<PING_PONG_PHY; i=i+1) begin
	 ppp_cal_CKE[i*CKEBITS*8+:CKEBITS*8] = {cal_CKE, cal_CKE};
	 ppp_cal_ODT[i*ODTBITS*8+:ODTBITS*8] = {cal_ODT, cal_ODT};
      end
      if (EN_PP_4R_MIR == 1) begin
        ppp_cal_CS_n = cal_CS_n;      
      end else begin
        for (i=0; i<PING_PONG_PHY; i=i+1) begin
          ppp_cal_CS_n[i*CSBITS*8+:CSBITS*8]  = {cal_CS_n, cal_CS_n};      
        end
      end
   end
endgenerate

always @(posedge clk) if (calDone) begin
   mcal_ACT_n_dly[0] <= #TCQ mc_ACT_nMod;
   mcal_WE_n_dly[0]  <= #TCQ mc_WE_nMod;
   mcal_CAS_n_dly[0] <= #TCQ mc_CAS_nMod;
   mcal_RAS_n_dly[0] <= #TCQ mc_RAS_nMod;
   if (REG_CTRL == "OFF")
     mcal_PAR_dly[0] <= #TCQ mc_PARMod_int;
   else
     mcal_PAR_dly[0] <= #TCQ {mc_PARMod_int[5:0], mc_PARMod_int7, mc_PARMod_int6};
   for (i = 0; i < ABITS; i=i+1) mcal_ADR_dly[0][i*8+:8]   <= #TCQ mc_ADRMod[i*8+:8];
   for (i = 0; i < BABITS; i=i+1) mcal_BA_dly[0][i*8+:8]   <= #TCQ mc_BAMod[i*8+:8];
   for (i = 0; i < BGBITS; i=i+1) mcal_BG_dly[0][i*8+:8]   <= #TCQ mc_BGMod[i*8+:8];
   for (i = 0; i < LR_WIDTH; i=i+1) mcal_C_dly[0][i*8+:8]  <= #TCQ mc_CMod[i*8+:8];
   for (i = 0; i < CKEBITS*PING_PONG_PHY; i=i+1) mcal_CKE_dly[0][i*8+:8] <= #TCQ mc_CKEMod[i*8+:8];
   for (i = 0; i < CSBITS*PING_PONG_PHY; i=i+1) mcal_CS_n_dly[0][i*8+:8] <= #TCQ mc_CS_nMod[i*8+:8];
   for (i = 0; i < ODTBITS*PING_PONG_PHY; i=i+1) mcal_ODT_dly[0][i*8+:8] <= #TCQ mc_ODTMod[i*8+:8];
end else begin
   mcal_ACT_n_dly[0] <= #TCQ cal_ACT_n;
   mcal_CAS_n_dly[0] <= #TCQ cal_CAS_n;
   mcal_RAS_n_dly[0] <= #TCQ cal_RAS_n;
   mcal_WE_n_dly[0]  <= #TCQ cal_WE_n;
   if (REG_CTRL == "OFF")
     mcal_PAR_dly[0]   <= #TCQ cal_PAR_int;
   else
     mcal_PAR_dly[0]   <= #TCQ {cal_PAR_int[5:0], cal_PAR_int7, cal_PAR_int6};
   for (i = 0; i < ABITS; i=i+1) mcal_ADR_dly[0][i*8+:8]   <= #TCQ cal_ADR[i*8+:8];
   for (i = 0; i < BABITS; i=i+1) mcal_BA_dly[0][i*8+:8]   <= #TCQ cal_BA[i*8+:8];
   for (i = 0; i < BGBITS; i=i+1) mcal_BG_dly[0][i*8+:8]   <= #TCQ cal_BG[i*8+:8];
   for (i = 0; i < LR_WIDTH; i=i+1) mcal_C_dly[0][i*8+:8]  <= #TCQ cal_C[i*8+:8];
   for (i = 0; i < CKEBITS*PING_PONG_PHY; i=i+1) mcal_CKE_dly[0][i*8+:8] <= #TCQ ppp_cal_CKE[i*8+:8];
   for (i = 0; i < CSBITS*PING_PONG_PHY; i=i+1) mcal_CS_n_dly[0][i*8+:8] <= #TCQ ppp_cal_CS_n[i*8+:8];
   for (i = 0; i < ODTBITS*PING_PONG_PHY; i=i+1) mcal_ODT_dly[0][i*8+:8] <= #TCQ ppp_cal_ODT[i*8+:8];
end

always @(posedge clk)
begin
  if (rst_r1) begin
    mcal_CK_t   <= #TCQ (SELF_REFRESH == 1) ? {CKBITS{8'b0}} : {CKBITS{8'b01010101}};
    mcal_CK_c   <= #TCQ (SELF_REFRESH == 1) ? {CKBITS{8'b0}} : {CKBITS{8'b10101010}};
  end else if (calDone) begin
    mcal_CK_t   <= #TCQ {CKBITS{mcCKt}};
    mcal_CK_c   <= #TCQ {CKBITS{mcCKc}};
  end else if (bisc_complete) begin
    mcal_CK_t   <= #TCQ {CKBITS{8'b01010101}};//{CKBITS{8'b01010101}};
    mcal_CK_c   <= #TCQ {CKBITS{8'b10101010}};//{CKBITS{8'b10101010}};
  end
end

// Shift command into additional delay stages if they exist
generate
if (EXTRA_CMD_DELAY > 0) begin
  always @(posedge clk) begin
     for (i = 0; i < EXTRA_CMD_DELAY; i=i+1) begin
       if (rst_r1) begin
         mcal_CKE_dly[i+1]    <= #TCQ {CKEBITS*PING_PONG_PHY{8'b0}};
       end else begin
         mcal_PAR_dly[i+1]    <= #TCQ mcal_PAR_dly[i];
         mcal_ACT_n_dly[i+1]  <= #TCQ mcal_ACT_n_dly[i];
         mcal_CAS_n_dly[i+1]  <= #TCQ mcal_CAS_n_dly[i];
         mcal_RAS_n_dly[i+1]  <= #TCQ mcal_RAS_n_dly[i];
         mcal_WE_n_dly[i+1]   <= #TCQ mcal_WE_n_dly[i];
         mcal_ADR_dly[i+1]    <= #TCQ mcal_ADR_dly[i];
         mcal_BA_dly[i+1]     <= #TCQ mcal_BA_dly[i];
         mcal_BG_dly[i+1]     <= #TCQ mcal_BG_dly[i];
         mcal_C_dly[i+1]      <= #TCQ mcal_C_dly[i];
         mcal_CKE_dly[i+1]    <= #TCQ mcal_CKE_dly[i];
         mcal_CS_n_dly[i+1]   <= #TCQ mcal_CS_n_dly[i];
         mcal_ODT_dly[i+1]    <= #TCQ mcal_ODT_dly[i];
       end
    end //(for)
  end //(always)
end //(if)
endgenerate

// Select the last command delay shift register stage for module output
assign mcal_PAR    = mcal_PAR_dly[EXTRA_CMD_DELAY];
assign mcal_ACT_n  = mcal_ACT_n_dly[EXTRA_CMD_DELAY];
assign mcal_CAS_n  = mcal_CAS_n_dly[EXTRA_CMD_DELAY];
assign mcal_RAS_n  = mcal_RAS_n_dly[EXTRA_CMD_DELAY];
assign mcal_WE_n   = mcal_WE_n_dly[EXTRA_CMD_DELAY];
assign mcal_ADR    = mcal_ADR_dly[EXTRA_CMD_DELAY];
assign mcal_BA     = mcal_BA_dly[EXTRA_CMD_DELAY];
assign mcal_BG     = mcal_BG_dly[EXTRA_CMD_DELAY];
generate
  if (S_HEIGHT > 1)
    assign mcal_C      = mcal_C_dly[EXTRA_CMD_DELAY];
  else
    assign mcal_C      = '0;
endgenerate
assign mcal_CKE    = mcal_CKE_dly[EXTRA_CMD_DELAY];
assign mcal_CS_n   = mcal_CS_n_dly[EXTRA_CMD_DELAY];
assign mcal_ODT    = mcal_ODT_dly[EXTRA_CMD_DELAY];


always @(posedge clk) begin
 if (rst_r1)
   cal_RESET_n <= #TCQ {8{SELF_REFRESH}};
 else
   cal_RESET_n <= #TCQ cal_RESET_n_int;
end

wire        cal_warning;
wire [8:0]  cal_warning_nibble;
wire [8:0]  cal_warning_code;


reg io_addr_strobe;
reg io_addr_strobe_lvl_r1;
reg io_addr_strobe_lvl_r2;
// IO Address Strobe Level to Pulse conversion
  always @(posedge clk) begin
    io_addr_strobe_lvl_r1  <= #TCQ io_addr_strobe_lvl;
    io_addr_strobe_lvl_r2  <= #TCQ io_addr_strobe_lvl_r1;
    io_addr_strobe  <= #TCQ io_addr_strobe_lvl_r1 ^ io_addr_strobe_lvl_r2;
  end

ddr4_v2_2_10_cal #
(
    .ABITS              (ABITS)
   ,.BABITS             (BABITS)
   ,.BGBITS             (BGBITS)
   ,.CKEBITS            (CKEBITS)
   ,.CKBITS             (CKBITS)
   ,.CSBITS             (EN_PP_4R_MIR_WID*CSBITS)
   ,.S_HEIGHT           (S_HEIGHT)
   ,.LR_WIDTH           (LR_WIDTH)
   ,.ODTBITS            (ODTBITS)
   ,.ODTWR              (ODTWR)
   ,.ODTWRDEL           (ODTWRDEL)
   ,.ODTWRDUR           (ODTWRDUR)
   ,.ODTWRODEL          (ODTWRODEL)
   ,.ODTWRODUR          (ODTWRODUR)
   ,.ODTRD              (ODTRD)
   ,.ODTRDDEL           (ODTRDDEL)
   ,.ODTRDDUR           (ODTRDDUR)
   ,.ODTRDODEL          (ODTRDODEL)
   ,.ODTRDODUR          (ODTRDODUR)
   ,.ODTNOP             (ODTNOP)
   ,.MEM                (MEM)
   ,.DQ_WIDTH           (DQ_WIDTH)
   ,.DBYTES             (DBYTES)
   ,.SAVE_RESTORE       (SAVE_RESTORE)
   ,.SELF_REFRESH       (SELF_REFRESH)
   ,.RESTORE_CRC        (RESTORE_CRC)
   ,.EN_PP_4R_MIR       (EN_PP_4R_MIR)

   ,.MEMORY_CONFIGURATION (MEMORY_CONFIGURATION)
   ,.DRAM_WIDTH         (DRAM_WIDTH)
   ,.RANKS              (RANKS)
   ,.RNK_BITS           (RNK_BITS)
   ,.nCK_PER_CLK        (nCK_PER_CLK)
   ,.RTL_VERSION        (RTL_VERSION)
   ,.MEM_CODE           (MEM_CODE)
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
   ,.CAL_RD_VREF_PATTERN(CAL_RD_VREF_PATTERN)
   ,.CAL_WR_VREF        (CAL_WR_VREF)
   ,.CAL_WR_VREF_PATTERN(CAL_WR_VREF_PATTERN)
   ,.CAL_DQS_TRACKING   (CAL_DQS_TRACKING)
   ,.CAL_JITTER         (CAL_JITTER)
   ,.CLK_2TO1           (CLK_2TO1)
   ,.tCK                (tCK)
   ,.t200us             (t200us)
   ,.t500us             (t500us)
   ,.tXPR               (tXPR)
   ,.tMOD               (tMOD)
   ,.tMRD               (tMRD)
   ,.tZQINIT            (tZQINIT)
   ,.tRFC               (tRFC)
   ,.MR0                (MR0)
   ,.MR1                (MR1)
   ,.MR2                (MR2)
   ,.MR3                (MR3)
   ,.MR4                (MR4)
   ,.MR5                (MR5)
   ,.MR6                (MR6)
   ,.RD_VREF_VAL        (RD_VREF_VAL)
   ,.SLOT0_CONFIG       (SLOT0_CONFIG)
   ,.SLOT1_CONFIG       (SLOT1_CONFIG)     
   ,.SLOT0_FUNC_CS      (SLOT0_FUNC_CS)
   ,.SLOT1_FUNC_CS      (SLOT1_FUNC_CS)
   ,.SLOT0_ODD_CS       (SLOT0_ODD_CS)
   ,.SLOT1_ODD_CS       (SLOT1_ODD_CS)
   ,.REG_CTRL           (REG_CTRL)
   ,.LRDIMM_MODE        (LRDIMM_MODE)
   ,.DDR4_DB_HIF_RTT_NOM  (DDR4_DB_HIF_RTT_NOM)
   ,.DDR4_DB_HIF_RTT_WR   (DDR4_DB_HIF_RTT_WR)
   ,.DDR4_DB_HIF_RTT_PARK (DDR4_DB_HIF_RTT_PARK)
   ,.DDR4_DB_HIF_DI       (DDR4_DB_HIF_DI)
   ,.DDR4_DB_DIF_ODT      (DDR4_DB_DIF_ODT)
   ,.DDR4_DB_DIF_DI       (DDR4_DB_DIF_DI)
   ,.DDR4_DB_HIF_VREF     (DDR4_DB_HIF_VREF)
   ,.DDR4_DB_DIF_VREF     (DDR4_DB_DIF_VREF)
   ,.DDR4_CLAMSHELL     (DDR4_CLAMSHELL)
   ,.CA_MIRROR          (CA_MIRROR)
   ,.DDR4_REG_PARITY_ENABLE (DDR4_REG_PARITY_ENABLE)
   ,.DDR4_REG_RC03      (DDR4_REG_RC03)
   ,.DDR4_REG_RC04      (DDR4_REG_RC04)		   
   ,.DDR4_REG_RC05      (DDR4_REG_RC05)
   ,.DDR4_REG_RC3X      (DDR4_REG_RC3X)
   ,.EXTRA_CMD_DELAY    (EXTRA_CMD_DELAY)
   ,.WL                 (WL)
   ,.RL                 (RL)
   ,.PL                 (PL)
   ,.NIBBLE_CNT_WIDTH   (NIBBLE_CNT_WIDTH)
   ,.CPLX_PAT_LENGTH    (CPLX_PAT_LENGTH)
   ,.DM_DBI             (DM_DBI)
   ,.USE_CS_PORT        (USE_CS_PORT)
   ,.MEMORY_VOLTAGE     (MEMORY_VOLTAGE)
   ,.CLKFBOUT_MULT_PLL  (CLKFBOUT_MULT_PLL)
   ,.DIVCLK_DIVIDE_PLL  (DIVCLK_DIVIDE_PLL)
   ,.CLKOUT0_DIVIDE_PLL (CLKOUT0_DIVIDE_PLL)
   ,.CLKFBOUT_MULT_MMCM (CLKFBOUT_MULT_MMCM)
   ,.DIVCLK_DIVIDE_MMCM (DIVCLK_DIVIDE_MMCM)
   ,.CLKOUT0_DIVIDE_MMCM(CLKOUT0_DIVIDE_MMCM)
   ,.C_FAMILY           (C_FAMILY)
   ,.BISC_EN		(BISC_EN)

   ,.MIGRATION          (MIGRATION)
   ,.CK_SKEW            (CK_SKEW)
   ,.ADDR_SKEW          (ADDR_SKEW)
   ,.ACT_SKEW           (ACT_SKEW)
   ,.CKE_SKEW           (CKE_SKEW)
   ,.BA_SKEW            (BA_SKEW)
   ,.BG_SKEW            (BG_SKEW)
   ,.CS_SKEW            (CS_SKEW)
   ,.ODT_SKEW           (ODT_SKEW)
   ,.C_SKEW             (C_SKEW)
   ,.PAR_SKEW           (PAR_SKEW)

) u_ddr_cal (
    .clk (clk)
   ,.rst (rst)

   ,.pllGate                (pllGate)
   ,.riu2clb_valid          (riu2clb_valid)
   ,.phy2clb_rd_dq_bits     (phy2clb_rd_dq_bits)
   ,.io_address             (io_address)
   ,.io_addr_strobe         (io_addr_strobe)
   ,.io_write_data          (io_write_data)
   ,.io_write_strobe        (io_write_strobe)
   ,.io_read_data           (io_read_data)
   ,.io_ready_lvl               (io_ready_lvl)
   ,.bisc_complete          (bisc_complete)
   ,.bisc_byte		    (bisc_byte)
   ,.phy_ready              (phy_ready)
   ,.en_vtc                 (en_vtc)
   ,.clb2phy_fifo_rden      (cal_clb2phy_fifo_rden)
   ,.clb2phy_wrcs0_upp      (cal_clb2phy_wrcs0_upp)
   ,.clb2phy_wrcs1_upp      (cal_clb2phy_wrcs1_upp)
   ,.clb2phy_wrcs0_low      (cal_clb2phy_wrcs0_low)
   ,.clb2phy_wrcs1_low      (cal_clb2phy_wrcs1_low)
   ,.clb2phy_rdcs0_upp      (cal_clb2phy_rdcs0_upp)
   ,.clb2phy_rdcs1_upp      (cal_clb2phy_rdcs1_upp)
   ,.clb2phy_rdcs0_low      (cal_clb2phy_rdcs0_low)
   ,.clb2phy_rdcs1_low      (cal_clb2phy_rdcs1_low)
   
   ,.rd_vref_value          (mcal_rd_vref_value)

   ,.calDone                (calDone)
   ,.cal_CAS_n              (cal_CAS_n)
   ,.cal_RAS_n              (cal_RAS_n)
   ,.cal_WE_n               (cal_WE_n)
   ,.cal_ACT_n              (cal_ACT_n)
   ,.cal_ADR                (cal_ADR)
   ,.cal_BA                 (cal_BA)
   ,.cal_BG                 (cal_BG)
   ,.cal_C                  (cal_C)
   ,.cal_CKE                (cal_CKE[CKEBITS*8-1:0])
   ,.cal_CS_n               (cal_CS_n)
   ,.cal_DMOut_n            (cal_DMOut_n)
   ,.cal_DQOut              (cal_DQOut)
   ,.cal_ODT                (cal_ODT[ODTBITS*8-1:0])
   ,.cal_PAR                (cal_PAR)
   ,.cal_RESET_n            (cal_RESET_n_int)

   ,.mcal_DQIn                (cal_mcal_DQIn) //mcal_DQIn
   ,.mcal_DMIn_n              (cal_mcal_DMIn_n) //mcal_DMIn_n
   ,.mc_clb2phy_fifo_rden_nxt (mc_clb2phy_fifo_rden_nxt_r) //mc_clb2phy_fifo_rden_nxt[0]

   ,.lowCL0                 (lowCL0)
   ,.lowCL1                 (lowCL1)
   ,.lowCL2                 (lowCL2)
   ,.lowCL3                 (lowCL3)
   ,.uppCL0                 (uppCL0)
   ,.uppCL1                 (uppCL1)
   ,.uppCL2                 (uppCL2)
   ,.uppCL3                 (uppCL3)
   ,.max_rd_lat             (max_rd_lat)

   ,.cal_dbi_wr             (cal_dbi_wr)
   ,.cal_dbi_rd             (cal_dbi_rd)
   ,.calCasSlot             (calCasSlot)
   ,.calRank                (calRank)
   ,.calRdCAS               (calRdCAS)
   ,.cal_clear_fifo_rden    (cal_clear_fifo_rden)
   ,.calWrCAS               (calWrCAS)

   ,.wrDataEn               (|wrDataEn_pi)

   ,.cal_oe_dis_low         (cal_oe_dis_low)
   ,.cal_oe_dis_upp         (cal_oe_dis_upp)
   
   ,.traffic_wr_done              (traffic_wr_done)
   ,.traffic_status_err_bit_valid (traffic_status_err_bit_valid)
   ,.traffic_status_err_type_valid(traffic_status_err_type_valid)
   ,.traffic_status_err_type      (traffic_status_err_type)
   ,.traffic_status_done          (traffic_status_done)
   ,.traffic_status_watch_dog_hang(traffic_status_watch_dog_hang)
   ,.traffic_error                (traffic_error_sw)
   ,.traffic_clr_error            (traffic_clr_error)
   ,.traffic_start                (traffic_start)
   ,.traffic_rst                  (traffic_rst)
   ,.traffic_err_chk_en           (traffic_err_chk_en)
   ,.traffic_instr_addr_mode      (traffic_instr_addr_mode)
   ,.traffic_instr_data_mode      (traffic_instr_data_mode)
   ,.traffic_instr_rw_mode        (traffic_instr_rw_mode)
   ,.traffic_instr_rw_submode     (traffic_instr_rw_submode)
   ,.traffic_instr_num_of_iter    (traffic_instr_num_of_iter)
   ,.traffic_instr_nxt_instr      (traffic_instr_nxt_instr)
   
   ,.win_start              (win_start)
   ,.gt_data_ready          (gt_data_ready)

   ,.cal_pre_status         (cal_pre_status)
   ,.cal_r0_status          (cal_r0_status)
   ,.cal_r1_status          (cal_r1_status)
   ,.cal_r2_status          (cal_r2_status)
   ,.cal_r3_status          (cal_r3_status)
   ,.cal_post_status        (cal_post_status)
   ,.cal_error              (cal_error)
   ,.cal_error_bit          (cal_error_bit)
   ,.cal_error_nibble       (cal_error_nibble)
   ,.cal_error_code         (cal_error_code)
   ,.cal_warning            (cal_warning)
   ,.cal_warning_nibble     (cal_warning_nibble)
   ,.cal_warning_code       (cal_warning_code)
   ,.cal_crc_error          (cal_crc_error)

   ,.sl_iport0              (sl_iport0)
   ,.sl_oport0              (sl_oport0)
   ,.dbg_cal_seq            (dbg_cal_seq)
   ,.dbg_cal_seq_cnt        (dbg_cal_seq_cnt)
   ,.dbg_cal_seq_rd_cnt     (dbg_cal_seq_rd_cnt)
   ,.dbg_rd_valid           (dbg_rd_valid)
   ,.dbg_cmp_byte           (dbg_cmp_byte)
   ,.dbg_rd_data            (dbg_rd_data)
   ,.dbg_rd_data_cmp        (dbg_rd_data_cmp) 
   ,.dbg_expected_data      (dbg_expected_data)
   ,.dbg_cplx_config        (dbg_cplx_config)
   ,.dbg_cplx_status        (dbg_cplx_status)
   ,.win_status             (win_status)

   // Self-Refresh and Save/Restore
   ,.stop_gate_tracking_req (stop_gate_tracking_req)
   ,.stop_gate_tracking_ack (stop_gate_tracking_ack_lcl)
   ,.app_mem_init_skip      (app_mem_init_skip)
   ,.app_restore_en         (app_restore_en)
   ,.app_restore_complete   (app_restore_complete)
   ,.usr_xsdb_select        (xsdb_select)
   ,.usr_xsdb_rd_en         (xsdb_rd_en)
   ,.usr_xsdb_wr_en         (xsdb_wr_en)
   ,.usr_xsdb_addr          (xsdb_addr)
   ,.usr_xsdb_wr_data       (xsdb_wr_data)
   ,.usr_xsdb_rd_data       (xsdb_rd_data)
   ,.usr_xsdb_rdy           (xsdb_rdy)
);
assign stop_gate_tracking_ack = (BYPASS_CAL=="TRUE") ? stop_gate_tracking_req : stop_gate_tracking_ack_lcl;

function wrDBI;
   input [7:0] d;
casez (d)
   8'b00000000: wrDBI = 0;
   8'b00000001: wrDBI = 0;
   8'b00000010: wrDBI = 0;
   8'b00000011: wrDBI = 0;
   8'b00000100: wrDBI = 0;
   8'b00000101: wrDBI = 0;
   8'b00000110: wrDBI = 0;
   8'b00000111: wrDBI = 0;
   8'b00001000: wrDBI = 0;
   8'b00001001: wrDBI = 0;
   8'b00001010: wrDBI = 0;
   8'b00001011: wrDBI = 0;
   8'b00001100: wrDBI = 0;
   8'b00001101: wrDBI = 0;
   8'b00001110: wrDBI = 0;
   8'b00001111: wrDBI = 1;
   8'b00010000: wrDBI = 0;
   8'b00010001: wrDBI = 0;
   8'b00010010: wrDBI = 0;
   8'b00010011: wrDBI = 0;
   8'b00010100: wrDBI = 0;
   8'b00010101: wrDBI = 0;
   8'b00010110: wrDBI = 0;
   8'b00010111: wrDBI = 1;
   8'b00011000: wrDBI = 0;
   8'b00011001: wrDBI = 0;
   8'b00011010: wrDBI = 0;
   8'b00011011: wrDBI = 1;
   8'b00011100: wrDBI = 0;
   8'b00011101: wrDBI = 1;
   8'b00011110: wrDBI = 1;
   8'b00011111: wrDBI = 1;
   8'b00100000: wrDBI = 0;
   8'b00100001: wrDBI = 0;
   8'b00100010: wrDBI = 0;
   8'b00100011: wrDBI = 0;
   8'b00100100: wrDBI = 0;
   8'b00100101: wrDBI = 0;
   8'b00100110: wrDBI = 0;
   8'b00100111: wrDBI = 1;
   8'b00101000: wrDBI = 0;
   8'b00101001: wrDBI = 0;
   8'b00101010: wrDBI = 0;
   8'b00101011: wrDBI = 1;
   8'b00101100: wrDBI = 0;
   8'b00101101: wrDBI = 1;
   8'b00101110: wrDBI = 1;
   8'b00101111: wrDBI = 1;
   8'b00110000: wrDBI = 0;
   8'b00110001: wrDBI = 0;
   8'b00110010: wrDBI = 0;
   8'b00110011: wrDBI = 1;
   8'b00110100: wrDBI = 0;
   8'b00110101: wrDBI = 1;
   8'b00110110: wrDBI = 1;
   8'b00110111: wrDBI = 1;
   8'b00111000: wrDBI = 0;
   8'b00111001: wrDBI = 1;
   8'b00111010: wrDBI = 1;
   8'b00111011: wrDBI = 1;
   8'b00111100: wrDBI = 1;
   8'b00111101: wrDBI = 1;
   8'b00111110: wrDBI = 1;
   8'b00111111: wrDBI = 1;
   8'b01000000: wrDBI = 0;
   8'b01000001: wrDBI = 0;
   8'b01000010: wrDBI = 0;
   8'b01000011: wrDBI = 0;
   8'b01000100: wrDBI = 0;
   8'b01000101: wrDBI = 0;
   8'b01000110: wrDBI = 0;
   8'b01000111: wrDBI = 1;
   8'b01001000: wrDBI = 0;
   8'b01001001: wrDBI = 0;
   8'b01001010: wrDBI = 0;
   8'b01001011: wrDBI = 1;
   8'b01001100: wrDBI = 0;
   8'b01001101: wrDBI = 1;
   8'b01001110: wrDBI = 1;
   8'b01001111: wrDBI = 1;
   8'b01010000: wrDBI = 0;
   8'b01010001: wrDBI = 0;
   8'b01010010: wrDBI = 0;
   8'b01010011: wrDBI = 1;
   8'b01010100: wrDBI = 0;
   8'b01010101: wrDBI = 1;
   8'b01010110: wrDBI = 1;
   8'b01010111: wrDBI = 1;
   8'b01011000: wrDBI = 0;
   8'b01011001: wrDBI = 1;
   8'b01011010: wrDBI = 1;
   8'b01011011: wrDBI = 1;
   8'b01011100: wrDBI = 1;
   8'b01011101: wrDBI = 1;
   8'b01011110: wrDBI = 1;
   8'b01011111: wrDBI = 1;
   8'b01100000: wrDBI = 0;
   8'b01100001: wrDBI = 0;
   8'b01100010: wrDBI = 0;
   8'b01100011: wrDBI = 1;
   8'b01100100: wrDBI = 0;
   8'b01100101: wrDBI = 1;
   8'b01100110: wrDBI = 1;
   8'b01100111: wrDBI = 1;
   8'b01101000: wrDBI = 0;
   8'b01101001: wrDBI = 1;
   8'b01101010: wrDBI = 1;
   8'b01101011: wrDBI = 1;
   8'b01101100: wrDBI = 1;
   8'b01101101: wrDBI = 1;
   8'b01101110: wrDBI = 1;
   8'b01101111: wrDBI = 1;
   8'b01110000: wrDBI = 0;
   8'b01110001: wrDBI = 1;
   8'b01110010: wrDBI = 1;
   8'b01110011: wrDBI = 1;
   8'b01110100: wrDBI = 1;
   8'b01110101: wrDBI = 1;
   8'b01110110: wrDBI = 1;
   8'b01110111: wrDBI = 1;
   8'b01111000: wrDBI = 1;
   8'b01111001: wrDBI = 1;
   8'b01111010: wrDBI = 1;
   8'b01111011: wrDBI = 1;
   8'b01111100: wrDBI = 1;
   8'b01111101: wrDBI = 1;
   8'b01111110: wrDBI = 1;
   8'b01111111: wrDBI = 1;
   8'b10000000: wrDBI = 0;
   8'b10000001: wrDBI = 0;
   8'b10000010: wrDBI = 0;
   8'b10000011: wrDBI = 0;
   8'b10000100: wrDBI = 0;
   8'b10000101: wrDBI = 0;
   8'b10000110: wrDBI = 0;
   8'b10000111: wrDBI = 1;
   8'b10001000: wrDBI = 0;
   8'b10001001: wrDBI = 0;
   8'b10001010: wrDBI = 0;
   8'b10001011: wrDBI = 1;
   8'b10001100: wrDBI = 0;
   8'b10001101: wrDBI = 1;
   8'b10001110: wrDBI = 1;
   8'b10001111: wrDBI = 1;
   8'b10010000: wrDBI = 0;
   8'b10010001: wrDBI = 0;
   8'b10010010: wrDBI = 0;
   8'b10010011: wrDBI = 1;
   8'b10010100: wrDBI = 0;
   8'b10010101: wrDBI = 1;
   8'b10010110: wrDBI = 1;
   8'b10010111: wrDBI = 1;
   8'b10011000: wrDBI = 0;
   8'b10011001: wrDBI = 1;
   8'b10011010: wrDBI = 1;
   8'b10011011: wrDBI = 1;
   8'b10011100: wrDBI = 1;
   8'b10011101: wrDBI = 1;
   8'b10011110: wrDBI = 1;
   8'b10011111: wrDBI = 1;
   8'b10100000: wrDBI = 0;
   8'b10100001: wrDBI = 0;
   8'b10100010: wrDBI = 0;
   8'b10100011: wrDBI = 1;
   8'b10100100: wrDBI = 0;
   8'b10100101: wrDBI = 1;
   8'b10100110: wrDBI = 1;
   8'b10100111: wrDBI = 1;
   8'b10101000: wrDBI = 0;
   8'b10101001: wrDBI = 1;
   8'b10101010: wrDBI = 1;
   8'b10101011: wrDBI = 1;
   8'b10101100: wrDBI = 1;
   8'b10101101: wrDBI = 1;
   8'b10101110: wrDBI = 1;
   8'b10101111: wrDBI = 1;
   8'b10110000: wrDBI = 0;
   8'b10110001: wrDBI = 1;
   8'b10110010: wrDBI = 1;
   8'b10110011: wrDBI = 1;
   8'b10110100: wrDBI = 1;
   8'b10110101: wrDBI = 1;
   8'b10110110: wrDBI = 1;
   8'b10110111: wrDBI = 1;
   8'b10111000: wrDBI = 1;
   8'b10111001: wrDBI = 1;
   8'b10111010: wrDBI = 1;
   8'b10111011: wrDBI = 1;
   8'b10111100: wrDBI = 1;
   8'b10111101: wrDBI = 1;
   8'b10111110: wrDBI = 1;
   8'b10111111: wrDBI = 1;
   8'b11000000: wrDBI = 0;
   8'b11000001: wrDBI = 0;
   8'b11000010: wrDBI = 0;
   8'b11000011: wrDBI = 1;
   8'b11000100: wrDBI = 0;
   8'b11000101: wrDBI = 1;
   8'b11000110: wrDBI = 1;
   8'b11000111: wrDBI = 1;
   8'b11001000: wrDBI = 0;
   8'b11001001: wrDBI = 1;
   8'b11001010: wrDBI = 1;
   8'b11001011: wrDBI = 1;
   8'b11001100: wrDBI = 1;
   8'b11001101: wrDBI = 1;
   8'b11001110: wrDBI = 1;
   8'b11001111: wrDBI = 1;
   8'b11010000: wrDBI = 0;
   8'b11010001: wrDBI = 1;
   8'b11010010: wrDBI = 1;
   8'b11010011: wrDBI = 1;
   8'b11010100: wrDBI = 1;
   8'b11010101: wrDBI = 1;
   8'b11010110: wrDBI = 1;
   8'b11010111: wrDBI = 1;
   8'b11011000: wrDBI = 1;
   8'b11011001: wrDBI = 1;
   8'b11011010: wrDBI = 1;
   8'b11011011: wrDBI = 1;
   8'b11011100: wrDBI = 1;
   8'b11011101: wrDBI = 1;
   8'b11011110: wrDBI = 1;
   8'b11011111: wrDBI = 1;
   8'b11100000: wrDBI = 0;
   8'b11100001: wrDBI = 1;
   8'b11100010: wrDBI = 1;
   8'b11100011: wrDBI = 1;
   8'b11100100: wrDBI = 1;
   8'b11100101: wrDBI = 1;
   8'b11100110: wrDBI = 1;
   8'b11100111: wrDBI = 1;
   8'b11101000: wrDBI = 1;
   8'b11101001: wrDBI = 1;
   8'b11101010: wrDBI = 1;
   8'b11101011: wrDBI = 1;
   8'b11101100: wrDBI = 1;
   8'b11101101: wrDBI = 1;
   8'b11101110: wrDBI = 1;
   8'b11101111: wrDBI = 1;
   8'b11110000: wrDBI = 1;
   8'b11110001: wrDBI = 1;
   8'b11110010: wrDBI = 1;
   8'b11110011: wrDBI = 1;
   8'b11110100: wrDBI = 1;
   8'b11110101: wrDBI = 1;
   8'b11110110: wrDBI = 1;
   8'b11110111: wrDBI = 1;
   8'b11111000: wrDBI = 1;
   8'b11111001: wrDBI = 1;
   8'b11111010: wrDBI = 1;
   8'b11111011: wrDBI = 1;
   8'b11111100: wrDBI = 1;
   8'b11111101: wrDBI = 1;
   8'b11111110: wrDBI = 1;
   8'b11111111: wrDBI = 1;
endcase
endfunction

reg   [DBYTES*8-1:0] calDBIMask;
reg [DBYTES*8*8-1:0] calDQOutDBI;
reg   [DBYTES*8-1:0] DMOut;
reg [DBYTES*8*8-1:0] DQOut;
reg   [DBYTES*8-1:0] wrDBIMask;
reg [DBYTES*8*8-1:0] wrDataDBI;
reg [DBYTES*8*8-1:0] wrDataSW;
reg [DBYTES*8*8-1:0] wrDataDBISW;

always @(*) for (i = 0; i < (DBYTES * 8); i = i + 1)
   calDBIMask[i] = wrDBI(cal_DQOut[i*8+:8]);

always @(*) for (i = 0; i < (DBYTES * 8); i = i + 1)
   calDQOutDBI[i*8+:8] = cal_DQOut[i*8+:8] ^ ~{8{calDBIMask[i]}};

always @(*) for (i = 0; i < (DBYTES * 8); i = i + 1)
   wrDBIMask[i] = wrDBI(wrData[i*8+:8]);

always @(*) for (i = 0; i < (DBYTES * 8); i = i + 1)
   wrDataDBI[i*8+:8] = wrData[i*8+:8] ^ ~{8{wrDBIMask[i]}};

always @(*) for (i = 0; i < DBYTES; i = i + 1)
   wrDataSW[i*64+:64] = swizzle(wrData[i*64+:64]);

always @(*) for (i = 0; i < DBYTES; i = i + 1)
   wrDataDBISW[i*64+:64] = swizzle(wrDataDBI[i*64+:64]);

generate
   case (DM_DBI)
      "DM_NODBI", "DM_DBIRD", "NODM_DBIRD", "NONE", "NODM_NODBI": begin
        always @(*) if (calDone) begin
          DQOut = wrDataSW;
          DMOut = (MEM == "DDR4") ? ~wrDataMask : wrDataMask;
        end else begin
          DQOut = cal_DQOut;
          DMOut = (MEM == "DDR4") ? ~cal_DMOut_n : cal_DMOut_n;
        end
      end
	  "NODM_DBIWR", "NODM_DBIWRRD": begin
        always @(*) if (calDone) begin
          DQOut = (cal_dbi_wr_r[1] == 1'b1) ? wrDataDBISW : wrDataSW;
          DMOut = (cal_dbi_wr_r[1] == 1'b1) ? wrDBIMask : 
                  (MEM == "DDR4") ? ~wrDataMask : wrDataMask;
        end else begin
          DQOut = (cal_dbi_wr_r[1] == 1'b1) ? calDQOutDBI : cal_DQOut;
          DMOut = (cal_dbi_wr_r[1] == 1'b1) ? calDBIMask : 
                   (MEM == "DDR4") ? ~cal_DMOut_n : cal_DMOut_n;
        end
	  end
      default: ;
   endcase
endgenerate

  wire phy_rden_or  = |mcal_clb2phy_rden_upp[3:0];
  wire phy_rden_and = &mcal_clb2phy_rden_upp[3:0];

  reg [11:0] phy_rden_or_stg;
  reg [11:0] phy_rden_and_stg;
    
  always @ (posedge clk) begin
     phy_rden_or_stg <= {phy_rden_or_stg, phy_rden_or};
     phy_rden_and_stg <= {phy_rden_and_stg, phy_rden_and};
  end

  wire [11:0] vio_phy_rden_or_stg = 12'b1111_0000_0111;
  wire [11:0] vio_phy_rden_and_stg = 12'b0000_1111_1000;

  wire [11:0] phy_rden_or_stg_gt = phy_rden_or_stg & ~vio_phy_rden_or_stg;
  wire [11:0] phy_rden_and_stg_gt = phy_rden_and_stg | ~vio_phy_rden_and_stg;

  wire phy_rden_no_rd = ~(|phy_rden_or_stg_gt);
  wire phy_rden_all_rd = &phy_rden_and_stg_gt;

  always @ (posedge clk) begin
    sample_gts <= phy_rden_no_rd | phy_rden_all_rd;
  end

ddr4_v2_2_10_cal_pi # (
    .DBAW             (DBAW)
   ,.DBYTES           (DBYTES)
   ,.DBYTES_PI        (CH0_DBYTES_PI)
   ,.MEM              (MEM)
   ,.DM_DBI           (DM_DBI)
   ,.RL               (RL)
   ,.WL               (WL)
   ,.RANKS            (RANKS)
   ,.RDSTAGES         (RDSTAGES)
   ,.EARLY_WR_DATA    (EARLY_WR_DATA)
   ,.EXTRA_CMD_DELAY  (EXTRA_CMD_DELAY)
   ,.ECC              (ECC)
   ,.TCQ              (TCQ)
)u_ddr_mc_pi(
    .clk     (clk)
   ,.rst     (rst)

   ,.mc_clb2phy_rden_upp  (mcal_clb2phy_rden_upp)
   ,.mc_clb2phy_rden_low  (mcal_clb2phy_rden_low)
   ,.mcal_clb2phy_odt_upp (mcal_clb2phy_odt_upp)
   ,.mcal_clb2phy_odt_low (mcal_clb2phy_odt_low)

   ,.lowCL0     (lowCL0)
   ,.lowCL1     (lowCL1)
   ,.lowCL2     (lowCL2)
   ,.lowCL3     (lowCL3)
   ,.uppCL0     (uppCL0)
   ,.uppCL1     (uppCL1)
   ,.uppCL2     (uppCL2)
   ,.uppCL3     (uppCL3)
   ,.max_rd_lat (max_rd_lat)


   ,.mc_clb2phy_rdcs0_upp (mcal_clb2phy_rdcs0_upp)
   ,.mc_clb2phy_rdcs1_upp (mcal_clb2phy_rdcs1_upp)
   ,.mc_clb2phy_rdcs0_low (mcal_clb2phy_rdcs0_low)
   ,.mc_clb2phy_rdcs1_low (mcal_clb2phy_rdcs1_low)
   ,.mc_clb2phy_wrcs0_upp (mcal_clb2phy_wrcs0_upp)
   ,.mc_clb2phy_wrcs1_upp (mcal_clb2phy_wrcs1_upp)
   ,.mc_clb2phy_wrcs0_low (mcal_clb2phy_wrcs0_low)
   ,.mc_clb2phy_wrcs1_low (mcal_clb2phy_wrcs1_low)
   ,.mc_clb2phy_t_b_upp   (mcal_clb2phy_t_b_upp)
   ,.mc_clb2phy_t_b_low   (mcal_clb2phy_t_b_low)

   ,.mc_clb2phy_fifo_rden_nxt (mc_clb2phy_fifo_rden_nxt)

   ,.rdDataAddr           (rdDataAddr[DBAW-1:0]) 
   ,.rdDataEn             (rdDataEn_pi[0]) 
   ,.rdDataEnd            (rdDataEnd[0]) 
   ,.rdInj                (rdInj[0]) 
   ,.rdRmw                (rdRmw[0]) 
   ,.wrDataEn             (wrDataEn_pi[0]) 
   ,.wrDataAddr           (wrDataAddr[DBAW-1:0]) 

   ,.DQOut                (DQOut)
   ,.DMOut                (DMOut)

   ,.mcal_DMOut_n         (mcal_DMOut_n)
   ,.mcal_DQOut           (mcal_DQOut)
   ,.mcal_DQSOut          (mcal_DQSOut)

   ,.mcal_DMIn_n          (mcal_DMIn_n)

   ,.casSlot              (mcalCasSlot[1:0]) 
   ,.mccasSlot2           (mcCasSlot2[0]) 
   ,.rdCAS                (mcalRdCAS[0]) 
   ,.calrdCAS             (calRdCAS) 
   ,.cal_clear_fifo_rden  (cal_clear_fifo_rden)
   ,.mcrdCAS              (mcRdCAS[0]) 
   ,.winInjTxn            (winInjTxn[0]) 
   ,.winRmw               (winRmw[0]) 
   ,.winBuf               (winBuf[DBAW-1:0]) 
   ,.winRank              (mcalRank[1:0])
   ,.calRank              (calRank) 
   ,.mcwinRank            (winRank[1:0])
   ,.wrCAS                (mcalWrCAS[0]) 
   ,.calwrCAS             (calWrCAS) 
   ,.mcwrCAS              (mcWrCAS[0]) 

   ,.cal_oe_dis_low       (cal_oe_dis_low)
   ,.cal_oe_dis_upp       (cal_oe_dis_upp)
   ,.calDone              (calDone)
);

generate

if (NUM_CHANNELS == 1) begin
  assign                   ch1_mcal_clb2phy_rden_upp    = '0;
  assign                   ch1_mcal_clb2phy_rden_low    = '0;
  assign                   ch1_mcal_clb2phy_odt_upp     = '0;
  assign                   ch1_mcal_clb2phy_odt_low     = '0;
  assign                   ch1_mcal_clb2phy_t_b_upp     = '0;
  assign                   ch1_mcal_clb2phy_t_b_low     = '0;
  assign                   ch1_mcal_clb2phy_wrcs0_upp   = '0;
  assign                   ch1_mcal_clb2phy_wrcs1_upp   = '0;
  assign                   ch1_mcal_clb2phy_wrcs0_low   = '0;
  assign                   ch1_mcal_clb2phy_wrcs1_low   = '0;
  assign                   ch1_mcal_clb2phy_rdcs0_upp   = '0;
  assign                   ch1_mcal_clb2phy_rdcs1_upp   = '0;
  assign                   ch1_mcal_clb2phy_rdcs0_low   = '0;
  assign                   ch1_mcal_clb2phy_rdcs1_low   = '0;
  assign                   ch1_mc_clb2phy_fifo_rden_nxt = '0;
  assign                   ch1_mcal_DMOut_n             = '0;
  assign                   ch1_mcal_DQOut               = '0;
  assign                   ch1_mcal_DQSOut              = '0;


end
else begin

ddr4_v2_2_10_cal_pi # (
   .DBAW             (DBAW)
   ,.DBYTES           (DBYTES)
   ,.DBYTES_PI        (CH1_DBYTES_PI)
   ,.MEM              (MEM)
   ,.DM_DBI           (DM_DBI)
   ,.RL               (RL)
   ,.WL               (WL)
   ,.RANKS            (RANKS)
   ,.RDSTAGES         (RDSTAGES)
   ,.EARLY_WR_DATA    (EARLY_WR_DATA)
   ,.EXTRA_CMD_DELAY  (EXTRA_CMD_DELAY)
   ,.ECC              (ECC)
   ,.TCQ              (TCQ)
)u_ddr_mc_pi_1(
    .clk     (clk)
   ,.rst     (rst)

   ,.mc_clb2phy_rden_upp  (ch1_mcal_clb2phy_rden_upp)
   ,.mc_clb2phy_rden_low  (ch1_mcal_clb2phy_rden_low)
   ,.mcal_clb2phy_odt_upp (ch1_mcal_clb2phy_odt_upp)
   ,.mcal_clb2phy_odt_low (ch1_mcal_clb2phy_odt_low)

   ,.lowCL0     (lowCL0)
   ,.lowCL1     (lowCL1)
   ,.lowCL2     (lowCL2)
   ,.lowCL3     (lowCL3)
   ,.uppCL0     (uppCL0)
   ,.uppCL1     (uppCL1)
   ,.uppCL2     (uppCL2)
   ,.uppCL3     (uppCL3)
   ,.max_rd_lat (max_rd_lat)


   ,.mc_clb2phy_rdcs0_upp (ch1_mcal_clb2phy_rdcs0_upp)
   ,.mc_clb2phy_rdcs1_upp (ch1_mcal_clb2phy_rdcs1_upp)
   ,.mc_clb2phy_rdcs0_low (ch1_mcal_clb2phy_rdcs0_low)
   ,.mc_clb2phy_rdcs1_low (ch1_mcal_clb2phy_rdcs1_low)
   ,.mc_clb2phy_wrcs0_upp (ch1_mcal_clb2phy_wrcs0_upp)
   ,.mc_clb2phy_wrcs1_upp (ch1_mcal_clb2phy_wrcs1_upp)
   ,.mc_clb2phy_wrcs0_low (ch1_mcal_clb2phy_wrcs0_low)
   ,.mc_clb2phy_wrcs1_low (ch1_mcal_clb2phy_wrcs1_low)
   ,.mc_clb2phy_t_b_upp   (ch1_mcal_clb2phy_t_b_upp)
   ,.mc_clb2phy_t_b_low   (ch1_mcal_clb2phy_t_b_low)

   ,.mc_clb2phy_fifo_rden_nxt (ch1_mc_clb2phy_fifo_rden_nxt)

   ,.rdDataAddr           (rdDataAddr[PING_PONG_PHY*DBAW-1:DBAW]) 
   ,.rdDataEn             (rdDataEn_pi[1]) 
   ,.rdDataEnd            (rdDataEnd[1]) 
   ,.rdInj                (rdInj[1]) 
   ,.rdRmw                (rdRmw[1]) 
   ,.wrDataEn             (wrDataEn_pi[1]) 
   ,.wrDataAddr           (wrDataAddr[PING_PONG_PHY*DBAW-1:DBAW]) 

   ,.DQOut                (DQOut)
   ,.DMOut                (DMOut)

   ,.mcal_DMOut_n         (ch1_mcal_DMOut_n)
   ,.mcal_DQOut           (ch1_mcal_DQOut)
   ,.mcal_DQSOut          (ch1_mcal_DQSOut)

   ,.mcal_DMIn_n          (mcal_DMIn_n)

   ,.casSlot              (mcalCasSlot[3:2]) 
   ,.mccasSlot2           (mcCasSlot2[1]) 
   ,.rdCAS                (mcalRdCAS[1]) 
   ,.calrdCAS             (calRdCAS)
   ,.cal_clear_fifo_rden  (cal_clear_fifo_rden)
   ,.mcrdCAS              (mcRdCAS[1]) 
   ,.winInjTxn            (winInjTxn[1]) 
   ,.winRmw               (winRmw[1]) 
   ,.winBuf               (winBuf[PING_PONG_PHY*DBAW-1:DBAW]) 
   ,.winRank              (mcalRank[RNK_BITS+1:RNK_BITS]) 
   ,.calRank              (calRank)
   ,.mcwinRank            (winRank[RNK_BITS+1:RNK_BITS]) 
   ,.wrCAS                (mcalWrCAS[1]) 
   ,.calwrCAS             (calWrCAS)
   ,.mcwrCAS              (mcWrCAS[1]) 

   ,.cal_oe_dis_low       (cal_oe_dis_low)
   ,.cal_oe_dis_upp       (cal_oe_dis_upp)
   ,.calDone              (calDone)
);
end  // if (NUM_CHANNELS == 2)

endgenerate
//synthesis translate_off

// After calibration completes the fifo_rden should never assert if fifo_empty is asserted
/* MAN - removed from original - need to see if can be moved
// Assertions
// =================
wire  [DBYTES*13-1:0] a_illegal_fifo_rden_vec = phy2clb_fifo_empty & mcal_clb2phy_fifo_rden;
wire                  a_illegal_fifo_rden     = ( | a_illegal_fifo_rden_vec ) & calDone;

// After calibration completes gate training the fifo_rden should never assert if fifo_empty is asserted
wire  [DBYTES*13-1:0] a_illegal_fifo_rden_cal_vec = phy2clb_fifo_empty & mcal_clb2phy_fifo_rden;
wire                  a_illegal_fifo_rden_cal     = | a_illegal_fifo_rden_vec;
*/
wire  a_mc_cal_tCWL_ovf = (BYPASS_CAL=="TRUE") ? WL > 63 : WL + 1 > 63;
always @(posedge clk) if (~rst_r1) assert property (~a_mc_cal_tCWL_ovf);

//synthesis translate_on

`include "ddr4_v2_2_10_cal_assert.vh"
//synthesis translate_off 
`ifdef DIS_GT_ASSERT

wire rd_cmd = (mcRdCAS | winInjTxn | winRmw); 
wire rd_done = (rdDataEn | per_rd_done | rmw_rd_done);
localparam PR_RD_INTL = $ceil(1000000.0/(tCK*nCK_PER_CLK)) + (tRFC/4) + 15 ; // Refresh takes higher priority

// one read in every 1us
property rd_cmd_per;
@(posedge clk)
(calDone_gated)##0 $fell(rd_cmd)|-> ##[0:PR_RD_INTL] $rose(rd_cmd); 
endproperty 

property rd_first_cmd; 
@(posedge clk)
$rose(calDone_gated)|->##[0:PR_RD_INTL] $rose(rd_cmd); 
endproperty

// one gt_data_rdy pulse in every 1us
property gt_data_rdy_per;
int x;
@(posedge clk)
(calDone_gated)##0 $fell(gt_data_ready)|-> ##[0:PR_RD_INTL] $rose(gt_data_ready); 
endproperty

property gt_first_pulse; 
@(posedge clk)
$rose(calDone_gated)|->##[0:PR_RD_INTL] $rose(gt_data_ready); 
endproperty

// gt_data_rdy assert 
property gt_data_rdy_tim;
@(posedge clk) 
$rose(gt_data_ready) |-> ($past(gt_data_ready) == 1'b0) 	
endproperty

ASSERT_GT_DATA_READY_PER : assert property (gt_data_rdy_per)
else
	$error("VT_TRACK : gt_data_ready is not asserted periodically");
ASSERT_GT_DATA_READY     : assert property (gt_data_rdy_tim)
else
	$error("VT_TRACK : gt_data_rdy is not asserted for one clock cycle");
ASSERT_RD_CMD_PER	 : assert property (rd_cmd_per)
else
	$error("VT_TRACK : periodic read is not asserted");
ASSERT_RD_CMD		 : assert property (rd_first_cmd)
else
	$error("VT_TRACK : First read command is not assrted in 1us");
ASSERT_GT_FIRST_PULSE	 : assert property (gt_first_pulse)
else
	$error("VT_TRACK : First gt_data_ready is not asserted in 1us ");
`endif
//synthesis translate_on


   
endmodule


