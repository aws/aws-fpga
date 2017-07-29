
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
//  \   \         Application        : DDR4
//  /   /         Filename           : ddr4_core_ddr4.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4_SDRAM
// Purpose          :
//   Top-level  module. This module can be instantiated in the
//   system and interconnect as shown in user design wrapper file 
//   (user top module).
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

(*

  X_MIG_OLYMPUS = 1,  
  X_ULTRASCALE_IO_FLOW = "xilinx.com:ip:ddr4_phy:2.2",
  LIVE_DESIGN = 0,
  MEM_CORE_VER = "xilinx.com:ip:mem:1.4",
  PhyIP_CUSTOM_PART_ATTRIBUTES = "NONE",
  ControllerType = "ddr4_sdram",
  PhyIP_TimePeriod = 937,
  PhyIP_InputClockPeriod = 3332,
  PhyIP_MemoryType = "RDIMMs",
  PhyIP_MemoryPart = "MTA18ASF2G72PZ-2G3",
  PhyIP_PhyClockRatio = "4:1",
  PhyIP_ECC = "true",
  PhyIP_CasLatency = 17,
  PhyIP_CasWriteLatency = 12,
  PhyIP_DataWidth = 72,
  PhyIP_ChipSelect = "true",
  PhyIP_Slot = "Single",
  PhyIP_isCKEShared = "false",
  PhyIP_DataMask = "NONE",
  PhyIP_MemoryVoltage = "1.2V",
  PhyIP_PARTIAL_RECONFIG_FLOW_MIG = "true",
  
  PhyIP_SELF_REFRESH = "true",
  PhyIP_SAVE_RESTORE = "true",
  
  PhyIP_CLKFBOUT_MULT = "8",
  PhyIP_DIVCLK_DIVIDE = "3",
  PhyIP_CLKOUT0_DIVIDE = "3",
  PhyIP_CLKOUT1_DIVIDE = "0",
  PhyIP_CLKOUT2_DIVIDE = "0",
  PhyIP_CLKOUT3_DIVIDE = "0",
  PhyIP_CLKOUT4_DIVIDE = "0",
  PhyIP_VrefVoltage = "0.84",
  PhyIP_StackHeight = "1",
  PhyIP_IS_FROM_PHY = "1",
  PhyIP_CA_MIRROR = "0",

  PhyIP_System_Clock = "Differential",
  PhyIP_Simulation_Mode = "BFM",
  PhyIP_Phy_Only = "Complete_Memory_Controller",
  PhyIP_DEBUG_SIGNAL = "Disable",
  PhyIP_CLKOUTPHY_MODE = "VCO_2X",
  PhyIP_DQ_WIDTH = 72,
  PhyIP_MEM_DEVICE_WIDTH = 72,
  PhyIP_MIN_PERIOD = 833,
  PhyIP_USE_DM_PORT = "NONE",
  PhyIP_USE_CS_PORT = "true",
  PhyIP_ADDR_WIDTH = 17,
  PhyIP_BANK_WIDTH = 2,
  PhyIP_BANK_GROUP_WIDTH = 2,
  PhyIP_CKE_WIDTH = 1,
  PhyIP_CK_WIDTH = 1,
  PhyIP_CS_WIDTH = 1,
  PhyIP_CLAMSHELL = "false",
  PhyIP_RANK_WIDTH = 1,
  PhyIP_tCK = 937,
  PhyIP_HR_MIN_FREQ = 0,
  PhyIP_DCI_CASCADE_CUTOFF = 938,
  PhyIP_IS_FASTER_SPEED_RAM = "No",
  PhyIP_ODT_WIDTH = 1,
  PhyIP_nCS_PER_RANK = 1,
  PhyIP_DATABITS_PER_STROBE = 4,
  PhyIP_DQS_WIDTH = 18,
  PhyIP_DM_WIDTH = 18

*)
module ddr4_core_ddr4 #
  (
    parameter integer ADDR_WIDTH              = 17,
    parameter integer ROW_WIDTH               = 17,
    parameter integer BANK_WIDTH              = 2,
    parameter integer BANK_GROUP_WIDTH        = 2,
    parameter integer S_HEIGHT                = 1,
    parameter integer LR_WIDTH                = 1,
    parameter integer CKE_WIDTH               = 1,
    parameter integer CK_WIDTH                = 1,
    parameter integer COL_WIDTH               = 10,
    parameter integer CS_WIDTH                = 1,
    parameter integer ODT_WIDTH               = 1,
    parameter integer DQ_WIDTH                = 72,
    parameter integer DQS_WIDTH               = 18,
    parameter integer DM_WIDTH                = 9,

    parameter         DRAM_TYPE               = "DDR4",
    parameter         MEM_ADDR_ORDER          = "ROW_COLUMN_BANK_INTLV",

    parameter DM_DBI                          = "NONE",

    parameter         PARTIAL_RECONFIG        = "Enable", // Partial Reconfig enablement
    parameter         USE_CS_PORT             = 1,
    parameter         NUMREF                  = 1,
    parameter         REG_CTRL                = "ON",
    parameter         LRDIMM_MODE             = "OFF", // LRDIMM Mode
    parameter         MCS_ECC_ENABLE       = "FALSE",
    parameter         tCK                     = 937,  // Memory clock period (DDR4 clock cycle)

    parameter         tFAW                    = 16,//In DDR4 clock cycles
    parameter         tRTW                    = 11, // CL + (BL/2) - CWL + 2tCK In DDR4 clock cycles
    parameter         tWTR_L                  = 9, //In DDR4 clock cycles
    parameter         tWTR_S                  = 3, //In DDR4 clock cycles
    parameter         tRFC                    = 374, //In DDR4 clock cycles
//AK     parameter         tREFI                   = 8324, //In DDR4 clock cycles
     parameter         tREFI                   = 4162, //In DDR4 clock cycles
    parameter         ZQINTVL                 = 1067235860, //In DDR4 clock cycles
    parameter         tZQCS                   = 128, //In DDR4 clock cycles
    parameter         tRP                     = 16, //In DDR4 clock cycles
    parameter         tRRD_L                  = 6, //In DDR4 clock cycles
    parameter         tRRD_S                  = 4, //In DDR4 clock cycles
    parameter         tRAS                    = 35, //In DDR4 clock cycles
    parameter         tRCD                    = 16, //In DDR4 clock cycles
    parameter         tRTP                    = 9, //In DDR4 clock cycles

    parameter         tWR                     = 18, //In DDR4 clock cycles
    parameter         PER_RD_INTVL            = 32'd267,
    parameter         ODTWRDEL                = 5'd12,
    parameter         ODTWRDUR                = 4'd6,
    parameter         ODTWRODEL               = 5'd9,
    parameter         ODTWRODUR               = 4'd6,
    parameter         ODTRDDEL                = 5'd17,
    parameter         ODTRDDUR                = 4'd6,
    parameter         ODTRDODEL               = 5'd9,
    parameter         ODTRDODUR               = 4'd6,
    parameter         ODTNOP                  = 16'h0000,

    parameter real    TCQ                     = 100,
    parameter         DRAM_WIDTH              = 4,
    parameter         RANKS                   = 1,
    parameter         ORDERING                = "NORM",
    parameter         RTL_VERSION             = 0,
    parameter         TXN_FIFO_BYPASS         = "ON",
    parameter         TXN_FIFO_PIPE           = "OFF",
    parameter         PER_RD_PERF             = 1'b1,
    parameter         CAS_FIFO_BYPASS         = "ON",
    parameter         ALIAS_PAGE              = "OFF",
    parameter         ALIAS_P_CNT             = "OFF",
    parameter         NOP_ADD_LOW             = 1'b0,
    parameter         STARVATION_EN           = 1'b1,
    parameter         STARVE_COUNT_WIDTH      = 9,
    parameter         EXTRA_CMD_DELAY         = 1,
    parameter         nCK_PER_CLK             = 4,
    parameter         APP_ADDR_WIDTH          = 31,
    parameter         APP_DATA_WIDTH          = 512,
    parameter         APP_MASK_WIDTH          = 64,

    parameter         CLKIN_PERIOD_MMCM        = 3332,
    parameter         CLKFBOUT_MULT_MMCM       = 8,
    parameter         DIVCLK_DIVIDE_MMCM       = 3,
    parameter         CLKOUT0_DIVIDE_MMCM      = 3,
    parameter         CLKOUT1_DIVIDE_MMCM      = 3,
    parameter         CLKOUT2_DIVIDE_MMCM      = 3,
    parameter         CLKOUT3_DIVIDE_MMCM      = 3,
    parameter         CLKOUT4_DIVIDE_MMCM      = 3,
    parameter         CLKOUT6_DIVIDE_MMCM      = 6,
    parameter         CLKOUTPHY_MODE           = "VCO_2X",
    parameter         C_FAMILY                 = "virtexuplus",

    parameter C_S_AXI_ID_WIDTH                = 16,
                                              // Width of all master and slave ID signals.
                                              // # = >= 1.
    parameter C_S_AXI_ADDR_WIDTH              = 34,
                                              // Width of S_AXI_AWADDR, S_AXI_ARADDR, M_AXI_AWADDR and
                                              // M_AXI_ARADDR for all SI/MI slots.
                                              // # = 32.
    parameter C_S_AXI_DATA_WIDTH              = 512,
                                              // Width of WDATA and RDATA on SI slot.
                                              // Must be <= APP_DATA_WIDTH.
                                              // # = 32, 64, 128, 256.
    parameter BURST_MODE                      = "8",     // Burst length
    parameter C_S_AXI_SUPPORTS_NARROW_BURST   = 1,
                                              // Indicates whether to instatiate upsizer
                                              // Range: 0, 1
    parameter C_RD_WR_ARB_ALGORITHM           = "RD_PRI_REG",
                                             // Indicates the Arbitration
                                             // Allowed values - "TDM", "ROUND_ROBIN",
                                             // "RD_PRI_REG", "RD_PRI_REG_STARVE_LIMIT"
    parameter C_S_AXI_REG_EN0                 = 20'h00000,
                                             // Instatiates register slices before upsizer.
                                             // The type of register is specified for each channel
                                             // in a vector. 4 bits per channel are used.
                                             // C_S_AXI_REG_EN0[03:00] = AW CHANNEL REGISTER SLICE
                                             // C_S_AXI_REG_EN0[07:04] =  W CHANNEL REGISTER SLICE
                                             // C_S_AXI_REG_EN0[11:08] =  B CHANNEL REGISTER SLICE
                                             // C_S_AXI_REG_EN0[15:12] = AR CHANNEL REGISTER SLICE
                                             // C_S_AXI_REG_EN0[20:16] =  R CHANNEL REGISTER SLICE
                                             // Possible values for each channel are:
                                             //
                                             //   0 => BYPASS    = The channel is just wired through the
                                             //                    module.
                                             //   1 => FWD       = The master VALID and payload signals
                                             //                    are registrated.
                                             //   2 => REV       = The slave ready signal is registrated
                                             //   3 => FWD_REV   = Both FWD and REV
                                             //   4 => SLAVE_FWD = All slave side signals and master
                                             //                    VALID and payload are registrated.
                                             //   5 => SLAVE_RDY = All slave side signals and master
                                             //                    READY are registrated.
                                             //   6 => INPUTS    = Slave and Master side inputs are
                                             //                    registrated.
    parameter C_S_AXI_REG_EN1                 = 20'h00000,
                                             // Same as C_S_AXI_REG_EN0, but this register is after
                                             // the upsizer
    parameter C_S_AXI_CTRL_ADDR_WIDTH         = 32,
                                             // Width of AXI-4-Lite address bus
    parameter C_S_AXI_CTRL_DATA_WIDTH         = 32,
                                             // Width of AXI-4-Lite data buses
    parameter C_S_AXI_BASEADDR                = 32'h0000_0000,
                                             // Base address of AXI4 Memory Mapped bus.
    parameter C_ECC_ONOFF_RESET_VALUE         = 1,
                                             // Controls ECC on/off value at startup/reset
    parameter C_ECC_CE_COUNTER_WIDTH          = 8,
                                             // The external memory to controller clock ratio.
    parameter ECC                               = "ON",
    parameter ECC_TEST                          = "OFF",
    parameter PAYLOAD_WIDTH                     = (ECC == "OFF") ? DQ_WIDTH : APP_DATA_WIDTH/8,
    parameter AUTO_AP_COL_A3                    = "ON",
    parameter MIG_PARAM_CHECKS                  ="FALSE",
    parameter INTERFACE                         ="AXI",
    parameter ADV_USER_REQ                      ="NONE",
    parameter FPGA			                        = "xcvu9p-flgb2104-2-i-",
    parameter DEVICE			                      = "xcvu9p-",
    parameter FAMILY                            = "ULTRASCALEPLUS",
    parameter DEBUG_SIGNAL		                  = "Disable",
    parameter AL                                = "0",
    parameter SELF_REFRESH                      = "true",
    parameter SAVE_RESTORE                      = "true",

    parameter IS_CKE_SHARED                     = "false",
    parameter MEMORY_PART                       = "MTA18ASF2G72PZ-2G3",
    parameter integer COMPONENT_WIDTH           = 72,
    parameter NUM_SLOT                          = 1,
    parameter RANK_SLOT                         = 1,
    parameter         PING_PONG_PHY             = 1, 
    parameter MEMORY_DENSITY                    = "8Gb",
    parameter MEMORY_SPEED_GRADE                = "083",
    parameter MEMORY_WIDTH                      = "4",
    parameter MEMORY_CONFIGURATION              = "RDIMM",
    parameter         SYSCLK_TYPE             = "DIFFERENTIAL",
                                // input clock type
    parameter CALIB_HIGH_SPEED                  = "FALSE",
    parameter         CA_MIRROR                 = "OFF",

    // Clamshell architecture of DRAM parts on PCB
    parameter         DDR4_CLAMSHELL       = "OFF",

    parameter DDR4_REG_PARITY_ENABLE            = "ON",
    parameter integer DBYTES                    = 9,
    parameter         MR0                       = 13'b0100101100100,
    parameter         DDR4_DB_HIF_RTT_NOM     = 4'b0011, 
    parameter         DDR4_DB_HIF_RTT_WR      = 4'b0000, 
    parameter         DDR4_DB_HIF_RTT_PARK    = 4'b0000, 
    parameter         DDR4_DB_HIF_DI          = 4'b0001, 
    parameter         DDR4_DB_DIF_ODT         = 4'b0011, 
    parameter         DDR4_DB_DIF_DI          = 4'b0000, 
    parameter         DDR4_DB_HIF_VREF        = 8'b0001_1011,
    parameter         DDR4_DB_DIF_VREF        = 8'b0001_1011,

    parameter         ODTWR                     = 16'h0001,
    parameter         ODTRD                     = 16'h0000,
    parameter         MR1                       = 13'b0001100000001,
    parameter         MR5                       = 13'b0000000000000,
    parameter         MR6                       = 13'b0100000011011,


    parameter         MR2                       = 13'b0000000011000,
    parameter         MR3                       = 13'b0001000000000,
    parameter         MR4                       = 13'b0000000000000,

    parameter         RD_VREF_VAL               = 7'h1D,
    parameter         SLOT0_CONFIG              = {{(8-CS_WIDTH){1'b0}},{CS_WIDTH{1'b1}}},
    parameter         SLOT1_CONFIG              = 8'b0000_0000,
    parameter         SLOT0_FUNC_CS             = {{(8-CS_WIDTH){1'b0}},{CS_WIDTH{1'b1}}},
    parameter         SLOT1_FUNC_CS             = 8'b0000_0000,
    parameter         SLOT0_ODD_CS              = 8'b0000_0000,
    parameter         SLOT1_ODD_CS              = 8'b0000_0000,

    parameter         DDR4_REG_RC03             = {9'b0_0000_0011, 4'b0101},

    parameter         DDR4_REG_RC04             = {9'b0_0000_0100, 4'b0101},

    parameter         DDR4_REG_RC05             = {9'b0_0000_0101, 4'b0101},
    parameter         tXPR                      = 97, // In fabric clock cycles
    parameter         tMOD                      = 6, // In fabric clock cycles
    parameter         tMRD                      = 2, // In fabric clock cycles
    parameter         tZQINIT                   = 256, // In fabric clock cycles
    parameter         MEM_CODE                  = 0,
    parameter         C_DEBUG_ENABLED           = 0,
    parameter         CPLX_PAT_LENGTH           = "LONG",
    parameter         EARLY_WR_DATA             = "OFF",

    // Migration parameters
    parameter                    MIGRATION = "OFF",

    parameter [8*CK_WIDTH-1:0]   CK_SKEW   = 8'd0,
    parameter [8*ADDR_WIDTH-1:0] ADDR_SKEW = {8'd0,8'd0,8'd0,8'd0,8'd0,8'd0,8'd0,8'd0,8'd0,8'd0,8'd0,8'd0,8'd0,8'd0,8'd0,8'd0,8'd0},
    parameter [8*BANK_WIDTH-1:0] BA_SKEW   = {8'd0,8'd0},
    parameter [8*BANK_GROUP_WIDTH-1:0] BG_SKEW   = {8'd0,8'd0},
    parameter [8*1-1:0]          ACT_SKEW  = 8'd0,
    parameter [8*1-1:0]          PAR_SKEW  = 8'd0,
    parameter [8*CS_WIDTH-1:0]   CS_SKEW   = 8'd0,
    parameter [8*CKE_WIDTH-1:0]  CKE_SKEW  = 8'd0,
    parameter [8*ODT_WIDTH-1:0]  ODT_SKEW  = 8'd0,
    parameter [8*LR_WIDTH-1:0]   C_SKEW    = 8'd0,

  `ifdef SIMULATION
    parameter         SIM_MODE                  = "BFM",
    parameter         BISC_EN                   = 0,
    parameter         BYPASS_CAL                = "TRUE",
    parameter         CAL_DQS_GATE              = "SKIP",
    parameter         CAL_WRLVL                 = "SKIP",
    parameter         CAL_RDLVL                 = "SKIP",
    parameter         CAL_RDLVL_DBI             = "SKIP",
    parameter         CAL_WR_DQS_DQ             = "SKIP",
    parameter         CAL_WR_DQS_DM_DBI         = "SKIP",
    parameter         CAL_WRITE_LAT             = "FAST",
    parameter         CAL_RDLVL_COMPLEX         = "SKIP",
    parameter         CAL_WR_DQS_COMPLEX        = "SKIP",
    parameter         CAL_RD_VREF               = "SKIP",
    parameter         CAL_RD_VREF_PATTERN       = "SIMPLE",
    parameter         CAL_WR_VREF               = "SKIP",
    parameter         CAL_WR_VREF_PATTERN       = "SIMPLE",
    parameter         CAL_DQS_TRACKING          = "SKIP",
    parameter         CAL_JITTER                = "NONE",
    parameter         t200us                    = 100, // In fabric clock cycles
    parameter         t500us                    = 150 // In fabric clock cycles
  `else
    parameter         SIM_MODE                  = "FULL",
    parameter         BISC_EN                   = 1,
    parameter         BYPASS_CAL                = "FALSE",
    parameter         CAL_DQS_GATE              = "FULL",
    parameter         CAL_WRLVL                 = "FULL",
    parameter         CAL_RDLVL                 = "FULL",
    parameter         CAL_RDLVL_DBI             = "SKIP",
    parameter         CAL_WR_DQS_DQ             = "FULL",
    parameter         CAL_WR_DQS_DM_DBI         = "SKIP",
    parameter         CAL_WRITE_LAT             = "FULL",
    parameter         CAL_RDLVL_COMPLEX         = "FULL",
    parameter         CAL_WR_DQS_COMPLEX        = "FULL",
    parameter         CAL_RD_VREF               = "SKIP",
    parameter         CAL_RD_VREF_PATTERN       = "SIMPLE",
    parameter         CAL_WR_VREF               = "SKIP",
    parameter         CAL_WR_VREF_PATTERN       = "SIMPLE",
    parameter         CAL_DQS_TRACKING          = "FULL",
    parameter         CAL_JITTER                = "FULL",
    parameter         t200us                    = 53362, // In fabric clock cycles
    parameter         t500us                    = 133405 // In fabric clock cycles
  `endif
    )
   (
   input  sys_rst,

   // iob<>DDR4 signals

   input                           c0_sys_clk_p,
   input                           c0_sys_clk_n,

    
    // Self-Refresh
    input         c0_ddr4_app_sref_req,        // application interface self-refresh request (to memory controller)
    output        c0_ddr4_app_sref_ack,        // application interface self-refresh acknowledgement (from memory controller)
    input         c0_ddr4_app_mem_init_skip,  
    // Save-Restore
    input         c0_ddr4_app_restore_en,  
    input         c0_ddr4_app_restore_complete,
    input         c0_ddr4_app_xsdb_select,
    input         c0_ddr4_app_xsdb_rd_en,
    input         c0_ddr4_app_xsdb_wr_en,
    input  [15:0] c0_ddr4_app_xsdb_addr,
    input  [8:0]  c0_ddr4_app_xsdb_wr_data,
    output [8:0]  c0_ddr4_app_xsdb_rd_data,
    output        c0_ddr4_app_xsdb_rdy,
    output [31:0] c0_ddr4_app_dbg_out,
   output                          c0_ddr4_act_n,
   output [ADDR_WIDTH-1:0]         c0_ddr4_adr,
   output [BANK_WIDTH-1:0]         c0_ddr4_ba,
   output [BANK_GROUP_WIDTH-1:0]   c0_ddr4_bg,
   output [CKE_WIDTH-1:0]          c0_ddr4_cke,
   output [ODT_WIDTH-1:0]          c0_ddr4_odt,
   output [CS_WIDTH-1:0]           c0_ddr4_cs_n,
   output [CK_WIDTH-1:0]           c0_ddr4_ck_t,
   output [CK_WIDTH-1:0]           c0_ddr4_ck_c,
   output                          c0_ddr4_reset_n,
   output                          c0_ddr4_parity,
   inout  [DQ_WIDTH-1:0]           c0_ddr4_dq,
   inout  [DQS_WIDTH-1:0]          c0_ddr4_dqs_c,
   inout  [DQS_WIDTH-1:0]          c0_ddr4_dqs_t,

   output                          c0_init_calib_complete,

   output                             addn_ui_clkout1,
   output                             addn_ui_clkout2,
   output                             addn_ui_clkout3,
   output                             addn_ui_clkout4,
   output                             dbg_clk,
   (* KEEP = "true" *) input [36:0]   sl_iport0,
   (* KEEP = "true" *) output [16:0]  sl_oport0,
   output                              c0_ddr4_ui_clk,
   output                              c0_ddr4_ui_clk_sync_rst,
   // AXI CTRL port
   input                                c0_ddr4_s_axi_ctrl_awvalid,
   output                               c0_ddr4_s_axi_ctrl_awready,
   input  [C_S_AXI_CTRL_ADDR_WIDTH-1:0] c0_ddr4_s_axi_ctrl_awaddr,
   // Slave Interface Write Data Ports
   input                                c0_ddr4_s_axi_ctrl_wvalid,
   output                               c0_ddr4_s_axi_ctrl_wready,
   input  [C_S_AXI_CTRL_DATA_WIDTH-1:0] c0_ddr4_s_axi_ctrl_wdata,
   // Slave Interface Write Response Ports
   output                               c0_ddr4_s_axi_ctrl_bvalid,
   input                                c0_ddr4_s_axi_ctrl_bready,
   output [1:0]                         c0_ddr4_s_axi_ctrl_bresp,
   // Slave Interface Read Address Ports
   input                                c0_ddr4_s_axi_ctrl_arvalid,
   output                               c0_ddr4_s_axi_ctrl_arready,
   input  [C_S_AXI_CTRL_ADDR_WIDTH-1:0] c0_ddr4_s_axi_ctrl_araddr,
   // Slave Interface Read Data Ports
   output                               c0_ddr4_s_axi_ctrl_rvalid,
   input                                c0_ddr4_s_axi_ctrl_rready,
   output [C_S_AXI_CTRL_DATA_WIDTH-1:0] c0_ddr4_s_axi_ctrl_rdata,
   output [1:0]                         c0_ddr4_s_axi_ctrl_rresp,

   // Interrupt output
   output                               c0_ddr4_interrupt,
   // Slave Interface Write Address Ports
   input                              c0_ddr4_aresetn,
   input  [C_S_AXI_ID_WIDTH-1:0]      c0_ddr4_s_axi_awid,
   input  [C_S_AXI_ADDR_WIDTH-1:0]    c0_ddr4_s_axi_awaddr,
   input  [7:0]                       c0_ddr4_s_axi_awlen,
   input  [2:0]                       c0_ddr4_s_axi_awsize,
   input  [1:0]                       c0_ddr4_s_axi_awburst,
   input  [0:0]                       c0_ddr4_s_axi_awlock,
   input  [3:0]                       c0_ddr4_s_axi_awcache,
   input  [2:0]                       c0_ddr4_s_axi_awprot,
   input  [3:0]                       c0_ddr4_s_axi_awqos,
   input                              c0_ddr4_s_axi_awvalid,
   output                             c0_ddr4_s_axi_awready,
   // Slave Interface Write Data Ports
   input  [C_S_AXI_DATA_WIDTH-1:0]    c0_ddr4_s_axi_wdata,
   input  [C_S_AXI_DATA_WIDTH/8-1:0]  c0_ddr4_s_axi_wstrb,
   input                              c0_ddr4_s_axi_wlast,
   input                              c0_ddr4_s_axi_wvalid,
   output                             c0_ddr4_s_axi_wready,
   // Slave Interface Write Response Ports
   input                              c0_ddr4_s_axi_bready,
   output [C_S_AXI_ID_WIDTH-1:0]      c0_ddr4_s_axi_bid,
   output [1:0]                       c0_ddr4_s_axi_bresp,
   output                             c0_ddr4_s_axi_bvalid,
   // Slave Interface Read Address Ports
   input  [C_S_AXI_ID_WIDTH-1:0]      c0_ddr4_s_axi_arid,
   input  [C_S_AXI_ADDR_WIDTH-1:0]    c0_ddr4_s_axi_araddr,
   input  [7:0]                       c0_ddr4_s_axi_arlen,
   input  [2:0]                       c0_ddr4_s_axi_arsize,
   input  [1:0]                       c0_ddr4_s_axi_arburst,
   input  [0:0]                       c0_ddr4_s_axi_arlock,
   input  [3:0]                       c0_ddr4_s_axi_arcache,
   input  [2:0]                       c0_ddr4_s_axi_arprot,
   input  [3:0]                       c0_ddr4_s_axi_arqos,
   input                              c0_ddr4_s_axi_arvalid,
   output                             c0_ddr4_s_axi_arready,
   // Slave Interface Read Data Ports
   input                              c0_ddr4_s_axi_rready,
   output [C_S_AXI_ID_WIDTH-1:0]      c0_ddr4_s_axi_rid,
   output [C_S_AXI_DATA_WIDTH-1:0]    c0_ddr4_s_axi_rdata,
   output [1:0]                       c0_ddr4_s_axi_rresp,
   output                             c0_ddr4_s_axi_rlast,
   output                             c0_ddr4_s_axi_rvalid,

   // Debug Port
   output wire [511:0]             dbg_bus
   );

  function integer clogb2 (input integer size);
    begin
      size = size - 1;
      for (clogb2=1; size>1; clogb2=clogb2+1)
        size = size >> 1;
    end
  endfunction // clogb2

  localparam RANK_WIDTH = clogb2(RANKS);
  localparam ECC_WIDTH = 8;
  localparam DATA_BUF_OFFSET_WIDTH = 1;
  // Fixed error log definition for all DRAM configs
  // Field:  reserved 3DS_C reserved RMW  Row     Column  reserved  Rank   Group   Bank
  // Bit:       51    50:48   47:45  44  43:24     23:8      7:6     5:4    3:2    1:0
  localparam MC_ERR_ADDR_WIDTH = 52;

  wire c0_rst;
  wire c0_div_clk;
  wire c0_div_clk_rst;
  (* keep = "TRUE" *) reg div_clk_rst_r1;
  wire c0_riu_clk;
  wire c0_riu_clk_rst;
  wire c0_mmcm_clk_in;
  wire sys_clk_in;
  wire mmcm_lock;
  wire pll_lock;
  wire reset_ub;
  wire pllGate;

  wire                                   c0_ddr4_correct_en;
  wire [2*nCK_PER_CLK-1:0]               c0_ddr4_raw_not_ecc;
  wire [2*nCK_PER_CLK-1:0]               c0_ddr4_ecc_single_int;
  wire [2*nCK_PER_CLK-1:0]               c0_ddr4_ecc_multiple_int;
  wire [MC_ERR_ADDR_WIDTH-1:0]           c0_ddr4_ecc_err_addr_int;
  wire                                   c0_ddr4_app_correct_en;
  wire [2*nCK_PER_CLK-1:0]               c0_ddr4_app_ecc_multiple_err;

  wire                                   c0_ddr4_app_correct_en_i;
  reg                                    c0_ddr4_init_calib_complete_r;
  wire [DQ_WIDTH*8-1:0]                  c0_ddr4_rd_data_phy2mc;

  wire [2*nCK_PER_CLK-1:0]               c0_ddr4_app_raw_not_ecc;
  wire [DQ_WIDTH/8-1:0]                  c0_ddr4_fi_xor_we;
  wire [DQ_WIDTH-1:0]                    c0_ddr4_fi_xor_wrdata;

  reg  [MC_ERR_ADDR_WIDTH-1:0]           c0_ddr4_ecc_err_addr_r1;
  reg  [2*nCK_PER_CLK-1:0]               c0_ddr4_ecc_single_r1;
  reg  [2*nCK_PER_CLK-1:0]               c0_ddr4_ecc_multiple_r1;

  // Added a single register stage to fix timing
  always@(posedge c0_div_clk)begin
    c0_ddr4_ecc_err_addr_r1 <= #TCQ c0_ddr4_ecc_err_addr_int;
    c0_ddr4_ecc_single_r1 <= #TCQ c0_ddr4_ecc_single_int;
    c0_ddr4_ecc_multiple_r1 <= #TCQ c0_ddr4_ecc_multiple_int;
  end

  //***************************************************************************
  // Added a single register stage for the calib_done to fix timing
  //***************************************************************************

  always @(posedge c0_div_clk)
    c0_ddr4_init_calib_complete_r <= c0_init_calib_complete;

  wire aclk;

  wire [APP_ADDR_WIDTH-1:0]              c0_ddr4_app_addr;
  wire [2:0]                             c0_ddr4_app_cmd;
  wire                                   c0_ddr4_app_en;
  wire                                   c0_ddr4_app_hi_pri;
  wire                                   c0_ddr4_app_autoprecharge;
  wire                                   c0_ddr4_app_wdf_end;
  wire                                   c0_ddr4_app_wdf_wren;
  wire                                   c0_ddr4_app_rd_data_end;
  wire                                   c0_ddr4_app_rd_data_valid;
  wire                                   c0_ddr4_app_rdy;
  wire                                   c0_ddr4_app_wdf_rdy;
  wire [APP_DATA_WIDTH-1:0]              c0_ddr4_app_wdf_data;
  wire [APP_MASK_WIDTH-1:0]              c0_ddr4_app_wdf_mask;
  wire [APP_DATA_WIDTH-1:0]              c0_ddr4_app_rd_data;

  assign aclk =  c0_div_clk;

  always @(posedge c0_div_clk)
    div_clk_rst_r1 <= c0_div_clk_rst;

  assign c0_ddr4_ui_clk = c0_div_clk;
  assign c0_ddr4_ui_clk_sync_rst = div_clk_rst_r1;


  ddr4_v2_2_0_infrastructure #
    (
     .CLKIN_PERIOD_MMCM   (CLKIN_PERIOD_MMCM),
     .CLKFBOUT_MULT_MMCM  (CLKFBOUT_MULT_MMCM),
     .DIVCLK_DIVIDE_MMCM  (DIVCLK_DIVIDE_MMCM),
     .CLKOUT0_DIVIDE_MMCM (CLKOUT0_DIVIDE_MMCM),
     .CLKOUT1_DIVIDE_MMCM (CLKOUT1_DIVIDE_MMCM),
     .CLKOUT2_DIVIDE_MMCM (CLKOUT2_DIVIDE_MMCM),
     .CLKOUT3_DIVIDE_MMCM (CLKOUT3_DIVIDE_MMCM),
     .CLKOUT4_DIVIDE_MMCM (CLKOUT4_DIVIDE_MMCM),
     .CLKOUT6_DIVIDE_MMCM (CLKOUT6_DIVIDE_MMCM),
     .C_FAMILY            (C_FAMILY),
     .TCQ                 (TCQ)
     )
  u_ddr4_infrastructure
    (
     .sys_rst          (sys_rst),
     .sys_clk_in       (sys_clk_in),
     .mmcm_clk_in      (c0_mmcm_clk_in),
     .pll_lock         (pll_lock),

     .mmcm_lock        (mmcm_lock),
     .div_clk          (c0_div_clk),
     .riu_clk          (c0_riu_clk),
     .addn_ui_clkout1  (addn_ui_clkout1),
     .addn_ui_clkout2  (addn_ui_clkout2),
     .addn_ui_clkout3  (addn_ui_clkout3),
     .addn_ui_clkout4  (addn_ui_clkout4),
     .dbg_clk          (dbg_clk),
     .rstdiv0          (c0_div_clk_rst),
     .rstdiv1          (c0_riu_clk_rst),
     .reset_ub         (reset_ub),
     .pllgate          (pllGate)
     );

ddr4_core_ddr4_mem_intfc #
  (
     .ADDR_WIDTH            (ADDR_WIDTH),
     .ROW_WIDTH             (ROW_WIDTH),
     .BANK_WIDTH            (BANK_WIDTH),
     .BANK_GROUP_WIDTH      (BANK_GROUP_WIDTH),
     .S_HEIGHT              (S_HEIGHT),
     .CKE_WIDTH             (CKE_WIDTH),
     .CK_WIDTH              (CK_WIDTH),
     .COL_WIDTH             (COL_WIDTH),
     .CS_WIDTH              (CS_WIDTH),
     .ODT_WIDTH             (ODT_WIDTH),
     .DRAM_TYPE             (DRAM_TYPE),
     .DQ_WIDTH              (DQ_WIDTH),
     .DBYTES                (DBYTES),
     .DEVICE                (DEVICE),
     .SAVE_RESTORE          (1'b1),
     .SELF_REFRESH          (1'b1),
     .NUM_SLOT              (NUM_SLOT),
     .RANK_SLOT             (RANK_SLOT),
     .DQS_WIDTH             (DQS_WIDTH),
     .DM_WIDTH              (DM_WIDTH),
     .MEM_ADDR_ORDER        (MEM_ADDR_ORDER),
     .DM_DBI                (DM_DBI),
     .USE_CS_PORT           (USE_CS_PORT),
     .ADDR_FIFO_WIDTH       (MC_ERR_ADDR_WIDTH),
     .ECC                   (ECC),
     .ECC_WIDTH             (ECC_WIDTH),
     .PAYLOAD_WIDTH         (PAYLOAD_WIDTH),
     .AUTO_AP_COL_A3        (AUTO_AP_COL_A3),

     .SLOT0_CONFIG          (SLOT0_CONFIG),
     .SLOT1_CONFIG          (SLOT1_CONFIG),
     .SLOT0_FUNC_CS         (SLOT0_FUNC_CS),
     .SLOT1_FUNC_CS         (SLOT1_FUNC_CS),

     .PARTIAL_RECONFIG      (PARTIAL_RECONFIG),
     .REG_CTRL              (REG_CTRL),
     .LRDIMM_MODE           (LRDIMM_MODE),
     .DDR4_DB_HIF_RTT_NOM   (DDR4_DB_HIF_RTT_NOM),
     .DDR4_DB_HIF_RTT_WR    (DDR4_DB_HIF_RTT_WR),
     .DDR4_DB_HIF_RTT_PARK  (DDR4_DB_HIF_RTT_PARK),
     .DDR4_DB_HIF_DI        (DDR4_DB_HIF_DI),
     .DDR4_DB_DIF_ODT       (DDR4_DB_DIF_ODT),
     .DDR4_DB_DIF_DI        (DDR4_DB_DIF_DI),
     .DDR4_DB_HIF_VREF      (DDR4_DB_HIF_VREF),
     .DDR4_DB_DIF_VREF      (DDR4_DB_DIF_VREF),
     .DDR4_REG_RC03         (DDR4_REG_RC03),
     .DDR4_REG_RC04         (DDR4_REG_RC04),
     .DDR4_REG_RC05         (DDR4_REG_RC05),
     .MCS_ECC_ENABLE        (MCS_ECC_ENABLE),
     .tCK                   (tCK),
     .tFAW                  (tFAW),
     .tRTW                  (tRTW),
     .tWTR_L                (tWTR_L),
     .tWTR_S                (tWTR_S),
     .tRFC                  (tRFC),
     .tREFI                 (tREFI),
     .ZQINTVL               (ZQINTVL),
     .tZQCS                 (tZQCS),
     .tRP                   (tRP),
     .tRRD_L                (tRRD_L),
     .tRRD_S                (tRRD_S),
     .tRAS                  (tRAS),
     .tRCD                  (tRCD),
     .tRTP                  (tRTP),
     .tWR                   (tWR),
     .NUMREF                (NUMREF),
     .PER_RD_INTVL          (PER_RD_INTVL),
     .ODTWR                 (ODTWR),
     .ODTWRDEL              (ODTWRDEL),
     .ODTWRDUR              (ODTWRDUR),
     .ODTWRODEL             (ODTWRODEL),
     .ODTWRODUR             (ODTWRODUR),
     .ODTRD                 (ODTRD),
     .ODTRDDEL              (ODTRDDEL),
     .ODTRDDUR              (ODTRDDUR),
     .ODTRDODEL             (ODTRDODEL),
     .ODTRDODUR             (ODTRDODUR),
     .ODTNOP                (ODTNOP),
     .DRAM_WIDTH            (DRAM_WIDTH),
     .RANKS                 (RANKS),
     .RANK_WIDTH            (RANK_WIDTH),
     .ORDERING              (ORDERING),
     .RTL_VERSION           (RTL_VERSION),
     .TXN_FIFO_BYPASS       (TXN_FIFO_BYPASS),
     .TXN_FIFO_PIPE         (TXN_FIFO_PIPE),
     .PER_RD_PERF           (PER_RD_PERF),
     .CAS_FIFO_BYPASS       (CAS_FIFO_BYPASS),
     .ALIAS_PAGE            (ALIAS_PAGE),
     .ALIAS_P_CNT           (ALIAS_P_CNT),
     .NOP_ADD_LOW           (NOP_ADD_LOW),
     .STARVATION_EN         (STARVATION_EN),
     .STARVE_COUNT_WIDTH    (STARVE_COUNT_WIDTH),
     .EXTRA_CMD_DELAY       (EXTRA_CMD_DELAY),
     .nCK_PER_CLK           (nCK_PER_CLK),
     .APP_DATA_WIDTH        (APP_DATA_WIDTH),
     .APP_MASK_WIDTH        (APP_MASK_WIDTH),
     .APP_ADDR_WIDTH        (APP_ADDR_WIDTH),

     .MIG_PARAM_CHECKS      (MIG_PARAM_CHECKS),
     .INTERFACE             (INTERFACE),
     .C_S_AXI_ADDR_WIDTH    (C_S_AXI_ADDR_WIDTH),
     .ADV_USER_REQ          (ADV_USER_REQ),
     .MEMORY_DENSITY        (MEMORY_DENSITY),
     .MEMORY_SPEED_GRADE    (MEMORY_SPEED_GRADE),
     .MEMORY_WIDTH          (MEMORY_WIDTH),
     .MEMORY_CONFIGURATION  (MEMORY_CONFIGURATION),
     .CALIB_HIGH_SPEED      (CALIB_HIGH_SPEED),

     .MR0                   (MR0),
     .MR1                   (MR1),
     .MR2                   (MR2),
     .MR3                   (MR3),
     .MR4                   (MR4),
     .MR5                   (MR5),
     .MR6                   (MR6),

     .RD_VREF_VAL           (RD_VREF_VAL),  
     .SLOT0_ODD_CS          (SLOT0_ODD_CS),
     .SLOT1_ODD_CS          (SLOT1_ODD_CS),
     
     .DDR4_CLAMSHELL         (DDR4_CLAMSHELL),
     .CA_MIRROR              (CA_MIRROR),
     .DDR4_REG_PARITY_ENABLE (DDR4_REG_PARITY_ENABLE),
     
     .t200us                 (t200us),
     .t500us                 (t500us),
     .tXPR                   (tXPR),
     .tMOD                   (tMOD),
     .tMRD                   (tMRD),
     .tZQINIT                (tZQINIT),
     .TCQ                    (TCQ),
     
     .EARLY_WR_DATA          (EARLY_WR_DATA),
     .MEM_CODE               (MEM_CODE),
 
     .MIGRATION              (MIGRATION),
     .CK_SKEW                (CK_SKEW),
     .ADDR_SKEW              (ADDR_SKEW),
     .BA_SKEW                (BA_SKEW),
     .BG_SKEW                (BG_SKEW),
     .ACT_SKEW               (ACT_SKEW),
     .PAR_SKEW               (PAR_SKEW),
     .CKE_SKEW               (CKE_SKEW),
     .CS_SKEW                (CS_SKEW),
     .ODT_SKEW               (ODT_SKEW),
     .C_SKEW                 (C_SKEW),

     .BISC_EN                (BISC_EN),
     .BYPASS_CAL             (BYPASS_CAL),
     .CAL_DQS_GATE           (CAL_DQS_GATE),
     .CAL_WRLVL              (CAL_WRLVL),
     .CAL_RDLVL              (CAL_RDLVL),
     .CAL_RDLVL_DBI          (CAL_RDLVL_DBI),
     .CAL_WR_DQS_DQ          (CAL_WR_DQS_DQ),
     .CAL_WR_DQS_DM_DBI      (CAL_WR_DQS_DM_DBI),
     .CAL_WRITE_LAT          (CAL_WRITE_LAT),
     .CAL_RDLVL_COMPLEX      (CAL_RDLVL_COMPLEX),
     .CAL_WR_DQS_COMPLEX     (CAL_WR_DQS_COMPLEX),
     .CAL_RD_VREF            (CAL_RD_VREF),
     .CAL_RD_VREF_PATTERN    (CAL_RD_VREF_PATTERN),
     .CAL_WR_VREF            (CAL_WR_VREF),
     .CAL_WR_VREF_PATTERN    (CAL_WR_VREF_PATTERN),
     .CAL_DQS_TRACKING       (CAL_DQS_TRACKING),
     .CAL_JITTER             (CAL_JITTER),
     .CPLX_PAT_LENGTH        (CPLX_PAT_LENGTH),
     .C_FAMILY               (C_FAMILY),
     
     .CLKOUTPHY_MODE         (CLKOUTPHY_MODE),
     .CLKFBOUT_MULT_MMCM     (CLKFBOUT_MULT_MMCM),
     .DIVCLK_DIVIDE_MMCM     (DIVCLK_DIVIDE_MMCM),
     .CLKOUT0_DIVIDE_MMCM    (CLKOUT0_DIVIDE_MMCM)
   )
u_ddr4_mem_intfc
  (

   .sys_clk_p           (c0_sys_clk_p),
   .sys_clk_n           (c0_sys_clk_n),
   .mmcm_lock           (mmcm_lock),
   .reset_ub            (reset_ub),
   .pllGate             (pllGate),
   .div_clk             (c0_div_clk),
   .div_clk_rst         (c0_div_clk_rst),
   .riu_clk             (c0_riu_clk),
   .riu_clk_rst         (c0_riu_clk_rst),
   .pll_lock            (pll_lock),
   .sys_clk_in          (sys_clk_in),
   .mmcm_clk_in         (c0_mmcm_clk_in),
   .calDone             (c0_init_calib_complete),

   .ddr4_act_n          (c0_ddr4_act_n),
   .ddr4_adr            (c0_ddr4_adr),
   .ddr4_ba             (c0_ddr4_ba),
   .ddr4_bg             (c0_ddr4_bg),
   .ddr4_c              (),
   .ddr4_cke            (c0_ddr4_cke),
   .ddr4_odt            (c0_ddr4_odt),
   .ddr4_cs_n           (c0_ddr4_cs_n),
   .ddr4_ck_t           (c0_ddr4_ck_t),
   .ddr4_ck_c           (c0_ddr4_ck_c),
   .ddr4_reset_n        (c0_ddr4_reset_n),
     .ddr4_parity         (c0_ddr4_parity),
   .ddr4_dm_dbi_n       (),
   .ddr4_dq             (c0_ddr4_dq),
   .ddr4_dqs_c          (c0_ddr4_dqs_c),
   .ddr4_dqs_t          (c0_ddr4_dqs_t),

   .app_addr              (c0_ddr4_app_addr),
   .app_cmd               (c0_ddr4_app_cmd),
   .app_en                (c0_ddr4_app_en),
   .app_hi_pri            (c0_ddr4_app_hi_pri),
   .app_autoprecharge     (c0_ddr4_app_autoprecharge),
   .app_wdf_data          (c0_ddr4_app_wdf_data),
   .app_wdf_end           (c0_ddr4_app_wdf_end),
   .app_wdf_mask          (c0_ddr4_app_wdf_mask),
   .app_wdf_wren          (c0_ddr4_app_wdf_wren),
   .app_correct_en_i      (c0_ddr4_app_correct_en_i),
   .app_raw_not_ecc       (c0_ddr4_app_raw_not_ecc),
   .app_ecc_multiple_err  (c0_ddr4_app_ecc_multiple_err),
   .app_rd_data           (c0_ddr4_app_rd_data),
   .app_rd_data_end       (c0_ddr4_app_rd_data_end),
   .app_rd_data_valid     (c0_ddr4_app_rd_data_valid),
   .app_rdy               (c0_ddr4_app_rdy),
   .app_wdf_rdy           (c0_ddr4_app_wdf_rdy),
   .app_ref_req           (1'b0),
   .app_ref_ack           (),
   .app_zq_req            (1'b0),
   .app_zq_ack            (),   
   .sl_iport0             (sl_iport0),
   .sl_oport0             (sl_oport0),
   .ddr4_mcs_lmb_ue                (),
   .ddr4_mcs_lmb_ce                (),
   .cal_pre_status        (),
   .cal_r1_status         (),
   .cal_r2_status         (),
   .cal_r3_status         (),
   .cal_post_status       (),
   .cal_error             (),
   .cal_error_bit         (),
   .cal_error_nibble      (),
   .cal_error_code        (),
   .app_sr_req            (c0_ddr4_app_sref_req),
   .app_sr_active         (c0_ddr4_app_sref_ack), 
   .app_mem_init_skip     (c0_ddr4_app_mem_init_skip),
   .app_save_req          (1'b0),
   .app_save_ack          (),
   .app_restore_en        (c0_ddr4_app_restore_en),
   .app_restore_complete  (c0_ddr4_app_restore_complete),
   .xsdb_select           (c0_ddr4_app_xsdb_select),
   .xsdb_rd_en            (c0_ddr4_app_xsdb_rd_en),
   .xsdb_wr_en            (c0_ddr4_app_xsdb_wr_en),
   .xsdb_addr             (c0_ddr4_app_xsdb_addr),
   .xsdb_wr_data          (c0_ddr4_app_xsdb_wr_data),
   .xsdb_rd_data          (c0_ddr4_app_xsdb_rd_data),
   .xsdb_rdy              (c0_ddr4_app_xsdb_rdy),
   .dbg_out               (c0_ddr4_app_dbg_out),

   .traffic_wr_done               (1'b0),
   .traffic_status_err_bit_valid  (1'b0),
   .traffic_status_err_type_valid (1'b0),
   .traffic_status_err_type       (1'b0),
   .traffic_status_done           (1'b0),
   .traffic_status_watch_dog_hang (1'b0),
   .traffic_error                 ({APP_DATA_WIDTH{1'b0}}),
   .win_start                     (4'b0),
   .traffic_clr_error             (),
   .traffic_start                 (),
   .traffic_rst                   (),
   .traffic_err_chk_en            (),
   .traffic_instr_addr_mode       (),
   .traffic_instr_data_mode       (),
   .traffic_instr_rw_mode         (),
   .traffic_instr_rw_submode      (),
   .traffic_instr_num_of_iter     (),
   .traffic_instr_nxt_instr       (),
   .win_status                    (),
   .ecc_err_addr          (c0_ddr4_ecc_err_addr_int),
   .eccSingle             (c0_ddr4_ecc_single_int),
   .eccMultiple           (c0_ddr4_ecc_multiple_int),
   .fi_xor_we             (c0_ddr4_fi_xor_we),
   .fi_xor_wrdata         (c0_ddr4_fi_xor_wrdata),
   .rd_data_phy2mc        (c0_ddr4_rd_data_phy2mc),
     //Debug Port
   .dbg_bus               (dbg_bus), 
   .dbg_rd_data_cmp           (),
   .dbg_expected_data         (),
   .dbg_cal_seq               (),
   .dbg_cal_seq_cnt           (),
   .dbg_cal_seq_rd_cnt        (),
   .dbg_rd_valid              (),
   .dbg_cmp_byte              (),
   .dbg_rd_data               (),
   .dbg_cplx_config           (),
   .dbg_cplx_status           (),
   .dbg_io_address            (),
   .dbg_pllGate               (),
   .dbg_phy2clb_fixdly_rdy_low(),
   .dbg_phy2clb_fixdly_rdy_upp(),
   .dbg_phy2clb_phy_rdy_low   (),
   .dbg_phy2clb_phy_rdy_upp   (),
   .cal_r0_status             ()
   );
ddr4_v2_2_0_axi #
  (
   .C_ECC                         (ECC),
   .C_S_AXI_ID_WIDTH              (C_S_AXI_ID_WIDTH),
   .C_S_AXI_ADDR_WIDTH            (C_S_AXI_ADDR_WIDTH),
   .C_S_AXI_DATA_WIDTH            (C_S_AXI_DATA_WIDTH),
   .C_MC_DATA_WIDTH               (APP_DATA_WIDTH),
   .C_MC_ADDR_WIDTH               (APP_ADDR_WIDTH),
   .C_MC_BURST_MODE               (BURST_MODE),
   .C_MC_nCK_PER_CLK              (nCK_PER_CLK),
   .C_S_AXI_SUPPORTS_NARROW_BURST (C_S_AXI_SUPPORTS_NARROW_BURST),
   .C_RD_WR_ARB_ALGORITHM         (C_RD_WR_ARB_ALGORITHM),
   .C_S_AXI_REG_EN0               (C_S_AXI_REG_EN0),
   .C_S_AXI_REG_EN1               (C_S_AXI_REG_EN1)
  )
  u_ddr_axi
    (
     .aclk                                   (aclk),

     // Slave Interface Write Address Ports
     .aresetn                                (c0_ddr4_aresetn),
     .s_axi_awid                             (c0_ddr4_s_axi_awid),
     .s_axi_awaddr                           (c0_ddr4_s_axi_awaddr),
     .s_axi_awlen                            (c0_ddr4_s_axi_awlen),
     .s_axi_awsize                           (c0_ddr4_s_axi_awsize),
     .s_axi_awburst                          (c0_ddr4_s_axi_awburst),
     .s_axi_awlock                           (c0_ddr4_s_axi_awlock),
     .s_axi_awcache                          (c0_ddr4_s_axi_awcache),
     .s_axi_awprot                           (c0_ddr4_s_axi_awprot),
     .s_axi_awqos                            (c0_ddr4_s_axi_awqos),
     .s_axi_awvalid                          (c0_ddr4_s_axi_awvalid),
     .s_axi_awready                          (c0_ddr4_s_axi_awready),
     // Slave Interface Write Data Ports
     .s_axi_wdata                            (c0_ddr4_s_axi_wdata),
     .s_axi_wstrb                            (c0_ddr4_s_axi_wstrb),
     .s_axi_wlast                            (c0_ddr4_s_axi_wlast),
     .s_axi_wvalid                           (c0_ddr4_s_axi_wvalid),
     .s_axi_wready                           (c0_ddr4_s_axi_wready),
     // Slave Interface Write Response Ports
     .s_axi_bid                              (c0_ddr4_s_axi_bid),
     .s_axi_bresp                            (c0_ddr4_s_axi_bresp),
     .s_axi_bvalid                           (c0_ddr4_s_axi_bvalid),
     .s_axi_bready                           (c0_ddr4_s_axi_bready),
     // Slave Interface Read Address Ports
     .s_axi_arid                             (c0_ddr4_s_axi_arid),
     .s_axi_araddr                           (c0_ddr4_s_axi_araddr),
     .s_axi_arlen                            (c0_ddr4_s_axi_arlen),
     .s_axi_arsize                           (c0_ddr4_s_axi_arsize),
     .s_axi_arburst                          (c0_ddr4_s_axi_arburst),
     .s_axi_arlock                           (c0_ddr4_s_axi_arlock),
     .s_axi_arcache                          (c0_ddr4_s_axi_arcache),
     .s_axi_arprot                           (c0_ddr4_s_axi_arprot),
     .s_axi_arqos                            (c0_ddr4_s_axi_arqos),
     .s_axi_arvalid                          (c0_ddr4_s_axi_arvalid),
     .s_axi_arready                          (c0_ddr4_s_axi_arready),
     // Slave Interface Read Data Ports
     .s_axi_rid                              (c0_ddr4_s_axi_rid),
     .s_axi_rdata                            (c0_ddr4_s_axi_rdata),
     .s_axi_rresp                            (c0_ddr4_s_axi_rresp),
     .s_axi_rlast                            (c0_ddr4_s_axi_rlast),
     .s_axi_rvalid                           (c0_ddr4_s_axi_rvalid),
     .s_axi_rready                           (c0_ddr4_s_axi_rready),

     // MC Master Interface
     //CMD PORT
     .mc_app_en                              (c0_ddr4_app_en),
     .mc_app_cmd                             (c0_ddr4_app_cmd),
     .mc_app_sz                              (),
     .mc_app_addr                            (c0_ddr4_app_addr),
     .mc_app_hi_pri                          (c0_ddr4_app_hi_pri),
     .mc_app_autoprecharge                   (c0_ddr4_app_autoprecharge),
     .mc_app_rdy                             (c0_ddr4_app_rdy),
     .mc_init_complete                       (c0_init_calib_complete),

     //DATA PORT
     .mc_app_wdf_wren                        (c0_ddr4_app_wdf_wren),
     .mc_app_wdf_mask                        (c0_ddr4_app_wdf_mask),
     .mc_app_wdf_data                        (c0_ddr4_app_wdf_data),
     .mc_app_wdf_end                         (c0_ddr4_app_wdf_end),
     .mc_app_wdf_rdy                         (c0_ddr4_app_wdf_rdy),

     .mc_app_rd_valid                        (c0_ddr4_app_rd_data_valid),
     .mc_app_rd_data                         (c0_ddr4_app_rd_data),
     .mc_app_rd_end                          (c0_ddr4_app_rd_data_end),
     .mc_app_ecc_multiple_err                (c0_ddr4_app_ecc_multiple_err)
     );

    reg  [DQ_WIDTH*8-1:0]                  c0_ddr4_rd_data_phy2mc_r1;
    reg  [DQ_WIDTH*8-1:0]                  c0_ddr4_rd_data_phy2mc_r2;
  always@(posedge c0_div_clk)begin
    c0_ddr4_rd_data_phy2mc_r1 <= #TCQ c0_ddr4_rd_data_phy2mc;
    c0_ddr4_rd_data_phy2mc_r2 <= #TCQ c0_ddr4_rd_data_phy2mc_r1;
  end

  ddr4_v2_2_0_axi_ctrl_top # (
    .C_S_AXI_CTRL_ADDR_WIDTH (C_S_AXI_CTRL_ADDR_WIDTH) ,
    .C_S_AXI_CTRL_DATA_WIDTH (C_S_AXI_CTRL_DATA_WIDTH) ,
    .C_S_AXI_ADDR_WIDTH      (C_S_AXI_ADDR_WIDTH) ,
    .C_S_AXI_BASEADDR        (C_S_AXI_BASEADDR) ,
    .C_ECC_TEST              (ECC_TEST) ,
    .C_DQ_WIDTH              (DQ_WIDTH) ,
    .C_ECC_WIDTH             (ECC_WIDTH) ,
    .C_MEM_ADDR_ORDER        (MEM_ADDR_ORDER) ,
    .C_BANK_WIDTH            (BANK_WIDTH) ,
    .C_ROW_WIDTH             (ROW_WIDTH) ,
    .C_COL_WIDTH             (COL_WIDTH) ,
    .C_ECC_ONOFF_RESET_VALUE (C_ECC_ONOFF_RESET_VALUE) ,
    .C_ECC_CE_COUNTER_WIDTH  (C_ECC_CE_COUNTER_WIDTH) ,
    .C_NCK_PER_CLK           (nCK_PER_CLK) ,
    .C_MC_ERR_ADDR_WIDTH     (MC_ERR_ADDR_WIDTH)
  ) axi_ctrl_top_0 (
    .aclk           (aclk) ,
    .aresetn        (c0_ddr4_aresetn) ,
    .s_axi_awvalid  (c0_ddr4_s_axi_ctrl_awvalid) ,
    .s_axi_awready  (c0_ddr4_s_axi_ctrl_awready) ,
    .s_axi_awaddr   (c0_ddr4_s_axi_ctrl_awaddr) ,
    .s_axi_wvalid   (c0_ddr4_s_axi_ctrl_wvalid) ,
    .s_axi_wready   (c0_ddr4_s_axi_ctrl_wready) ,
    .s_axi_wdata    (c0_ddr4_s_axi_ctrl_wdata) ,
    .s_axi_bvalid   (c0_ddr4_s_axi_ctrl_bvalid) ,
    .s_axi_bready   (c0_ddr4_s_axi_ctrl_bready) ,
    .s_axi_bresp    (c0_ddr4_s_axi_ctrl_bresp) ,
    .s_axi_arvalid  (c0_ddr4_s_axi_ctrl_arvalid) ,
    .s_axi_arready  (c0_ddr4_s_axi_ctrl_arready) ,
    .s_axi_araddr   (c0_ddr4_s_axi_ctrl_araddr) ,
    .s_axi_rvalid   (c0_ddr4_s_axi_ctrl_rvalid) ,
    .s_axi_rready   (c0_ddr4_s_axi_ctrl_rready) ,
    .s_axi_rdata    (c0_ddr4_s_axi_ctrl_rdata) ,
    .s_axi_rresp    (c0_ddr4_s_axi_ctrl_rresp) ,
    .interrupt      (c0_ddr4_interrupt) ,
    .init_complete  (c0_ddr4_init_calib_complete_r) ,
    .ecc_single     (c0_ddr4_ecc_single_r1) ,
    .ecc_multiple   (c0_ddr4_ecc_multiple_r1) ,
    .ecc_err_addr   (c0_ddr4_ecc_err_addr_r1) ,
    .app_correct_en (c0_ddr4_app_correct_en) ,
    .dfi_rddata     (c0_ddr4_rd_data_phy2mc_r2) ,
    .fi_xor_we      (c0_ddr4_fi_xor_we) ,
    .fi_xor_wrdata  (c0_ddr4_fi_xor_wrdata)
  );

  assign c0_ddr4_app_correct_en_i = c0_ddr4_app_correct_en ;
  generate
    if(ECC_TEST == "ON") begin :gen_ECC_TEST
      assign c0_ddr4_app_raw_not_ecc = {2*nCK_PER_CLK{1'b1}};
    end else begin
      assign c0_ddr4_app_raw_not_ecc = {2*nCK_PER_CLK{1'b0}};
    end
  endgenerate

endmodule
