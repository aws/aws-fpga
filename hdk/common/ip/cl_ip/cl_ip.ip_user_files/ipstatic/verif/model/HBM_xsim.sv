// (c) Copyright 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and international copyright
// and other intellectual property laws.
//
// DISCLAIMER
// This disclaimer is not a license and does not grant any
// rights to the materials distributed herewith. Except as
// otherwise provided in a valid license issued to you by
// AMD, and to the maximum extent permitted by applicable
// law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// WITH ALL FAULTS, AND AMD HEREBY DISCLAIMS ALL WARRANTIES
// AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// (2) AMD shall not be liable (whether in contract or tort,
// including negligence, or under any other theory of
// liability) for any loss or damage of any kind or nature
// related to, arising under or in connection with these
// materials, including for any direct, or any indirect,
// special, incidental, or consequential loss or damage
// (including loss of data, profits, goodwill, or any type of
// loss or damage suffered as a result of any action brought
// by a third party) even if such damage or loss was
// reasonably foreseeable or AMD had been advised of the
// possibility of the same.
//
// CRITICAL APPLICATIONS
// AMD products are not designed or intended to be fail-
// safe, or for use in any application requiring fail-safe
// performance, such as life-support or safety devices or
// systems, Class III medical devices, nuclear facilities,
// applications related to the deployment of airbags, or any
// other applications that could lead to death, personal
// injury, or severe property or environmental damage
// (individually and collectively, "Critical
// Applications"). Customer assumes the sole risk and
// liability of any use of AMD products in Critical
// Applications, subject only to applicable laws and
// regulations governing limitations on product liability.
//
// THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// PART OF THIS FILE AT ALL TIMES.
////////////////////////////////////////////////////////////
`ifndef __HBM2_RESPONDER_IF_SV__
`define __HBM2_RESPONDER_IF_SV__


//`define EN_HBM_RESPONDER_DBG_MODE

`ifdef EN_HBM_RESPONDER_DBG_MODE
typedef enum  bit[8:0]  {HBM_NONE=0, HBM_LOW=100, HBM_MEDIUM=200, HBM_HIGH=300, HBM_FULL=400, HBM_DEBUG=500}      hbm_verbosity_t;
typedef enum  bit[4:0]  {RNOP, ACT, PRE, PREA, REFSB, REF, PDE, SRE, PDX, SRX, CNOP, RD, RDA, WR, WRA, MRS}       hbm_command_t;
`endif

//////////////////////////////////////////////////////////////////////
// File: hbm_responder_if.sv 
//
// Descrtiption: 
// This is the HBM responder interface contains HBM memory signals, 
// core support signlas and debug signlas
//////////////////////////////////////////////////////////////////////

`timescale 1ps/1ps
interface hbm2_responder_if(input clk, input reset_n);
    
    // Single Channel Signals
    logic                     hbm_ck_t    ;           // clock
    logic  	                  hbm_ck_c    ;           // clock
    logic  	                  hbm_cke     ;           // clock enable
    logic  	                  hbm_cke_r   ;           // clock enable flopped
    logic   [6  : 0]          hbm_r       ;           // row address              // 6:0 incase of HBM2e, 5:0 incase of HBM2
    logic   [8  : 0]          hbm_c       ;           // column address           // 8:0 incase of HBM2e, 7:0 incase of HBM2
    wire    [3  : 0]          hbm_par     ;           // data parity              // 1 PAR per 32 DQs
    logic   [3  : 0]          hbm_par_reg  = 'z;      // read data parity         // 1 PAR per 32 DQs
    wire    [15 : 0]          hbm_dm      ;           // data mask                // 1 DM per 8DQs
    logic   [15 : 0]          hbm_dm_reg   = 'z;      // read data mask           // 1 DM per 8DQs
    wire    [15 : 0]          hbm_dbi     ;           // data byte inversion      // 1 DBI per 8DQs
    logic   [15 : 0]          hbm_dbi_reg  = 'z;      // readdata byte inversion  // 1 DBI per 8DQs
    wire    [127: 0]          hbm_dq      ;           // Write/Read data
    logic   [127: 0]          hbm_dq_reg   = 'z;      // read data DQ
    logic   [3  : 0]          hbm_wdqs_t  ;           // write DQ steobe          // 1 WDQS_t per 32DQs
    logic   [3  : 0]          hbm_wdqs_c  ;           // write DQ steobe          // 1 WDQS_c per 32DQs
    logic   [3  : 0]          hbm_rdqs_t = '0;           // read DQ strobe           // 1 RDQS_t per 32DQs
    logic   [3  : 0]          hbm_rdqs_c  ;           // read DQ strobe           // 1 RDQS_c per 32DQs
    logic   [3  : 0]          hbm_derr   = '0;           // data parity error        // 1 DERR per 32 DQs
    logic                     hbm_aerr   = '0;           // address parity error
    logic                     hbm_rr      ;           // reduntant row address pin for remapping 
    logic                     hbm_rc      ;           // reduntant column address pin for remapping
    wire    [7  : 0]          hbm_rd      ;           // reduntant data pin for remapping
    logic   [7  : 0]          hbm_rd_reg   = 'z;      // reduntant read data pin for remapping

    assign  hbm_par             =  hbm_par_reg;
    assign  hbm_dm              =  hbm_dm_reg;
    assign  hbm_dbi             =  hbm_dbi_reg;
    assign  hbm_dq              =  hbm_dq_reg;
    assign  hbm_rd              =  hbm_rd_reg;

    assign  hbm_rdqs_c          = ~hbm_rdqs_t;

    modport hbm_port 
    (
      input     hbm_ck_t    , 
      input     hbm_ck_c    , 
      input     hbm_cke     , 
      input     hbm_r       , 
      input     hbm_c       , 
      input     hbm_par     , 
      output    hbm_par_reg , 
      input     hbm_dm      , 
      output    hbm_dm_reg  , 
      input     hbm_dbi     , 
      output    hbm_dbi_reg , 
      input     hbm_dq      , 
      output    hbm_dq_reg  , 
      input     hbm_wdqs_t  , 
      input     hbm_wdqs_c  , 
      output    hbm_rdqs_t  , 
      output    hbm_rdqs_c  , 
      output    hbm_derr    ,  
      output    hbm_aerr    ,
      input     hbm_rr      ,  
      input     hbm_rc      ,  
      input     hbm_rd      ,       
      output    hbm_rd_reg       
    );

    // Support Signals
    always_ff@(posedge hbm_ck_t) begin
      hbm_cke_r <=  hbm_cke;
    end
    
    //wire    clk_valid;
    //assign  clk_valid     = (hbm_ck_t === 1) | (hbm_ck_t === 0); // Not used. By using #0 after edge event in responder_class, taken care the ULTRASCALE HOOD HBM2 MC RTL ck_t inout signal Hi-Z glitch issue

    wire    cke_valid_cmd;
    wire    cke_valid_row_entry_cmd;
    wire    cke_valid_row_exit_cmd;
    assign  cke_valid_cmd              = (hbm_cke_r === 1 && hbm_cke === 1) ? 1 : 0;
    assign  cke_valid_row_entry_cmd    = (hbm_cke_r === 1 && hbm_cke === 0) ? 1 : 0;
    assign  cke_valid_row_exit_cmd     = (hbm_cke_r === 0 && hbm_cke === 1) ? 1 : 0;

    `ifdef EN_HBM_RESPONDER_DBG_MODE
    // Debug Signlas
    hbm_command_t   col_cmd_symbol                  = CNOP;
    logic [3:0]     col_cmd                         = 0; 
    logic           col_pc                          = 0;
    logic [1:0]     col_sid                         = 0;
    logic [3:0]     col_ba                          = 0;
    logic [1:0]     col_bg                          = 0;
    logic [1:0]     col_b                           = 0;
    logic [5:0]     col_addr                        = 0; 
    logic [4:0]     col_addr_5d1                    = 0; 
    logic [7:0]     col_mrs_op                      = 0;
    logic           col_par                         = 0;
    logic [14:0]    col_row_addr                    = 0;
    logic [31:0]    col_mem_addr                    = 0; // concatenated addr of column command of pc, sid, bg, bank, activated row and colum addr
    logic           valid_col_cmd                   = 0;
    
    hbm_command_t   row_cmd_symbol                  = RNOP;
    logic [2:0]     row_cmd                         = 0;
    logic           row_all                         = 0;
    logic           row_pc                          = 0;
    logic [1:0]     row_sid                         = 0;
    logic [3:0]     row_ba                          = 0;
    logic [1:0]     row_bg                          = 0;
    logic [1:0]     row_b                           = 0;
    logic [14:0]    row_addr                        = 0;
    logic           row_par                         = 0;
    logic           valid_row_cmd                   = 0;

    logic           entered_in_power_down_mode      = 0;
    logic           entered_in_self_ref_mode        = 0;

    logic [31:0]    mrs_cmd_cnt                     = 0;
    logic [31:0]    wr_cmd_cnt_pc0                  = 0;
    logic [31:0]    wr_cmd_cnt_pc1                  = 0;
    logic [31:0]    wra_cmd_cnt_pc0                 = 0;
    logic [31:0]    wra_cmd_cnt_pc1                 = 0;
    logic [31:0]    rd_cmd_cnt_pc0                  = 0;
    logic [31:0]    rd_cmd_cnt_pc1                  = 0;
    logic [31:0]    rda_cmd_cnt_pc0                 = 0;
    logic [31:0]    rda_cmd_cnt_pc1                 = 0;
    
    logic [31:0]    act_cmd_cnt_pc0                 = 0;
    logic [31:0]    act_cmd_cnt_pc1                 = 0;
    logic [31:0]    pre_cmd_cnt_pc0                 = 0;
    logic [31:0]    pre_cmd_cnt_pc1                 = 0;
    logic [31:0]    pre_all_cmd_cnt_pc0             = 0;
    logic [31:0]    pre_all_cmd_cnt_pc1             = 0;
    logic [31:0]    ref_sb_cmd_cnt_pc0              = 0;
    logic [31:0]    ref_sb_cmd_cnt_pc1              = 0;
    logic [31:0]    ref_cmd_cnt_pc0                 = 0;
    logic [31:0]    ref_cmd_cnt_pc1                 = 0;
    `endif // EN_HBM_RESPONDER_DBG_MODE

endinterface


`endif


`ifndef __HBM2_RESPONDER_SV__
`define __HBM2_RESPONDER_SV__


//////////////////////////////////////////////////////////////////////
// File: hbm_responder.sv
//
// Descrtiption: 
// This is top module for HBM Responder(Memory Model). 
// It supports HBM2/HBM2e protocol with upto 8 channels.
//
// Features Supported:
// - Protocol: HBM2, HBM2e
// - Channel Mode: PSEUDO_CHANNEL
// - No of Channels : Upto 8 (Channel a-h/0-7)
// - Density: All HBM2 and HBM2e densities
// - Burst Length: 4
// - Mode Registers
// - COL Commands: RD, RDA, WR, WRA, MRS
// - ROW Commands: ACT, PRE, PREA, REF, REFSB
// - Data Mask(DM) for Write DQ
// - Bank Groups Enabled/Disabled
// - MRS registers update via Parameters (Responder specific feature)
// - Memory Array Initialization: Initialize to 0 or 1 or random data. (Responder specific feature)
// - Inter Reset
// - Invalid MRS register programming check
//
// Features Not Supported:
// - Channel Mode: LEGACY
// - Burst Length: 2
// - DBI
// - ECC
// - Cmd/Data Parity Check
// - Power Down Entry/Exit
// - Self Refresh Entry/Exit
// - Timing Violation Checks
// - Redundant Data
// - Clock Frequency Change
// - Temperature Compensated Refresh Reporting
// - TRR
// - Loopback Test Mode
// - Direct Acees Test
// - IEEE Standard 1500 Test
// - Memory Array Initialization: Initialize using File Input (Responder specific feature)
//
//////////////////////////////////////////////////////////////////////

//`include "hbm_responder_defines.svh"
//`include "hbm_responder_if.sv"

`timescale 1ps/1ps
module HBM#(
  //========================================
  // HBM Device configuration Settings
  //========================================
  parameter   C_HBM_VERSION                       = "HBM2"
                                                        // options are: HBM2, HBM2e
                                                        // Future support: HBM3
  ,parameter   C_HBM_CHANNEL_MODE                 = "PSEUDO_CHANNEL"
                                                        // options are: PSEUDO_CHANNEL
                                                        // Future support: LEGACY
  ,parameter  C_HBM_DENSITY_CONFIG                = "8G8H"
                                                        //------------------------------------------------------------
                                                        //  options   Density   Description 
                                                        //            Code      
                                                        //------------------------------------------------------------
                                                        //  2G4H      0010      2Gb per Channel (1Gb per PC) and 4-High (RA[13:0], CA[5:1], BA[2:0])
                                                        //                      i.e. 2Gb/8=0.25GB per Channel, total of 2GB density (for 8 Channels)
                                                        //------------------------------------------------------------
                                                        //  4G4H      0011      4Gb per Channel (2Gb per PC) and 4-High (RA[13:0], CA[5:1], BA[3:0])
                                                        //                      i.e. 4Gb/8=0.5GB per Channel, total of 4GB density (for 8 Channels)
                                                        //------------------------------------------------------------
                                                        //  6G4H      0101      6Gb per Channel (3Gb per PC) and 4-High (RA[14:0], CA[5:1], BA[3:0])
                                                        //                      RA[14:13] = 11 is invalid
                                                        //                      i.e. 6Gb/8=0.75GB per Channel, total of 6GB density (for 8 Channels)
                                                        //------------------------------------------------------------
                                                        //  8G4H      0110      8Gb per Channel (4Gb per PC) and 4-High (RA[14:0], CA[5:1], BA[3:0])
                                                        //                      i.e. 8Gb/8=1GB per Channel, total of 8GB density (for 8 Channels)
                                                        //------------------------------------------------------------
                                                        //  8G8H      0100      8Gb per Channel (4Gb per PC) and 8-High (RA[13:0], CA[5:1], SID, BA[3:0])
                                                        //                      i.e. 8Gb/8=1GB per Channel, total of 8GB density (for 8 Channels)
                                                        //------------------------------------------------------------
                                                        //  8G12H     1001      8Gb per Channel (4Gb per PC) and 12-High (RA[13:0], CA[5:1], SID[1:0], BA[3:0])
                                                        //                      SID[1:0] = 11 is invalid
                                                        //                      i.e. 8Gb/8=1GB per Channel, total of 8GB density (for 8 Channels)
                                                        //------------------------------------------------------------
                                                        //  12G8H     1000      12Gb per Channel (6Gb per PC) and 8-High (RA[14:0], CA[5:1], SID, BA[3:0]) 
                                                        //                      RA[14:13] = 11 is invalid
                                                        //                      i.e. 12Gb/8=1.5GB per Channel, total of 12GB density (for 8 Channels)
                                                        //------------------------------------------------------------
                                                        //  12G12H    1011      12Gb per Channel (6Gb per PC) and 12-High (RA[14:0], CA[5:1], SID[1:0], BA[3:0])
                                                        //                      RA[14:13] = 11 is invalid
                                                        //                      SID[1:0] = 11 is invalid
                                                        //                      i.e. 12Gb/8=1.5GB per Channel, total of 12GB density (for 8 Channels)
                                                        //------------------------------------------------------------
                                                        //  16G8H     1010      16Gb per Channel (8Gb per PC) and 8-High (RA[14:0], CA[5:1], SID, BA[3:0])
                                                        //                      i.e. 16Gb/8=2GB per Channel, total of 16GB density (for 8 Channels)
                                                        //------------------------------------------------------------
                                                        //  16G12H    1110      16Gb per Channel (8Gb per PC) and 12-High (RA[14:0], CA[5:1], SID[1:0], BA[3:0])
                                                        //                      SID[1:0] = 11 is invalid
                                                        //                      i.e. 16Gb/8=2GB per Channel, total of 16GB density (for 8 Channels)
                                                        //------------------------------------------------------------
  ,parameter  C_HBM_NO_OF_CHANNEL                 = 8
  ,parameter  C_HBM_NO_OF_PC                      = C_HBM_CHANNEL_MODE == "PSEUDO_CHANNEL" ? 2 : 1

  //========================================
  // HBM DRAM Sigals Width 
  //========================================
  ,parameter  C_HBM_BURST_DATA_WIDTH              = 256 // No_of_burst(BL)xDQ_Width_Per_beat= 4x64= 256
  ,parameter  C_HBM_SID_ADDR_WIDTH                = C_HBM_DENSITY_CONFIG inside {"8G8H", "12G8H", "16G8H"}    ? 1 /*8H*/  : 
                                                    C_HBM_DENSITY_CONFIG inside {"8G12H", "12G12H", "16G12H"} ? 2 /*12H*/ : 0/*4H*/
  ,parameter  C_HBM_BANKGROUP_ADDR_WIDTH          = 2
  ,parameter  C_HBM_BANK_ADDR_WIDTH               = C_HBM_DENSITY_CONFIG == "2G4H" ? 1 : 2 
  ,parameter  C_HBM_ROW_ADDR_WIDTH                = C_HBM_DENSITY_CONFIG inside {"6G4H", "8G4H", "12G8H", "12G12H", "16G8H", "16G12H"} ? 15 : 14
  ,parameter  C_HBM_COL_ADDR_WIDTH                = 5
  ,parameter  C_HBM_BANKPERSID_ADDR_WIDTH         = C_HBM_BANKGROUP_ADDR_WIDTH + C_HBM_BANK_ADDR_WIDTH
  ,parameter  C_HBM_ALLBANKS_ADDR_WIDTH           = C_HBM_SID_ADDR_WIDTH + C_HBM_BANKGROUP_ADDR_WIDTH + C_HBM_BANK_ADDR_WIDTH
  ,parameter  C_HBM_PAGE_ADDR_WIDTH               = C_HBM_ALLBANKS_ADDR_WIDTH + 1/*1bit for PC indicator*/
  ,parameter  C_HBM_MEM_ADDR_WIDTH                = C_HBM_PAGE_ADDR_WIDTH + C_HBM_ROW_ADDR_WIDTH + C_HBM_COL_ADDR_WIDTH
  ,parameter  C_HBM_NO_OF_BANKS                   = 2**C_HBM_ALLBANKS_ADDR_WIDTH
  
  //========================================
  // HBM DRAM Mode Registers Settings
  //========================================
  ,parameter  C_HBM_MRS_BURST_LENGTH              = 4
  ,parameter  C_HBM_MRS_READ_LATENCY              = 14
  ,parameter  C_HBM_MRS_WRITE_LATENCY             = 12
  ,parameter  C_HBM_MRS_PARITY_LATENCY            = 3
  ,parameter  C_HBM_MRS_CMD_PARITY_EN             = 0
  ,parameter  C_HBM_MRS_DQ_WRITE_PARITY_EN        = 0
  ,parameter  C_HBM_MRS_DQ_READ_PARITY_EN         = 0
  ,parameter  C_HBM_MRS_DBI_WRITE_EN              = 0 // As per Jedec spec, the default value is 1
  ,parameter  C_HBM_MRS_DBI_READ_EN               = 0 // As per Jedec spec, the default value is 1
  ,parameter  C_HBM_MRS_BANK_GROUP_EN             = 1
  ,parameter  C_HBM_MRS_WRITE_DM_EN               = 0
  ,parameter  C_HBM_MRS_WRITE_ECC_EN              = 0
  ,parameter  C_HBM_MRS_WRITE_RECOVERY            = 7
  ,parameter  C_HBM_MRS_RAS                       = 33
  ,parameter  C_HBM_MRS_IMPRE_TRP                 = 0
  
  //========================================
  // HBM DRAM Timing parameters
  //========================================
  ,parameter  C_HBM_TCK                           = 625 
                                                        // Speed bins are, 3.2GT/s, TCK= 625ps
                                                        //                 2.8GT/s, TCK= 714ps (714.2857)
                                                        //                 2.4GT/s, TCK= 833ps (833.3333)
                                                        //                 2.0GT/s, TCK= 1000ps
                                                        //                 1.6GT/s, TCK= 1250ps
                                                        //                 1.0GT/s, TCK= 2000ps
  ,parameter  C_HBM_TDQSCK                        = 1.5   
                                                        // RDQS rising edge output access time from CK rising edge
                                                        // in ns 0.6 to 3.5
  ,parameter  C_HBM_TDQSQ                         = 0   
                                                        // RDQS edge to DQ, DBI skew
                                                        // in ps  none to 53
  ,parameter  C_HBM_TDQSS                         = 0   
                                                        // WDQS rising edge to CK rising edge delay
                                                        // in tck -0.2 to 0.2
  ,parameter  C_HBM_TRCD_RD                       = 6'h0E
  ,parameter  C_HBM_TRCD_WR                       = 6'h10
  ,parameter  C_HBM_TCCD_R                        = 6'h04
  ,parameter  C_HBM_TCCD_L                        = 6'h04
  ,parameter  C_HBM_TCCD_S                        = 6'h02
  ,parameter  C_HBM_TCKESR                        = 10'h006
  ,parameter  C_HBM_TFAW_L                        = 6'h0C
  ,parameter  C_HBM_TFAW_S                        = 6'h0C
  ,parameter  C_HBM_TINIT0                        = 10'h0C8
  ,parameter  C_HBM_TINIT1                        = 10'h0C8
  ,parameter  C_HBM_TINIT2                        = 10'h0C8
  ,parameter  C_HBM_TINIT3                        = 10'h0C8
  ,parameter  C_HBM_TINIT4                        = 10'h0C8
  ,parameter  C_HBM_TINIT5                        = 10'h0C8
  ,parameter  C_HBM_TINIT6                        = 10
                                                        // in ns
  ,parameter  C_HBM_TMOD                          = 10'h00F
  ,parameter  C_HBM_TMRD                          = 10'h008
  ,parameter  C_HBM_TRAS                          = 6'h21
  ,parameter  C_HBM_TRC                           = 7'h2D
  ,parameter  C_HBM_TREFI                         = 16'h0F3C
  ,parameter  C_HBM_TRFC                          = 12'h15E
  ,parameter  C_HBM_TRFCSB                        = 12'h0A0
  ,parameter  C_HBM_TRP                           = 6'h15
  ,parameter  C_HBM_TRRD_L                        = 6'h04
  ,parameter  C_HBM_TRRD_S                        = 6'h04
  ,parameter  C_HBM_TRREFD                        = 6'h08
  ,parameter  C_HBM_TRTP                          = 6'h05
  ,parameter  C_HBM_TRTW                          = 6'h1C
  ,parameter  C_HBM_TWTR_L                        = 6'h08
  ,parameter  C_HBM_TWTR_S                        = 6'h04
  ,parameter  C_HBM_TXP                           = 27'h1220008
  ,parameter  C_HBM_TXS                           = 27'h1220008
  ,parameter  C_HBM_TWR                           = 5'h07
  ,parameter  C_HBM_TWTP                          = 6'h10

  //========================================
  // HBM Responder Specific Add-On features
  //========================================
  ,parameter  C_HBM_MEM_INIT_MODE                 = "INIT_0"
                                                        // options are INIT_0, INIT_1, INIT_RANDOM
                                                        // Future support : INIT_FILE
  ,parameter  C_HBM_RDATA_ERR_INJ_MODE            = "DISABLED"
                                                        // DISABLED, FILE_ERR, RANDOM_1BIT_ERR, RANDOM_2BIT_ERR, RANDOM_BITS_ERR
  ,parameter  C_HBM_TIMING_CHECK_EN               = 0
  ,parameter  C_HBM_VERBOSITY_EN                  = 0
)
(
  // Global Signals
  input                   RESET_n           // Asynchronous Active Low reset 
  ,input                  TEMP0             // Temperature compensated Refresh
  ,input                  TEMP1             // Temperature compensated Refresh
  ,input                  TEMP2             // Temperature compensated Refresh
  ,input                  CATTRIP           // Catastrophic Temperature Sensor
  ,inout  [59:0]          DA                // Direct Access Test port
  ,input                  WRCK              // IEEE-1500 Wrapper Serial Port Clock 
  ,input                  WRST_n            // IEEE-1500 Wrapper Serial Port Reset
  ,input                  SelectWIR         // IEEE-1500 Wrapper Serial Port Instruction Register Select
  ,input                  ShiftWR           // IEEE-1500 Wrapper Serial Port Shift
  ,input                  CaptureWR         // IEEE-1500 Wrapper Serial Port Capture
  ,input                  UpdateWR          // IEEE-1500 Wrapper Serial Port Update
  ,input                  WSI               // IEEE-1500 Wrapper Serial Port Data
  ,output [7:0]           WSO               // IEEE-1500 Wrapper Serial Port Data Out // NOTE: This is not global signal, WSO[7:0] is mapped to channel as WSO[a:h]

  // Channel-A Signals
  ,input                  ck_t_CHA      // diffrential clock(true) for address channel
  ,input   	              ck_c_CHA      // diffrential clock(comp) for address channel
  ,input   	              cke_CHA       // clock enable
  ,input  [(C_HBM_VERSION == "HBM2" ? 5 : 6)  : 0]        r_CHA         // row address                     // 6:0 incase of HBM2e, 5:0 incase of HBM2
  ,input  [(C_HBM_VERSION == "HBM2" ? 7 : 8)  : 0]        c_CHA         // column address                  // 8:0 incase of HBM2e, 7:0 incase of HBM2
  ,inout  [3  : 0]        par_CHA       // write/read data parity          // 1 PAR per 32 DQs
  ,inout  [15 : 0]        dm_CHA        // write/read data mask            // 1 DM per 8DQs
  ,inout  [15 : 0]        dbi_CHA       // write/read data byte inversion  // 1 DBI per 8DQs
  ,inout  [127: 0]        dq_CHA        // write/read DQ data
  ,input  [3  : 0]        wdqs_t_CHA    // write DQ data strobe            // 1 WDQS_t per 32DQs
  ,input  [3  : 0]        wdqs_c_CHA    // write DQ data strobe            // 1 WDQS_c per 32DQs
  ,output [3  : 0]        rdqs_t_CHA    // read DQ data strobe             // 1 RDQS_t per 32DQs
  ,output [3  : 0]        rdqs_c_CHA    // read DQ data strobe             // 1 RDQS_c per 32DQs
  ,output [3  : 0]        derr_CHA      // write data parity error         // 1 DERR per 32 DQs
  ,output                 aerr_CHA      // address parity error
  ,input                  rr_CHA        // reduntant row address pin for remapping 
  ,input                  rc_CHA        // reduntant column address pin for remapping
  ,inout  [7  : 0]        rd_CHA        // reduntant write/read data pin for remapping

  // Channel-B Signals
  ,input                  ck_t_CHB      // diffrential clock(true) for address channel
  ,input   	              ck_c_CHB      // diffrential clock(comp) for address channel
  ,input   	              cke_CHB       // clock enable
  ,input  [(C_HBM_VERSION == "HBM2" ? 5 : 6)  : 0]        r_CHB         // row address                     // 6:0 incase of HBM2e, 5:0 incase of HBM2
  ,input  [(C_HBM_VERSION == "HBM2" ? 7 : 8)  : 0]        c_CHB         // column address                  // 8:0 incase of HBM2e, 7:0 incase of HBM2
  ,inout  [3  : 0]        par_CHB       // write/read data parity          // 1 PAR per 32 DQs
  ,inout  [15 : 0]        dm_CHB        // write/read data mask            // 1 DM per 8DQs
  ,inout  [15 : 0]        dbi_CHB       // write/read data byte inversion  // 1 DBI per 8DQs
  ,inout  [127: 0]        dq_CHB        // write/read DQ data
  ,input  [3  : 0]        wdqs_t_CHB    // write DQ data strobe            // 1 WDQS_t per 32DQs
  ,input  [3  : 0]        wdqs_c_CHB    // write DQ data strobe            // 1 WDQS_c per 32DQs
  ,output [3  : 0]        rdqs_t_CHB    // read DQ data strobe             // 1 RDQS_t per 32DQs
  ,output [3  : 0]        rdqs_c_CHB    // read DQ data strobe             // 1 RDQS_c per 32DQs
  ,output [3  : 0]        derr_CHB      // write data parity error         // 1 DERR per 32 DQs
  ,output                 aerr_CHB      // address parity error
  ,input                  rr_CHB        // reduntant row address pin for remapping 
  ,input                  rc_CHB        // reduntant column address pin for remapping
  ,inout  [7  : 0]        rd_CHB        // reduntant write/read data pin for remapping

  // Channel-C Signals
  ,input                  ck_t_CHC      // diffrential clock(true) for address channel
  ,input   	              ck_c_CHC      // diffrential clock(comp) for address channel
  ,input   	              cke_CHC       // clock enable
  ,input  [(C_HBM_VERSION == "HBM2" ? 5 : 6)  : 0]        r_CHC         // row address                     // 6:0 incase of HBM2e, 5:0 incase of HBM2
  ,input  [(C_HBM_VERSION == "HBM2" ? 7 : 8)  : 0]        c_CHC         // column address                  // 8:0 incase of HBM2e, 7:0 incase of HBM2
  ,inout  [3  : 0]        par_CHC       // write/read data parity          // 1 PAR per 32 DQs
  ,inout  [15 : 0]        dm_CHC        // write/read data mask            // 1 DM per 8DQs
  ,inout  [15 : 0]        dbi_CHC       // write/read data byte inversion  // 1 DBI per 8DQs
  ,inout  [127: 0]        dq_CHC        // write/read DQ data
  ,input  [3  : 0]        wdqs_t_CHC    // write DQ data strobe            // 1 WDQS_t per 32DQs
  ,input  [3  : 0]        wdqs_c_CHC    // write DQ data strobe            // 1 WDQS_c per 32DQs
  ,output [3  : 0]        rdqs_t_CHC    // read DQ data strobe             // 1 RDQS_t per 32DQs
  ,output [3  : 0]        rdqs_c_CHC    // read DQ data strobe             // 1 RDQS_c per 32DQs
  ,output [3  : 0]        derr_CHC      // write data parity error         // 1 DERR per 32 DQs
  ,output                 aerr_CHC      // address parity error
  ,input                  rr_CHC        // reduntant row address pin for remapping 
  ,input                  rc_CHC        // reduntant column address pin for remapping
  ,inout  [7  : 0]        rd_CHC        // reduntant write/read data pin for remapping

  // Channel-D Signals
  ,input                  ck_t_CHD      // diffrential clock(true) for address channel
  ,input   	              ck_c_CHD      // diffrential clock(comp) for address channel
  ,input   	              cke_CHD       // clock enable
  ,input  [(C_HBM_VERSION == "HBM2" ? 5 : 6)  : 0]        r_CHD         // row address                     // 6:0 incase of HBM2e, 5:0 incase of HBM2
  ,input  [(C_HBM_VERSION == "HBM2" ? 7 : 8)  : 0]        c_CHD         // column address                  // 8:0 incase of HBM2e, 7:0 incase of HBM2
  ,inout  [3  : 0]        par_CHD       // write/read data parity          // 1 PAR per 32 DQs
  ,inout  [15 : 0]        dm_CHD        // write/read data mask            // 1 DM per 8DQs
  ,inout  [15 : 0]        dbi_CHD       // write/read data byte inversion  // 1 DBI per 8DQs
  ,inout  [127: 0]        dq_CHD        // write/read DQ data
  ,input  [3  : 0]        wdqs_t_CHD    // write DQ data strobe            // 1 WDQS_t per 32DQs
  ,input  [3  : 0]        wdqs_c_CHD    // write DQ data strobe            // 1 WDQS_c per 32DQs
  ,output [3  : 0]        rdqs_t_CHD    // read DQ data strobe             // 1 RDQS_t per 32DQs
  ,output [3  : 0]        rdqs_c_CHD    // read DQ data strobe             // 1 RDQS_c per 32DQs
  ,output [3  : 0]        derr_CHD      // write data parity error         // 1 DERR per 32 DQs
  ,output                 aerr_CHD      // address parity error
  ,input                  rr_CHD        // reduntant row address pin for remapping 
  ,input                  rc_CHD        // reduntant column address pin for remapping
  ,inout  [7  : 0]        rd_CHD        // reduntant write/read data pin for remapping

  // Channel-E Signals
  ,input                  ck_t_CHE      // diffrential clock(true) for address channel
  ,input   	              ck_c_CHE      // diffrential clock(comp) for address channel
  ,input   	              cke_CHE       // clock enable
  ,input  [(C_HBM_VERSION == "HBM2" ? 5 : 6)  : 0]        r_CHE         // row address                     // 6:0 incase of HBM2e, 5:0 incase of HBM2
  ,input  [(C_HBM_VERSION == "HBM2" ? 7 : 8)  : 0]        c_CHE         // column address                  // 8:0 incase of HBM2e, 7:0 incase of HBM2
  ,inout  [3  : 0]        par_CHE       // write/read data parity          // 1 PAR per 32 DQs
  ,inout  [15 : 0]        dm_CHE        // write/read data mask            // 1 DM per 8DQs
  ,inout  [15 : 0]        dbi_CHE       // write/read data byte inversion  // 1 DBI per 8DQs
  ,inout  [127: 0]        dq_CHE        // write/read DQ data
  ,input  [3  : 0]        wdqs_t_CHE    // write DQ data strobe            // 1 WDQS_t per 32DQs
  ,input  [3  : 0]        wdqs_c_CHE    // write DQ data strobe            // 1 WDQS_c per 32DQs
  ,output [3  : 0]        rdqs_t_CHE    // read DQ data strobe             // 1 RDQS_t per 32DQs
  ,output [3  : 0]        rdqs_c_CHE    // read DQ data strobe             // 1 RDQS_c per 32DQs
  ,output [3  : 0]        derr_CHE      // write data parity error         // 1 DERR per 32 DQs
  ,output                 aerr_CHE      // address parity error
  ,input                  rr_CHE        // reduntant row address pin for remapping 
  ,input                  rc_CHE        // reduntant column address pin for remapping
  ,inout  [7  : 0]        rd_CHE        // reduntant write/read data pin for remapping

  // Channel-F Signals
  ,input                  ck_t_CHF      // diffrential clock(true) for address channel
  ,input   	              ck_c_CHF      // diffrential clock(comp) for address channel
  ,input   	              cke_CHF       // clock enable
  ,input  [(C_HBM_VERSION == "HBM2" ? 5 : 6)  : 0]        r_CHF         // row address                     // 6:0 incase of HBM2e, 5:0 incase of HBM2
  ,input  [(C_HBM_VERSION == "HBM2" ? 7 : 8)  : 0]        c_CHF         // column address                  // 8:0 incase of HBM2e, 7:0 incase of HBM2
  ,inout  [3  : 0]        par_CHF       // write/read data parity          // 1 PAR per 32 DQs
  ,inout  [15 : 0]        dm_CHF        // write/read data mask            // 1 DM per 8DQs
  ,inout  [15 : 0]        dbi_CHF       // write/read data byte inversion  // 1 DBI per 8DQs
  ,inout  [127: 0]        dq_CHF        // write/read DQ data
  ,input  [3  : 0]        wdqs_t_CHF    // write DQ data strobe            // 1 WDQS_t per 32DQs
  ,input  [3  : 0]        wdqs_c_CHF    // write DQ data strobe            // 1 WDQS_c per 32DQs
  ,output [3  : 0]        rdqs_t_CHF    // read DQ data strobe             // 1 RDQS_t per 32DQs
  ,output [3  : 0]        rdqs_c_CHF    // read DQ data strobe             // 1 RDQS_c per 32DQs
  ,output [3  : 0]        derr_CHF      // write data parity error         // 1 DERR per 32 DQs
  ,output                 aerr_CHF      // address parity error
  ,input                  rr_CHF        // reduntant row address pin for remapping 
  ,input                  rc_CHF        // reduntant column address pin for remapping
  ,inout  [7  : 0]        rd_CHF        // reduntant write/read data pin for remapping

  // Channel-G Signals
  ,input                  ck_t_CHG      // diffrential clock(true) for address channel
  ,input   	              ck_c_CHG      // diffrential clock(comp) for address channel
  ,input   	              cke_CHG       // clock enable
  ,input  [(C_HBM_VERSION == "HBM2" ? 5 : 6)  : 0]        r_CHG         // row address                     // 6:0 incase of HBM2e, 5:0 incase of HBM2
  ,input  [(C_HBM_VERSION == "HBM2" ? 7 : 8)  : 0]        c_CHG         // column address                  // 8:0 incase of HBM2e, 7:0 incase of HBM2
  ,inout  [3  : 0]        par_CHG       // write/read data parity          // 1 PAR per 32 DQs
  ,inout  [15 : 0]        dm_CHG        // write/read data mask            // 1 DM per 8DQs
  ,inout  [15 : 0]        dbi_CHG       // write/read data byte inversion  // 1 DBI per 8DQs
  ,inout  [127: 0]        dq_CHG        // write/read DQ data
  ,input  [3  : 0]        wdqs_t_CHG    // write DQ data strobe            // 1 WDQS_t per 32DQs
  ,input  [3  : 0]        wdqs_c_CHG    // write DQ data strobe            // 1 WDQS_c per 32DQs
  ,output [3  : 0]        rdqs_t_CHG    // read DQ data strobe             // 1 RDQS_t per 32DQs
  ,output [3  : 0]        rdqs_c_CHG    // read DQ data strobe             // 1 RDQS_c per 32DQs
  ,output [3  : 0]        derr_CHG      // write data parity error         // 1 DERR per 32 DQs
  ,output                 aerr_CHG      // address parity error
  ,input                  rr_CHG        // reduntant row address pin for remapping 
  ,input                  rc_CHG        // reduntant column address pin for remapping
  ,inout  [7  : 0]        rd_CHG        // reduntant write/read data pin for remapping

  // Channel-H Signals
  ,input                  ck_t_CHH      // diffrential clock(true) for address channel
  ,input   	              ck_c_CHH      // diffrential clock(comp) for address channel
  ,input   	              cke_CHH       // clock enable
  ,input  [(C_HBM_VERSION == "HBM2" ? 5 : 6)  : 0]        r_CHH         // row address                     // 6:0 incase of HBM2e, 5:0 incase of HBM2
  ,input  [(C_HBM_VERSION == "HBM2" ? 7 : 8)  : 0]        c_CHH         // column address                  // 8:0 incase of HBM2e, 7:0 incase of HBM2
  ,inout  [3  : 0]        par_CHH       // write/read data parity          // 1 PAR per 32 DQs
  ,inout  [15 : 0]        dm_CHH        // write/read data mask            // 1 DM per 8DQs
  ,inout  [15 : 0]        dbi_CHH       // write/read data byte inversion  // 1 DBI per 8DQs
  ,inout  [127: 0]        dq_CHH        // write/read DQ data
  ,input  [3  : 0]        wdqs_t_CHH    // write DQ data strobe            // 1 WDQS_t per 32DQs
  ,input  [3  : 0]        wdqs_c_CHH    // write DQ data strobe            // 1 WDQS_c per 32DQs
  ,output [3  : 0]        rdqs_t_CHH    // read DQ data strobe             // 1 RDQS_t per 32DQs
  ,output [3  : 0]        rdqs_c_CHH    // read DQ data strobe             // 1 RDQS_c per 32DQs
  ,output [3  : 0]        derr_CHH      // write data parity error         // 1 DERR per 32 DQs
  ,output                 aerr_CHH      // address parity error
  ,input                  rr_CHH        // reduntant row address pin for remapping 
  ,input                  rc_CHH        // reduntant column address pin for remapping
  ,inout  [7  : 0]        rd_CHH        // reduntant write/read data pin for remapping
);


//////////////////////////////////////////////////////////////////////
// File: hbm_responder_defines.svh 
//
// Descrtiption: 
// This file has all the defines/enums declrations
//////////////////////////////////////////////////////////////////////

`define hbm_warning(TAG, MSG) \
  $warning("[%s] (%m) %0t : WARNING :: %s", TAG, $time, MSG);

`define HBM_VERBOSITY 100 // 0 - HBM_NONE, 100 - HBM_LOW, 200 - HBM_MEDIUM, 300 - HBM_HIGH, 400 - HBM_FULL, 500 - HBM_DEBUG // this define value can be changed from simulator command line argument. for e.g. In vcs simulator, setting +define+HBM_VERBOSITY=500 during compilation will enable all the messages on the testbench
`define hbm_info(TAG, MSG, LEVEL) \
  if(LEVEL <= `HBM_VERBOSITY) \
  $display("INFO: [%s] (%m) %0t : %s", TAG, $time, MSG);

`define hbm_error(TAG, MSG) \
  $error("[%s] (%m) %0t : ERROR :: %s", TAG, $time, MSG);

`define hbm_fatal(TAG, MSG) \
  $fatal(1,"[%s] (%m) %0t : FATAL_ERROR :: %s", TAG, $time, MSG);


`ifndef EN_HBM_RESPONDER_DBG_MODE
typedef enum  bit[8:0]  {HBM_NONE=0, HBM_LOW=100, HBM_MEDIUM=200, HBM_HIGH=300, HBM_FULL=400, HBM_DEBUG=500}      hbm_verbosity_t;
typedef enum  bit[4:0]  {RNOP, ACT, PRE, PREA, REFSB, REF, PDE, SRE, PDX, SRX, CNOP, RD, RDA, WR, WRA, MRS}       hbm_command_t;
`endif
typedef enum  bit[4:0]  {START, CNOP_F1, RNOP_F1, ACT_F1, ACT_R2, ACT_F2, PRE_F1, REF_F1, PDE_F1, SRE_F1, PDX_F1, SRX_F1, WR_F1, RD_F1, WRA_F1, RDA_F1, MRS_F1}   hbm_command_state_t;
typedef enum  bit[3:0]  {RESET, IDLE, CONFIGURE_DEVICE, SELF_REFRESH, PRECHARGE_POWER_DOWN, ACTIVATING, ACTIVE, WRITING, READING, PRECHARGING, ACTIVE_POWER_DOWN, REFRESHING}  hbm_bank_state_t;


//////////////////////////////////////////////////////
// HBM Channel Interface
//////////////////////////////////////////////////////
hbm2_responder_if  CHa_mem_if(ck_t_CHA, RESET_n);
hbm2_responder_if  CHb_mem_if(ck_t_CHB, RESET_n);
hbm2_responder_if  CHc_mem_if(ck_t_CHC, RESET_n);
hbm2_responder_if  CHd_mem_if(ck_t_CHD, RESET_n);
hbm2_responder_if  CHe_mem_if(ck_t_CHE, RESET_n);
hbm2_responder_if  CHf_mem_if(ck_t_CHF, RESET_n);
hbm2_responder_if  CHg_mem_if(ck_t_CHG, RESET_n);
hbm2_responder_if  CHh_mem_if(ck_t_CHH, RESET_n);

// Channel-A signal mapping
assign CHa_mem_if.hbm_ck_t                = ck_t_CHA;
assign CHa_mem_if.hbm_ck_c                = ck_c_CHA;
assign CHa_mem_if.hbm_cke                 = cke_CHA; 
assign CHa_mem_if.hbm_r                   = r_CHA; 
assign CHa_mem_if.hbm_c                   = c_CHA;
assign CHa_mem_if.hbm_par                 = par_CHA; 
assign CHa_mem_if.hbm_dm                  = dm_CHA;
assign CHa_mem_if.hbm_dbi                 = dbi_CHA;
assign CHa_mem_if.hbm_dq                  = dq_CHA; 
assign par_CHA                            = CHa_mem_if.hbm_par_reg; 
assign dm_CHA                             = CHa_mem_if.hbm_dm_reg;
assign dbi_CHA                            = CHa_mem_if.hbm_dbi_reg;
assign dq_CHA                             = CHa_mem_if.hbm_dq_reg; 
assign CHa_mem_if.hbm_wdqs_t              = wdqs_t_CHA;    
assign CHa_mem_if.hbm_wdqs_c              = wdqs_c_CHA;   
assign rdqs_t_CHA                         = CHa_mem_if.hbm_rdqs_t;
assign rdqs_c_CHA                         = CHa_mem_if.hbm_rdqs_c;   
assign derr_CHA                           = CHa_mem_if.hbm_derr; 
assign aerr_CHA                           = CHa_mem_if.hbm_aerr;
assign CHa_mem_if.hbm_rr                  = rr_CHA;       
assign CHa_mem_if.hbm_rc                  = rc_CHA;   
assign CHa_mem_if.hbm_rd                  = rd_CHA;        
assign rd_CHA                             = CHa_mem_if.hbm_rd_reg;        

// Channel-B signal mapping
assign CHb_mem_if.hbm_ck_t                = ck_t_CHB;
assign CHb_mem_if.hbm_ck_c                = ck_c_CHB;
assign CHb_mem_if.hbm_cke                 = cke_CHB; 
assign CHb_mem_if.hbm_r                   = r_CHB; 
assign CHb_mem_if.hbm_c                   = c_CHB;
assign CHb_mem_if.hbm_par                 = par_CHB; 
assign CHb_mem_if.hbm_dm                  = dm_CHB;
assign CHb_mem_if.hbm_dbi                 = dbi_CHB;
assign CHb_mem_if.hbm_dq                  = dq_CHB; 
assign par_CHB                            = CHb_mem_if.hbm_par_reg; 
assign dm_CHB                             = CHb_mem_if.hbm_dm_reg;
assign dbi_CHB                            = CHb_mem_if.hbm_dbi_reg;
assign dq_CHB                             = CHb_mem_if.hbm_dq_reg; 
assign CHb_mem_if.hbm_wdqs_t              = wdqs_t_CHB;    
assign CHb_mem_if.hbm_wdqs_c              = wdqs_c_CHB;   
assign rdqs_t_CHB                         = CHb_mem_if.hbm_rdqs_t;
assign rdqs_c_CHB                         = CHb_mem_if.hbm_rdqs_c;   
assign derr_CHB                           = CHb_mem_if.hbm_derr; 
assign aerr_CHB                           = CHb_mem_if.hbm_aerr;
assign CHb_mem_if.hbm_rr                  = rr_CHB;       
assign CHb_mem_if.hbm_rc                  = rc_CHB;   
assign CHb_mem_if.hbm_rd                  = rd_CHB;        
assign rd_CHB                             = CHb_mem_if.hbm_rd_reg;        

// Channel-C signal mapping
assign CHc_mem_if.hbm_ck_t                = ck_t_CHC;
assign CHc_mem_if.hbm_ck_c                = ck_c_CHC;
assign CHc_mem_if.hbm_cke                 = cke_CHC; 
assign CHc_mem_if.hbm_r                   = r_CHC; 
assign CHc_mem_if.hbm_c                   = c_CHC;
assign CHc_mem_if.hbm_par                 = par_CHC; 
assign CHc_mem_if.hbm_dm                  = dm_CHC;
assign CHc_mem_if.hbm_dbi                 = dbi_CHC;
assign CHc_mem_if.hbm_dq                  = dq_CHC; 
assign par_CHC                            = CHc_mem_if.hbm_par_reg; 
assign dm_CHC                             = CHc_mem_if.hbm_dm_reg;
assign dbi_CHC                            = CHc_mem_if.hbm_dbi_reg;
assign dq_CHC                             = CHc_mem_if.hbm_dq_reg; 
assign CHc_mem_if.hbm_wdqs_t              = wdqs_t_CHC;    
assign CHc_mem_if.hbm_wdqs_c              = wdqs_c_CHC;   
assign rdqs_t_CHC                         = CHc_mem_if.hbm_rdqs_t;
assign rdqs_c_CHC                         = CHc_mem_if.hbm_rdqs_c;   
assign derr_CHC                           = CHc_mem_if.hbm_derr; 
assign aerr_CHC                           = CHc_mem_if.hbm_aerr;
assign CHc_mem_if.hbm_rr                  = rr_CHC;       
assign CHc_mem_if.hbm_rc                  = rc_CHC;   
assign CHc_mem_if.hbm_rd                  = rd_CHC;        
assign rd_CHC                             = CHc_mem_if.hbm_rd_reg;        

// Channel-D signal mapping
assign CHd_mem_if.hbm_ck_t                = ck_t_CHD;
assign CHd_mem_if.hbm_ck_c                = ck_c_CHD;
assign CHd_mem_if.hbm_cke                 = cke_CHD; 
assign CHd_mem_if.hbm_r                   = r_CHD; 
assign CHd_mem_if.hbm_c                   = c_CHD;
assign CHd_mem_if.hbm_par                 = par_CHD; 
assign CHd_mem_if.hbm_dm                  = dm_CHD;
assign CHd_mem_if.hbm_dbi                 = dbi_CHD;
assign CHd_mem_if.hbm_dq                  = dq_CHD; 
assign par_CHD                            = CHd_mem_if.hbm_par_reg; 
assign dm_CHD                             = CHd_mem_if.hbm_dm_reg;
assign dbi_CHD                            = CHd_mem_if.hbm_dbi_reg;
assign dq_CHD                             = CHd_mem_if.hbm_dq_reg; 
assign CHd_mem_if.hbm_wdqs_t              = wdqs_t_CHD;    
assign CHd_mem_if.hbm_wdqs_c              = wdqs_c_CHD;   
assign rdqs_t_CHD                         = CHd_mem_if.hbm_rdqs_t;
assign rdqs_c_CHD                         = CHd_mem_if.hbm_rdqs_c;   
assign derr_CHD                           = CHd_mem_if.hbm_derr; 
assign aerr_CHD                           = CHd_mem_if.hbm_aerr;
assign CHd_mem_if.hbm_rr                  = rr_CHD;       
assign CHd_mem_if.hbm_rc                  = rc_CHD;   
assign CHd_mem_if.hbm_rd                  = rd_CHD;        
assign rd_CHD                             = CHd_mem_if.hbm_rd_reg;        

// Channel-E signal mapping
assign CHe_mem_if.hbm_ck_t                = ck_t_CHE;
assign CHe_mem_if.hbm_ck_c                = ck_c_CHE;
assign CHe_mem_if.hbm_cke                 = cke_CHE; 
assign CHe_mem_if.hbm_r                   = r_CHE; 
assign CHe_mem_if.hbm_c                   = c_CHE;
assign CHe_mem_if.hbm_par                 = par_CHE; 
assign CHe_mem_if.hbm_dm                  = dm_CHE;
assign CHe_mem_if.hbm_dbi                 = dbi_CHE;
assign CHe_mem_if.hbm_dq                  = dq_CHE; 
assign par_CHE                            = CHe_mem_if.hbm_par_reg; 
assign dm_CHE                             = CHe_mem_if.hbm_dm_reg;
assign dbi_CHE                            = CHe_mem_if.hbm_dbi_reg;
assign dq_CHE                             = CHe_mem_if.hbm_dq_reg; 
assign CHe_mem_if.hbm_wdqs_t              = wdqs_t_CHE;    
assign CHe_mem_if.hbm_wdqs_c              = wdqs_c_CHE;   
assign rdqs_t_CHE                         = CHe_mem_if.hbm_rdqs_t;
assign rdqs_c_CHE                         = CHe_mem_if.hbm_rdqs_c;   
assign derr_CHE                           = CHe_mem_if.hbm_derr; 
assign aerr_CHE                           = CHe_mem_if.hbm_aerr;
assign CHe_mem_if.hbm_rr                  = rr_CHE;       
assign CHe_mem_if.hbm_rc                  = rc_CHE;   
assign CHe_mem_if.hbm_rd                  = rd_CHE;        
assign rd_CHE                             = CHe_mem_if.hbm_rd_reg;        

// Channel-F signal mapping
assign CHf_mem_if.hbm_ck_t                = ck_t_CHF;
assign CHf_mem_if.hbm_ck_c                = ck_c_CHF;
assign CHf_mem_if.hbm_cke                 = cke_CHF; 
assign CHf_mem_if.hbm_r                   = r_CHF; 
assign CHf_mem_if.hbm_c                   = c_CHF;
assign CHf_mem_if.hbm_par                 = par_CHF; 
assign CHf_mem_if.hbm_dm                  = dm_CHF;
assign CHf_mem_if.hbm_dbi                 = dbi_CHF;
assign CHf_mem_if.hbm_dq                  = dq_CHF; 
assign par_CHF                            = CHf_mem_if.hbm_par_reg; 
assign dm_CHF                             = CHf_mem_if.hbm_dm_reg;
assign dbi_CHF                            = CHf_mem_if.hbm_dbi_reg;
assign dq_CHF                             = CHf_mem_if.hbm_dq_reg; 
assign CHf_mem_if.hbm_wdqs_t              = wdqs_t_CHF;    
assign CHf_mem_if.hbm_wdqs_c              = wdqs_c_CHF;   
assign rdqs_t_CHF                         = CHf_mem_if.hbm_rdqs_t;
assign rdqs_c_CHF                         = CHf_mem_if.hbm_rdqs_c;   
assign derr_CHF                           = CHf_mem_if.hbm_derr; 
assign aerr_CHF                           = CHf_mem_if.hbm_aerr;
assign CHf_mem_if.hbm_rr                  = rr_CHF;       
assign CHf_mem_if.hbm_rc                  = rc_CHF;   
assign CHf_mem_if.hbm_rd                  = rd_CHF;        
assign rd_CHF                             = CHf_mem_if.hbm_rd_reg;        

// Channel-G signal mapping
assign CHg_mem_if.hbm_ck_t                = ck_t_CHG;
assign CHg_mem_if.hbm_ck_c                = ck_c_CHG;
assign CHg_mem_if.hbm_cke                 = cke_CHG; 
assign CHg_mem_if.hbm_r                   = r_CHG; 
assign CHg_mem_if.hbm_c                   = c_CHG;
assign CHg_mem_if.hbm_par                 = par_CHG; 
assign CHg_mem_if.hbm_dm                  = dm_CHG;
assign CHg_mem_if.hbm_dbi                 = dbi_CHG;
assign CHg_mem_if.hbm_dq                  = dq_CHG; 
assign par_CHG                            = CHg_mem_if.hbm_par_reg; 
assign dm_CHG                             = CHg_mem_if.hbm_dm_reg;
assign dbi_CHG                            = CHg_mem_if.hbm_dbi_reg;
assign dq_CHG                             = CHg_mem_if.hbm_dq_reg; 
assign CHg_mem_if.hbm_wdqs_t              = wdqs_t_CHG;    
assign CHg_mem_if.hbm_wdqs_c              = wdqs_c_CHG;   
assign rdqs_t_CHG                         = CHg_mem_if.hbm_rdqs_t;
assign rdqs_c_CHG                         = CHg_mem_if.hbm_rdqs_c;   
assign derr_CHG                           = CHg_mem_if.hbm_derr; 
assign aerr_CHG                           = CHg_mem_if.hbm_aerr;
assign CHg_mem_if.hbm_rr                  = rr_CHG;       
assign CHg_mem_if.hbm_rc                  = rc_CHG;   
assign CHg_mem_if.hbm_rd                  = rd_CHG;        
assign rd_CHG                             = CHg_mem_if.hbm_rd_reg;        

// Channel-H signal mapping
assign CHh_mem_if.hbm_ck_t                = ck_t_CHH;
assign CHh_mem_if.hbm_ck_c                = ck_c_CHH;
assign CHh_mem_if.hbm_cke                 = cke_CHH; 
assign CHh_mem_if.hbm_r                   = r_CHH; 
assign CHh_mem_if.hbm_c                   = c_CHH;
assign CHh_mem_if.hbm_par                 = par_CHH; 
assign CHh_mem_if.hbm_dm                  = dm_CHH;
assign CHh_mem_if.hbm_dbi                 = dbi_CHH;
assign CHh_mem_if.hbm_dq                  = dq_CHH; 
assign par_CHH                            = CHh_mem_if.hbm_par_reg; 
assign dm_CHH                             = CHh_mem_if.hbm_dm_reg;
assign dbi_CHH                            = CHh_mem_if.hbm_dbi_reg;
assign dq_CHH                             = CHh_mem_if.hbm_dq_reg; 
assign CHh_mem_if.hbm_wdqs_t              = wdqs_t_CHH;    
assign CHh_mem_if.hbm_wdqs_c              = wdqs_c_CHH;   
assign rdqs_t_CHH                         = CHh_mem_if.hbm_rdqs_t;
assign rdqs_c_CHH                         = CHh_mem_if.hbm_rdqs_c;   
assign derr_CHH                           = CHh_mem_if.hbm_derr; 
assign aerr_CHH                           = CHh_mem_if.hbm_aerr;
assign CHh_mem_if.hbm_rr                  = rr_CHH;       
assign CHh_mem_if.hbm_rc                  = rc_CHH;   
assign CHh_mem_if.hbm_rd                  = rd_CHH;        
assign rd_CHH                             = CHh_mem_if.hbm_rd_reg;        

assign WSO                                = 8'hFF; // IEEE-1500 Wrapper Serial Port is not supported. Drive always 1 to make it work with ULTRASCALE HOOD HBM2 MC RTL


//`include "hbm_responder_class.sv"
//////////////////////////////////////////////////////////////////////
// File: hbm_responder_class.sv 
//
// Descrtiption:
// This is the main/core implementation class for hbm responder
//////////////////////////////////////////////////////////////////////
class hbm_responder_class;

string                TAG                     = "HBM_RESPONDER_CLASS";

int signed            TCK                     = 0;
//FIXME add timing parameter print logic

// Memory Arrays
bit [C_HBM_BURST_DATA_WIDTH-1:0]  hbm_memory [bit[C_HBM_MEM_ADDR_WIDTH-1:0]]; // HBM Memory Array
bit [C_HBM_ROW_ADDR_WIDTH-1:0]    hbm_memory_page_table [C_HBM_NO_OF_PC][bit[C_HBM_PAGE_ADDR_WIDTH-1:0]]; // Page Table to store open bank details

// Memory Interface
virtual interface           hbm2_responder_if mem_vif;

// MRS Command Register Variables
bit                         reg_mr0_test_mode               = 0;
bit                         reg_mr0_add_cmd_parity          = C_HBM_MRS_CMD_PARITY_EN;
bit                         reg_mr0_dq_write_parity         = C_HBM_MRS_DQ_WRITE_PARITY_EN;
bit                         reg_mr0_dq_read_parity          = C_HBM_MRS_DQ_READ_PARITY_EN;
bit                         reg_mr0_tcsr                    = 1; // Temperature Compensated Self Refresh
bit                         reg_mr0_dbi_ac_write            = C_HBM_MRS_DBI_WRITE_EN;
bit                         reg_mr0_dbi_ac_read             = C_HBM_MRS_DBI_READ_EN;

bit [2:0]                   reg_mr1_driver_strength         = 0;
bit [4:0]                   reg_mr1_write_recovery          = C_HBM_MRS_WRITE_RECOVERY; // NOTE: Default value is not specified on spec. might use timing param value or user value

bit [4:0]                   reg_mr2_read_latency            = 0; // NOTE: Default value is not specified on spec. might use timing param value or user value //FIXME
bit [2:0]                   reg_mr2_write_latency           = 0; // NOTE: Default value is not specified on spec. might use timing param value or user value //FIXME
int                         reg_mr2_read_latency_dc         = C_HBM_MRS_READ_LATENCY; // decoded value
int                         reg_mr2_write_latency_dc        = C_HBM_MRS_WRITE_LATENCY; // decoded value

bit                         reg_mr3_burst_length            = 0; // NOTE: Default value is not specified on spec. might use user value
int                         reg_mr3_burst_length_dc         = C_HBM_MRS_BURST_LENGTH; // decoded value
bit                         reg_mr3_bank_group              = 1; 
bit [5:0]                   reg_mr3_ras                     = C_HBM_MRS_RAS; // NOTE: Default value is not specified on spec. might use timing param value

bit                         reg_mr4_ext_read_latency        = 0;
bit                         reg_mr4_ext_write_latency       = 0;
bit [1:0]                   reg_mr4_parity_latency          = C_HBM_MRS_PARITY_LATENCY; // NOTE: Default value is not specified on spec. might use timing param value or user value //FIXME
bit                         reg_mr4_dm                      = 0; // NOTE: Default value is not specified on spec. might use user value
bit                         reg_mr4_dm_en                   = C_HBM_MRS_WRITE_DM_EN; // NOTE: Default value is not specified on spec. might use user value
bit                         reg_mr4_ecc                     = C_HBM_MRS_WRITE_ECC_EN; // NOTE: Default value is not specified on spec. might use user value
// FIXME add checker for "DM and ECC can      not be enabled simultaneously". i.e., OP[1:0] = 01 is not allowed.

bit                         reg_mr5_trr                     = 0;
bit                         reg_mr5_trr_pc_select           = 0; // NOTE 1 Only applicable when MR5 OP[7] = 1. NOTE 2 Only applicable when DEVICE_ID Wrapper Data Register bits [17:16] = 01.
bit [3:0]                   reg_mr5_trr_mode_ba             = 0; // NOTE: Default value is not specified on spec. might use user value

bit [4:0]                   reg_mr6_imPRE_tRP_value         = 0; // NOTE: Default value is not specified on spec. might use timing param value or user value //FIXME
int                         reg_mr6_imPRE_tRP_value_dc      = C_HBM_MRS_IMPRE_TRP; // NOTE: Default value is not specified on spec. might use timing param value or user value //FIXME
//NOTE 2 imPRE is only available inPseudo Channel mode. DEVICE_ID Wrapper Data Register bits [17:16] = 01.

bit                         reg_mr7_cattrip                 = 0; // NOTE 1 The CATTRIP pin can be asserted to “1” from any of the channels [a:h] MR7 [OP7] bit (logic OR).
bit [2:0]                   reg_mr7_misr_control            = 0; // NOTE: Default value is not specified on spec. might use user value // Only applicable if Loopback is enabled in OP[0]
bit [1:0]                   reg_mr7_read_mux_control        = 1;
bit                         reg_mr7_loopback                = 0;

bit                         reg_mr8_da28_lockout            = 0; // NOTE 1 DA[28] lockout is defined for channels a and e only. Once enabled, the DA[28] lockout can only be cleared when power is removed. The bit is also not accessible via IEEE1500 instruction MODE_REGISTER_DUMP_SET

bit [2:0]                   reg_mr15_opt_int_vref           = 0; // NOTE: Default value is not specified on spec. might use user value

string                      reg_mr0_test_mode_ascii         = "";
string                      reg_mr0_add_cmd_parity_ascii    = "";
string                      reg_mr0_dq_write_parity_ascii   = "";
string                      reg_mr0_dq_read_parity_ascii    = "";
string                      reg_mr0_tcsr_ascii              = "";
string                      reg_mr0_dbi_ac_write_ascii      = "";
string                      reg_mr0_dbi_ac_read_ascii       = "";

string                      reg_mr1_driver_strength_ascii   = "";
string                      reg_mr1_write_recovery_ascii    = "";

string                      reg_mr2_read_latency_ascii      = "";
string                      reg_mr2_write_latency_ascii     = "";

string                      reg_mr3_burst_length_ascii      = "";
string                      reg_mr3_bank_group_ascii        = "";
string                      reg_mr3_ras_ascii               = "";

string                      reg_mr4_ext_read_latency_ascii  = "";
string                      reg_mr4_ext_write_latency_ascii = "";
string                      reg_mr4_parity_latency_ascii    = "";
string                      reg_mr4_dm_ascii                = "";
string                      reg_mr4_ecc_ascii               = "";

string                      reg_mr5_trr_ascii               = "";
string                      reg_mr5_trr_pc_select_ascii     = "";
string                      reg_mr5_trr_mode_ba_n_ascii     = "";

string                      reg_mr6_imPRE_tRP_value_ascii   = "";

string                      reg_mr7_cattrip_ascii           = "";
string                      reg_mr7_misr_control_ascii      = "";
string                      reg_mr7_read_mux_control_ascii  = "";
string                      reg_mr7_loopback_ascii          = "";

string                      reg_mr8_da28_lockout_ascii      = "";

string                      reg_mr15_opt_int_vref_ascii     = "";


// Column Command Variables
hbm_command_state_t         col_state                       = START;

hbm_command_t               col_cmd_symbol                  = CNOP;
bit [3:0]                   col_cmd                         = 0; 
bit [5:0]                   col_addr                        = 0; 
bit [3:0]                   col_ba                          = 0;
bit [1:0]                   col_sid                         = 0;
bit                         col_pc                          = 0;
bit [7:0]                   col_mrs_op                      = 0;
bit [14:0]                  col_row                         = 0;
bit                         col_par                         = 0; // FIXME need to add cmd parity check
bit [31:0]                  col_mem_addr                    = 0; // concatenated addr of column command of pc, sid, bg, bank, activated row and colum addr
bit                         valid_col_cmd                   = 0;

// Row Command Variables
hbm_command_state_t         row_state                       = START;

hbm_command_t               row_cmd_symbol                  = RNOP;
bit [2:0]                   row_cmd                         = 0;
bit [14:0]                  row_addr                        = 0;
bit [3:0]                   row_ba                          = 0;
bit [1:0]                   row_sid                         = 0;
bit                         row_pc                          = 0;
bit                         row_all                         = 0; // it will be used to indicate whether the row command is PRECHARGE_ALL/REFRESH_ALL
bit                         row_par                         = 0; // FIXME need to add cmd parity check
bit                         valid_row_cmd                   = 0;

bit                         entered_in_power_down_mode      = 0;
bit                         entered_in_self_ref_mode        = 0;

//hbm_bank_state_t            bank_state[C_HBM_NO_OF_BANKS]; // FIXME need to add it for debugging

// Command Counter variables
int                         mrs_cmd_cnt;
int                         wr_cmd_cnt_pc0;
int                         wr_cmd_cnt_pc1;
int                         wra_cmd_cnt_pc0;
int                         wra_cmd_cnt_pc1;
int                         rd_cmd_cnt_pc0;
int                         rd_cmd_cnt_pc1;
int                         rda_cmd_cnt_pc0;
int                         rda_cmd_cnt_pc1;

int                         act_cmd_cnt_pc0;
int                         act_cmd_cnt_pc1;
int                         pre_cmd_cnt_pc0;
int                         pre_cmd_cnt_pc1;
int                         pre_all_cmd_cnt_pc0;
int                         pre_all_cmd_cnt_pc1;
int                         ref_sb_cmd_cnt_pc0;
int                         ref_sb_cmd_cnt_pc1;
int                         ref_cmd_cnt_pc0;
int                         ref_cmd_cnt_pc1;

// Performance status variables
//time                        first_cmd_reg_time_pc0;
//time                        first_cmd_reg_time_pc1;
//time                        last_cmd_reg_time_pc0;
//time                        last_cmd_reg_time_pc1;
//bit                         last_cmd_pc0;
//bit                         last_cmd_pc1;
//int                         dram_deff;
//int                         act_ovhd;
//int                         pre_ovhd;
//int                         ref_ovhd;
//int                         min_lat;
//int                         max_lat;
//int                         avg_lat;

bit                         is_it_por = 1;
bit                         b2b_read_tracker_q[$];


////////////////////////////////////////////////////////////////
// Function Description: run
// 
////////////////////////////////////////////////////////////////
function new(string TAG);
  this.TAG = TAG;
endfunction


////////////////////////////////////////////////////////////////
// Task Description: run
// This main run task 
////////////////////////////////////////////////////////////////
task run();
  fork
    do_reset();
    row_cmd_decoder();
    col_cmd_decoder();
    //memory_timing_check();
  join_none
endtask


////////////////////////////////////////////////////////////////
// Task Description: do_reset 
//
////////////////////////////////////////////////////////////////
task do_reset();
  forever begin
    wait_for_reset_asserted();
    fork
      initialize_vif();
      calc_clk_period();
      row_initialize();
      col_initialize();
      mem_initialize();
    join
  end
endtask


////////////////////////////////////////////////////////////////
// Task Description: initialize_vif 
//
////////////////////////////////////////////////////////////////
task initialize_vif();
  wait_for_tinit6(); 
  mem_vif.hbm_rdqs_t    <=  4'b0;
  mem_vif.hbm_aerr      <=  0;
  mem_vif.hbm_derr      <=  0;
endtask


////////////////////////////////////////////////////////////////
// Task Description: calc_clk_period
// Calculating CK clock period
////////////////////////////////////////////////////////////////
task calc_clk_period();
  time t, t1, t2, t_q[$];

  TCK = 0;

  // wait for reset deasserted
  wait_for_reset_deasserted();

  // wait for cke asserted
  wait_for_cke_posedge();
  
  wait_for_ck_t_posedge();
  
  repeat(10) begin
    t1  = $time;
    wait_for_ck_t_posedge();
    t2  = $time;
    t   = t2-t1;
    t_q.push_back(t);
  end

  t   = t_q.sum()/10; // FIXME is it correct to calculate TCK as average 10 clk period?
  TCK = t;
  `hbm_info(TAG, $sformatf("HBMDBG :: clock period is calculated :: TCK= %0dps", TCK), HBM_DEBUG)
endtask


////////////////////////////////////////////////////////////////
// Task Description: mem_initialize
//
////////////////////////////////////////////////////////////////
task mem_initialize();
  // delete HBM Memory Array
  hbm_memory.delete();
  
  // delete Page Table Array 
  foreach(hbm_memory_page_table[i]) hbm_memory_page_table[i].delete();

  // Initialize the HBM Memory incase of mem_init_mode set to FILE_INIT
  //if(C_HBM_MEM_INIT_MODE == "INIT_FILE") memory_backdoor_init(); 

  // FIXME do we need to initialize entire content, will it slow down simulation?
  // Think about other ideas, for e.g. we can have a extra bit(initialize_bit) on memory array to indicate it has been initialized or not and whenever the unwritten location read is occuring with initialize_bit=0, we will initialize the mem location and set the initialize_bit.
  // And Do we need to load all the file content in the local array or whenever read occurs to the unwritten location shall we read the file? Need to explore it and has to pick method which simulation time friendly.
endtask


////////////////////////////////////////////////////////////////
// Task Description: memory_backdoor_init
//
////////////////////////////////////////////////////////////////
task memory_backdoor_init();
endtask


////////////////////////////////////////////////////////////////
// Task Description: memory_timing_check
//
////////////////////////////////////////////////////////////////
task memory_timing_check();
endtask


////////////////////////////////////////////////////////////////
// Function Description: 
//
////////////////////////////////////////////////////////////////
function bit is_valid_page_addr(input bit pc, input bit[C_HBM_PAGE_ADDR_WIDTH-1:0] page_addr, output bit[C_HBM_ROW_ADDR_WIDTH-1:0] row);
  
  if(hbm_memory_page_table[pc].exists(page_addr)) begin row = hbm_memory_page_table[pc][page_addr]; return 1; end
  else return 0;
endfunction


////////////////////////////////////////////////////////////////
// Function Description: 
//
////////////////////////////////////////////////////////////////
function bit[C_HBM_PAGE_ADDR_WIDTH-1:0] get_page_addr(bit pc, bit [1:0] sid, bit [3:0] ba);
  bit [C_HBM_PAGE_ADDR_WIDTH-1:0] page_addr;

  case(C_HBM_DENSITY_CONFIG)
    "2G4H"      : page_addr = {pc, ba[2:0]};

    "4G4H",
    "6G4H",
    "8G4H"      : page_addr = {pc, ba};

    "8G8H",
    "12G8H",
    "16G8H"     : page_addr = {pc, sid[0], ba}; 

    "8G12H",
    "12G12H",
    "16G12H"    : page_addr = {pc, sid, ba}; 
  endcase
  
  return page_addr;
endfunction


////////////////////////////////////////////////////////////////
// Function Description: 
//
////////////////////////////////////////////////////////////////
function bit[C_HBM_MEM_ADDR_WIDTH-1:0] get_mem_addr(bit pc, bit [1:0] sid, bit [3:0] ba, bit [14:0] row, bit [5:0] col);
  bit [C_HBM_MEM_ADDR_WIDTH-1:0] mem_addr;

  case(C_HBM_DENSITY_CONFIG)
    "2G4H"      : mem_addr = {pc, ba[2:0], row[13:0], col[5:1]};

    "4G4H"      : mem_addr = {pc, ba, row[13:0], col[5:1]};

    "6G4H",
    "8G4H"      : mem_addr = {pc, ba, row, col[5:1]};

    "8G8H"      : mem_addr = {pc, sid[0], ba, row[13:0], col[5:1]};

    "8G12H"     : mem_addr = {pc, sid, ba, row[13:0], col[5:1]};

    "12G8H",
    "16G8H"     : mem_addr = {pc, sid[0], ba, row, col[5:1]};

    "12G12H",
    "16G12H"    : mem_addr = {pc, sid, ba, row, col[5:1]};
  endcase

  return mem_addr;
endfunction


////////////////////////////////////////////////////////////////
// Function Description: 
//
////////////////////////////////////////////////////////////////
function string get_page_info(bit[C_HBM_PAGE_ADDR_WIDTH-1:0] page_addr);
  string page_info;

  case(C_HBM_DENSITY_CONFIG)
    "16G8H",
    "12G8H",
    "8G8H"      : page_info = $sformatf("PC= %0d, SID= 0x%0h, BG= 0x%0h, BANK= 0x%0h, PAGE_ADDR= 0x%0h", page_addr[5], page_addr[4], page_addr[3:2], page_addr[1:0], page_addr);

    "16G12H",
    "12G12H",
    "8G12H"     : page_info = $sformatf("PC= %0d, SID= 0x%0h, BG= 0x%0h, BANK= 0x%0h, PAGE_ADDR= 0x%0h", page_addr[6], page_addr[5:4], page_addr[3:2], page_addr[1:0], page_addr);

    "8G4H",
    "6G4H",
    "4G4H"      : page_info = $sformatf("PC= %0d, BG= 0x%0h, BANK= 0x%0h, PAGE_ADDR= 0x%0h", page_addr[4], page_addr[3:2], page_addr[1:0], page_addr);

    "2G4H"      : page_info = $sformatf("PC= %0d, BG= 0x%0h, BANK= 0x%0h, PAGE_ADDR= 0x%0h", page_addr[3], page_addr[2:1], page_addr[0], page_addr);
  endcase

  return page_info;
endfunction


////////////////////////////////////////////////////////////////
// Function Description: 
//
////////////////////////////////////////////////////////////////
function string get_mem_info(bit[C_HBM_MEM_ADDR_WIDTH-1:0] mem_addr);
  string mem_info;

  case(C_HBM_DENSITY_CONFIG)
    "12G12H",
    "16G12H"    : mem_info = $sformatf("PC= %0d, SID= 0x%0h, BG= 0x%0h, BANK= 0x%0h, ROW= 0x%0h, COL= 0x%0h, MEM_ADDR= 0x%0h", mem_addr[26], mem_addr[25:24], mem_addr[23:22], mem_addr[21:20], mem_addr[19:5], mem_addr[4:0], mem_addr); 

    "12G8H",
    "16G8H"     : mem_info = $sformatf("PC= %0d, SID= 0x%0h, BG= 0x%0h, BANK= 0x%0h, ROW= 0x%0h, COL= 0x%0h, MEM_ADDR= 0x%0h", mem_addr[25], mem_addr[24], mem_addr[23:22], mem_addr[21:20], mem_addr[19:5], mem_addr[4:0], mem_addr); 

    "8G12H"     : mem_info = $sformatf("PC= %0d, SID= 0x%0h, BG= 0x%0h, BANK= 0x%0h, ROW= 0x%0h, COL= 0x%0h, MEM_ADDR= 0x%0h", mem_addr[25], mem_addr[24:23], mem_addr[22:21], mem_addr[20:19], mem_addr[18:5], mem_addr[4:0], mem_addr); 

    "8G8H"      : mem_info = $sformatf("PC= %0d, SID= 0x%0h, BG= 0x%0h, BANK= 0x%0h, ROW= 0x%0h, COL= 0x%0h, MEM_ADDR= 0x%0h", mem_addr[24], mem_addr[23], mem_addr[22:21], mem_addr[20:19], mem_addr[18:5], mem_addr[4:0], mem_addr); 

    "6G4H",
    "8G4H"      : mem_info = $sformatf("PC= %0d, BG= 0x%0h, BANK= 0x%0h, ROW= 0x%0h, COL= 0x%0h, MEM_ADDR= 0x%0h", mem_addr[24], mem_addr[23:22], mem_addr[21:20], mem_addr[19:5], mem_addr[4:0], mem_addr);

    "4G4H"      : mem_info = $sformatf("PC= %0d, BG= 0x%0h, BANK= 0x%0h, ROW= 0x%0h, COL= 0x%0h, MEM_ADDR= 0x%0h", mem_addr[23], mem_addr[22:21], mem_addr[20:19], mem_addr[18:5], mem_addr[4:0], mem_addr);

    "2G4H"      : mem_info = $sformatf("PC= %0d, BG= 0x%0h, BANK= 0x%0h, ROW= 0x%0h, COL= 0x%0h, MEM_ADDR= 0x%0h", mem_addr[22], mem_addr[21:20], mem_addr[19], mem_addr[18:5], mem_addr[4:0], mem_addr);
  endcase

  return mem_info;
endfunction


////////////////////////////////////////////////////////////////
// Task Description: 
//
////////////////////////////////////////////////////////////////
task col_initialize();
  col_cmd             = {mem_vif.hbm_c[0], mem_vif.hbm_c[1], mem_vif.hbm_c[2], mem_vif.hbm_c[3]};
  col_addr            = 0;
  col_ba              = 0;
  col_sid             = 0;
  col_pc              = 0;
  col_mrs_op          = 0;
  col_par             = 0;
  //col_cmd_symbol      = CNOP;
endtask


////////////////////////////////////////////////////////////////
// Task Description: 
//
////////////////////////////////////////////////////////////////
task col_cmd_decoder();
  forever begin
    wait_for_ck_t_edge();
    case(col_state)
      START : begin
          valid_col_cmd       = 0;
          if(mem_vif.hbm_ck_t == 1/*to detect rise edge*/ && mem_vif.cke_valid_cmd == 1) begin
            col_cmd           = {mem_vif.hbm_c[0], mem_vif.hbm_c[1], mem_vif.hbm_c[2], mem_vif.hbm_c[3]};
            
            casex(col_cmd) // Rising 1
              4'b1000   : begin  /*WR*/
                col_ba          = mem_vif.hbm_c[7:4];
                col_sid[1]      = mem_vif.hbm_c[8]; // HBM2e Specific
                col_cmd_symbol  = WR; 
                col_state       = WR_F1; // move to Falling 1 
              end  
              4'b1001   : begin /*WRA*/
                col_ba          = mem_vif.hbm_c[7:4];
                col_sid[1]      = mem_vif.hbm_c[8]; // HBM2e Specific
                col_cmd_symbol  = WRA;   
                col_state       = WRA_F1; // move to Falling 1 
              end 
              4'b1010   : begin /*RD*/
                col_ba          = mem_vif.hbm_c[7:4];
                col_sid[1]      = mem_vif.hbm_c[8]; // HBM2e Specific
                col_cmd_symbol  = RD;  
                col_state       = RD_F1; // move to Falling 1 
              end 
              4'b1011   : begin /*RDA*/
                col_ba          = mem_vif.hbm_c[7:4];
                col_sid[1]      = mem_vif.hbm_c[8]; // HBM2e Specific
                col_cmd_symbol  = RDA;   
                col_state       = RDA_F1; // move to Falling 1 
              end 
              4'b000?   : begin  /*MRS*/
                col_ba          = mem_vif.hbm_c[7:4];
                col_mrs_op[7]   = mem_vif.hbm_c[3];
                col_cmd_symbol  = MRS;   
                col_state       = MRS_F1; // move to Falling 1 
              end 
             4'b111?    : begin 
                col_initialize(); 
                col_cmd_symbol  = CNOP;   
                col_state       = CNOP_F1;
              end
             default    : begin 
                col_initialize(); 
                col_state       = START;
              end
            endcase
          end
          else begin
            col_initialize();
            col_state         = START;
          end
      end

      WR_F1  : begin // Falling 1
          col_addr[1:0]       = mem_vif.hbm_c[1:0];
          col_addr[5:2]       = mem_vif.hbm_c[6:3];
          col_pc              = mem_vif.hbm_c[7];
          col_sid[0]          = mem_vif.hbm_c[0]; // HBM2e Specific
          col_par             = mem_vif.hbm_c[2];
          col_state           = START;
          valid_col_cmd       = 1;
          if(col_pc) begin 
            wr_cmd_cnt_pc1++;  
            //last_cmd_pc1      =  0;
            //if(first_cmd_reg_time_pc1 == 0)  first_cmd_reg_time_pc1 = $time;
            //last_cmd_reg_time_pc1 = $time;
          end
          else begin 
            wr_cmd_cnt_pc0++;   
            //last_cmd_pc0      =  0;
            //if(first_cmd_reg_time_pc0 == 0)  first_cmd_reg_time_pc0 = $time; 
            //last_cmd_reg_time_pc0 = $time;
          end
      end

      WRA_F1  : begin // Falling 1
          col_addr[1:0]       = mem_vif.hbm_c[1:0];
          col_addr[5:2]       = mem_vif.hbm_c[6:3];
          col_pc              = mem_vif.hbm_c[7];
          col_sid[0]          = mem_vif.hbm_c[0]; // HBM2e Specific
          col_par             = mem_vif.hbm_c[2];
          col_state           = START;
          valid_col_cmd       = 1;
          if(col_pc) begin 
            wra_cmd_cnt_pc1++; 
            //last_cmd_pc1      =  0;
            //if(first_cmd_reg_time_pc1 == 0)  first_cmd_reg_time_pc1 = $time;
            //last_cmd_reg_time_pc1 = $time;
          end
          else begin
            wra_cmd_cnt_pc0++;  
            //last_cmd_pc0      =  0;
            //if(first_cmd_reg_time_pc0 == 0)  first_cmd_reg_time_pc0 = $time; 
            //last_cmd_reg_time_pc0 = $time;
          end
      end

      RD_F1  : begin // Falling 1
          col_addr[1:0]       = mem_vif.hbm_c[1:0];
          col_addr[5:2]       = mem_vif.hbm_c[6:3];
          col_pc              = mem_vif.hbm_c[7];
          col_sid[0]          = mem_vif.hbm_c[0]; // HBM2e Specific
          col_par             = mem_vif.hbm_c[2];
          col_state           = START;
          valid_col_cmd       = 1;
          if(col_pc) begin 
            rd_cmd_cnt_pc1++; 
            //last_cmd_pc1      =  1;
            //if(first_cmd_reg_time_pc1 == 0)  first_cmd_reg_time_pc1 = $time;
            //last_cmd_reg_time_pc1 = $time;
          end
          else begin
            rd_cmd_cnt_pc0++;  
            //last_cmd_pc0      =  1;
            //if(first_cmd_reg_time_pc0 == 0)  first_cmd_reg_time_pc0 = $time; 
            //last_cmd_reg_time_pc0 = $time;
          end
      end

      RDA_F1  : begin // Falling 1
          col_addr[1:0]       = mem_vif.hbm_c[1:0];
          col_addr[5:2]       = mem_vif.hbm_c[6:3];
          col_pc              = mem_vif.hbm_c[7];
          col_sid[0]          = mem_vif.hbm_c[0]; // HBM2e Specific
          col_par             = mem_vif.hbm_c[2];
          col_state           = START;
          valid_col_cmd       = 1;
          if(col_pc) begin 
            rda_cmd_cnt_pc1++; 
            //last_cmd_pc1      =  1;
            //if(first_cmd_reg_time_pc1 == 0)  first_cmd_reg_time_pc1 = $time;
            //last_cmd_reg_time_pc1 = $time;
          end
          else begin
            rda_cmd_cnt_pc0++; 
            //last_cmd_pc0      =  1;
            //if(first_cmd_reg_time_pc0 == 0)  first_cmd_reg_time_pc0 = $time; 
            //last_cmd_reg_time_pc0 = $time;
          end
      end

      MRS_F1  : begin // Falling 1
          col_mrs_op[1:0]     = mem_vif.hbm_c[1:0];
          col_mrs_op[6:2]     = {mem_vif.hbm_c[7], mem_vif.hbm_c[6], mem_vif.hbm_c[5], mem_vif.hbm_c[4], mem_vif.hbm_c[3]};
          col_par             = mem_vif.hbm_c[2];
          col_cmd_symbol      = MRS;   
          col_state           = START;
          valid_col_cmd       = 1;
          mrs_cmd_cnt++; 
      end

      CNOP_F1  : begin // Falling 1
          col_par             = mem_vif.hbm_c[2];
          col_state           = START;
          //valid_col_cmd       = 1; // FIXME do we need to consider it as valid command
      end
    endcase
    
    if(valid_col_cmd == 1) begin
      execute_col_cmd(col_cmd_symbol, col_pc, col_sid, col_ba, col_addr, col_mrs_op);
      if(C_HBM_VERBOSITY_EN == 1) print_col_cmd_info();
    end
    invalid_traffic_check(col_cmd_symbol, col_pc, col_sid, col_ba, 15'b0, col_addr); // invalid RA/SID check as per device config
    `ifdef EN_HBM_RESPONDER_DBG_MODE
    update_col_dbg_signals_vif();
    `endif
  end
endtask


////////////////////////////////////////////////////////////////
// Task Description: execute_col_cmd 
//
////////////////////////////////////////////////////////////////
task execute_col_cmd(input hbm_command_t cmd, input bit col_pc, input bit [1:0] col_sid, input bit[3:0] col_ba, input bit[5:0] col_addr, input bit[7:0] col_mrs_op);
  bit [C_HBM_MEM_ADDR_WIDTH-1:0]        mem_addr                  = 0;
  bit [C_HBM_PAGE_ADDR_WIDTH-1:0]       page_addr                 = 0; // FIXME page_addr needs to be renamed as bank_addr?
  bit [C_HBM_ROW_ADDR_WIDTH-1:0]        col_row_addr              = 0;
  bit                                   dqs_preamble_en           = 1; //FIXME default to 1, need to add proper logic
  bit                                   dqs_postamble_en          = 1; //FIXME default to 1, need to add proper logic
  bit                                   dq_pre_condition_en       = 0;
  bit                                   is_valid_cmd              = 0;

  if(cmd == MRS) is_valid_cmd = 1;
  else begin
    page_addr     = get_page_addr(col_pc, col_sid, col_ba);
    is_valid_cmd  = is_valid_page_addr(col_pc, page_addr, col_row_addr);
    mem_addr      = get_mem_addr(col_pc, col_sid[0], col_ba, col_row_addr, col_addr);
    col_row       = col_row_addr; // global variable update for dbg print
    col_mem_addr  = mem_addr; // global variable update for dbg print
  end
  
  if(is_valid_cmd) begin
    case(cmd)
      MRS   : begin
          do_mrs_write(col_ba, col_mrs_op);
      end

      WR    : begin
          do_col_write(col_pc, mem_addr);
      end
      
      WRA   : begin
          do_col_write_ap(col_pc, mem_addr);
      end

      RD    : begin
          do_col_read(col_pc, mem_addr, dqs_preamble_en, dqs_postamble_en, dq_pre_condition_en);
      end
      
      RDA   : begin
          do_col_read_ap(col_pc, mem_addr, dqs_preamble_en, dqs_postamble_en, dq_pre_condition_en);
      end
    endcase
  end
  else  `hbm_fatal(TAG, $sformatf("Invalid Column Command Error. Sending %0s column command when page closed is invalid. PC= %0d, SID= 0x%0h, BA= 0x%0h, COL= 0x%0h", cmd, col_pc, col_sid, col_ba, col_addr[5:1]))
endtask


////////////////////////////////////////////////////////////////
// Task Description: 
//
////////////////////////////////////////////////////////////////
task do_mrs_write (input bit [3:0] mrs_addr, input bit [7:0] mrs_opcode);
  case(mrs_addr)
    4'b0000 : begin //  MR0
        reg_mr0_test_mode               = mrs_opcode[7];
        reg_mr0_add_cmd_parity          = mrs_opcode[6];
        reg_mr0_dq_write_parity         = mrs_opcode[5];
        reg_mr0_dq_read_parity          = mrs_opcode[4];
        reg_mr0_tcsr                    = mrs_opcode[2];
        reg_mr0_dbi_ac_write            = mrs_opcode[1];
        reg_mr0_dbi_ac_read             = mrs_opcode[0];

        reg_mr0_test_mode_ascii         = mrs_opcode[7]  ===  0   ?   "Normal Operation"  :
                                          mrs_opcode[7]  ===  1   ?   "Test Mode"         :  "";
        reg_mr0_add_cmd_parity_ascii    = mrs_opcode[6]  ===  0   ?   "Disable" :
                                          mrs_opcode[6]  ===  1   ?   "Enable"  : "";
        reg_mr0_dq_write_parity_ascii   = mrs_opcode[5]  ===  0   ?   "Disable" :
                                          mrs_opcode[5]  ===  1   ?   "Enable"  : "";
        reg_mr0_dq_read_parity_ascii    = mrs_opcode[4]  ===  0   ?   "Disable" :
                                          mrs_opcode[4]  ===  1   ?   "Enable"  : "";
        reg_mr0_tcsr_ascii              = mrs_opcode[2]  ===  0   ?   "Disable" :
                                          mrs_opcode[2]  ===  1   ?   "Enable"  : "";
        reg_mr0_dbi_ac_write_ascii      = mrs_opcode[1]  ===  0   ?   "Disable" :
                                          mrs_opcode[1]  ===  1   ?   "Enable"  : "";
        reg_mr0_dbi_ac_read_ascii       = mrs_opcode[0]  ===  0   ?   "Disable" :
                                          mrs_opcode[0]  ===  1   ?   "Enable"  : "";
    end
    4'b0001 : begin //  MR1
        reg_mr1_driver_strength         = mrs_opcode[7:5];
        reg_mr1_write_recovery          = mrs_opcode[4:0];

        `ifdef ENABLE_INVALID_MRS_CHECK
        if(reg_mr1_driver_strength inside {5,6,7}) 
          `hbm_fatal(TAG, $sformatf("Invalid MRS Opcode Error(MR1). Normal Driver Strength set to reserved value= 0x%0h", reg_mr1_driver_strength)) 
        `endif

        `ifdef ENABLE_INVALID_MRS_CHECK
        if(reg_mr1_write_recovery inside {0,1,2}) 
          `hbm_fatal(TAG, $sformatf("Invalid MRS Opcode Error(MR1). Write Recovery(WR) set to reserved value= 0x%0h", reg_mr1_write_recovery)) 
        `endif

        reg_mr1_driver_strength_ascii   = mrs_opcode[7:5]  ===  3'b000  ?  "6 mA driver"  :
                                          mrs_opcode[7:5]  ===  3'b001  ?  "9 mA driver"  :
                                          mrs_opcode[7:5]  ===  3'b010  ?  "12 mA driver" :
                                          mrs_opcode[7:5]  ===  3'b011  ?  "15 mA driver" :
                                          mrs_opcode[7:5]  ===  3'b100  ?  "18 mA driver" :  "";
        reg_mr1_write_recovery_ascii    = mrs_opcode[4:0] inside {5'd0, 5'd1, 5'd2} ? "RESERVED"  : $sformatf("%0d nCK", mrs_opcode[5:0]);
    end
    4'b0010 : begin //  MR2
        reg_mr2_read_latency            = mrs_opcode[7:3]/*+2*/;
        reg_mr2_write_latency           = mrs_opcode[2:0]/*+1*/;
        if(C_HBM_VERSION == "HBM2e") begin
          reg_mr2_read_latency_dc         = reg_mr4_ext_read_latency == 0 ? reg_mr2_read_latency + 2 : reg_mr2_read_latency + 34; 
          reg_mr2_write_latency_dc        = reg_mr4_ext_write_latency == 0 ? reg_mr2_write_latency + 1 : reg_mr2_write_latency + 9;
        end else if(C_HBM_VERSION == "HBM2") begin
          reg_mr2_read_latency_dc         = reg_mr2_read_latency + 2; 
          reg_mr2_write_latency_dc        = reg_mr2_write_latency + 1;
        end

        `ifdef ENABLE_INVALID_MRS_CHECK
        if(C_HBM_VERSION == "HBM2e" && reg_mr4_ext_read_latency == 0 && reg_mr2_read_latency == 0) 
          `hbm_fatal(TAG, "Invalid MRS Opcode Error(MR2). Read Latency set to reserved value=0 when MR4 OP5=0") 
        if(C_HBM_VERSION == "HBM2e" && reg_mr4_ext_read_latency == 1 && reg_mr2_read_latency > 5'b01110) 
          `hbm_fatal(TAG, $sformatf("Invalid MRS Opcode Error(MR2). Read Latency set to reserved value=5'b%0b when MR4 OP5=1", reg_mr2_read_latency)) 
        `endif

        reg_mr2_read_latency_ascii      = $sformatf("%0d nCK", reg_mr2_read_latency_dc);
        reg_mr2_write_latency_ascii     = $sformatf("%0d nCK", reg_mr2_write_latency_dc);
    end
    4'b0011 : begin //  MR3
        reg_mr3_burst_length            = mrs_opcode[7];
        reg_mr3_bank_group              = mrs_opcode[6];
        reg_mr3_ras                     = mrs_opcode[5:0];
        reg_mr3_burst_length_dc         = reg_mr3_burst_length == 0 ? 2 :
                                          reg_mr3_burst_length == 1 ? 4 : 0;

        `ifdef ENABLE_INVALID_MRS_CHECK
        if(reg_mr3_ras inside {0,1,2}) 
          `hbm_fatal(TAG, $sformatf("Invalid MRS Opcode Error(MR3). Activate to Precharge RAS set to reserved value= 0x%0h", reg_mr3_ras)) 
        `endif
        
        reg_mr3_burst_length_ascii      = mrs_opcode[7]  ===  0  ?  "BL2" :
                                          mrs_opcode[7]  ===  1  ?  "BL4" : "" ;
        reg_mr3_bank_group_ascii        = mrs_opcode[6]  ===  0  ?  "Disable" : 
                                          mrs_opcode[6]  ===  1  ?  "Enable"  : "";
        reg_mr3_ras_ascii               = mrs_opcode[5:0] inside {6'd0, 6'd1, 6'd2} ? "RESERVED"  : $sformatf("%0d nCK", mrs_opcode[5:0]);
    end
    4'b0100 : begin //  MR4
        reg_mr4_ext_read_latency        = mrs_opcode[5]; // HBM2e Specific
        reg_mr4_ext_write_latency       = mrs_opcode[4]; // HBM2e Specific
        reg_mr4_parity_latency          = mrs_opcode[3:2];
        reg_mr4_dm                      = mrs_opcode[1];
        reg_mr4_dm_en                   = ~reg_mr4_dm;
        reg_mr4_ecc                     = mrs_opcode[0];

        // FIXME need to confirm the MR2/MR4 or MR4/MR2 sequence from rtl team? no mention on spec
        reg_mr2_read_latency_dc         = reg_mr4_ext_read_latency == 0 ? reg_mr2_read_latency + 2 : reg_mr2_read_latency + 34;
        reg_mr2_write_latency_dc        = reg_mr4_ext_write_latency == 0 ? reg_mr2_write_latency + 1 : reg_mr2_write_latency + 9;


        if(reg_mr4_dm == 0 && reg_mr4_ecc == 1) begin
          `hbm_fatal(TAG, "Invalid MRS Opcode Error(MR4). DM and ECC cannot be enabled simultaneously") 
        end

        reg_mr4_ext_read_latency_ascii  = mrs_opcode[5]  ===  0  ?  "Disable" : 
                                          mrs_opcode[5]  ===  1  ?  "Enable"  : "";
        reg_mr4_ext_write_latency_ascii = mrs_opcode[4]  ===  0  ?  "Disable" : 
                                          mrs_opcode[4]  ===  1  ?  "Enable"  : "";
        reg_mr4_parity_latency_ascii    = $sformatf("%0d nCK", mrs_opcode[3:2]);
        reg_mr4_dm_ascii                = mrs_opcode[1]  ===  0  ?  "Enable"  : 
                                          mrs_opcode[1]  ===  1  ?  "Disable" : "";
        reg_mr4_ecc_ascii               = mrs_opcode[0]  ===  0  ?  "Disable" : 
                                          mrs_opcode[0]  ===  1  ?  "Enable"  : "";
    end
    4'b0101 : begin //  MR5
        reg_mr5_trr                     = mrs_opcode[7];
        reg_mr5_trr_pc_select           = mrs_opcode[6];
        reg_mr5_trr_mode_ba             = mrs_opcode[3:0];

        reg_mr5_trr_ascii               = mrs_opcode[7]  ===  0  ? "Disable"  :
                                          mrs_opcode[7]  ===  1  ? "Enable"   : "";
        reg_mr5_trr_pc_select_ascii     = mrs_opcode[6]  ===  0 && mrs_opcode[7]  ===  1  ?  "Enable TRR for Pseudo Channel 0"  :
                                          mrs_opcode[6]  ===  1 && mrs_opcode[7]  ===  1  ?  "Enable TRR for Pseudo Channel 1"  : "";
        reg_mr5_trr_mode_ba_n_ascii     = $sformatf("Bank %0d", mrs_opcode[3:0]);
    end
    4'b0110 : begin //  MR6
        reg_mr6_imPRE_tRP_value         = mrs_opcode[7:3] /*+ 2*/;
        reg_mr6_imPRE_tRP_value_dc      = reg_mr6_imPRE_tRP_value + 2;

        reg_mr6_imPRE_tRP_value_ascii   = $sformatf("%0d nCK", mrs_opcode[7:3] + 2);
    end
    4'b0111 : begin //  MR7
        reg_mr7_cattrip                 = mrs_opcode[7];
        reg_mr7_misr_control            = mrs_opcode[5:3];
        reg_mr7_read_mux_control        = mrs_opcode[2:1];
        reg_mr7_loopback                = mrs_opcode[0];

        `ifdef ENABLE_INVALID_MRS_CHECK
        if(reg_mr7_loopback == 1 && reg_mr7_misr_control > 3'b100)
          `hbm_fatal(TAG, $sformatf("Invalid MRS Opcode Error(MR7). DWORD MISR Control set to reserved value= 0x%0h", reg_mr7_misr_control)) 
        if(reg_mr7_loopback == 1 && reg_mr7_read_mux_control == 0)
          `hbm_fatal(TAG, $sformatf("Invalid MRS Opcode Error(MR7). DWORD Read Mux Control set to reserved value= 0x%0h", reg_mr7_read_mux_control)) 
        `endif

        reg_mr7_cattrip_ascii           = mrs_opcode[7]  ===  0  ?  "Clear CATTRIP Pin"         :
                                          mrs_opcode[7]  ===  1  ?  "Assert CATTRIP pin to 1"   : "";
        reg_mr7_misr_control_ascii      = mrs_opcode[5:3]  ===  3'b000  ?  "Preset"                                     : 
                                          mrs_opcode[5:3]  ===  3'b001  ?  "LFSR mode(read direction)"                  : 
                                          mrs_opcode[5:3]  ===  3'b010  ?  "Register mode(read and write directions)"   : 
                                          mrs_opcode[5:3]  ===  3'b011  ?  "MISR mode(write direction)"                 : 
                                          mrs_opcode[5:3]  ===  3'b100  ?  "LFSR compare mode(write direction)"         : ""; 
        reg_mr7_read_mux_control_ascii  = mrs_opcode[2:1]  ===  2'b01   ?  "Return data from MISR Registers"  : 
                                          mrs_opcode[2:1]  ===  2'b10   ?  "Return data from Rx path sampler" : 
                                          mrs_opcode[2:1]  ===  2'b11   ?  "Return LFSR_COMPARE_STICKY"       :  ""; 
        reg_mr7_loopback_ascii          = mrs_opcode[0]  ===  0  ?  "Disable" : 
                                          mrs_opcode[0]  ===  1  ?  "Enable"  : ""; 
    end
    4'b1000 : begin //  MR8
        reg_mr8_da28_lockout            = mrs_opcode[0];

        reg_mr8_da28_lockout_ascii      = mrs_opcode[0]  ===  0  ?  "Disable" :
                                          mrs_opcode[0]  ===  1  ?  "Enable"  : "";
    end
    4'b1001 : begin //  MR9
      // RESERVED
    end
    4'b1010 : begin //  MR10
      // RESERVED
    end
    4'b1011 : begin //  MR11
      // RESERVED
    end
    4'b1100 : begin //  MR12
      // RESERVED
    end
    4'b1101 : begin //  MR13
      // RESERVED
    end
    4'b1110 : begin //  MR14
      // RESERVED
    end
    4'b1111 : begin //  MR15
        reg_mr15_opt_int_vref           = mrs_opcode[2:0];

        reg_mr15_opt_int_vref_ascii     = mrs_opcode[2:0]  ===  3'b000  ?  "50% VDD"  : 
                                          mrs_opcode[2:0]  ===  3'b001  ?  "46% VDD"  : 
                                          mrs_opcode[2:0]  ===  3'b010  ?  "42% VDD"  : 
                                          mrs_opcode[2:0]  ===  3'b011  ?  "38% VDD"  : 
                                          mrs_opcode[2:0]  ===  3'b100  ?  "54% VDD"  : 
                                          mrs_opcode[2:0]  ===  3'b101  ?  "58% VDD"  : 
                                          mrs_opcode[2:0]  ===  3'b110  ?  "62% VDD"  : 
                                          mrs_opcode[2:0]  ===  3'b111  ?  "66% VDD"  : "" ; 
    end
  endcase
endtask


////////////////////////////////////////////////////////////////
// Task Description: do_col_write
// Column Write
////////////////////////////////////////////////////////////////
task do_col_write(input bit pc, input bit[C_HBM_MEM_ADDR_WIDTH-1:0] mem_addr);
  fork
    get_write_data(pc, mem_addr);   
  join_none
endtask


////////////////////////////////////////////////////////////////
// Task Description: do_col_write_ap
// Column Write with Auto-Precharge
////////////////////////////////////////////////////////////////
task do_col_write_ap(input bit pc, input bit[C_HBM_MEM_ADDR_WIDTH-1:0] mem_addr);
  fork
    get_write_data(pc, mem_addr);   
    do_row_precharge(/*WRA*/PRE, col_pc, col_sid, col_ba);
  join_none
endtask


////////////////////////////////////////////////////////////////
// Task Description: do_col_read
// Column Read
////////////////////////////////////////////////////////////////
task do_col_read(input bit pc, input bit[C_HBM_MEM_ADDR_WIDTH-1:0] mem_addr, input bit dqs_preamble_en, input bit dqs_postamble_en, input bit dq_pre_condition_en);
  fork
    update_b2b_read_tracker(pc);
    `ifdef XILINX_SIMULATOR // XSIM Fix for CR-1178515. In XSIM simulator, ck_t/ck_c signal is having odd TCK on some cycles randomly which is causing to shrinken only the dq data eye window. So, the dqs samples the stale data and causes the data integrity error. As a workaround, we are splited the dqs generation into three phases as preamble, during burst and postamble and waiting for latency as per ck_t edges instead of #delay. Also all #delay events are replaced with wait for ck_t edge event.
    send_read_dqs_preamble(pc);   
    send_read_dqs_burst(pc);   
    send_read_dqs_postamble(pc);   
    `else
    send_read_dqs(pc, dqs_preamble_en, dqs_postamble_en);   
    `endif
    send_read_data(pc, mem_addr, dq_pre_condition_en);   
  join_none
endtask


////////////////////////////////////////////////////////////////
// Task Description: do_col_read_ap 
// Column Read with Auto-Precharge
////////////////////////////////////////////////////////////////
task do_col_read_ap(input bit pc, input bit[C_HBM_MEM_ADDR_WIDTH-1:0] mem_addr, input bit dqs_preamble_en, input bit dqs_postamble_en, input bit dq_pre_condition_en);
  fork
    update_b2b_read_tracker(pc);
    `ifdef XILINX_SIMULATOR
    send_read_dqs_preamble(pc);   
    send_read_dqs_burst(pc);   
    send_read_dqs_postamble(pc);   
    `else
    send_read_dqs(pc, dqs_preamble_en, dqs_postamble_en);   
    `endif
    send_read_data(pc, mem_addr, dq_pre_condition_en);   
    do_row_precharge(/*RDA*/PRE, col_pc, col_sid, col_ba);
  join_none
endtask


////////////////////////////////////////////////////////////////
// Task Description: 
//
////////////////////////////////////////////////////////////////
task get_write_data(bit pc, bit[C_HBM_MEM_ADDR_WIDTH-1:0] mem_addr);
  bit[C_HBM_BURST_DATA_WIDTH-1:0] mem_wr_data;
  bit[(C_HBM_BURST_DATA_WIDTH/8)-1:0] mem_wr_data_mask;

  wait_for_write_latency(); // wait till one clk cycle earlier than latency

  fork
    begin : WDQ_LOWER32BIT_CAPTURE
      // Rise-0 data (D0)
      wait_for_wdqs_t_posedge((pc*2)+0);
      mem_wr_data[31:0]         = mem_vif.hbm_dq[(((pc*2)+0)*32)+:32];
      mem_wr_data_mask[3:0]     = mem_vif.hbm_dm[(((pc*2)+0)*4)+:4];

      // Fall-0 data (D1)
      wait_for_wdqs_t_negedge((pc*2)+0);
      mem_wr_data[95:64]        = mem_vif.hbm_dq[(((pc*2)+0)*32)+:32];
      mem_wr_data_mask[11:8]    = mem_vif.hbm_dm[(((pc*2)+0)*4)+:4];

      // Rise-1 data (D2)
      wait_for_wdqs_t_posedge((pc*2)+0);
      mem_wr_data[159:128]      = mem_vif.hbm_dq[(((pc*2)+0)*32)+:32];
      mem_wr_data_mask[19:16]   = mem_vif.hbm_dm[(((pc*2)+0)*4)+:4];

      // Fall-1 data (D3)
      wait_for_wdqs_t_negedge((pc*2)+0);
      mem_wr_data[223:192]      = mem_vif.hbm_dq[(((pc*2)+0)*32)+:32];
      mem_wr_data_mask[27:24]   = mem_vif.hbm_dm[(((pc*2)+0)*4)+:4];
    end
    begin : WDQ_UPPER32BIT_CAPTURE
      // Rise-0 data (D0)
      wait_for_wdqs_t_posedge((pc*2)+1);
      mem_wr_data[63:32]        = mem_vif.hbm_dq[(((pc*2)+1)*32)+:32];
      mem_wr_data_mask[7:4]     = mem_vif.hbm_dm[(((pc*2)+1)*4)+:4];

      // Fall-0 data (D1)
      wait_for_wdqs_t_negedge((pc*2)+1);
      mem_wr_data[127:96]       = mem_vif.hbm_dq[(((pc*2)+1)*32)+:32];
      mem_wr_data_mask[15:12]   = mem_vif.hbm_dm[(((pc*2)+1)*4)+:4];
      
      // Rise-1 data (D2)
      wait_for_wdqs_t_posedge((pc*2)+1);
      mem_wr_data[191:160]      = mem_vif.hbm_dq[(((pc*2)+1)*32)+:32];
      mem_wr_data_mask[23:20]   = mem_vif.hbm_dm[(((pc*2)+1)*4)+:4];
      
      // Fall-1 data (D3)
      wait_for_wdqs_t_negedge((pc*2)+1);
      mem_wr_data[255:224]      = mem_vif.hbm_dq[(((pc*2)+1)*32)+:32];
      mem_wr_data_mask[31:28]   = mem_vif.hbm_dm[(((pc*2)+1)*4)+:4];
    end
  join

  hbm_mem_write(mem_addr, mem_wr_data, mem_wr_data_mask);
  
endtask


////////////////////////////////////////////////////////////////
// Task Description: 
//
////////////////////////////////////////////////////////////////
task send_read_dqs(bit pc, bit dqs_preamble_en, bit dqs_postamble_en);

  wait_for_read_dqs_latency(); // wait till one clk cycle earlier than latency
  
  // Read Preamble
  if(dqs_preamble_en == 1) begin
    mem_vif.hbm_rdqs_t[(pc*2)+:2]   <=  2'b11;
    wait_for_half_tck();
    
    mem_vif.hbm_rdqs_t[(pc*2)+:2]   <=  2'b00;
    wait_for_half_tck();
  end
  else begin
    wait_for_tck();
  end

  // D0- Rise0 data
  mem_vif.hbm_rdqs_t[(pc*2)+:2]   <=  2'b11;
  wait_for_half_tck();

  // D1- Fall0 data
  mem_vif.hbm_rdqs_t[(pc*2)+:2]   <=  2'b00;
  wait_for_half_tck();
  
  // D2- Rise1 data
  mem_vif.hbm_rdqs_t[(pc*2)+:2]   <=  2'b11;
  wait_for_half_tck();
  
  // D3- Fall1 data
  mem_vif.hbm_rdqs_t[(pc*2)+:2]   <=  2'b00;
  wait_for_half_tck();

  // Read Postamble
  if(dqs_postamble_en == 1) begin
    mem_vif.hbm_rdqs_t[(pc*2)+:2]   <=  2'b11;
    wait_for_half_tck();

    mem_vif.hbm_rdqs_t[(pc*2)+:2]   <=  2'b00;
    wait_for_half_tck();
  end
  else begin
    //FIXME anything needs to be added?
  end
endtask


////////////////////////////////////////////////////////////////
// Task Description: 
//
////////////////////////////////////////////////////////////////
task send_read_dqs_preamble(bit pc);

  wait_for_read_dqs_latency(.wait_for_preamble(1), .wait_for_postamble(0)); // wait till one clk cycle earlier than latency
  
  // Read Preamble
  mem_vif.hbm_rdqs_t[(pc*2)+:2]   <=  2'b11;
  wait_for_half_tck();
  
  mem_vif.hbm_rdqs_t[(pc*2)+:2]   <=  2'b00;
  wait_for_half_tck();
endtask


////////////////////////////////////////////////////////////////
// Task Description: 
//
////////////////////////////////////////////////////////////////
task send_read_dqs_burst(bit pc);

  wait_for_read_dqs_latency(.wait_for_preamble(0), .wait_for_postamble(0)); // wait till the latency
  
  // D0- Rise0 data
  mem_vif.hbm_rdqs_t[(pc*2)+:2]   <=  2'b11;
  wait_for_half_tck();

  // D1- Fall0 data
  mem_vif.hbm_rdqs_t[(pc*2)+:2]   <=  2'b00;
  wait_for_half_tck();
  
  // D2- Rise1 data
  mem_vif.hbm_rdqs_t[(pc*2)+:2]   <=  2'b11;
  wait_for_half_tck();
  
  // D3- Fall1 data
  mem_vif.hbm_rdqs_t[(pc*2)+:2]   <=  2'b00;
  wait_for_half_tck();

endtask


////////////////////////////////////////////////////////////////
// Task Description: 
//
////////////////////////////////////////////////////////////////
task send_read_dqs_postamble(bit pc);

  wait_for_read_dqs_latency(.wait_for_preamble(0), .wait_for_postamble(1)); // wait till two clk cycle after the latency
  
  // Read Postamble
  mem_vif.hbm_rdqs_t[(pc*2)+:2]   <=  2'b11;
  wait_for_half_tck();
  
  mem_vif.hbm_rdqs_t[(pc*2)+:2]   <=  2'b00;
  wait_for_half_tck();
endtask


////////////////////////////////////////////////////////////////
// Task Description: 
//
////////////////////////////////////////////////////////////////
task send_read_data (bit pc, bit[C_HBM_MEM_ADDR_WIDTH-1:0] mem_addr, bit data_pre_condition);
  bit[C_HBM_BURST_DATA_WIDTH-1:0] mem_rd_data;
  bit data_post_condition;

  wait_for_read_data_latency(); // wait till one clk cycle earlier than latency

  hbm_mem_read(mem_addr, mem_rd_data);
  
  // Read data pre-conditioning
  //if(data_pre_condition == 1) begin
  //  //FIXME need to add
  //end

  //FIXME as per jedec spec, what is odd/even bytes in read data?
  // D0- Rise0 data
  mem_vif.hbm_dq_reg[(pc*64)+:64]   <= mem_rd_data[63:0];
  wait_for_half_tck();

  // D1- Fall0 data
  mem_vif.hbm_dq_reg[(pc*64)+:64]   <= mem_rd_data[127:64];
  wait_for_half_tck();
  
  // D2- Rise1 data
  mem_vif.hbm_dq_reg[(pc*64)+:64]   <= mem_rd_data[191:128];
  wait_for_half_tck();
  
  // D3- Fall1 data
  mem_vif.hbm_dq_reg[(pc*64)+:64]   <= mem_rd_data[255:192];
  wait_for_half_tck();

  // Read data post-conditioning
  data_post_condition = ~(b2b_read_tracker_q.pop_front());
  if(data_post_condition == 1) begin
    wait_for_half_tck();
    mem_vif.hbm_dq_reg[(pc*64)+:64]   <= 'z;
  end
endtask


////////////////////////////////////////////////////////////////
// Task Description: update_b2b_read_tracker 
// This method monitors the back2back read request to the same PC
// to decide on the post_condition of read data transfer
////////////////////////////////////////////////////////////////
task update_b2b_read_tracker(bit pc);
  bit   is_it_b2b_read  = 1'b0; 

  `hbm_info(TAG, $sformatf("HBMDBG :: update_b2b_read_tracker :: started waiting for seamless_read_burst_window :: pc= %0d", pc), HBM_DEBUG)

  wait_for_seamless_read_burst_window();

  if(col_cmd_symbol inside {RD, RDA} && col_pc == pc) is_it_b2b_read  = 1;
    
  `hbm_info(TAG, $sformatf("HBMDBG :: update_b2b_read_tracker :: seamless_read_burst_window wait done :: is_it_b2b_read= %0d, col_cmd_symbol= %0s, col_pc= %0d, pc= %0d", is_it_b2b_read, col_cmd_symbol.name, col_pc, pc), HBM_DEBUG)

  b2b_read_tracker_q.push_back(is_it_b2b_read);
endtask


////////////////////////////////////////////////////////////////
// Task Description: hbm_mem_write 
// HBM Memory Array Write
////////////////////////////////////////////////////////////////
task hbm_mem_write(input bit[C_HBM_MEM_ADDR_WIDTH-1:0] mem_addr, input bit[C_HBM_BURST_DATA_WIDTH-1:0] mem_data, input bit[(C_HBM_BURST_DATA_WIDTH/8)-1:0] mem_data_mask);
  bit[C_HBM_BURST_DATA_WIDTH-1:0] old_data;
  bit[C_HBM_BURST_DATA_WIDTH-1:0] updated_data;
  bit[C_HBM_BURST_DATA_WIDTH-1:0] rand_data;
  bit partial_write;

  if(reg_mr4_dm_en == 1) begin // DM Enabled
    if(hbm_memory.exists(mem_addr)) begin // old data exists
      old_data  = hbm_memory[mem_addr];
      for(int i = 0; i < C_HBM_BURST_DATA_WIDTH/8; i++) begin
        if(mem_data_mask[i] == 0/*DQ Valid*/)
          updated_data[i*8+:8]  = mem_data[i*8+:8];
        else/*DQ Masked*/
          updated_data[i*8+:8]  = old_data[i*8+:8];
      end
      hbm_memory[mem_addr]  = updated_data;
    //end else // old data not exists (i.e. first write)
    //  hbm_memory[mem_addr]  = mem_data;
    end else begin // old data not exists (i.e. first write)
      partial_write = |mem_data_mask; // active_low dm bits

      if(partial_write) begin // write only the partial data to the hbm memory with unwritten locations are initialized as per INIT_MODE parameter settings
        // Initialize the burst
        case(C_HBM_MEM_INIT_MODE)
          "INIT_0"  : begin
              updated_data  = {C_HBM_BURST_DATA_WIDTH{1'b0}};
          end
          
          "INIT_1"  : begin
              updated_data  = {C_HBM_BURST_DATA_WIDTH{1'b1}};
          end

          "INIT_RANDOM" : begin
              for(int i=0; i < C_HBM_BURST_DATA_WIDTH/32; i++)begin
                updated_data[(i*32)+:32] = $urandom(); //FIXME all channels must generate diff set of random data. Also, every read to the same location will return different rand value within channel. shall seed it with addresss? think further about seeding.. 
              end
          end
        endcase

        for(int i = 0; i < C_HBM_BURST_DATA_WIDTH/8; i++) begin
          if(mem_data_mask[i] == 0/*DQ Valid*/)
            updated_data[i*8+:8]  = mem_data[i*8+:8];
        end
      end // write entire burst into hbm memory
      else updated_data = mem_data;

      hbm_memory[mem_addr]  = updated_data;
    end
  end else begin // DM Disabled
    hbm_memory[mem_addr]  = mem_data;
  end

  if(C_HBM_VERBOSITY_EN == 1) begin
    `hbm_info(TAG, $sformatf(">>>> WRITE_DATA >>>> %0s, MEM_WR_DATA= 0x%0h, DM= 0x%0h(MR4 DM Enable= %0d)", get_mem_info(mem_addr), mem_data, mem_data_mask, reg_mr4_dm_en), HBM_LOW)
  end
endtask


////////////////////////////////////////////////////////////////
// Task Description: hbm_mem_read 
// HBM Memory Array Read
////////////////////////////////////////////////////////////////
task hbm_mem_read(input bit[C_HBM_MEM_ADDR_WIDTH-1:0] mem_addr, output bit[C_HBM_BURST_DATA_WIDTH-1:0] mem_data);
  bit[C_HBM_BURST_DATA_WIDTH-1:0] rand_data;

  if(hbm_memory.exists(mem_addr)) begin 
    mem_data  = hbm_memory[mem_addr];
  end else begin
    if(C_HBM_MEM_INIT_MODE == "INIT_RANDOM") begin
      for(int i=0; i < C_HBM_BURST_DATA_WIDTH/32; i++)begin
        rand_data[(i*32)+:32] = $urandom(); //FIXME all channels must generate diff set of random data. shall seed it with addresss? think further about seeding..
      end
    end
    mem_data  = C_HBM_MEM_INIT_MODE == "INIT_0"       ? {C_HBM_BURST_DATA_WIDTH{1'b0}}  :
                C_HBM_MEM_INIT_MODE == "INIT_1"       ? {C_HBM_BURST_DATA_WIDTH{1'b1}}  :
                C_HBM_MEM_INIT_MODE == "INIT_RANDOM"  ?  rand_data : 0 ;

    if(C_HBM_VERBOSITY_EN == 1) begin
      `hbm_warning(TAG, $sformatf("Reading from Unwritten location. %0s", get_mem_info(mem_addr)))
    end
  end

  if(C_HBM_VERBOSITY_EN == 1) begin
    `hbm_info(TAG, $sformatf(">>>> READ_DATA >>>> %0s, MEM_RD_DATA= 0x%0h", get_mem_info(mem_addr), mem_data), HBM_LOW)
  end
endtask


////////////////////////////////////////////////////////////////
// Task Description: print_col_cmd_info
//
////////////////////////////////////////////////////////////////
function void print_col_cmd_info();
  string  col_cmd_print_str;
  string  col_cmd_name;

  case(col_cmd_symbol)
    WR  : begin
        col_cmd_name      = "WRITE";
        col_cmd_print_str = $sformatf("CMD_ID= %0d, PC= %0d, SID= 0x%0h, BG= 0x%0h, BANK= 0x%0h, ROW= 0x%0h, COL= 0x%0h, MEM_ADDR= 0x%0h", (col_pc == 0) ? wr_cmd_cnt_pc0 : wr_cmd_cnt_pc1, col_pc, col_sid[0], col_ba[3:2], col_ba[1:0], col_row, col_addr[5:1], col_mem_addr);
    end
    WRA : begin
        col_cmd_name      = "WRITE_AP";
        col_cmd_print_str = $sformatf("CMD_ID= %0d, PC= %0d, SID= 0x%0h, BG= 0x%0h, BANK= 0x%0h, ROW= 0x%0h, COL= 0x%0h, MEM_ADDR= 0x%0h", (col_pc == 0) ? wra_cmd_cnt_pc0 : wra_cmd_cnt_pc1, col_pc, col_sid[0], col_ba[3:2], col_ba[1:0], col_row, col_addr[5:1], col_mem_addr);
    end
    RD : begin
        col_cmd_name      = "READ";
        col_cmd_print_str = $sformatf("CMD_ID= %0d, PC= %0d, SID= 0x%0h, BG= 0x%0h, BANK= 0x%0h, ROW= 0x%0h, COL= 0x%0h, MEM_ADDR= 0x%0h", (col_pc == 0) ? rd_cmd_cnt_pc0 : rd_cmd_cnt_pc1, col_pc, col_sid[0], col_ba[3:2], col_ba[1:0], col_row, col_addr[5:1], col_mem_addr);
    end
    RDA : begin
        col_cmd_name      = "READ_AP";
        col_cmd_print_str = $sformatf("CMD_ID= %0d, PC= %0d, SID= 0x%0h, BG= 0x%0h, BANK= 0x%0h, ROW= 0x%0h, COL= 0x%0h, MEM_ADDR= 0x%0h", (col_pc == 0) ? rda_cmd_cnt_pc0 : rda_cmd_cnt_pc1, col_pc, col_sid[0], col_ba[3:2], col_ba[1:0], col_row, col_addr[5:1], col_mem_addr);
    end
    MRS : begin
        col_cmd_name      = "MRS";
        case(col_ba)
          4'b0000 : col_cmd_print_str = $sformatf("CMD_ID= %0d, MODE_REGISTER= MR%0d, OPCODE= %0b >>> Test Mode= %0s, ADD/CMD Parity= %0s, DQ Write Parity= %0s, DQ Read Parity= %0s, TCSR= %0s, DBIac Write= %0s, DBIac Read= %0s", mrs_cmd_cnt, col_ba, col_mrs_op, reg_mr0_test_mode, reg_mr0_add_cmd_parity, reg_mr0_dq_write_parity, reg_mr0_dq_read_parity, reg_mr0_tcsr_ascii, reg_mr0_dbi_ac_write_ascii, reg_mr0_dbi_ac_read_ascii);
          4'b0001 : col_cmd_print_str = $sformatf("CMD_ID= %0d, MODE_REGISTER= MR%0d, OPCODE= %0b >>> Driver Strength= %0s, Write Recovery (WR)= %0s", mrs_cmd_cnt, col_ba, col_mrs_op, reg_mr1_driver_strength_ascii, reg_mr1_write_recovery_ascii);
          4'b0010 : col_cmd_print_str = $sformatf("CMD_ID= %0d, MODE_REGISTER= MR%0d, OPCODE= %0b >>> Read Latency= %0s, Write Latency= %0s", mrs_cmd_cnt, col_ba, col_mrs_op, reg_mr2_read_latency_ascii, reg_mr2_write_latency_ascii);
          4'b0011 : col_cmd_print_str = $sformatf("CMD_ID= %0d, MODE_REGISTER= MR%0d, OPCODE= %0b >>> Burst Length= %0s, Bank Group= %0s, Activate to Precharge (RAS)= %0s", mrs_cmd_cnt, col_ba, col_mrs_op, reg_mr3_burst_length_ascii, reg_mr3_bank_group_ascii, reg_mr3_ras_ascii);
          4'b0100 : begin 
               if(C_HBM_VERSION == "HBM2") begin
                 col_cmd_print_str = $sformatf("CMD_ID= %0d, MODE_REGISTER= MR%0d, OPCODE= %0b >>> Parity Latency (PL)= %0s, DM= %0s, ECC= %0s", mrs_cmd_cnt, col_ba, col_mrs_op, reg_mr4_parity_latency_ascii, reg_mr4_dm_ascii, reg_mr4_ecc_ascii);
               end else if(C_HBM_VERSION == "HBM2e") begin
                 col_cmd_print_str = $sformatf("CMD_ID= %0d, MODE_REGISTER= MR%0d, OPCODE= %0b >>> Extended Read Latency (ERL)= %0s (As per ERL, Read Latency= %0d nCK), Extended Write Latency (EWL)= %0s (As per EWL, Write Latency= %0d nCK), Parity Latency (PL)= %0s, DM= %0s, ECC= %0s", mrs_cmd_cnt, col_ba, col_mrs_op, reg_mr4_ext_read_latency_ascii, reg_mr2_read_latency_dc, reg_mr4_ext_write_latency_ascii, reg_mr2_write_latency_dc, reg_mr4_parity_latency_ascii, reg_mr4_dm_ascii, reg_mr4_ecc_ascii);
               end
          end
          4'b0101 : col_cmd_print_str = $sformatf("CMD_ID= %0d, MODE_REGISTER= MR%0d, OPCODE= %0b >>> TRR= %0s, TRR-PS Select= %0s, TRR Mode BAn= %0s", mrs_cmd_cnt, col_ba, col_mrs_op, reg_mr5_trr_ascii, reg_mr5_trr_pc_select_ascii, reg_mr5_trr_mode_ba_n_ascii);
          4'b0110 : col_cmd_print_str = $sformatf("CMD_ID= %0d, MODE_REGISTER= MR%0d, OPCODE= %0b >>> imPRE tRP Value= %0s", mrs_cmd_cnt, col_ba, col_mrs_op, reg_mr6_imPRE_tRP_value_ascii);
          4'b0111 : col_cmd_print_str = $sformatf("CMD_ID= %0d, MODE_REGISTER= MR%0d, OPCODE= %0b >>> CATTRIP= %0s, MISR Control= %0s, Read Mux Control= %0s, Loopback= %0s", mrs_cmd_cnt, col_ba, col_mrs_op, reg_mr7_cattrip_ascii, reg_mr7_misr_control_ascii, reg_mr7_read_mux_control_ascii, reg_mr7_loopback_ascii);
          4'b1000 : col_cmd_print_str = $sformatf("CMD_ID= %0d, MODE_REGISTER= MR%0d, OPCODE= %0b >>> DA[28] Lockout= %0s", mrs_cmd_cnt, col_ba, col_mrs_op, reg_mr8_da28_lockout_ascii);
          4'b1001 : col_cmd_print_str = $sformatf("CMD_ID= %0d, MODE_REGISTER= MR%0d, OPCODE= %0b >>> RESERVED", mrs_cmd_cnt, col_ba, col_mrs_op);
          4'b1010 : col_cmd_print_str = $sformatf("CMD_ID= %0d, MODE_REGISTER= MR%0d, OPCODE= %0b >>> RESERVED", mrs_cmd_cnt, col_ba, col_mrs_op);
          4'b1011 : col_cmd_print_str = $sformatf("CMD_ID= %0d, MODE_REGISTER= MR%0d, OPCODE= %0b >>> RESERVED", mrs_cmd_cnt, col_ba, col_mrs_op);
          4'b1100 : col_cmd_print_str = $sformatf("CMD_ID= %0d, MODE_REGISTER= MR%0d, OPCODE= %0b >>> RESERVED", mrs_cmd_cnt, col_ba, col_mrs_op);
          4'b1101 : col_cmd_print_str = $sformatf("CMD_ID= %0d, MODE_REGISTER= MR%0d, OPCODE= %0b >>> RESERVED", mrs_cmd_cnt, col_ba, col_mrs_op);
          4'b1110 : col_cmd_print_str = $sformatf("CMD_ID= %0d, MODE_REGISTER= MR%0d, OPCODE= %0b >>> RESERVED", mrs_cmd_cnt, col_ba, col_mrs_op);
          4'b1111 : col_cmd_print_str = $sformatf("CMD_ID= %0d, MODE_REGISTER= MR%0d, OPCODE= %0b >>> Optional Internal Vref= %0s", mrs_cmd_cnt, col_ba, col_mrs_op, reg_mr15_opt_int_vref_ascii);
        endcase
    end
  endcase

  `hbm_info(TAG, $sformatf(">>>> %0s_COMMAND >>>> %0s", col_cmd_name, col_cmd_print_str), HBM_LOW)
endfunction


////////////////////////////////////////////////////////////////
// Task Description: update_col_dbg_signals_vif
//
////////////////////////////////////////////////////////////////
`ifdef EN_HBM_RESPONDER_DBG_MODE
task update_col_dbg_signals_vif();
  mem_vif.col_cmd_symbol        <=  col_cmd_symbol  ;        
  mem_vif.col_cmd               <=  col_cmd         ;        
  mem_vif.col_pc                <=  col_pc          ;        
  mem_vif.col_sid               <=  col_sid         ;        
  mem_vif.col_ba                <=  col_ba          ;        
  mem_vif.col_bg                <=  col_ba[3:2]     ;        
  mem_vif.col_b                 <=  col_ba[1:0]     ;        
  mem_vif.col_addr              <=  col_addr        ;        
  mem_vif.col_addr_5d1          <=  col_addr[5:1]   ;        
  mem_vif.col_mrs_op            <=  col_mrs_op      ;        
  mem_vif.col_par               <=  col_par         ;        
  mem_vif.col_row_addr          <=  col_row         ;        
  mem_vif.col_mem_addr          <=  col_mem_addr    ;       
  mem_vif.valid_col_cmd         <=  valid_col_cmd   ;        

  mem_vif.mrs_cmd_cnt           <=  mrs_cmd_cnt     ;
  mem_vif.wr_cmd_cnt_pc0        <=  wr_cmd_cnt_pc0  ;
  mem_vif.wr_cmd_cnt_pc1        <=  wr_cmd_cnt_pc1  ;
  mem_vif.wra_cmd_cnt_pc0       <=  wra_cmd_cnt_pc0 ;
  mem_vif.wra_cmd_cnt_pc1       <=  wra_cmd_cnt_pc1 ;
  mem_vif.rd_cmd_cnt_pc0        <=  rd_cmd_cnt_pc0  ;
  mem_vif.rd_cmd_cnt_pc1        <=  rd_cmd_cnt_pc1  ;
  mem_vif.rda_cmd_cnt_pc0       <=  rda_cmd_cnt_pc0 ;
  mem_vif.rda_cmd_cnt_pc1       <=  rda_cmd_cnt_pc1 ;
endtask
`endif


////////////////////////////////////////////////////////////////
// Task Description: 
//
////////////////////////////////////////////////////////////////
task row_initialize();
  row_cmd             = mem_vif.hbm_r[2:0];
  row_addr            = 0;
  row_ba              = 0;
  row_sid             = 0;
  row_pc              = 0;
  row_all             = 0;
  row_par             = 0;
  //row_cmd_symbol      = RNOP;
endtask


////////////////////////////////////////////////////////////////
// Task Description: 
//
////////////////////////////////////////////////////////////////
task row_cmd_decoder();
  forever begin
    wait_for_ck_t_edge();
    case(row_state)
      START  : begin
          valid_row_cmd       = 0;
          if(mem_vif.hbm_ck_t == 1/*to detect rise edge*/ && mem_vif.cke_valid_cmd) begin
            casex(mem_vif.hbm_r[2:0]) // Rising 1
              3'b?10  : begin /*ACTIVATE*/
                row_cmd[1:0]      = mem_vif.hbm_r[1:0];
                row_addr[14]      = C_HBM_VERSION == "HBM2e" ? mem_vif.hbm_r[6] : 
                                    C_HBM_VERSION == "HBM2" && C_HBM_DENSITY_CONFIG != "8G8H" ? mem_vif.hbm_r[2] : 0; //HBM2e Specific
                row_sid[0]        = C_HBM_VERSION == "HBM2e" ? mem_vif.hbm_r[2] : 
                                    C_HBM_VERSION == "HBM2" && C_HBM_DENSITY_CONFIG == "8G8H" ? mem_vif.hbm_r[2] : 0; //HBM2e Specific
                row_ba[2:0]       = mem_vif.hbm_r[5:3];
                row_cmd_symbol    = ACT;
                row_state         = ACT_F1; // move to Falling 1
              end
              3'b011  : begin /*PRECHARGE*/
                row_cmd           = mem_vif.hbm_r[2:0];
                row_ba[2:0]       = mem_vif.hbm_r[5:3];
                row_sid[1]        = mem_vif.hbm_r[6]; //HBM2e Specific
                row_cmd_symbol    = PRE;
                row_state         = PRE_F1; // move to Falling 1
              end
              3'b100  : begin /*REFRESH*/
                row_cmd           = mem_vif.hbm_r[2:0];
                row_ba[2:0]       = mem_vif.hbm_r[5:3];
                row_sid[1]        = mem_vif.hbm_r[6]; //HBM2e Specific
                row_cmd_symbol    = REF;
                row_state         = REF_F1; // move to Falling 1
              end
              3'b111  : begin /*RNOP*/
                row_initialize();
                row_cmd_symbol    = RNOP;
                row_state         = RNOP_F1;
              end
              default : begin
                row_initialize();
                row_state         = START;
                //`hbm_fatal(TAG, $sformatf("Invalid Row command Error. Seeing Invalid row command(R[2:0]= 3'b%0b when CKE=1 and CKE_r=1)", mem_vif.hbm_r[2:0]))
              end
            endcase
          end
          else if(mem_vif.hbm_ck_t == 1/*to detect rise edge*/ && mem_vif.cke_valid_row_entry_cmd) begin
            casex(mem_vif.hbm_r[2:0]) // Rising 1
              3'b111  : begin /*POWER-DOWN ENTRY*/
                row_cmd           = mem_vif.hbm_r[2:0];
                row_cmd_symbol    = PDE;
                row_state         = PDE_F1; // move to Falling 1
                entered_in_power_down_mode = 1;
              end
              3'b100  : begin /*SELF-REFRESH ENTRY*/
                row_cmd           = mem_vif.hbm_r[2:0];
                row_cmd_symbol    = SRE;
                row_state         = SRE_F1; // move to Falling 1
                entered_in_self_ref_mode = 1;
              end
              default : begin
                row_initialize();
                row_state         = START;
              end
            endcase
          end
          else if(mem_vif.hbm_ck_t == 1/*to detect rise edge*/ && mem_vif.cke_valid_row_exit_cmd) begin
            casex(mem_vif.hbm_r[2:0]) // Rising 1
              3'b111  : begin
                if(entered_in_power_down_mode == 1) begin /*POWER-DOWN EXIT*/
                  row_cmd           = mem_vif.hbm_r[2:0];
                  row_cmd_symbol    = PDX;
                  row_state         = PDX_F1; // move to Falling 1
                  entered_in_power_down_mode = 0;
                end
                else if(entered_in_self_ref_mode == 1) begin /*SELF-REFRESH EXIT*/
                  row_cmd           = mem_vif.hbm_r[2:0];
                  row_cmd_symbol    = SRX;
                  row_state         = SRX_F1; // move to Falling 1
                  entered_in_self_ref_mode = 0;
                end
                else begin /*Initialization Sequence*/ //FIXME need to write logic to detect initialization sequence
                  //`hbm_fatal(TAG, "Invalid Row Command Error. Sending Power-Down or Self Refresh Exit command when HBM device is not on Power-Down or Self Refresh Entry mode is invalid.")
                  //row_initialize();
                  //row_state     = "START";
                  row_initialize();
                  row_cmd_symbol    = RNOP;
                  row_state         = RNOP_F1;
                end
              end 
              default : begin
                row_initialize();
                row_state         = START;
              end
            endcase
          end
          else begin
            row_initialize();
            row_state         = START;
          end
      end

      ACT_F1 : begin // Falling 1
          row_addr[12:11]   = mem_vif.hbm_r[1:0];
          row_addr[13]      = mem_vif.hbm_r[4];
          row_pc            = mem_vif.hbm_r[3]; // pseudo channel selector
          row_ba[3]         = mem_vif.hbm_r[5];
          row_sid[1]        = mem_vif.hbm_r[6]; //HBM2e Specific
          row_par           = mem_vif.hbm_r[2];
          row_state         = ACT_R2; // move to Rising 2
      end
      
      ACT_R2  : begin // Rising 2
          row_addr[10:5]    = mem_vif.hbm_r[5:0];
          row_state         = ACT_F2; // move to Falling 2
      end
      
      ACT_F2  : begin // Falling 2
          row_addr[1:0]     = mem_vif.hbm_r[1:0];
          row_addr[4:2]     = mem_vif.hbm_r[5:3];
          row_par           = mem_vif.hbm_r[2];
          row_state         = START;
          valid_row_cmd     = 1;
          if(row_pc) act_cmd_cnt_pc1++; else act_cmd_cnt_pc0++;
      end

      PRE_F1  : begin // Falling 1
          row_all           = mem_vif.hbm_r[4];
          row_ba[3]         = mem_vif.hbm_r[5];
          row_pc            = mem_vif.hbm_r[3];
          row_sid[0]        = mem_vif.hbm_r[1]; //HBM2e Specific
          row_par           = mem_vif.hbm_r[2];
          row_state         = START;
          valid_row_cmd     = 1;
          if(row_all) begin 
            if(row_pc) pre_all_cmd_cnt_pc1++; else pre_all_cmd_cnt_pc0++;
            row_cmd_symbol    = PREA;
          end
          else begin 
            if(row_pc) pre_cmd_cnt_pc1++; else pre_cmd_cnt_pc0++;
          end
      end
      
      REF_F1  : begin // Falling 1
          row_all           = mem_vif.hbm_r[4];
          row_ba[3]         = mem_vif.hbm_r[5];
          row_pc            = mem_vif.hbm_r[3];
          row_sid[0]        = mem_vif.hbm_r[1]; //HBM2e Specific
          row_par           = mem_vif.hbm_r[2];
          row_state         = START;
          valid_row_cmd     = 1;
          if(row_all) begin 
            if(row_pc) ref_cmd_cnt_pc1++; else ref_cmd_cnt_pc0++;
          end
          else begin
            if(row_pc) ref_sb_cmd_cnt_pc1++; else ref_sb_cmd_cnt_pc0++;
            row_cmd_symbol    = REFSB;
          end
      end
      
      PDE_F1  : begin // Falling 1
          row_par           = mem_vif.hbm_r[2];
          row_state         = START;
          valid_row_cmd     = 1;
      end
      
      SRE_F1  : begin // Falling 1
          row_par           = mem_vif.hbm_r[2];
          row_state         = START;
          valid_row_cmd     = 1;
      end
      
      PDX_F1  : begin // Falling 1
          row_state         = START;
          valid_row_cmd     = 1;
      end
      
      SRX_F1  : begin // Falling 1
          row_state         = START;
          valid_row_cmd     = 1;
      end

      RNOP_F1  : begin // Falling 1
          row_par           = mem_vif.hbm_r[2];
          row_state         = START;
          //valid_row_cmd     = 1; // FIXME do we need to consider it as valid command
      end
    endcase

    if(valid_row_cmd == 1) begin
      execute_row_cmd(row_cmd_symbol, row_pc, row_sid, row_ba, row_addr);
      if(C_HBM_VERBOSITY_EN == 1) print_row_cmd_info();
    end
    invalid_traffic_check(row_cmd_symbol, row_pc, row_sid, row_ba, row_addr, 6'b0); // invalid RA/SID check as per device config
    `ifdef EN_HBM_RESPONDER_DBG_MODE
    update_row_dbg_signals_vif();
    `endif
  end
endtask


////////////////////////////////////////////////////////////////
// Task Description: execute_row_cmd 
//
////////////////////////////////////////////////////////////////
task execute_row_cmd(input hbm_command_t cmd, input bit row_pc, input bit [1:0] row_sid, input bit[3:0] row_ba, input bit[14:0] row_addr);
  case(cmd)
    ACT   : begin
          do_row_activate(row_pc, row_sid, row_ba, row_addr);
    end

    PRE,PREA    : begin
          do_row_precharge(cmd, row_pc, row_sid, row_ba);
    end
    
    //REF,REFSB   : begin
    //      do_refresh(row_cmd_symbol, row_pc, row_sid, row_ba);
    //end

    //PDE    : begin
    //      do_power_down_entry();
    //end

    //SRE    : begin
    //      do_self_refresh_entry();
    //end

    //PDX    : begin
    //      do_power_down_exit();
    //end
    //
    //SRX   : begin
    //      do_self_refresh_exit();
    //end
  endcase
endtask


////////////////////////////////////////////////////////////////
// Task Description: invalid_traffic_check
//
////////////////////////////////////////////////////////////////
task invalid_traffic_check(input hbm_command_t cmd, input bit pc, input bit [1:0] sid, input bit[3:0] ba, input bit[14:0] row, bit[5:0] col);
  // row addr check
  if(cmd == ACT) begin
    if(C_HBM_DENSITY_CONFIG inside {"6G4H", "12G8H", "12G12H"}) begin 
      if(row[14:13] == 2'b11) `hbm_fatal(TAG, $sformatf("Invalid value seen on Row Address[14:13]= 2'b11 as per JEDEC for Density= %0s(Density Code= %0s) :: MEM_CMD= %0s :: PC= 0x%0h, SID= 0x%0h, BA= 0x%0h, ROW= 0x%0h, COL= 0x%0h", C_HBM_DENSITY_CONFIG, get_density_code(C_HBM_DENSITY_CONFIG), cmd.name, pc, sid, ba, row, col))
    end

    if(C_HBM_DENSITY_CONFIG inside {"2G4H", "4G4H", "8G8H", "8G12H"}) begin
      if(row[14] == 1'b1) `hbm_fatal(TAG, $sformatf("Invalid value seen on Row Address[14]= 1 for Density= %0s(Density Code= %0s). The selected density supports only 14 row bits, but the given row addr is exceeding it :: MEM_CMD= %0s :: PC= 0x%0h, SID= 0x%0h, BA= 0x%0h, ROW= 0x%0h, COL= 0x%0h", C_HBM_DENSITY_CONFIG, get_density_code(C_HBM_DENSITY_CONFIG), cmd.name, pc, sid, ba, row, col))
    end
  end

  // sid and bank addr check
  if(cmd inside {ACT, PRE, REFSB, RD, RDA, WR, WRA}) begin
    // bank addr check
    if(C_HBM_DENSITY_CONFIG == "2G4H") begin
      if(ba[3] == 1'b1) `hbm_fatal(TAG, $sformatf("Invalid value seen on Bank Address[3]= 1 for Density= %0s(Density Code= %0s). The selected density supports only 3 bank bits, but the given bank addr is exceeding it :: MEM_CMD= %0s :: PC= 0x%0h, SID= 0x%0h, BA= 0x%0h, ROW= 0x%0h, COL= 0x%0h", C_HBM_DENSITY_CONFIG, get_density_code(C_HBM_DENSITY_CONFIG), cmd.name, pc, sid, ba, row, col))
    end

    // sid addr check
    if(C_HBM_DENSITY_CONFIG inside {"8G12H", "12G12H", "16G12H"}) begin 
      if(sid[1:0] == 2'b11) `hbm_fatal(TAG, $sformatf("Invalid value seen on SID[1:0]= 2'b11 as per JEDEC for Density= %0s(Density Code= %0s) :: MEM_CMD= %0s :: PC= 0x%0h, SID= 0x%0h, BA= 0x%0h, ROW= 0x%0h, COL= 0x%0h", C_HBM_DENSITY_CONFIG, get_density_code(C_HBM_DENSITY_CONFIG), cmd.name, pc, sid, ba, row, col))
    end

    if(C_HBM_DENSITY_CONFIG inside {"8G8H", "12G8H", "16G8H"}) begin 
      if(sid[1] == 1'b1) `hbm_fatal(TAG, $sformatf("Invalid value seen on SID[1]= 1 for Density= %0s(Density Code= %0s). The selected density supports only 1 sid bit, but the given sid addr is exceeding it :: MEM_CMD= %0s :: PC= 0x%0h, SID= 0x%0h, BA= 0x%0h, ROW= 0x%0h, COL= 0x%0h", C_HBM_DENSITY_CONFIG, get_density_code(C_HBM_DENSITY_CONFIG), cmd.name, pc, sid, ba, row, col))
    end

    if(C_HBM_DENSITY_CONFIG inside {"2G4H", "4G4H", "6G4H", "8G4H"}) begin
      if(sid != 0) `hbm_fatal(TAG, $sformatf("Invalid value seen on SID for Density= %0s(Density Code= %0s). The selected density does not support sid bits :: MEM_CMD= %0s :: PC= 0x%0h, SID= 0x%0h, BA= 0x%0h, ROW= 0x%0h, COL= 0x%0h", C_HBM_DENSITY_CONFIG, get_density_code(C_HBM_DENSITY_CONFIG), cmd.name, pc, sid, ba, row, col))
    end
  end
endtask


////////////////////////////////////////////////////////////////
// Function Description: get_density_code
//
////////////////////////////////////////////////////////////////
function string get_density_code(string density);
  string density_code = "";

  case(density)
    "2G4H"    : density_code  = "0010";
    "4G4H"    : density_code  = "0011";
    "6G4H"    : density_code  = "0101";
    "8G4H"    : density_code  = "0110";
    "8G8H"    : density_code  = "0100";
    "8G12H"   : density_code  = "1001";
    "12G8H"   : density_code  = "1000";
    "12G12H"  : density_code  = "1011";
    "16G8H"   : density_code  = "1010";
    "16G12H"  : density_code  = "1100";
  endcase

  return(density_code);
endfunction


////////////////////////////////////////////////////////////////
// Task Description: 
//
////////////////////////////////////////////////////////////////
task update_page_table(hbm_command_t cmd, bit pc, bit [1:0] row_sid, bit[3:0] row_ba, bit[C_HBM_ROW_ADDR_WIDTH-1:0] row_addr = 0);
  bit [C_HBM_PAGE_ADDR_WIDTH-1:0] page_addr;

  page_addr = get_page_addr(pc, row_sid, row_ba);
  
  case(cmd)
    ACT     :  begin 
                  if(!(hbm_memory_page_table[pc].exists(page_addr))) hbm_memory_page_table[pc][page_addr] = row_addr; 
                  else begin // Activate with Implicit Precharge 
                    if(C_HBM_CHANNEL_MODE == "PSEUDO_CHANNEL") hbm_memory_page_table[pc][page_addr] = row_addr;
                    else `hbm_fatal(TAG, $sformatf("Sending ACTIVATE command to open Row is invalid in LEGACY Mode. %0s", get_page_info(page_addr))) //FIXME does this check required?
                  end
    end
    PRE     : begin
                  if(hbm_memory_page_table[pc].exists(page_addr)) hbm_memory_page_table[pc].delete(page_addr); 
                  //else `hbm_warning(TAG, $sformatf("Sending PRECHARGE command to closed Row is invalid. %0s", get_page_info(page_addr))) //FIXME does this check required?
    end
    PREA    :
                  if(hbm_memory_page_table[pc].num() > 0) hbm_memory_page_table[pc].delete(); 
                  //else `hbm_warning(TAG, $sformatf("Sending PRECHARGE_ALL command while none of the Rows are opened is invalid. %0s", get_page_info(page_addr))) //FIXME does this check required?
    default : `hbm_fatal(TAG, $sformatf("IERR-01: Internal Error."))
  endcase
endtask


////////////////////////////////////////////////////////////////
// Task Description: 
//
////////////////////////////////////////////////////////////////
task do_row_activate(bit row_pc, bit row_sid, bit[3:0] row_ba, bit [C_HBM_ROW_ADDR_WIDTH-1:0] row_addr);
  update_page_table(ACT, row_pc, row_sid, row_ba, row_addr);
endtask


////////////////////////////////////////////////////////////////
// Task Description: 
//
////////////////////////////////////////////////////////////////
task do_row_precharge(hbm_command_t cmd, bit row_pc, bit row_sid, bit[3:0] row_ba);
  update_page_table(cmd, row_pc, row_sid, row_ba);
endtask


////////////////////////////////////////////////////////////////
// Task Description: 
//
////////////////////////////////////////////////////////////////
task do_refresh(hbm_command_t cmd, bit row_pc, bit row_sid, bit[3:0] row_ba);
  case(cmd)
    REF   : begin 
    end 
    REFSB : begin
    end
  endcase
endtask


////////////////////////////////////////////////////////////////
// Task Description: 
//
////////////////////////////////////////////////////////////////
task do_power_down_entry();
endtask


////////////////////////////////////////////////////////////////
// Task Description: 
//
////////////////////////////////////////////////////////////////
task do_power_down_exit();
endtask


////////////////////////////////////////////////////////////////
// Task Description: 
//
////////////////////////////////////////////////////////////////
task do_self_refresh_entry();
endtask


////////////////////////////////////////////////////////////////
// Task Description: 
//
////////////////////////////////////////////////////////////////
task do_self_refresh_exit();
endtask


////////////////////////////////////////////////////////////////
// Task Description: print_row_cmd_info 
//
////////////////////////////////////////////////////////////////
function void print_row_cmd_info();
  string  row_cmd_print_str;
  string  row_cmd_name; 

  case(row_cmd_symbol)
    ACT : begin
        row_cmd_name      = "ACTIVATE";
        row_cmd_print_str = $sformatf("CMD_ID= %0d, PC= %0d, SID= 0x%0h, BG= 0x%0h, BANK= 0x%0h, ROW= %0h", (row_pc == 0) ? act_cmd_cnt_pc0 : act_cmd_cnt_pc1, row_pc, row_sid, row_ba[3:2], row_ba[1:0], row_addr);
    end
    PRE : begin
        row_cmd_name      = "PRECHARGE";
        row_cmd_print_str = $sformatf("CMD_ID= %0d, PC= %0d, SID= 0x%0h, BG= 0x%0h, BANK= 0x%0h", (row_pc == 0) ? pre_cmd_cnt_pc0 : pre_cmd_cnt_pc1, row_pc, row_sid[0], row_ba[3:2], row_ba[1:0]);
    end
    PREA : begin
        row_cmd_name      = "PRECHARGE_ALL";
        row_cmd_print_str = $sformatf("CMD_ID= %0d, PC= %0d", (row_pc == 0) ? pre_all_cmd_cnt_pc0 : pre_all_cmd_cnt_pc1, row_pc);
    end
    REFSB : begin
        row_cmd_name      = "SINGLE_BANK_REFRESH";
        row_cmd_print_str = $sformatf("CMD_ID= %0d, PC= %0d, SID= 0x%0h, BG= 0x%0h, BANK= 0x%0h", (row_pc == 0) ? ref_sb_cmd_cnt_pc0 : ref_sb_cmd_cnt_pc1, row_pc, row_sid[0], row_ba[3:2], row_ba[1:0]);
    end
    REF : begin
        row_cmd_name      = "REFRESH";
        row_cmd_print_str = $sformatf("CMD_ID= %0d, PC= %0d", (row_pc == 0) ? ref_cmd_cnt_pc0 : ref_cmd_cnt_pc1, row_pc);
    end
    PDE : begin
        row_cmd_name      = "POWER_DOWN_ENTRY";
        row_cmd_print_str = $sformatf("DRAM into Power Down Entry Mode");
    end
    SRE : begin
        row_cmd_name      = "SELF_REFRESH_ENTRY";
        row_cmd_print_str = $sformatf("DRAM into Self Refresh Entry Mode");
    end
    PDX : begin
        row_cmd_name      = "POWER_DOWN_EXIT";
        row_cmd_print_str = $sformatf("DRAM into Power Down Exit Mode");
    end
    SRX : begin
        row_cmd_name      = "SELF_REFRESH_EXIT";
        row_cmd_print_str = $sformatf("DRAM into Self Refresh Exit Mode");
    end
  endcase

  `hbm_info(TAG, $sformatf(">>>> %0s_COMMAND >>>> %0s", row_cmd_name, row_cmd_print_str), HBM_LOW)
endfunction


////////////////////////////////////////////////////////////////
// Task Description: update_row_dbg_signals_vif
//
////////////////////////////////////////////////////////////////
`ifdef EN_HBM_RESPONDER_DBG_MODE
task update_row_dbg_signals_vif();
  mem_vif.row_cmd_symbol                <=  row_cmd_symbol          ;        
  mem_vif.row_cmd                       <=  row_cmd                 ;        
  mem_vif.row_all                       <=  row_all                 ;        
  mem_vif.row_pc                        <=  row_pc                  ;        
  mem_vif.row_sid                       <=  row_sid                 ;        
  mem_vif.row_ba                        <=  row_ba                  ;        
  mem_vif.row_bg                        <=  row_ba[3:2]             ;        
  mem_vif.row_b                         <=  row_ba[1:0]             ;        
  mem_vif.row_addr                      <=  row_addr                ;        
  mem_vif.row_par                       <=  row_par                 ;        
  mem_vif.valid_row_cmd                 <=  valid_row_cmd           ;        

  mem_vif.entered_in_power_down_mode    <=  entered_in_power_down_mode;
  mem_vif.entered_in_self_ref_mode      <=  entered_in_self_ref_mode;

  mem_vif.act_cmd_cnt_pc0               <=  act_cmd_cnt_pc0         ;
  mem_vif.act_cmd_cnt_pc1               <=  act_cmd_cnt_pc1         ;
  mem_vif.pre_cmd_cnt_pc0               <=  pre_cmd_cnt_pc0         ;
  mem_vif.pre_cmd_cnt_pc1               <=  pre_cmd_cnt_pc1         ;
  mem_vif.pre_all_cmd_cnt_pc0           <=  pre_all_cmd_cnt_pc0     ;
  mem_vif.pre_all_cmd_cnt_pc1           <=  pre_all_cmd_cnt_pc1     ;
  mem_vif.ref_sb_cmd_cnt_pc0            <=  ref_sb_cmd_cnt_pc0      ;
  mem_vif.ref_sb_cmd_cnt_pc1            <=  ref_sb_cmd_cnt_pc1      ;
  mem_vif.ref_cmd_cnt_pc0               <=  ref_cmd_cnt_pc0         ;
  mem_vif.ref_cmd_cnt_pc1               <=  ref_cmd_cnt_pc1         ;
endtask
`endif


////////////////////////////////////////////////////////////////
// Task Description: wait_for_ck_t_edge 
//
////////////////////////////////////////////////////////////////
task wait_for_ck_t_edge();
  //@(edge mem_vif.hbm_ck_t);
  @(posedge mem_vif.hbm_ck_t or negedge mem_vif.hbm_ck_t); // Fix for CR-109677. @(edge clk) is not supported on IUS and XCELIUM tool
  #0; // Fix for Inout signal Hi-Z glitch noticed on ULTRASCALE HOOD HBM2 MC RTL CHa_ck_t_lt_pad signal. This glitch causes the edge event to happen twice at same timeslot and end-up with false FSM state advancing in less edges than actual in col_cmd_decoder/row_cmd_decoder.
endtask

////////////////////////////////////////////////////////////////
// Task Description: wait_for_ck_t_edge_clks
//
////////////////////////////////////////////////////////////////
task wait_for_ck_t_edge_clks(int count);
  repeat(count) begin
    //@(edge mem_vif.hbm_ck_t);
    @(posedge mem_vif.hbm_ck_t or negedge mem_vif.hbm_ck_t); // Fix for CR-109677. @(edge clk) is not supported on IUS and XCELIUM tool
    #0; // Fix for Inout signal Hi-Z glitch noticed on ULTRASCALE HOOD HBM2 MC RTL CHa_ck_t_lt_pad signal. This glitch causes the edge event to happen twice at same timeslot and end-up with false FSM state advancing in less edges than actual in col_cmd_decoder/row_cmd_decoder.
  end
endtask


////////////////////////////////////////////////////////////////
// Task Description: wait_for_ck_t_posedge
//
////////////////////////////////////////////////////////////////
task wait_for_ck_t_posedge();
  @(posedge mem_vif.hbm_ck_t);
  #0; // Fix for Inout signal Hi-Z glitch noticed on ULTRASCALE HOOD HBM2 MC RTL CHa_ck_t_lt_pad signal. This glitch causes the edge event to happen twice at same timeslot and end-up false TCK calculation
endtask


////////////////////////////////////////////////////////////////
// Task Description: wait_for_ck_t_posedge_clks
//
////////////////////////////////////////////////////////////////
task wait_for_ck_t_posedge_clks(int count);
  repeat(count) begin
    @(posedge mem_vif.hbm_ck_t);
  end
  #0; // Fix for Inout signal Hi-Z glitch noticed on ULTRASCALE HOOD HBM2 MC RTL CHa_ck_t_lt_pad signal. This glitch causes the edge event to happen twice at same timeslot
endtask


////////////////////////////////////////////////////////////////
// Task Description: wait_for_ck_t_negedge
//
////////////////////////////////////////////////////////////////
task wait_for_ck_t_negedge();
  @(negedge mem_vif.hbm_ck_t);
  #0; // Fix for Inout signal Hi-Z glitch noticed on ULTRASCALE HOOD HBM2 MC RTL CHa_ck_t_lt_pad signal. This glitch causes the edge event to happen twice at same timeslot
endtask


////////////////////////////////////////////////////////////////
// Task Description: wait_for_cke_posedge
//
////////////////////////////////////////////////////////////////
task wait_for_cke_posedge();
  @(posedge mem_vif.hbm_cke);
endtask


////////////////////////////////////////////////////////////////
// Task Description: wait_for_cke_negedge
//
////////////////////////////////////////////////////////////////
task wait_for_cke_negedge();
  @(negedge mem_vif.hbm_cke);
endtask


////////////////////////////////////////////////////////////////
// Task Description: wait_for_wdqs_t_posedge
//
////////////////////////////////////////////////////////////////
task wait_for_wdqs_t_posedge(input bit[1:0] index = 0);
  @(posedge mem_vif.hbm_wdqs_t[index]);
endtask


////////////////////////////////////////////////////////////////
// Task Description: wait_for_wdqs_t_negedge
//
////////////////////////////////////////////////////////////////
task wait_for_wdqs_t_negedge(input bit[1:0] index = 0);
  @(negedge mem_vif.hbm_wdqs_t[index]);
endtask


////////////////////////////////////////////////////////////////
// Task Description: wait_for_reset_asserted
//
////////////////////////////////////////////////////////////////
task wait_for_reset_asserted();
  if(is_it_por) begin 
    wait(mem_vif.reset_n === 0);
    is_it_por = 0;
  end
  else begin 
    @(negedge mem_vif.reset_n);
  end
endtask


////////////////////////////////////////////////////////////////
// Task Description: wait_for_reset_deasserted
//
////////////////////////////////////////////////////////////////
task wait_for_reset_deasserted();
  @(posedge mem_vif.reset_n);
endtask


////////////////////////////////////////////////////////////////
// Task Description: wait_for_write_latency
//
////////////////////////////////////////////////////////////////
task wait_for_write_latency();
  time time_step = 1ps;

  int wait_num_ck_t_edge;

  `hbm_info(TAG, $sformatf("HBMDBG :: wait_for_write_latency :: Wait Started with reg_mr2_write_latency_dc=%0d, C_HBM_TDQSS=%0d, TCK=%0d, delay=%0dps", reg_mr2_write_latency_dc, C_HBM_TDQSS, TCK, (((reg_mr2_write_latency_dc-1)*TCK) + (C_HBM_TDQSS*TCK) + (TCK/2))), HBM_DEBUG)

  do_tck_check();

  `ifndef XILINX_SIMULATOR
  //#((((reg_mr2_write_latency_dc-1)*TCK) + (C_HBM_TDQSS*TCK) + (TCK/2)) * time_step);
  #((((reg_mr2_write_latency_dc-1)*TCK) + (C_HBM_TDQSS*TCK)) * time_step);
  `else
  wait_num_ck_t_edge =  ((reg_mr2_write_latency_dc-1)+C_HBM_TDQSS)*2;
  wait_for_ck_t_edge_clks(wait_num_ck_t_edge);
  `endif
  
  `hbm_info(TAG, "HBMDBG :: wait_for_write_latency :: Wait Done", HBM_DEBUG)
endtask


////////////////////////////////////////////////////////////////
// Task Description: wait_for_read_data_latency
//
////////////////////////////////////////////////////////////////
task wait_for_read_data_latency();
  time time_step = 1ps;

  int wait_num_ck_t_edge;

  `hbm_info(TAG, $sformatf("HBMDBG :: wait_for_read_data_latency :: Wait Started with reg_mr2_read_latency_dc=%0d, C_HBM_TDQSCK=%0f, C_HBM_TDQSQ=%0d, TCK=%0d, delay=%0dps", reg_mr2_read_latency_dc, C_HBM_TDQSCK, C_HBM_TDQSQ, TCK, (((reg_mr2_read_latency_dc*TCK) + (C_HBM_TDQSCK*1000) + C_HBM_TDQSQ)-(TCK/2))), HBM_DEBUG)

  do_tck_check();

  `ifndef XILINX_SIMULATOR
  #((((reg_mr2_read_latency_dc*TCK) + (C_HBM_TDQSCK*1000) + C_HBM_TDQSQ)-(TCK/2)) * time_step);
  `else
  wait_num_ck_t_edge =  (reg_mr2_read_latency_dc * 2) - 1;
  wait_for_ck_t_edge_clks(wait_num_ck_t_edge);
  #(((C_HBM_TDQSCK*1000) + C_HBM_TDQSQ) * time_step);
  `endif
  
  `hbm_info(TAG, "HBMDBG :: :: wait_for_read_data_latency :: Wait Done", HBM_DEBUG)
endtask


////////////////////////////////////////////////////////////////
// Task Description: wait_for_read_dqs_latency
//
////////////////////////////////////////////////////////////////
task wait_for_read_dqs_latency(bit wait_for_preamble = 1, bit wait_for_postamble = 0);
  time          time_step = 1ps;

  int wait_num_ck_t_edge;

  //NOTE : wait_for_preamble and wait_for_postamble setting should not be enbaled together in single task call

  if(wait_for_preamble)
   `hbm_info(TAG, $sformatf("HBMDBG :: wait_for_read_dqs_latency :: wait_for_preamble :: Wait Started with reg_mr2_read_latency_dc=%0d, C_HBM_TDQSCK=%0f, TCK=%0d, delay=%0dps", reg_mr2_read_latency_dc, C_HBM_TDQSCK, TCK, ((((reg_mr2_read_latency_dc-1)*TCK)+(C_HBM_TDQSCK*1000))-(TCK/2))), HBM_DEBUG)
  else if(wait_for_postamble)
   `hbm_info(TAG, $sformatf("HBMDBG :: wait_for_read_dqs_latency :: wait_for_preamble :: Wait Started with reg_mr2_read_latency_dc=%0d, C_HBM_TDQSCK=%0f, TCK=%0d, delay=%0dps", reg_mr2_read_latency_dc, C_HBM_TDQSCK, TCK, ((((reg_mr2_read_latency_dc+2)*TCK)+(C_HBM_TDQSCK*1000))-(TCK/2))), HBM_DEBUG)
  else
    `hbm_info(TAG, $sformatf("HBMDBG :: wait_for_read_dqs_latency :: Wait Started with reg_mr2_read_latency_dc=%0d, C_HBM_TDQSCK=%0f, TCK=%0d, delay=%0dps", reg_mr2_read_latency_dc, C_HBM_TDQSCK, TCK, ((((reg_mr2_read_latency_dc)*TCK)+(C_HBM_TDQSCK*1000))-(TCK/2))), HBM_DEBUG)

  do_tck_check();

  `ifndef XILINX_SIMULATOR
  if(wait_for_preamble)
    #(((((reg_mr2_read_latency_dc-1)*TCK)+(C_HBM_TDQSCK*1000))-(TCK/2)) * time_step);
  else // wait_for_burst
    #((((reg_mr2_read_latency_dc*TCK) + (C_HBM_TDQSCK*1000))-(TCK/2)) * time_step); // removed preamble
  `else
  if(wait_for_preamble)
    wait_num_ck_t_edge =  ((reg_mr2_read_latency_dc-1) * 2) - 1;
  else if(wait_for_postamble)
    wait_num_ck_t_edge =  ((reg_mr2_read_latency_dc+2) * 2) - 1;
  else // wait_for_burst
    wait_num_ck_t_edge =  (reg_mr2_read_latency_dc * 2) - 1;
  wait_for_ck_t_edge_clks(wait_num_ck_t_edge);
  #((C_HBM_TDQSCK*1000) * time_step);
  `endif
  
  `hbm_info(TAG, "HBMDBG :: wait_for_read_dqs_latency :: Wait Done", HBM_DEBUG)
endtask


////////////////////////////////////////////////////////////////
// Task Description: wait_for_seamless_read_burst_window
//
////////////////////////////////////////////////////////////////
task wait_for_seamless_read_burst_window();
  time time_step = 1ps;

  int wait_num_ck_t_edge;

  do_tck_check();

  `hbm_info(TAG, $sformatf("HBMDBG :: wait_for_seamless_read_burst_window :: reg_mr3_burst_length_dc= %0d, TCK= %0d, delay= %0d", reg_mr3_burst_length_dc, TCK, (((reg_mr3_burst_length_dc/2)+0.2)*TCK)), HBM_DEBUG)

  `ifndef XILINX_SIMULATOR
  #((((reg_mr3_burst_length_dc/2)+0.2)*TCK)*time_step); // added 0.2TCK to sample valid PC value 
  `else
  wait_num_ck_t_edge = (reg_mr3_burst_length_dc/2)*2;
  wait_for_ck_t_edge_clks(wait_num_ck_t_edge);
  #(0.2*TCK*time_step); // added 0.2TCK to sample valid PC value
  `endif

  `hbm_info(TAG, "HBMDBG :: wait_for_seamless_read_burst_window :: Wait Done", HBM_DEBUG)
endtask


////////////////////////////////////////////////////////////////
// Task Description: wait_for_half_tck
//
////////////////////////////////////////////////////////////////
task wait_for_half_tck();
  time time_step = 1ps;

  do_tck_check();

  //`hbm_info(TAG, $sformatf("HBMDBG :: wait_for_half_tck :: Wait Started with TCK=%0d, delay=%0dps", TCK, TCK/2), HBM_DEBUG)
  #((TCK/2) * time_step);
  //`hbm_info(TAG, "HBMDBG :: wait_for_half_tck :: Wait Done", HBM_DEBUG)
endtask


////////////////////////////////////////////////////////////////
// Task Description: wait_for_tck 
//
////////////////////////////////////////////////////////////////
task wait_for_tck();
  time time_step = 1ps;

  do_tck_check();

  //`hbm_info(TAG, $sformatf("HBMDBG :: wait_for_tck :: Wait Started with delay(TCK)=%0dps", TCK), HBM_DEBUG)
  #(TCK * time_step);
  //`hbm_info(TAG, "HBMDBG :: wait_for_tck :: Wait Done", HBM_DEBUG)
endtask


////////////////////////////////////////////////////////////////
// Task Description: wait_for_tinit6 
//
////////////////////////////////////////////////////////////////
task wait_for_tinit6();
  time time_step = 1ps;

  #((C_HBM_TINIT6*1000)*time_step); 
endtask


////////////////////////////////////////////////////////////////
// Task Description: do_tck_check
//
////////////////////////////////////////////////////////////////
function void do_tck_check();
  if(TCK <= 0) `hbm_fatal(TAG, $sformatf("IERR-02: Internal Error."))
endfunction


////////////////////////////////////////////////////////////////
// Task Description:  set_tck
//
////////////////////////////////////////////////////////////////
function void set_tck(int TCK);
  this.TCK = TCK;
endfunction


////////////////////////////////////////////////////////////////
// Task Description:  get_tck
//
////////////////////////////////////////////////////////////////
function int get_tck();
  do_tck_check();
  return(TCK);
endfunction

endclass


//////////////////////////////////////////////////////
// HBM Responder class instance
//////////////////////////////////////////////////////
hbm_responder_class  hbm_mem_ch[C_HBM_NO_OF_CHANNEL];


//////////////////////////////////////////////////////
// Main
//////////////////////////////////////////////////////
initial begin
  for(int CHANNEL=0; CHANNEL < C_HBM_NO_OF_CHANNEL; CHANNEL++) begin
    case(CHANNEL)
      0 : begin
            hbm_mem_ch[0]           = new($sformatf("HBM_CHa"));
            hbm_mem_ch[0].mem_vif   = CHa_mem_if;
            hbm_mem_ch[0].run();
      end
      1 : begin
            hbm_mem_ch[1]           = new($sformatf("HBM_CHb"));
            hbm_mem_ch[1].mem_vif   = CHb_mem_if;
            hbm_mem_ch[1].run();
      end
      2 : begin
            hbm_mem_ch[2]           = new($sformatf("HBM_CHc"));
            hbm_mem_ch[2].mem_vif   = CHc_mem_if;
            hbm_mem_ch[2].run();
      end
      3 : begin
            hbm_mem_ch[3]           = new($sformatf("HBM_CHd"));
            hbm_mem_ch[3].mem_vif   = CHd_mem_if;
            hbm_mem_ch[3].run();
      end
      4 : begin
            hbm_mem_ch[4]           = new($sformatf("HBM_CHe"));
            hbm_mem_ch[4].mem_vif   = CHe_mem_if;
            hbm_mem_ch[4].run();
      end
      5 : begin
            hbm_mem_ch[5]           = new($sformatf("HBM_CHf"));
            hbm_mem_ch[5].mem_vif   = CHf_mem_if;
            hbm_mem_ch[5].run();
      end
      6 : begin
            hbm_mem_ch[6]           = new($sformatf("HBM_CHg"));
            hbm_mem_ch[6].mem_vif   = CHg_mem_if;
            hbm_mem_ch[6].run();
      end
      7 : begin
            hbm_mem_ch[7]           = new($sformatf("HBM_CHh"));
            hbm_mem_ch[7].mem_vif   = CHh_mem_if;
            hbm_mem_ch[7].run();
      end
    endcase
  end
end


//////////////////////////////////////////////////////
// Parameter Validation checks
//////////////////////////////////////////////////////
//string supported_density_cfg;
initial begin
// C_HBM_DENSITY_CONFIG
//  supported_density_cfg = "\
//                            \n\"16G8H\"   (JEDEC Density code= 1010)\
//                            \n\"8G8H\"    (JEDEC Density code= 0100)\
//                            \n\"8G4H\"    (JEDEC Density code= 0110)\
//                          ";
//  if(!(C_HBM_DENSITY_CONFIG inside {"16G8H", "8G8H", "8G4H"}))
//    `hbm_fatal("HBM_RESPONDER", $sformatf("Invalid Density configuration is set on C_HBM_DENSITY_CONFIG=%0s parameter. Supported values are, %0s", C_HBM_DENSITY_CONFIG, supported_density_cfg))

// C_HBM_CHANNEL_MODE 
  if(C_HBM_CHANNEL_MODE != "PSEUDO_CHANNEL")
    `hbm_fatal("HBM_RESPONDER", $sformatf("Invalid Channel type is set on C_HBM_CHANNEL_MODE=%0s parameter. Supported value is \"PSEUDO_CHANNEL\"", C_HBM_CHANNEL_MODE))

// C_HBM_VERSION
  if(!(C_HBM_VERSION inside {"HBM2", "HBM2e"}))
    `hbm_fatal("HBM_RESPONDER", $sformatf("Invalid HBM Version is set on C_HBM_VERSION=%0s parameter. Supported Versions are \"HBM2\" and \"HBM2e\"", C_HBM_VERSION))
end

endmodule


`endif
