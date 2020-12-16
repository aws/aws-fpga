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
//  /   /         Filename           : ddr4_v2_2_10_cal_addr_decode.sv
// /___/   /\     Date Last Modified : $Date: 2015/04/30 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                   ddr4_v2_2_10_cal_addr_decode module
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
`elsif _VCP 
    `ifndef CALIB_SIM
       `define SIMULATION
     `endif
`elsif XILINX_SIMULATOR 
    `ifndef CALIB_SIM
       `define SIMULATION
     `endif
`endif

module ddr4_v2_2_10_cal_addr_decode  #
  (
   parameter MEMORY_CONFIGURATION       = "COMPONENT", //COMPONENT/UDIMM/SODIMM/RDIMM
   parameter DRAM_WIDTH   = 8,
   parameter DBYTES       = 4, //Data Bytes
   parameter ABITS        = 18, //ADDRESS BITS
   parameter BABITS = 4,
   parameter BGBITS = 4,
   parameter CKEBITS =4,
   parameter CKBITS = 1,
   parameter CSBITS =2,
   parameter RANKS =2,
   parameter RNK_BITS = 1,
   parameter S_HEIGHT = 1,
   parameter LR_WIDTH = 1,
   parameter ODTBITS = 4,
   parameter ODTWR     = 16'h0033,
   parameter ODTWRDEL  = 5'd8,
   parameter ODTWRDUR  = 4'd6,
   parameter ODTWRODEL = 5'd9,
   parameter ODTWRODUR = 4'd6,
   parameter ODTRD     = 16'h0012,
   parameter ODTRDDEL  = 5'd11,
   parameter ODTRDDUR  = 4'd6,
   parameter ODTRDODEL = 5'd9,
   parameter ODTRDODUR = 4'd6,
   parameter ODTNOP    = 16'h0000,
   parameter USE_CS_PORT = 1,
   parameter MEM = "DDR4",
   parameter TCQ = 100,
   parameter CLK_2TO1 = "TRUE",
   parameter LRDIMM_EN = 0, // LRDIMM Mode
   parameter NIBBLE_CNT_WIDTH = 2,
   parameter CPLX_PAT_LENGTH  = "LONG",
   parameter EXTRA_CMD_DELAY = 0,
   parameter WL = 9,
   parameter INITIAL_DBI_WR      = 0,
   parameter INITIAL_DBI_RD      = 0,
   parameter RD_VREF_VAL         = 7'h2E,
   parameter CLAMSHELL           = "OFF",
   
   parameter CAL_STATUS_REG_SIZE = 0,
   parameter PRE_STATUS_ADDR     = 0,
   parameter POST_STATUS_ADDR    = 0,
   parameter RANK0_STATUS0_ADDR  = 0,
   parameter RANK1_STATUS0_ADDR  = 0,
   parameter RANK2_STATUS0_ADDR  = 0,
   parameter RANK3_STATUS0_ADDR  = 0,
   parameter ERROR0_ADDR         = 0,
   parameter ERROR1_ADDR         = 0,
   parameter ERROR_CODE_ADDR     = 0,

   // Migration parameters
   parameter                  MIGRATION = "OFF",
   parameter [8*CKBITS-1:0]   CK_SKEW   = {CKBITS{8'b0}},
   parameter [8*ABITS-1:0]    ADDR_SKEW = {{8'b0}},
   parameter [7:0]            ACT_SKEW  = 8'b0,
   parameter [7:0]            PAR_SKEW  = 8'b0,
   parameter [8*BABITS-1:0]   BA_SKEW   = {BABITS{8'b0}},
   parameter [8*BGBITS-1:0]   BG_SKEW   = {BGBITS{8'b0}},
   parameter [8*CSBITS-1:0]   CS_SKEW   = {CSBITS{8'b0}},
   parameter [8*CKEBITS-1:0]  CKE_SKEW  = {CKEBITS{8'b0}},
   parameter [8*ODTBITS-1:0]  ODT_SKEW  = {ODTBITS{8'b0}},
   parameter [8*LR_WIDTH-1:0] C_SKEW    = {LR_WIDTH{8'b0}}

  )
  (
   input                          clk,
   input                          rst,                    //sync reset

   //MicroBlaze signals
   input [27:0]                   io_address,
   input                          io_addr_strobe,
   input                          io_write_strobe,
   input [31:0]                   mb_to_addr_dec_data,    //io_write_data - MAN - change to io_write_data
   output reg [31:0]              io_read_data,  	
   output reg                     io_ready_lvl = 1'b0,
   output reg                     ub_ready = 1'b0,        //Initialize to zero at bit stream download

   //RIU signals
   input [20-1:0]            riu2clb_valid,          //read valid from RIU

   //FIFO Info from Xiphy
   output reg [DBYTES*13-1:0]     clb2phy_fifo_rden,
   
   input [7:0] phy2clb_rd_dq_bits,
   output [8:0] bisc_byte,


   
   //Vref value
   output reg [DBYTES*7-1:0]       rd_vref_value,
   //DBI control signals
   output reg                     cal_dbi_wr,
   output reg                     cal_dbi_rd,

   //Configuration Read from rom
   input [31:0]                   config_rd_data,
   output reg [7:0]               config_rd_addr,
   //XSDB Port
   output reg                     xsdb_rd_en,
   output reg                     xsdb_wr_en,
   output reg [8:0]               xsdb_wr_data,
   output reg [15:0]              xsdb_addr,
   input      [8:0]               xsdb_rd_data,

   //Initialization
   input                          bisc_complete,    // Initial BISC has completed, or is disabled
   input                          phy_ready,        // VTC is running, phy is ready
   input                          rtl_initDone,         // RTL initialization done
   output reg                     ub_initDone,      // MB initialization  done
   output reg                     calDone,          //calibration is done
   output reg                     en_vtc,          //calibration is done

   input                          stop_gate_tracking_req,
   output reg                     stop_gate_tracking_ack,
   input                          app_mem_init_skip,
   input                          app_restore_en,
   input                          app_restore_complete,

   input                          traffic_wr_done,
   input                          traffic_status_err_bit_valid,
   input                          traffic_status_err_type_valid,
   input                          traffic_status_err_type,
   input                          traffic_status_done,
   input                          traffic_status_watch_dog_hang,
   input [DBYTES*8*8-1:0]         traffic_error,
   
   output reg                     traffic_clr_error,
   output reg                     traffic_start,
   output reg                     traffic_rst,
   output reg                     traffic_err_chk_en,
   output reg [3:0]               traffic_instr_addr_mode,
   output reg [3:0] 			  traffic_instr_data_mode,
   output reg [3:0] 			  traffic_instr_rw_mode,
   output reg [1:0] 			  traffic_instr_rw_submode,
   output reg [31:0] 	          traffic_instr_num_of_iter,
   output reg [5:0]               traffic_instr_nxt_instr,
   
   input  [3:0]                   win_start,
   input                          gt_data_ready,
   //DQ In/Out signals
   input  [DBYTES*8*8-1:0]        mcal_DQIn,
   input  [DBYTES*8-1:0]          mcal_DMIn_n,
   input                          mc_clb2phy_fifo_rden_nxt,
   output reg [DBYTES*8*8-1:0]    cal_DQOut,
   output reg [DBYTES*8-1:0]      cal_DMOut_n = {(DBYTES*8){1'b0}},
   output wire [ABITS*8-1:0]      cal_ADR,
   output wire [7:0]              cal_RAS,
   output wire [7:0]              cal_CAS,
   output wire [7:0]              cal_WE,

   //Control signals
   output      [7:0]              cal_RESET_n,
   output wire [7:0]              cal_ACT_n,
   output      [BABITS*8-1:0]     cal_BA,
   output      [BGBITS*8-1:0]     cal_BG,
   output      [LR_WIDTH*8-1:0]   cal_C,
   output      [CKEBITS*8-1:0]    cal_CKE,
   output      [CSBITS*8-1:0]     cal_CS_n,
   output      [ODTBITS*8-1:0]    cal_ODT,
   output      [7:0]              cal_PAR,
   output reg                     cal_mrs,
   output reg                     cal_inv,

   //RANK selection
   output reg [DBYTES*4-1:0]       clb2phy_wrcs0_upp,
   output reg [DBYTES*4-1:0]       clb2phy_wrcs1_upp,
   output reg [DBYTES*4-1:0]       clb2phy_wrcs0_low,
   output reg [DBYTES*4-1:0]       clb2phy_wrcs1_low,

   //RANK selection
   output reg [DBYTES*4-1:0]       clb2phy_rdcs0_upp,
   output reg [DBYTES*4-1:0]       clb2phy_rdcs1_upp,
   output reg [DBYTES*4-1:0]       clb2phy_rdcs0_low,
   output reg [DBYTES*4-1:0]       clb2phy_rdcs1_low,

   //CS position
   output reg [1:0]               casSlot = 'b0,
   //For read
   output reg                     rdCAS = 'b0,
   output reg                     clear_fifo_rden,
   //For write
   output reg                     wrCAS = 'b0,
   input                          wrDataEn,
   input [1:0]                    calRank,
   //Read Latency
   output reg [DBYTES*6-1:0]       lowCL0 = 'b0,
   output reg [DBYTES*6-1:0]       lowCL1 = 'b0,
   output reg [DBYTES*6-1:0]       lowCL2 = 'b0,
   output reg [DBYTES*6-1:0]       lowCL3 = 'b0,
   output reg [DBYTES*6-1:0]       uppCL0 = 'b0,
   output reg [DBYTES*6-1:0]       uppCL1 = 'b0,
   output reg [DBYTES*6-1:0]       uppCL2 = 'b0,
   output reg [DBYTES*6-1:0]       uppCL3 = 'b0,
   output reg [5:0]               max_rd_lat,

   //Control the tri-state for write leveling
   output reg [DBYTES-1:0]         cal_oe_dis_low,
   output reg [DBYTES-1:0]         cal_oe_dis_upp,

   output reg [31:0]              cal_debug,
   output reg [8:0]               cal_pre_status,
   output reg [127:0]             cal_r0_status,
   output reg [127:0]             cal_r1_status,
   output reg [127:0]             cal_r2_status,
   output reg [127:0]             cal_r3_status,
   output reg [8:0]               cal_post_status,
   //Error signals are to be used in conjunction with "status" to determine
   //where calibration encountered an error
   output reg                     cal_error,
   output reg [7:0]               cal_error_bit,
   output reg [7:0]               cal_error_nibble,
   output reg [3:0]               cal_error_code,
   output reg                     cal_crc_error,

   output reg                    cal_warning,
   output reg [8:0]              cal_warning_nibble,
   output reg [8:0]              cal_warning_code,
   
   //Debug Port
   output reg [2:0]  dbg_cal_seq,
   output reg [31:0] dbg_cal_seq_cnt,
   output reg [7:0]  dbg_cal_seq_rd_cnt,
   output reg        dbg_rd_valid,
   output reg [5:0]  dbg_cmp_byte,
   output reg [63:0] dbg_rd_data,
   output reg [63:0] dbg_rd_data_cmp,
   output reg [63:0] dbg_expected_data,
   output reg [15:0] dbg_cplx_config,
   output reg [1:0]  dbg_cplx_status
   ,output reg [31:0] win_status = 0
   );


  function integer clogb2 (input integer size);
    begin
      size = size - 1;
      for (clogb2=1; size>1; clogb2=clogb2+1)
        size = size >> 1;
    end
  endfunction

  //chekcing how may 32bit registers are needed
  function integer numof32 (input integer size32);
    begin
        for (numof32=0; size32>0; numof32=numof32+1)
        size32 = size32 - 32;
    end
  endfunction

  // parameter that calculates the max no. of ddr interface pins for addr/cntrl
  // max CK_WIDTH is 4 (quad rank). same for CKE_WIDTH CS_WIDTH, ODT_WIDTH. 
  // one ACT and one PAR. max row width is 18. max LR_WIDTH is 3 (taking 4)
  localparam MAX_AC_PINS = 48;
  // register to save all migration information
  localparam [MAX_AC_PINS*8-1:0] MIGRATION_INFO = migration_info(CKBITS,CKEBITS,CSBITS,ABITS,ODTBITS,BABITS,BGBITS,LR_WIDTH);

  function [MAX_AC_PINS*8-1:0] migration_info (input integer ck,cke,cs,addr,odt,ba,bg,lr);
    begin
      integer lp;

      // Assign default value
      migration_info = 320'b0;

      // Assign CK pin skews for max 4 bits
      for (lp=0; lp<ck; lp++)
        migration_info[lp*8 +: 8] = 75-CK_SKEW[lp*8 +: 8];

      // Assign address pins skew for max 18 bits
      for (lp=0; lp<addr; lp++)
        migration_info[(lp*8+4*8) +: 8] = 75-ADDR_SKEW[lp*8 +: 8];

      // Assign ACT pin skew for 1 bit
      migration_info[(22*8) +: 8] = 75-ACT_SKEW;
 
      // Assign PAR pin skew for 1 bit
      migration_info[(23*8) +: 8] = 75-PAR_SKEW;
 
      // Assign BA pins skew for max 4 bits
      for (lp=0; lp<ba; lp++)
        migration_info[(lp*8+24*8) +: 8] = 75-BA_SKEW[lp*8 +: 8];
 
      // Assign BG pins skew for max 4 bits
      for (lp=0; lp<bg; lp++)
        migration_info[(lp*8+28*8) +: 8] = 75-BG_SKEW[lp*8 +: 8];
 
      // Assign CS pins skew for max 4 bits
      for (lp=0; lp<cs; lp++)
        migration_info[(lp*8+32*8) +: 8] = 75-CS_SKEW[lp*8 +: 8];
 
      // Assign CKE pins skew for max 4 bits
      for (lp=0; lp<cke; lp++)
        migration_info[(lp*8+36*8) +: 8] = 75-CKE_SKEW[lp*8 +: 8];
 
      // Assign ODT pins skew for max 4 bits
      for (lp=0; lp<odt; lp++)
        migration_info[(lp*8+40*8) +: 8] = 75-ODT_SKEW[lp*8 +: 8];
 
      // Assign C pins skew for max 4 bits
      for (lp=0; lp<lr; lp++)
        migration_info[(lp*8+44*8) +: 8] = 75-C_SKEW[lp*8 +: 8];
    end
  endfunction

  //localparam PRE_RECONFIG_IN_STOP_GATE_TRACKING_REQ = 0;
  //localparam PRE_RECONFIG_OUT_STOP_GATE_TRACKING_ACK = 0;         
  //localparam POST_RECONFIG_IN_HW_INIT_SKIP    = 0;
  //localparam POST_RECONFIG_IN_XSDB_RESTORE_EN = 1;
  //localparam POST_RECONFIG_IN_XSDB_RESTORE_COMPLETE = 2;
   
  //limit the count width to reduce the routing
  localparam NIBBLE_WIDTH = DBYTES*2;
  localparam MB_DQ_CNT_WIDTH = clogb2(DBYTES*2) >= 2 ? clogb2(DBYTES*2) : 2;  //DQ count width for MB. 4DQbit per one address
  localparam MB_ADDR_CNT_WIDTH = clogb2(ABITS);                               //ADDR count width for MB
  localparam MB_DM_CNT_WIDTH = clogb2 (DBYTES);
  localparam MB_RD_EN_CNT_WIDTH = MB_DQ_CNT_WIDTH;
  localparam MB_VREF_CNT_WIDTH = clogb2(DBYTES) >= 1 ? clogb2(DBYTES) : 1;
  
  // Delay counter counts abbreviated number of reads for simulation
  `ifdef SIMULATION
     localparam DLY_CNTR_WIDTH = 4;
  `else
     localparam DLY_CNTR_WIDTH = 16;
  `endif

  // each pin requires 7 bits to represent 75 ps and rounding it to 8.
  // thus, one MB register can fit 4 pins as 32 = 8*4.
  localparam MAX_REG_REQ = MAX_AC_PINS/4;

  // the parameter will be used in clamshell designs during MRS
  localparam CS_PAIR   = (CLAMSHELL=="ON") ? (CSBITS/2) : 1;
  localparam CSBITS_CS = (CLAMSHELL=="ON") ? (CSBITS/2) : CSBITS;
  //*************************************************************************//
  //******************MB Adress Apace****************************************//
  //*************************************************************************//

  localparam CAL_RDY             = 28'b ????_????_??1?_????_????_????_0000;
  localparam CAL_CMD_INIT_DONE   = 28'b ????_????_??1?_????_????_????_0001;
  localparam CAL_RESET           = 28'b ????_????_??1?_????_????_????_?010; //0020002
  localparam CAL_BISC            = 28'b ????_????_??1?_????_????_????_?011; //0020003
  localparam CAL_WRITE_VREF      = 28'b ????_????_??1?_????_????_????_?100; //0020004
  localparam CAL_RIU2CLB_VALID   = 28'b ????_????_??1?_????_????_????_?101; //0020005
  localparam CAL_MRS_INV         = 28'b ????_????_??1?_????_????_????_?110; //0020006
  localparam CAL_MAX_RD_LAT      = 28'b ????_????_??1?_????_????_????_?111; //0020007
  localparam CAL_RECONFIG        = 28'b ????_????_??1?_????_????_????_1000; //0020008
  localparam CAL_TIMER           = 28'b ????_????_??1?_????_????_????_1001; //0020009
  localparam CAL_DQOUT_A         = 28'b ????_????_?1??_????_????_000?_????;
  localparam CAL_DQOUT_B         = 28'b ????_????_?1??_????_????_001?_????;
  localparam CAL_DQPAT_A         = 28'b ????_????_?1??_????_????_010?_????;
  localparam CAL_DQPAT_B         = 28'b ????_????_?1??_????_????_100?_????;
  localparam CAL_CMP_EN          = 28'b ????_????_?1??_????_????_110?_????; //00400C0
  localparam CAL_DMOUT_N_A       = 28'b ????_????_1???_????_????_???0_????; //0080000
  localparam CAL_VREF            = 28'b ????_????_1???_????_????_???1_????; //0080010
  localparam CAL_MIGRATION       = 28'b ????_????_1???_????_????_??10_????; //0080020

  localparam MCAL_DQIN           = 28'b ????_????_?1??_????_????_??0?_????;
  localparam MCAL_CMP	         = 28'b ????_????_?1??_????_????_??1?_????;
  localparam MCAL_DMIN           = 28'b ????_????_1???_????_????_???0_????;

  localparam CAL_SEQ             = 28'b ????_0??1_????_????_00?1_????_?000;
  localparam CAL_SEQ_CNT         = 28'b ????_0??1_????_????_00?1_????_?001;
  localparam CAL_SEQ_A_A_DLY     = 28'b ????_0??1_????_????_00?1_????_?010;
  localparam CAL_SEQ_A_B_DLY     = 28'b ????_0??1_????_????_00?1_????_?011;
  localparam CAL_SEQ_B_A_DLY     = 28'b ????_0??1_????_????_00?1_????_?100;
  localparam CAL_SEQ_RD_CNT      = 28'b ????_0??1_????_????_00?1_????_?101;
  localparam CAL_SEQ_CLR         = 28'b ????_0??1_????_????_00?1_????_?110;
  localparam CAL_CS_POS          = 28'b ????_0??1_????_????_00?1_????_?111;  //10_0107
  localparam CAL_OE_DIS          = 28'b ????_0??1_????_????_001?_????_????;  //10_0200
  localparam CAL_TRAFFIC_CNT     = 28'b ????_0??1_????_????_0100_????_???0;  //10_0400
  localparam CAL_MARGIN_START    = 28'b ????_0??1_????_????_0100_????_??01;  //10_0401
  localparam CAL_MARGIN_RESULT   = 28'b ????_0??1_????_????_0100_????_??10;  //10_0402
  localparam CAL_MARGIN_STATUS   = 28'b ????_0??1_????_????_0100_????_??11;  //10_0403
  localparam CAL_TRAFFIC_ERR     = 28'b ????_0??1_????_????_0101_????_????;  //10_0500
  localparam CAL_TRAFFIC_STATUS  = 28'b ????_0??1_????_????_0110_????_??00;  //10_0600
  localparam CAL_TRAFFIC_INSTR   = 28'b ????_0??1_????_????_0110_????_??01;  //10_0601
  localparam CAL_TRAFFIC_ITER    = 28'b ????_0??1_????_????_0110_????_??10;  //10_0602
  localparam CAL_TRAFFIC_NXT     = 28'b ????_0??1_????_????_0110_????_??11;  //10_0603
  localparam CAL_TRAFFIC_START   = 28'b ????_0??1_????_????_0111_???0_??00;  //10_0700
  localparam CAL_TRAFFIC_RST     = 28'b ????_0??1_????_????_0111_???0_??01;  //10_0701
  localparam CAL_TRAFFIC_ERR_CHK = 28'b ????_0??1_????_????_0111_???0_??10;  //10_0702
  localparam CAL_TRAFFIC_ERR_R   = 28'b ????_0??1_????_????_0111_???1_??00;  //10_0710
  localparam CAL_TRAFFIC_ERR_F   = 28'b ????_0??1_????_????_0111_???1_??01;  //10_0711
  localparam CAL_TRAFFIC_ERR_RF  = 28'b ????_0??1_????_????_0111_???1_??10;  //10_0712
  localparam CAL_RD_LAT          = 28'b ????_0??1_????_????_1???_1???_????;  //10_0880

  localparam CPLX_CFG_STATUS     = 28'b ????_0??1_????_????_1?01_????_????;  //10_0900
  localparam CPLX_ERR_LOG        = 28'b ????_0??1_????_????_1?10_????_????;  //10_0A00
  localparam PERIODIC_RD_STATUS  = 28'b ????_0??1_????_????_1?11_????_????;  //10_0B00
  localparam CAL_LRDIMM_CONFIG   = 28'b ????_0??1_????_????_11?0_????_???0;  //10_0C00
  localparam CAL_LRDIMM_CMP_EN   = 28'b ????_0??1_????_????_11?0_????_???1;  //10_0C01
  localparam CAL_CRC_ERROR       = 28'b ????_0??1_????_????_11?1_????_???0;  //10_0D00

  localparam DDR_RST_CKE_ODT_PAR = 28'b ????_??1?_????_????_????_?1??_???1;  //41
  localparam DDR_AC_CMD_A        = 28'b ????_??1?_????_????_????_?1??_??1?;  //42
  localparam DDR_AC_CMD_B        = 28'b ????_?1??_????_????_????_?1??_??1?;   //42
  localparam DDR_AC_CS_A         = 28'b ????_??1?_????_????_??1?_????_????;   //200
  localparam DDR_AC_CS_B         = 28'b ????_?1??_????_????_??1?_????_????;   //200
  localparam DDR_AC_ADR_A        = 28'b ????_??1?_????_???1_????_????_????;   //1000
  localparam DDR_AC_ADR_B        = 28'b ????_?1??_????_???1_????_????_????;   //1000
  localparam DDR_DBI_WR          = 28'b ????_??1?_????_????_1???_????_????;   // 0200800
  localparam DDR_DBI_RD          = 28'b ????_?1??_????_????_1???_????_????;   // 0400800
  localparam DDR_AC_CAS_A        = 28'b ????_??1?_????_??1?_????_????_????;   //2000
  localparam DDR_AC_CAS_B        = 28'b ????_?1??_????_??1?_????_????_????;   //2000
  localparam DDR_AC_RAS_A        = 28'b ????_??1?_????_?1??_????_????_????;   //4000
  localparam DDR_AC_RAS_B        = 28'b ????_?1??_????_?1??_????_????_????;   //4000
  localparam DDR_AC_RANKSEL_LOW  = 28'b ????_??1?_????_1???_????_????_????;   //8000
  localparam DDR_AC_RANKSEL_UPP  = 28'b ????_?1??_????_1???_????_????_????;   //8000

  localparam CONFIGURATION       = 28'b ????_1??0_????_????_?000_????_????;   //80_0000
  localparam DEBUG               = 28'b ????_1??0_????_????_???1_????_???0;   //80_0100
  localparam ERROR               = 28'b ????_1??0_????_????_???1_????_??1?;   //80_0102
  localparam WARNING             = 28'b ????_1??0_????_????_???1_????_?1??;   //80_0104
  localparam CAL_DONE            = 28'b ????_1??0_????_????_??1?_????_????;   //80_0200
  localparam DEBUG_RAM           = 28'b ????_1??1_????_????_????_????_????;   //90_0000

  localparam CAL_DQOUT_PRE       = 28'b ???1_0??0_????_????_????_?1??_????;   //100_0040
  localparam CAL_DQOUT_POST      = 28'b ???1_0??0_????_????_????_1???_????;   //100_0080
  
  reg [2:0]                    cal_seq = 'b0;                   // 0: CMD A only
                                                                // 1: CMD A on even, CMD B on odd cycles
                                                                // 2: CMD A only, write-leveling mode
                                                                // 3: CMD A (even), B(odd), write-leveling mode

  reg [31:0]                   cal_seq_cnt = 'b0;               //sequence counter for cmd generation
  reg [31:0]                   cal_seq_a_a_dly = 'b1;                 // spyglass disable W498    CMD A -> A delay
  reg [31:0]                   cal_seq_a_b_dly = 'b1;                 // spyglass disable W498    CMD A -> A delay
  reg [31:0]                   cal_seq_b_a_dly = 'b1;                 // spyglass disable W498    CMD A -> A delay
  reg [7:0]                    cal_seq_rd_cnt;                  //sequence counter for the number of read
                                                                //it is decreased when actural read from fifo is happened)
  reg                          cal_seq_cnt_gt_0;
  reg [7:0]                    cal_cmp_en;
  reg                          traffic_clr_error_r;
  reg                          traffic_clr_error_r1;
  reg                          traffic_clr_error_r2;
  reg [DBYTES*8*8-1:0]         traffic_error_r;
  reg [8*8-1:0]                traffic_error_byte_r;
  wire [7:0]                   traffic_error_byte_rise;
  wire [7:0]                   traffic_error_byte_fall;
  wire [7:0]                   traffic_error_byte_rise_fall;
  reg [5:0]                    traffic_status_r1;
  reg [5:0]                    traffic_status_r2;
  reg                          traffic_start_r1;
  reg                          traffic_start_r2;
  reg                          traffic_rst_r1;
  reg                          traffic_rst_r2;
  reg                          traffic_err_chk_en_r1;
  reg                          traffic_err_chk_en_r2;
  reg [3:0]                    traffic_instr_addr_mode_r1;
  reg [3:0]                    traffic_instr_addr_mode_r2;
  reg [3:0] 			       traffic_instr_data_mode_r1;
  reg [3:0] 			       traffic_instr_data_mode_r2;
  reg [3:0] 			       traffic_instr_rw_mode_r1;
  reg [3:0] 			       traffic_instr_rw_mode_r2;
  reg [1:0] 			       traffic_instr_rw_submode_r1;
  reg [1:0] 			       traffic_instr_rw_submode_r2;
  reg [31:0] 	               traffic_instr_num_of_iter_r1;
  reg [31:0] 	               traffic_instr_num_of_iter_r2;
  reg [5:0]                    traffic_instr_nxt_instr_r1;
  reg [5:0]                    traffic_instr_nxt_instr_r2;
  reg                          cnt_clr = 'b0;                         //clear seq_cnt and rd_cnt to stop read process
  reg  [7:0]                   dqin_valid_shift;             // spyglass disable W498
  reg                          config_rd_val;                     //config_read_valid
  //Used for combinatorial logic
  reg                         riu_access;                       //MB access RIU registers
  reg                         config_access;                       //MB access RIU registers
  reg                         seq_cnt_access;                   //CAL SEQ CNT is accessed for write
  reg                         seq_cnt_access_b;

  reg                         cnt_clr_access;

  reg                         a_b_rd_sel_r;
  reg                         cmd_go;                         //CMD Processor is started
  reg [7:0]                   cmd_gen_dly;                    //delay between 2 command
  reg                         seq_cnt_dec;                    //Whenever cmd issued, this is set for decreasing cal_seq_cnt
  reg                         a_b_cmd_sel;                    //used to select command set between A and B
  reg                         a_b_cmd_sel_pre;                    //used to select command set between A and B
  reg                         a_b_cmd_sel_gen;                //used to checking delay between 2 commands
  reg                         a_b_cmd_sel_start;              //when A/B command generated alternatively, cal_seq_cnt[0] is used for toggling.
                                                              //cmd generation should be always from A set.
                                                              //if cal_seq_cnt[0] is odd when it is set, ~cal_seq_cnt[0] is used for toggling
  reg                         it_is_write;                    //indicate it is write command
  reg                         it_is_read;
  wire                        wrlvl_mode;
  reg                         io_ready;                   // ack back to MB for cal decode register access
  reg [31:0]              addr_dec_to_mb_data;      	//io_read_data 
  reg [MB_DQ_CNT_WIDTH-2:0]     cmp_byte = 'b0;                       //indicate which byte it is accessed for comparison

  //index is offset of the data from the base address
  //address index is limited by parameter width (DBYTES, ABITS...)
  reg [MB_DM_CNT_WIDTH-1:0]       dm_index;                     //LSB address range of DM in MB
  reg [MB_DQ_CNT_WIDTH-1:0]       dq_index;                       //LSB address range of DQ in MB
  reg [MB_RD_EN_CNT_WIDTH-2:0]    cl_index;
  reg [MB_VREF_CNT_WIDTH-1:0]     vref_index;

  //Local Register Set (A and B set)
  //initialize for shortening the simulation time
  reg [8*8-1:0]                cal_DQOut_A = 'b0;
  reg [8*8-1:0]                cal_DQOut_B = 'b0;
  reg [8*8-1:0]                cal_DQPat_A = 'b0;
  reg [8*8-1:0]                cal_DQPat_B = 'b0;
  reg [8*8-1:0]                cal_DQOut_pre  = 'b0;      //already optimized
  reg [8*8-1:0]                cal_DQOut_post = 'b0;      //already optimized
  reg [DBYTES*8*8-1:0]         cal_DQ;
  reg [DBYTES*8-1:0]           cal_DMOut_n_A_r = {(DBYTES*8){1'b0}};
  reg [31:0]                   cal_DMOut_n_A = 32'b0;
  reg [8*8-1:0]                mcal_dq_cmp;
  wire [8*8-1:0]               mcal_dq_cmp_vld;
  reg [CSBITS*8-1:0]           cal_CS_A ={(CSBITS*8){1'b1}};
  reg [CSBITS*8-1:0]           cal_CS_B ={(CSBITS*8){1'b1}};
  wire [CSBITS*8-1:0]          cal_CS_A_clm;
  wire [CSBITS*8-1:0]          cal_CS_B_clm;
  reg [CSBITS*8-1:0]           cal_CS_n_pre ={(CSBITS*8){1'b1}};
  reg [31:0]                   cal_ADR_A = 'b0;
  reg [31:0]                   cal_ADR_B = 'b0;
`ifdef RECONFIG_INIT_CKE_0
  reg [31:0]                   cal_RST_CKE_ODT_PAR = {8'hff, 8'h00, 8'h00, 8'hff};
`else
  reg [31:0]                   cal_RST_CKE_ODT_PAR = {8'hff, 8'hff, 8'h00, 8'hff};
`endif
  reg [ODTBITS-1:0]            cal_ODT_mux;
  reg [ODTBITS*8-1:0]          cal_ODT_mux_8;
  reg [7:0]                    cal_RAS_A = 8'hff;
  reg [7:0]                    cal_RAS_B = 8'hff;
  reg [7:0]                    cal_RAS_pre = 8'hff;
  reg [7:0]                    cal_RAS_pre_nxt;
  reg [7:0]                    cal_CAS_A = 8'hff;
  reg [7:0]                    cal_CAS_B = 8'hff;
  reg [7:0]                    cal_CAS_pre = 8'hff;
  reg [7:0]                    cal_CAS_pre_nxt;
  reg [7:0]                    cal_WE_A = 8'hff;
  reg [7:0]                    cal_WE_B =  8'hff;
  reg [7:0]                    cal_WE_pre =  8'hff;
  reg [7:0]                    cal_WE_pre_nxt;
  reg [7:0]                    cal_ACT_n_A = 8'hff;
  reg [7:0]                    cal_ACT_n_B = 8'hff;
  reg [7:0]                    cal_ACT_n_pre = 8'hff;
  reg [7:0]                    cal_ACT_n_pre_nxt;

  //debug signal - indicate MB access wrong address range
  reg                          wrong_addr_access_read;
  reg                          wrong_addr_access_write;

  //register for containing 1 byte of data from mcal_DQIn
  reg [8*8-1:0]               mcal_DQIn_byte_r;
  reg [DBYTES*8*8-1:0]        mcal_DQIn_r;
  reg [DBYTES*8*8-1:0]        mcal_DQIn_r_valid;
  reg [8*8-1:0]               mcal_DQIn_byte_r1;
  reg [DBYTES*8-1:0]          mcal_DMIn_n_r;
  reg [7:0]                   mcal_DMIn_bit_r1;

  //extended write
  reg extended_write_mode;

  reg [2:0] extended_write;
  reg [2:0] extended_write_r;
  reg       wren;

  //indicate the timing of cal_seq_cnt writing
  reg                          cmd_go_ind;

  reg [7:0]                    dram_device_sel;
  reg                          devices_dsel;
  reg                          write_vref_mode;

  //fabric clock signals
  reg                          io_addr_strobe_r1;
  reg                          io_addr_strobe_r2;

   reg [1:0]               cal_cs_pos;
   
   //Margin Results (may move these to BRAM eventually)
//   reg                     margin_done_r1;
//   reg                     margin_done_r2;
//   reg                     margin_done;
//   reg [7:0]               margin_bit;
//   reg [7:0]               margin_nibble;
   reg [31:0]              margin_status;
   reg                     margin_p_active;
   reg                     margin_n_active;
   reg [8:0]               margin_left;
   reg [8:0]               margin_right;
   reg [8:0]               margin_start_tap;
   
   //Registers to store the results to view in waveform
//   reg [7:0]               margin_nibble_r;
   reg [8:0]               margin_left_p;
   reg [8:0]               margin_right_p;
   reg [8:0]               margin_start_tap_p;
   reg [8:0]               margin_left_n;
   reg [8:0]               margin_right_n;
   reg [8:0]               margin_start_tap_n;
   
   //Delay counter signals
   reg                     delay_cntr_rd_valid;
   reg [DLY_CNTR_WIDTH-1:0]delay_cntr;
   wire                    delay_cntr_ce;
   wire                    delay_cntr_done;

   //Odt generation for calibration using the mc odt submodule
   wire [ODTBITS-1:0]       mc_cal_ODT_msb_nxt;
   reg  [ODTBITS-1:0]       mc_cal_ODT_msb;
   wire [ODTBITS*8-1:0]     mc_cal_ODT;
   wire [ODTBITS*8-1:0]     mc_cal_ODT_shifted;

   //Complex calibration
   reg  [31:0]              cplx_config;
   wire [31:0]              cplx_status;
   wire [31:0]              cplx_err_log30;
   wire [31:0]              cplx_err_log74;
   wire                     cplx_cal;
   wire [DBYTES*8*8-1:0]    cplx_DQOut;
   wire [DBYTES*8-1:0]      cplx_DMOut_n;
   wire [ABITS-1:0]         cplx_ADR;
   wire [7:0]               cplx_RAS;
   wire [7:0]               cplx_CAS;
   wire [7:0]               cplx_WE;
   wire [7:0]               cplx_ACT_n;
   wire [BABITS-1:0]        cplx_BA;
   wire [BGBITS-1:0]        cplx_BG;
   wire [CKEBITS*8-1:0]     cplx_CKE;
   reg  [CSBITS*8-1:0]      cplx_CS_n;
   wire [CSBITS_CS*8-1:0]   cplx_CS_n_cshell;
   wire [ODTBITS-1:0]       cplx_ODT;
   wire [7:0]               cplx_PAR;
   wire                     cplx_issue_cas_wr;
   wire                     cplx_issue_cas_rd;
   wire [63:0]              cplx_expected_data;
   
   //Registers for BISC K2 workaround
   reg [3:0]                bisc_bit;
   reg [5:0]                bisc_nibble;
  assign bisc_byte = {bisc_nibble[4:0],bisc_bit}; // MAN double check
/*   
   //Rank 0
   reg [8:0]                cal_r0_status0;
   reg [8:0]                cal_r0_status1;
   reg [8:0]                cal_r0_status2;
   reg [8:0]                cal_r0_status3;
   reg [8:0]                cal_r0_status4;
   reg [8:0]                cal_r0_status5;
   reg [8:0]                cal_r0_status6;
   
   //Rank 1
   reg [8:0]                cal_r1_status0;
   reg [8:0]                cal_r1_status1;
   reg [8:0]                cal_r1_status2;
   reg [8:0]                cal_r1_status3;
   reg [8:0]                cal_r1_status4;
   reg [8:0]                cal_r1_status5;
   reg [8:0]                cal_r1_status6;
   
   //Rank 2
   reg [8:0]                cal_r2_status0;
   reg [8:0]                cal_r2_status1;
   reg [8:0]                cal_r2_status2;
   reg [8:0]                cal_r2_status3;
   reg [8:0]                cal_r2_status4;
   reg [8:0]                cal_r2_status5;
   reg [8:0]                cal_r2_status6;
   
   //Rank 3
   reg [8:0]                cal_r3_status0;
   reg [8:0]                cal_r3_status1;
   reg [8:0]                cal_r3_status2;
   reg [8:0]                cal_r3_status3;
   reg [8:0]                cal_r3_status4;
   reg [8:0]                cal_r3_status5;
   reg [8:0]                cal_r3_status6;
*/   
   
 // Preiodic read uB interface
 reg  clear_gt_data_ready_flag;
 reg  gt_data_ready_flag;
 
 // LRDIMM related signals
  reg                         lrdimm_cal_mode;
  reg                         lrdimm_drive_dq;
  wire [DBYTES*2-1:0]                 mcal_DQ0In_lrdimm_or;
  wire [DBYTES*2-1:0]                 mcal_DQ0In_lrdimm_and;
  reg [DBYTES*2-1:0]                  mcal_DQ0In_lrdimm_or_r;
  reg [DBYTES*2-1:0]                  mcal_DQ0In_lrdimm_and_r;
  wire [DBYTES*2-1:0]                 mcal_DQ0In_lrdimm_st_one;
  wire [DBYTES*2-1:0]                 mcal_DQ0In_lrdimm_st_zero;
  reg                         lrdimm_cmp_access;
  reg                         lrdimm_cmp_en;
  reg                         lrdimm_cmp_clr;
  wire [8*8-1:0]              mcal_dq_cmp_lrdimm;
  wire [31:0]                 cal_ADR_A_ext;
  reg [RNK_BITS-1:0]                   lrdimm_cal_rank;
  wire [RNK_BITS-1:0]                  cal_mem_rank;
  integer                     rnk;

  //Debug output
  reg [5:0]                 dbg_cmp_byte_r;
  reg [8*8-1:0]             dbg_mcal_DQIn_byte_r;
  reg [31:0]                cal_timer;
  
  reg [2:0]  dbg_cal_seq_r;
  reg [31:0] dbg_cal_seq_cnt_r;
  reg [7:0]  dbg_cal_seq_rd_cnt_r;
  reg        dbg_rd_valid_r;
  reg [63:0] dbg_rd_data_r;
  reg [63:0] dbg_rd_data_cmp_r;
  reg [63:0] dbg_expected_data_r;
  reg [15:0] dbg_cplx_config_r;
  reg [1:0]  dbg_cplx_status_r;
  reg [63:0] dbg_cplx_err_log_r;

(* keep = "TRUE" *) reg rst_r1;

  // save/restore signals
  reg        app_restore_en_r;
  reg        app_restore_en_lpulse = 0;
  reg        app_restore_cmplt_r;
  reg        app_restore_cmplt_lpulse = 0;
  reg        stop_gate_trck_req_r;
  reg        stop_gate_trck_req_lpulse;
  reg        calDone_r;

  wire [3:0] migr_reg_idx;
  assign migr_reg_idx = io_address[3:0];

  // Creating rise edge sensitive pulses for restore enable, complete and
  // stop_gate_tracking_req signals
  always @(posedge clk) 
  begin
    if (rst_r1) begin
      app_restore_en_r     <= #TCQ 1'b0;
      app_restore_cmplt_r  <= #TCQ 1'b0;
      stop_gate_trck_req_r <= #TCQ 1'b0;
      calDone_r            <= #TCQ 1'b0;
    end else begin
      app_restore_en_r     <= #TCQ app_restore_en;
      app_restore_cmplt_r  <= #TCQ app_restore_complete;
      stop_gate_trck_req_r <= #TCQ stop_gate_tracking_req;
      calDone_r            <= #TCQ calDone;
    end

    // long pulse for restore enable
    if (rst_r1)
      app_restore_en_lpulse <= #TCQ 1'b0;
    else if (~app_restore_en_r & app_restore_en)
      app_restore_en_lpulse <= #TCQ 1'b1;
    else if (~calDone_r & calDone)
      app_restore_en_lpulse <= #TCQ 1'b0;

    // long pulse for restore complete
    if (rst_r1)
      app_restore_cmplt_lpulse <= #TCQ 1'b0;
    else if (~app_restore_cmplt_r & app_restore_complete)
      app_restore_cmplt_lpulse <= #TCQ 1'b1;
    else if (~calDone_r & calDone)
      app_restore_cmplt_lpulse <= #TCQ 1'b0;

    // long pulse for stop gate tracking request
    if (rst_r1)
      stop_gate_trck_req_lpulse <= #TCQ 1'b0;
    else if (~stop_gate_trck_req_r & stop_gate_tracking_req)
      stop_gate_trck_req_lpulse <= #TCQ 1'b1;
    else if (~calDone_r & calDone)
      stop_gate_trck_req_lpulse <= #TCQ 1'b0;
  end

  // Registering the input reset
  always @(posedge clk)
    rst_r1 <= rst;

  always @ (posedge clk)
  begin
    dbg_cmp_byte_r       <= #TCQ {6'b0, cmp_byte[MB_DQ_CNT_WIDTH-2:0]};
    dbg_mcal_DQIn_byte_r <= #TCQ mcal_DQIn_r[dbg_cmp_byte_r*64 +:64];
  
	dbg_cal_seq_r        <= #TCQ cal_seq;
	dbg_cal_seq_cnt_r    <= #TCQ cal_seq_cnt;
    dbg_cal_seq_rd_cnt_r <= #TCQ cal_seq_rd_cnt;
    dbg_rd_valid_r       <= #TCQ dqin_valid_shift[2];
    dbg_rd_data_r        <= #TCQ dbg_mcal_DQIn_byte_r;
    dbg_cplx_config_r    <= #TCQ cplx_config[15:0];
    dbg_cplx_status_r    <= #TCQ {cplx_status[31], cplx_status[0]};
    dbg_cplx_err_log_r   <= #TCQ {cplx_err_log74, cplx_err_log30};
	
	if (dbg_cplx_status_r[0] == 1'b1) begin
	  dbg_rd_data_cmp_r    <= #TCQ dbg_cplx_err_log_r;
	  dbg_expected_data_r  <= #TCQ cplx_expected_data;
	end else begin
	  dbg_rd_data_cmp_r    <= #TCQ mcal_dq_cmp_vld;
	  //For now only send back data associated with Pattern A. Only time Pattern
	  //B is used is during Deskew
	  dbg_expected_data_r  <= #TCQ cal_DQPat_A;
	end
	
	dbg_cal_seq          <= #TCQ dbg_cal_seq_r;
	dbg_cal_seq_cnt      <= #TCQ dbg_cal_seq_cnt_r;
    dbg_cal_seq_rd_cnt   <= #TCQ dbg_cal_seq_rd_cnt_r;
    dbg_rd_valid         <= #TCQ dbg_rd_valid_r;
	dbg_cmp_byte         <= #TCQ dbg_cmp_byte_r;
    dbg_rd_data          <= #TCQ dbg_rd_data_r;
    dbg_rd_data_cmp      <= #TCQ dbg_rd_data_cmp_r;
	dbg_expected_data    <= #TCQ dbg_expected_data_r;
    dbg_cplx_config      <= #TCQ dbg_cplx_config_r;
    dbg_cplx_status      <= #TCQ dbg_cplx_status_r;

     win_status <= #TCQ margin_status;
  end

  integer i, j, loc;

  //*************************************************************************//
  //******************Combinatirial logic************************************//
  //*************************************************************************//
  always @(*)
  begin
    riu_access       = (~io_address[23]) & (io_address[12] | io_address[13] | io_address[14] | io_address[15] | io_address [16] ) & (~io_address[21]) &(~io_address[22]);
    config_access    = io_address[23]    & (~io_address[20]) & (~io_address[8]) & (~io_address[9]) & (~io_address[10]);
    seq_cnt_access_b = (~io_address[23]) & io_address[20]    & io_address[8] & (io_address[2:0] == 'h1) & io_addr_strobe & io_write_strobe;   //0x0100001
    cnt_clr_access   = (~io_address[23]) & io_address[20]    & io_address[8]     & (io_address [2:0] =='h6) & io_addr_strobe & io_write_strobe;   //0x0100106
    lrdimm_cmp_access   = (~io_address[23]) & io_address[20] & io_address[11] & io_address[10] & (io_address [1:0] =='h1) & io_addr_strobe & io_write_strobe;   //0x0100C01 // CAL_LRDIMM_CMP_EN

    //select right range of io_address to access
    dq_index = io_address[MB_DQ_CNT_WIDTH-1:0];
    dm_index = io_address[MB_DM_CNT_WIDTH-1:0];
    xsdb_rd_en     = io_address[23] & (~io_address[22]) & (~io_address[21]) & (io_address[20]); // 0x900000
    xsdb_addr      = io_address[15:0];
    config_rd_addr = io_address[7:0];
    cl_index = io_address[MB_RD_EN_CNT_WIDTH-1:1];  //lsb used for deciding low/upp
    vref_index = io_address[MB_VREF_CNT_WIDTH-1:0];
 end

  //cmd selection is depending on cal_seq[0](A only or A/B alternative) and cal_seq_cnt (even is A, odd is B)
  always @ (*)
  begin
    //cmd selection is depending on cal_seq[0](A only or A/B alternative) and cal_seq_cnt (even is A, odd is B)
    a_b_cmd_sel_pre =  cal_seq[0] ? (a_b_cmd_sel_start ? ~cal_seq_cnt[0]: cal_seq_cnt[0]):0;
    a_b_cmd_sel_gen = a_b_cmd_sel_start ? (seq_cnt_dec? cal_seq_cnt[0]:~cal_seq_cnt[0]): (seq_cnt_dec ?~cal_seq_cnt[0]:cal_seq_cnt[0]);
  end

  // write leveling mode is indicated by cal_seq[1]
  assign wrlvl_mode = cal_seq[1];

  //Check WE_n and CAS_n for write/read
  //distinguish the command as write or read
  //Check it is not ACT (ACT_n is not 0)

  always @ (*)
  begin
    if (USE_CS_PORT == 1) begin
      it_is_write = ((~&cal_WE) & (~&cal_CAS) & (&cal_RAS) & (&cal_ACT_n));  //WE:L, CAS:L, RAS:H, ACT:H
      it_is_read  = ((&cal_WE) & (~&cal_CAS) & (&cal_RAS) & (&cal_ACT_n));   //WE:H, CAS:L, RAS:H, ACT:H
      cal_mrs     = ((~&cal_WE) & (~&cal_CAS) & (~&cal_RAS) & (&cal_ACT_n));   //WE:L, CAS:L, RAS:L, ACT:H
	end else begin
	  //Have to check what the command is earlier then when launched. This will
	  //be fine as long we don't do a single from location B or the command
	  //changes from A->B (not supported anyways)
	  it_is_write = ((~&cal_WE_A) & (~&cal_CAS_A) & (&cal_RAS_A) & (&cal_ACT_n_A));  //WE:L, CAS:L, RAS:H, ACT:H
      it_is_read  = ((&cal_WE_A) & (~&cal_CAS_A) & (&cal_RAS_A) & (&cal_ACT_n_A));   //WE:H, CAS:L, RAS:H, ACT:H
	   cal_mrs  = ((~&cal_WE_A) & (~&cal_CAS_A) & (~&cal_RAS_A) & (&cal_ACT_n_A));   //WE:L, CAS:L, RAS:L, ACT:H
	end
  end
  
  wire       [31:0]            cal_ADR_int_nxt; // spyglass disable W498
  wire       [31:0]            cal_C_int_nxt;


  generate
    genvar i1;
    for(i1=0; i1<ABITS; i1= i1+1)
      if (MEM == "DDR4") begin
        assign cal_ADR[i1*8+:8] = (i1==14)? cal_WE[7:0]
	                         :(i1==15)? cal_CAS[7:0]
 			         :(i1==16)? cal_RAS[7:0]
				 : {8{cal_ADR_int_nxt[i1]}};
      end
      else begin
	assign cal_ADR[i1*8+:8] ={8{ cal_ADR_int_nxt[i1]}};
      end
  endgenerate

   wire       [BABITS-1:0]      cal_BA_nxt = cplx_cal ? cplx_BA : cal_ADR_int_nxt[24+BABITS-1:24];

  //BA generation
  generate
    genvar i2;
    for (i2 = 0; i2 < BABITS; i2 = i2 + 1)
	  assign cal_BA[i2*8+:8] = {8{cal_BA_nxt[i2]}};
  endgenerate

   wire      [BGBITS-1:0]      cal_BG_nxt = cplx_cal ? cplx_BG : cal_ADR_int_nxt[28+BGBITS-1:28];

  //BG generation
  generate
    genvar i3;
    for (i3 = 0; i3 < BGBITS; i3 = i3 + 1)
	  assign cal_BG[i3*8 +:8] = {8{cal_BG_nxt[i3]}};
  endgenerate

 
  assign cal_C_int_nxt = cplx_cal ? 'b0 : ( a_b_cmd_sel? cal_ADR_B:   cal_ADR_A );
  wire       [LR_WIDTH-1:0]    cal_C_nxt = cplx_cal ? 'b0 : cal_C_int_nxt[20+LR_WIDTH-1:20];
  //3DS C generation
  generate
    genvar i4;
    for (i4 = 0; i4 < LR_WIDTH; i4 = i4 + 1)
      assign cal_C[i4*8+:8] = (S_HEIGHT < 2) ? 'b0 : {8{cal_C_nxt[i4]}};
  endgenerate

// KP 10_25 timing fix. changed clock and reset to riu clock and riu reset.
// split the case statement to read and write 

  always @ (posedge clk)
  begin
//	margin_done_r2 <= #TCQ margin_done_r1;
	
	if (rst_r1) begin
	  margin_start_tap_p <= #TCQ 'b0;
	  margin_left_p      <= #TCQ 'b0;
	  margin_right_p     <= #TCQ 'b0;
	end else if (margin_p_active) begin 
	  margin_start_tap_p <= #TCQ margin_start_tap;
	  margin_left_p      <= #TCQ margin_left;
	  margin_right_p     <= #TCQ margin_right;
	end else begin
	  margin_start_tap_p <= #TCQ margin_start_tap_p;
	  margin_left_p      <= #TCQ margin_left_p;
	  margin_right_p     <= #TCQ margin_right_p;
	end
	
	if (rst_r1) begin
	  margin_start_tap_n <= #TCQ 'b0;
	  margin_left_n      <= #TCQ 'b0;
	  margin_right_n     <= #TCQ 'b0;
	end else if (margin_n_active) begin 
	  margin_start_tap_n <= #TCQ margin_start_tap;
	  margin_left_n      <= #TCQ margin_left;
	  margin_right_n     <= #TCQ margin_right;
	end else begin
	  margin_start_tap_n <= #TCQ margin_start_tap_n;
	  margin_left_n      <= #TCQ margin_left_n;
	  margin_right_n     <= #TCQ margin_right_n;
	end
	
  end
  
  wire [1:0] casSlot_nxt = cplx_cal ? 2'd2 : cal_cs_pos;

  always @ (posedge clk)
  begin
    casSlot <= #TCQ casSlot_nxt;
  end
/*
  always @ (posedge clk)
  begin
    if (margin_p_active | margin_n_active)
      margin_nibble_r <= #TCQ margin_nibble;
	else
	  margin_nibble_r <= #TCQ margin_nibble_r;
  end
  

  //Create a single clock cycle "done" pulse for the margin check
  always @ (posedge clk)
  begin
    if (rst_r1)
	  margin_done <= #TCQ 1'b0;
	else if (margin_done_r1 && !margin_done_r2)
	  margin_done <= #TCQ 1'b1;
	else
	  margin_done <= #TCQ 1'b0;
  end
  */
 //*************************************************************************//
  //******************local Register Set CMD/DM/DQS *************************//
  //*************************************************************************//

   always @(posedge clk) begin
      if (rst_r1) begin
	 cal_timer <= #TCQ 'h0;
      end
      else if (io_addr_strobe & io_write_strobe & (io_address[17] && io_address[3] && io_address[0])) begin // CAL_TIMER address
	 cal_timer <= #TCQ mb_to_addr_dec_data[31:0];
      end
      else begin
	 cal_timer <= #TCQ (cal_timer == 32'hFFFFFFFF) ? cal_timer : cal_timer + 'h1;
      end
   end
   
  //write 
  always @(posedge clk)
  begin
    cplx_config <= #TCQ cplx_config & ~32'b1; // clear complex cal start bit
    xsdb_wr_en  <= 1'b0;
    if(rst_r1) begin
      ub_ready <= #TCQ 'b0;
      calDone  <= #TCQ 'b0;
      en_vtc <= #TCQ 'b0;
      ub_initDone <= #TCQ 'b0;
      wrong_addr_access_write <= #TCQ 'b0;  //debug signal
      cal_RAS_A <= #TCQ {8{1'b1}};
      cal_CAS_A <= #TCQ {8{1'b1}};
      cal_WE_A <= #TCQ {8{1'b1}};
      cal_seq <= #TCQ 'b0;
      cal_cmp_en <= #TCQ {8{1'b1}};
      lowCL0  <= #TCQ 'b0;
      lowCL1  <= #TCQ 'b0;
      lowCL2  <= #TCQ 'b0;
      lowCL3  <= #TCQ 'b0;
      uppCL0  <= #TCQ 'b0;
      uppCL1  <= #TCQ 'b0;
      uppCL2  <= #TCQ 'b0;
      uppCL3  <= #TCQ 'b0;
      cal_oe_dis_low <= #TCQ 'b0;
      cal_oe_dis_upp <= #TCQ 'b0;
      rd_vref_value  <= #TCQ {DBYTES{RD_VREF_VAL}};
      //rd_vref_value  <= #TCQ (MEMORY_CONFIGURATION == "COMPONENT") ? {DBYTES{7'h14}} : {DBYTES{7'h21}};
      cplx_config <= #TCQ 'b0;
	  bisc_bit    <= #TCQ 'b0;
	  bisc_nibble <= #TCQ 'b0;
  	  write_vref_mode    <= #TCQ 'b0;
	  dram_device_sel <= #TCQ 'b0;
	  devices_dsel    <= #TCQ 'b0;
	  cal_r0_status <= #TCQ 'b0;
	  cal_r1_status <= #TCQ 'b0;
	  cal_r2_status <= #TCQ 'b0;
	  cal_r3_status <= #TCQ 'b0;
/*
	  cal_r0_status0 <= #TCQ 'b0;
	  cal_r0_status1 <= #TCQ 'b0;
	  cal_r0_status2 <= #TCQ 'b0;
	  cal_r0_status3 <= #TCQ 'b0;
	  cal_r0_status4 <= #TCQ 'b0;
	  cal_r0_status5 <= #TCQ 'b0;
	  cal_r0_status6 <= #TCQ 'b0;
	  cal_r1_status0 <= #TCQ 'b0;
	  cal_r1_status1 <= #TCQ 'b0;
	  cal_r1_status2 <= #TCQ 'b0;
	  cal_r1_status3 <= #TCQ 'b0;
	  cal_r1_status4 <= #TCQ 'b0;
	  cal_r1_status5 <= #TCQ 'b0;
	  cal_r1_status6 <= #TCQ 'b0;
	  cal_r2_status0 <= #TCQ 'b0;
	  cal_r2_status1 <= #TCQ 'b0;
	  cal_r2_status2 <= #TCQ 'b0;
	  cal_r2_status3 <= #TCQ 'b0;
	  cal_r2_status4 <= #TCQ 'b0;
	  cal_r2_status5 <= #TCQ 'b0;
	  cal_r2_status6 <= #TCQ 'b0;
	  cal_r3_status0 <= #TCQ 'b0;
	  cal_r3_status1 <= #TCQ 'b0;
	  cal_r3_status2 <= #TCQ 'b0;
	  cal_r3_status3 <= #TCQ 'b0;
	  cal_r3_status4 <= #TCQ 'b0;
	  cal_r3_status5 <= #TCQ 'b0;
	  cal_r3_status6 <= #TCQ 'b0;
*/
	  cal_error_bit   <= #TCQ 'b0;
	  cal_error_nibble <= #TCQ 'b0;
	  cal_error_code   <= #TCQ 'b0;
      cal_error        <= #TCQ 'b0;
      cal_inv        <= #TCQ 'b0;
      cal_crc_error  <= #TCQ 1'b0;
       stop_gate_tracking_ack    <= #TCQ 'b0;
	  max_rd_lat  <= #TCQ 'b0;
       margin_status <= #TCQ 'b0;
       cal_DMOut_n_A <= #TCQ 'b0;
	   cal_dbi_wr        <= #TCQ INITIAL_DBI_WR;
	   cal_dbi_rd        <= #TCQ INITIAL_DBI_RD;
           lrdimm_drive_dq <= #TCQ 1'b0;
           lrdimm_cal_mode <= #TCQ 1'b0;
       traffic_start_r1             <= #TCQ 'b1;
       traffic_rst_r1               <= #TCQ 'b0;
       traffic_err_chk_en_r1        <= #TCQ 'b0;
	   traffic_instr_addr_mode_r1   <= #TCQ 'b0;
       traffic_instr_data_mode_r1   <= #TCQ 'b0;
       traffic_instr_rw_mode_r1     <= #TCQ 'b0;
       traffic_instr_rw_submode_r1  <= #TCQ 'b0;
       traffic_instr_num_of_iter_r1 <= #TCQ 'b0;
       traffic_instr_nxt_instr_r1   <= #TCQ 'b0;
       clb2phy_wrcs0_low <= #TCQ {4*DBYTES{1'b0}};
       clb2phy_wrcs1_low <= #TCQ {4*DBYTES{1'b0}};
       clb2phy_rdcs0_low <= #TCQ {4*DBYTES{1'b0}};
       clb2phy_rdcs1_low <= #TCQ {4*DBYTES{1'b0}};
       clb2phy_wrcs0_upp <= #TCQ {4*DBYTES{1'b0}};
       clb2phy_wrcs1_upp <= #TCQ {4*DBYTES{1'b0}};
       clb2phy_rdcs0_upp <= #TCQ {4*DBYTES{1'b0}};
       clb2phy_rdcs1_upp <= #TCQ {4*DBYTES{1'b0}};
    end else if(io_addr_strobe & io_write_strobe) begin  //write
      casez(io_address)
        //MB_READY
        CAL_CMD_INIT_DONE: begin
          ub_initDone <= #TCQ mb_to_addr_dec_data[0];
          ub_ready    <= #TCQ mb_to_addr_dec_data[1];
        end
		CAL_BISC: begin
		  bisc_bit    <= #TCQ mb_to_addr_dec_data[3:0];
		  bisc_nibble <= #TCQ mb_to_addr_dec_data[9:4];
		end
	    CAL_WRITE_VREF: begin
	      write_vref_mode    <= #TCQ mb_to_addr_dec_data[15];
          dram_device_sel <= #TCQ mb_to_addr_dec_data[7:0];
          devices_dsel    <= #TCQ mb_to_addr_dec_data[16];
	    end
        //MRS Write with inversion
	    CAL_MRS_INV: begin
	      cal_inv <= #TCQ mb_to_addr_dec_data[0];
	    end
		CAL_MAX_RD_LAT: begin
		  max_rd_lat <= #TCQ mb_to_addr_dec_data[5:0];
		end
    // Stop gate tracking acknowledge for save/restore and self-refresh
    CAL_RECONFIG: begin
      stop_gate_tracking_ack <= #TCQ mb_to_addr_dec_data[4];
    end

        //DQOUT/DMOUT/DQPAT
        CAL_DQOUT_A: begin
          cal_DQOut_A[dq_index[0]*32 +:32] <= #TCQ mb_to_addr_dec_data[31:0];
          cmp_byte <= #TCQ dq_index[MB_DQ_CNT_WIDTH-1:1];
        end
        CAL_DQOUT_B: begin
          cal_DQOut_B[dq_index[0]*32 +:32] <= #TCQ mb_to_addr_dec_data[31:0];
        end
        //DQOUT/DMOUT/DQPAT
        CAL_DQOUT_PRE: begin
          cal_DQOut_pre[dq_index[0]*32 +:32] <= #TCQ mb_to_addr_dec_data[31:0];  //only getting 64byte
        end
        CAL_DQOUT_POST: begin
          cal_DQOut_post[dq_index[0]*32 +:32] <= #TCQ mb_to_addr_dec_data[31:0];  //only getting 64byte
        end
        CAL_DMOUT_N_A: begin
		  cal_DMOut_n_A[31:0] <= #TCQ mb_to_addr_dec_data[31:0];
        end
        CAL_DQPAT_A: begin
          cal_DQPat_A[dq_index[0] *32 +:32] <= #TCQ mb_to_addr_dec_data[31:0];
          cmp_byte <= #TCQ dq_index[MB_DQ_CNT_WIDTH-1:1];  //indicate which byte you want to access
        end
        CAL_DQPAT_B: begin
          cal_DQPat_B[dq_index[0] *32 +:32] <= #TCQ mb_to_addr_dec_data[31:0];
          cmp_byte <= #TCQ dq_index[MB_DQ_CNT_WIDTH-1:1];  //indicate which byte you want to access
        end
	    CAL_VREF: begin
	      rd_vref_value[vref_index*7 +:7] <= #TCQ mb_to_addr_dec_data[6:0];
	    end
        CAL_SEQ: begin
          cal_seq <= #TCQ mb_to_addr_dec_data[2:0];
        end
        CAL_LRDIMM_CONFIG: begin
          lrdimm_drive_dq <= #TCQ mb_to_addr_dec_data[1];
          lrdimm_cal_mode <= #TCQ mb_to_addr_dec_data[0];
        end
        CAL_CMP_EN: begin
          cal_cmp_en <= #TCQ mb_to_addr_dec_data[7:0]; // DQ_CMP_EN
        end
	CAL_CRC_ERROR: begin
	  cal_crc_error <= #TCQ mb_to_addr_dec_data[0];
	end
	CAL_CS_POS: begin
	  cal_cs_pos <= #TCQ mb_to_addr_dec_data[1:0];
	end
	CAL_OE_DIS: begin
	  //For now all nibbles get the same value
	  cal_oe_dis_low <= #TCQ io_address[0]? cal_oe_dis_low : {DBYTES{mb_to_addr_dec_data[0]}};
	  cal_oe_dis_upp <= #TCQ io_address[0]? {DBYTES{mb_to_addr_dec_data[0]}} : cal_oe_dis_low; // RGAD Check the LOW/HIGH
	end
	    CAL_MARGIN_RESULT: begin
		  margin_start_tap    <= #TCQ mb_to_addr_dec_data[8:0];
		  margin_right        <= #TCQ mb_to_addr_dec_data[17:9];
		  margin_left         <= #TCQ mb_to_addr_dec_data[26:18];
		  margin_p_active     <= #TCQ mb_to_addr_dec_data[27];
		  margin_n_active     <= #TCQ mb_to_addr_dec_data[28];
		end
	    CAL_MARGIN_STATUS: begin
//		  margin_bit      <= #TCQ mb_to_addr_dec_data[7:0];
//          margin_nibble   <= #TCQ mb_to_addr_dec_data[15:8];
//		  margin_done_r1  <= #TCQ mb_to_addr_dec_data[16];
		  margin_status <= #TCQ mb_to_addr_dec_data;
		end
		CAL_TRAFFIC_INSTR: begin
		  traffic_instr_addr_mode_r1   <= #TCQ mb_to_addr_dec_data[3:0];
          traffic_instr_data_mode_r1   <= #TCQ mb_to_addr_dec_data[7:4];
          traffic_instr_rw_mode_r1     <= #TCQ mb_to_addr_dec_data[11:8];
          traffic_instr_rw_submode_r1  <= #TCQ mb_to_addr_dec_data[13:12];
		end
		CAL_TRAFFIC_ITER: begin
		  traffic_instr_num_of_iter_r1 <= #TCQ mb_to_addr_dec_data;
		end
		CAL_TRAFFIC_NXT: begin
		  traffic_instr_nxt_instr_r1   <= #TCQ mb_to_addr_dec_data[5:0];
		end
		CAL_TRAFFIC_START: begin
		  traffic_start_r1      <= #TCQ mb_to_addr_dec_data[0];
		end
		CAL_TRAFFIC_RST: begin
          traffic_rst_r1        <= #TCQ mb_to_addr_dec_data[0];
		end
		CAL_TRAFFIC_ERR_CHK: begin
          traffic_err_chk_en_r1 <= #TCQ mb_to_addr_dec_data[0];
		end
	CAL_RD_LAT: begin
          //update for even address
          lowCL0[cl_index*6 +:6] <= #TCQ io_address[0]? lowCL0[cl_index*6 +:6]: mb_to_addr_dec_data[5:0];
          lowCL1[cl_index*6 +:6] <= #TCQ io_address[0]? lowCL1[cl_index*6 +:6]: mb_to_addr_dec_data[13:8];
          lowCL2[cl_index*6 +:6] <= #TCQ io_address[0]? lowCL2[cl_index*6 +:6]: mb_to_addr_dec_data[21:16];
          lowCL3[cl_index*6 +:6] <= #TCQ io_address[0]? lowCL3[cl_index*6 +:6]: mb_to_addr_dec_data[29:24];

          //update for odd address
          uppCL0[cl_index*6 +:6] <= #TCQ io_address[0]? mb_to_addr_dec_data[5:0]:   uppCL0[cl_index*6 +:6];
          uppCL1[cl_index*6 +:6] <= #TCQ io_address[0]? mb_to_addr_dec_data[13:8]:  uppCL1[cl_index*6 +:6];
          uppCL2[cl_index*6 +:6] <= #TCQ io_address[0]? mb_to_addr_dec_data[21:16]: uppCL2[cl_index*6 +:6];
          uppCL3[cl_index*6 +:6] <= #TCQ io_address[0]? mb_to_addr_dec_data[29:24]: uppCL3[cl_index*6 +:6];
	end
        //DRAM Address, Control, Command Address map
	DDR_RST_CKE_ODT_PAR: begin
	   cal_RST_CKE_ODT_PAR   <= #TCQ mb_to_addr_dec_data;
	end
        DDR_AC_CMD_A: begin
          cal_ACT_n_A[7:0] <= mb_to_addr_dec_data[7:0];   // ACT
          cal_WE_A[7:0]    <= mb_to_addr_dec_data[15:8];  // WE
          cal_RAS_A[7:0]   <= mb_to_addr_dec_data[23:16]; // RAS
          cal_CAS_A[7:0]   <= mb_to_addr_dec_data[31:24]; // CAS
        end
        DDR_AC_CMD_B: begin
          cal_ACT_n_B[7:0] <= mb_to_addr_dec_data[7:0];   // ACT
          cal_WE_B[7:0]    <= mb_to_addr_dec_data[15:8];  // WE
          cal_RAS_B[7:0]   <= mb_to_addr_dec_data[23:16]; // RAS
          cal_CAS_B[7:0]   <= mb_to_addr_dec_data[31:24]; // CAS
        end
        DDR_AC_CS_A: begin
	  if (CLAMSHELL == "ON")
            cal_CS_A <= #TCQ {mb_to_addr_dec_data[15:8],mb_to_addr_dec_data[15:8],mb_to_addr_dec_data[7:0],mb_to_addr_dec_data[7:0]};
	  else if (RANKS == 8)
            cal_CS_A[dq_index[0]*32 +:32] <= #TCQ mb_to_addr_dec_data[31:0];
	  else
            cal_CS_A <= #TCQ mb_to_addr_dec_data[CSBITS*8-1:0];
        end
        DDR_AC_CS_B: begin
	  if (CLAMSHELL == "ON")
            cal_CS_B <= #TCQ {mb_to_addr_dec_data[15:8],mb_to_addr_dec_data[15:8],mb_to_addr_dec_data[7:0],mb_to_addr_dec_data[7:0]};
	  else if (RANKS == 8)
            cal_CS_B[dq_index[0]*32 +:32] <= #TCQ mb_to_addr_dec_data[31:0];
	  else
            cal_CS_B <= #TCQ mb_to_addr_dec_data[CSBITS*8-1:0];
        end
        DDR_AC_ADR_A: begin
	  cal_ADR_A <= #TCQ mb_to_addr_dec_data;
        end
        DDR_AC_ADR_B: begin
	  cal_ADR_B <= #TCQ mb_to_addr_dec_data;
        end
		DDR_DBI_WR: begin
		  cal_dbi_wr <= #TCQ mb_to_addr_dec_data[0];
		end
		DDR_DBI_RD: begin
		  cal_dbi_rd <= #TCQ mb_to_addr_dec_data[0];
		end
        DDR_AC_RANKSEL_LOW: begin
          clb2phy_wrcs0_low <= #TCQ {4*DBYTES{mb_to_addr_dec_data[0]}};
          clb2phy_wrcs1_low <= #TCQ {4*DBYTES{mb_to_addr_dec_data[1]}};
          clb2phy_rdcs0_low <= #TCQ {4*DBYTES{mb_to_addr_dec_data[0]}};
          clb2phy_rdcs1_low <= #TCQ {4*DBYTES{mb_to_addr_dec_data[1]}};
        end
        DDR_AC_RANKSEL_UPP: begin
          clb2phy_wrcs0_upp <= #TCQ {4*DBYTES{mb_to_addr_dec_data[0]}};
          clb2phy_wrcs1_upp <= #TCQ {4*DBYTES{mb_to_addr_dec_data[1]}};
          clb2phy_rdcs0_upp <= #TCQ {4*DBYTES{mb_to_addr_dec_data[0]}};
          clb2phy_rdcs1_upp <= #TCQ {4*DBYTES{mb_to_addr_dec_data[1]}};
        end
        CAL_SEQ_A_A_DLY: begin
          cal_seq_a_a_dly <= #TCQ mb_to_addr_dec_data[31:0];
        end
        CAL_SEQ_A_B_DLY: begin
          cal_seq_a_b_dly <= #TCQ mb_to_addr_dec_data[31:0];
        end
        CAL_SEQ_B_A_DLY: begin
          cal_seq_b_a_dly <= #TCQ mb_to_addr_dec_data[31:0];
        end
		ERROR: begin
		  cal_error   <= #TCQ mb_to_addr_dec_data[0];
		end
        WARNING: begin
	      cal_warning_nibble <= #TCQ mb_to_addr_dec_data[8:0];
	      cal_warning_code   <= #TCQ mb_to_addr_dec_data[17:9];
	      cal_warning        <= #TCQ mb_to_addr_dec_data[20];
	    end
        DEBUG: begin
          cal_debug <= #TCQ mb_to_addr_dec_data;
        end
	DEBUG_RAM: begin
	  xsdb_wr_data <= #TCQ mb_to_addr_dec_data[8:0];
	  xsdb_wr_en   <= #TCQ 1'b1;
          if((io_address >= RANK0_STATUS0_ADDR) && (io_address < (RANK0_STATUS0_ADDR + CAL_STATUS_REG_SIZE))) begin
            for(loc=0; loc < CAL_STATUS_REG_SIZE; loc++) begin
              if(io_address == (RANK0_STATUS0_ADDR + loc))
                cal_r0_status[loc*9+:9] <= #TCQ mb_to_addr_dec_data[8:0];
            end
          end else if((io_address >= RANK1_STATUS0_ADDR) && (io_address < (RANK1_STATUS0_ADDR + CAL_STATUS_REG_SIZE))) begin
            for(loc=0; loc < CAL_STATUS_REG_SIZE; loc++) begin
              if(io_address == (RANK1_STATUS0_ADDR + loc))
                cal_r1_status[loc*9+:9] <= #TCQ mb_to_addr_dec_data[8:0];
            end
          end else if((LRDIMM_EN == 0) && (io_address >= RANK2_STATUS0_ADDR) && (io_address < (RANK2_STATUS0_ADDR + CAL_STATUS_REG_SIZE))) begin
            for(loc=0; loc < CAL_STATUS_REG_SIZE; loc++) begin
              if(io_address == (RANK2_STATUS0_ADDR + loc))
                cal_r2_status[loc*9+:9] <= #TCQ mb_to_addr_dec_data[8:0];
            end
          end else if((LRDIMM_EN == 0) && (io_address >= RANK3_STATUS0_ADDR) && (io_address < (RANK3_STATUS0_ADDR + CAL_STATUS_REG_SIZE))) begin
            for(loc=0; loc < CAL_STATUS_REG_SIZE; loc++) begin
              if(io_address == (RANK3_STATUS0_ADDR + loc))
                cal_r3_status[loc*9+:9] <= #TCQ mb_to_addr_dec_data[8:0];
            end
          end else begin
	    case(io_address)
		PRE_STATUS_ADDR: begin
		  cal_pre_status <= #TCQ mb_to_addr_dec_data[8:0];
		end
		POST_STATUS_ADDR: begin
		  cal_post_status <= #TCQ mb_to_addr_dec_data[8:0];
		end
/*
	    RANK0_STATUS0_ADDR: begin
		  cal_r0_status0 <= #TCQ mb_to_addr_dec_data[8:0];
		end
		RANK0_STATUS0_ADDR+1: begin
		  cal_r0_status1 <= #TCQ mb_to_addr_dec_data[8:0];
		end
		RANK0_STATUS0_ADDR+2: begin
		  cal_r0_status2 <= #TCQ mb_to_addr_dec_data[8:0];
		end
		RANK0_STATUS0_ADDR+3: begin
		  cal_r0_status3 <= #TCQ mb_to_addr_dec_data[8:0];
		end
		RANK0_STATUS0_ADDR+4: begin
		  cal_r0_status4 <= #TCQ mb_to_addr_dec_data[8:0];
		end
		RANK0_STATUS0_ADDR+5: begin
		  cal_r0_status5 <= #TCQ mb_to_addr_dec_data[8:0];
		end
		RANK0_STATUS0_ADDR+6: begin
		  cal_r0_status6 <= #TCQ mb_to_addr_dec_data[8:0];
		end
		RANK1_STATUS0_ADDR: begin
		  cal_r1_status0 <= #TCQ mb_to_addr_dec_data[8:0];
		end
		RANK1_STATUS0_ADDR+1: begin
		  cal_r1_status1 <= #TCQ mb_to_addr_dec_data[8:0];
		end
		RANK1_STATUS0_ADDR+2: begin
		  cal_r1_status2 <= #TCQ mb_to_addr_dec_data[8:0];
		end
		RANK1_STATUS0_ADDR+3: begin
		  cal_r1_status3 <= #TCQ mb_to_addr_dec_data[8:0];
		end
		RANK1_STATUS0_ADDR+4: begin
		  cal_r1_status4 <= #TCQ mb_to_addr_dec_data[8:0];
		end
		RANK1_STATUS0_ADDR+5: begin
		  cal_r1_status5 <= #TCQ mb_to_addr_dec_data[8:0];
		end
		RANK1_STATUS0_ADDR+6: begin
		  cal_r1_status6 <= #TCQ mb_to_addr_dec_data[8:0];
		end
		RANK2_STATUS0_ADDR: begin
		  cal_r2_status0 <= #TCQ mb_to_addr_dec_data[8:0];
		end
		RANK2_STATUS0_ADDR+1: begin
		  cal_r2_status1 <= #TCQ mb_to_addr_dec_data[8:0];
		end
		RANK2_STATUS0_ADDR+2: begin
		  cal_r2_status2 <= #TCQ mb_to_addr_dec_data[8:0];
		end
		RANK2_STATUS0_ADDR+3: begin
		  cal_r2_status3 <= #TCQ mb_to_addr_dec_data[8:0];
		end
		RANK2_STATUS0_ADDR+4: begin
		  cal_r2_status4 <= #TCQ mb_to_addr_dec_data[8:0];
		end
		RANK2_STATUS0_ADDR+5: begin
		  cal_r2_status5 <= #TCQ mb_to_addr_dec_data[8:0];
		end
		RANK2_STATUS0_ADDR+6: begin
		  cal_r2_status6 <= #TCQ mb_to_addr_dec_data[8:0];
		end
		RANK3_STATUS0_ADDR: begin
		  cal_r3_status0 <= #TCQ mb_to_addr_dec_data[8:0];
		end
		RANK3_STATUS0_ADDR+1: begin
		  cal_r3_status1 <= #TCQ mb_to_addr_dec_data[8:0];
		end
		RANK3_STATUS0_ADDR+2: begin
		  cal_r3_status2 <= #TCQ mb_to_addr_dec_data[8:0];
		end
		RANK3_STATUS0_ADDR+3: begin
		  cal_r3_status3 <= #TCQ mb_to_addr_dec_data[8:0];
		end
		RANK3_STATUS0_ADDR+4: begin
		  cal_r3_status4 <= #TCQ mb_to_addr_dec_data[8:0];
		end
		RANK3_STATUS0_ADDR+5: begin
		  cal_r3_status5 <= #TCQ mb_to_addr_dec_data[8:0];
		end
		RANK3_STATUS0_ADDR+6: begin
		  cal_r3_status6 <= #TCQ mb_to_addr_dec_data[8:0];
		end
*/
		ERROR0_ADDR: begin
		  cal_error_bit    <= #TCQ mb_to_addr_dec_data[7:0];
		end
		ERROR1_ADDR: begin
		  cal_error_nibble <= #TCQ mb_to_addr_dec_data[7:0];
		end
		ERROR_CODE_ADDR: begin
		  cal_error_code   <= #TCQ mb_to_addr_dec_data[3:0];
		end
	    endcase
          end
	end
        CAL_DONE: begin
          calDone <=  #TCQ mb_to_addr_dec_data[1];
          en_vtc  <=  #TCQ mb_to_addr_dec_data[0];
        end
	CPLX_CFG_STATUS: begin
          cplx_config <= #TCQ mb_to_addr_dec_data;
	end
	default: begin
	  wrong_addr_access_write <= #TCQ ~riu_access & ~seq_cnt_access_b & ~cnt_clr_access & ~lrdimm_cmp_access;
	end
      endcase
    end
  end
/*  
  assign cal_r0_status = {cal_r0_status5, 
                          cal_r0_status4, 
                          cal_r0_status3, 
						  cal_r0_status2, 
						  cal_r0_status1, 
						  cal_r0_status0};
  assign cal_r1_status = {cal_r1_status5, 
                          cal_r1_status4, 
                          cal_r1_status3, 
						  cal_r1_status2, 
						  cal_r1_status1, 
						  cal_r1_status0};
  assign cal_r2_status = {cal_r2_status5, 
                          cal_r2_status4, 
                          cal_r2_status3, 
						  cal_r2_status2, 
						  cal_r2_status1, 
						  cal_r2_status0};
  assign cal_r3_status = {cal_r3_status5, 
                          cal_r3_status4, 
                          cal_r3_status3, 
						  cal_r3_status2, 
						  cal_r3_status1, 
						  cal_r3_status0};
*/

 // Preiodic read uB interface.  The MC sets a flag to indicate that a periodic read
 // interval has expired and that at least one read has completed in that interval.
 // The uB polls the flag.  Polling also clears the flag.
 wire gt_data_ready_flag_nxt = ~clear_gt_data_ready_flag & ( gt_data_ready_flag | gt_data_ready );
 always @(posedge clk) begin
    if(rst_r1) begin
       gt_data_ready_flag <= #TCQ 1'b0;
    end else begin
       gt_data_ready_flag <= #TCQ gt_data_ready_flag_nxt;
    end
 end

// read 
  always @(posedge clk)
  begin
     wrong_addr_access_read <= #TCQ 1'b0;
     clear_gt_data_ready_flag <= #TCQ 1'b0;
      casez(io_address)
        //whatever remain in mcal_DQIn is read out to MB regardless fifo empty
        //Once read command is sent from CMD Processor,
        //comparison logic automatically read out DQ data from fifo
        CAL_RDY: begin
          addr_dec_to_mb_data <= #TCQ {29'h0, phy_ready, rtl_initDone, bisc_complete};
        end
		CAL_BISC: begin
		  addr_dec_to_mb_data <= #TCQ {24'b0, phy2clb_rd_dq_bits};
		end
        DDR_AC_CS_A: begin
          if (RANKS == 8)
            addr_dec_to_mb_data <= #TCQ cal_CS_A[dq_index[0]*32 +:32];
	  else
            addr_dec_to_mb_data <= #TCQ cal_CS_A;
        end
        DDR_AC_CS_B: begin
          if (RANKS == 8)
            addr_dec_to_mb_data <= #TCQ cal_CS_B[dq_index[0]*32 +:32];
	  else
            addr_dec_to_mb_data <= #TCQ cal_CS_B;
        end
		CAL_RIU2CLB_VALID: begin
		  addr_dec_to_mb_data <= #TCQ {{(32-20){1'b0}}, riu2clb_valid};
		end

    // Self-Refresh and Save/Restore inputs
    CAL_RECONFIG: begin
      addr_dec_to_mb_data <= #TCQ {20'b0, 1'b0, app_restore_cmplt_lpulse, app_restore_en_lpulse, app_mem_init_skip, 3'b0,stop_gate_tracking_ack, 3'b0,stop_gate_trck_req_lpulse};
    end
    CAL_TIMER: begin
      addr_dec_to_mb_data <= #TCQ cal_timer;
    end
    CAL_MIGRATION: begin
      addr_dec_to_mb_data <= #TCQ (MIGRATION == "ON") ? MIGRATION_INFO[migr_reg_idx*32 +:32] : 32'b0;
    end

        MCAL_DQIN: begin
          addr_dec_to_mb_data <= #TCQ mcal_DQIn_byte_r1[dq_index[0]*32+:32];
        end
        MCAL_CMP: begin
          addr_dec_to_mb_data <= #TCQ lrdimm_cal_mode ? mcal_dq_cmp_lrdimm[dq_index[0]*32+:32] : mcal_dq_cmp_vld[dq_index[0]*32+:32];  // mcal_dq_cmp[dq_index[0]*32+:32];
        end
        MCAL_DMIN: begin
          addr_dec_to_mb_data <= #TCQ {24'h0, mcal_DMIn_bit_r1};
        end
	    CAL_VREF: begin
	      addr_dec_to_mb_data <= #TCQ {25'h0, rd_vref_value[vref_index*7+:7]};
	    end
        CAL_SEQ_CNT: begin
          addr_dec_to_mb_data <= #TCQ cal_seq_cnt;
        end
        CAL_SEQ_RD_CNT: begin
          addr_dec_to_mb_data <= #TCQ {24'd0,cal_seq_rd_cnt};
        end
	    DDR_AC_ADR_A:begin
	      addr_dec_to_mb_data <= #TCQ cal_ADR_A;
	    end
	    DDR_AC_ADR_B:begin
	      addr_dec_to_mb_data <= #TCQ cal_ADR_B;
	    end
	    DDR_RST_CKE_ODT_PAR:begin
	      addr_dec_to_mb_data <= #TCQ cal_RST_CKE_ODT_PAR;
	    end
	    CAL_TRAFFIC_CNT: begin
	      addr_dec_to_mb_data <= #TCQ { { 32-DLY_CNTR_WIDTH { 1'b0 } }, delay_cntr};
	    end
	    CAL_MARGIN_START: begin
	      addr_dec_to_mb_data <= #TCQ {28'b0, win_start};
	    end
	    CAL_RD_LAT: begin
	      addr_dec_to_mb_data <= #TCQ io_address[0]?
	                              {{2'h0, uppCL3[cl_index*6 +:6]},
	                               {2'h0, uppCL2[cl_index*6 +:6]},
	                               {2'h0, uppCL1[cl_index*6 +:6]},
	                               {2'h0, uppCL0[cl_index*6 +:6]}}
	                             :{{2'h0, lowCL3[cl_index*6 +:6]},
	                               {2'h0, lowCL2[cl_index*6 +:6]},
	                               {2'h0, lowCL1[cl_index*6 +:6]},
	                               {2'h0, lowCL0[cl_index*6 +:6]}};
	    end
	    CAL_TRAFFIC_ERR: begin
	      addr_dec_to_mb_data <= #TCQ traffic_error_byte_r[dq_index[0]*32+:32];
	    end
		CAL_TRAFFIC_STATUS: begin
		  addr_dec_to_mb_data <= #TCQ {26'b0, traffic_status_r2};
		end
		CAL_TRAFFIC_ERR_R: begin
		  addr_dec_to_mb_data <= #TCQ {24'b0, traffic_error_byte_rise};
		end
		CAL_TRAFFIC_ERR_F: begin
		  addr_dec_to_mb_data <= #TCQ {24'b0, traffic_error_byte_fall};
		end
		CAL_TRAFFIC_ERR_RF: begin
		  addr_dec_to_mb_data <= #TCQ {24'b0, traffic_error_byte_rise_fall};
		end
        DEBUG_RAM: begin
          addr_dec_to_mb_data <= #TCQ {23'b0, xsdb_rd_data};
        end
        CONFIGURATION: begin
          addr_dec_to_mb_data <= #TCQ config_rd_data;
        end
		CAL_DONE: begin
		  addr_dec_to_mb_data <= #TCQ {31'b0, calDone};
		end
	    CPLX_CFG_STATUS: begin
	      addr_dec_to_mb_data <= #TCQ { 1'b0, cplx_status[30:0] };
	    end
	    CPLX_ERR_LOG: begin
	      addr_dec_to_mb_data <= #TCQ (dq_index[0]) ? cplx_err_log74 : 
	                                              cplx_err_log30;
	    end
        PERIODIC_RD_STATUS: begin
	      addr_dec_to_mb_data          <= #TCQ {31'b0, gt_data_ready_flag};
          clear_gt_data_ready_flag <= #TCQ gt_data_ready_flag & 
		                                      io_addr_strobe & ~io_write_strobe;
        end
	    default: begin
          addr_dec_to_mb_data <= #TCQ 32'h0;
	      wrong_addr_access_read <= #TCQ  ~riu_access & io_addr_strobe;
	    end
      endcase
   // end
  end


  always @(posedge clk) begin // PS Level
    if(io_ready)
      io_ready_lvl <= #TCQ ~io_ready_lvl;
  end

  always @(posedge clk) begin // Sampling
    if (io_ready)
      io_read_data    <= #TCQ addr_dec_to_mb_data;
  end

  always @ (posedge clk) begin
    if (rst_r1) begin
      io_ready <= #TCQ 'b0;
    end else begin
      if (config_access)
        io_ready <= #TCQ  config_rd_val;
      else if (xsdb_rd_en)
        io_ready <= #TCQ  io_addr_strobe_r2;
      else
        io_ready <= #TCQ  io_addr_strobe;
    end
  end

  always @(posedge clk)begin
    config_rd_val <= #TCQ  io_addr_strobe & ~io_write_strobe;
    cmd_go_ind <= #TCQ io_addr_strobe & io_write_strobe;
    io_addr_strobe_r1 <= #TCQ io_addr_strobe;
    io_addr_strobe_r2 <= #TCQ io_addr_strobe_r1;
  end 
 
  //*************************************************************************//
  //******************Read Comparison logic**********************************//
  //*************************************************************************//
  //Whenever read become valid based on a shifted version of fifo_rden,compare actual and expected data (exclusive or)
  //comparison will be updated contiunously until it is cleared

  wire a_b_rd_sel = ( cal_seq[0] & ~cnt_clr ) ? (a_b_cmd_sel_start ? ~cal_seq_rd_cnt[0]: cal_seq_rd_cnt[0]): '0;
  wire [8*8-1:0] mcal_dq_cmp_xor = dqin_valid_shift[2] ? (mcal_DQIn_byte_r ^ (a_b_rd_sel_r? cal_DQPat_B: cal_DQPat_A)) : '0;
  wire [8*8-1:0] mcal_dq_cmp_nxt = cnt_clr ? '0 : ( mcal_dq_cmp | mcal_dq_cmp_xor );
  always @ (posedge clk)
  begin
    if ( rst_r1 ) begin
      mcal_dq_cmp  <= #TCQ '0;
      a_b_rd_sel_r  <= #TCQ '0;
    end
    else begin
      mcal_dq_cmp  <= #TCQ mcal_dq_cmp_nxt;
      a_b_rd_sel_r  <= #TCQ a_b_rd_sel;
    end
  end

  // Valid data for comparison
  generate
    genvar m1;
    for (m1 = 0; m1 < 8; m1 = m1 + 1)
      assign mcal_dq_cmp_vld[m1*8+:8] = mcal_dq_cmp[m1*8+:8] & ({8{cal_cmp_en[m1]}});
  endgenerate

  // LRDIMM DQ0 check: Reduced OR, Reduced AND
  always @(posedge clk) begin
    if(rst_r1) begin
      lrdimm_cmp_en <= #TCQ 1'b0;
      lrdimm_cmp_clr <= #TCQ 1'b0;
    end else if(lrdimm_cmp_access) begin
      lrdimm_cmp_en <= #TCQ mb_to_addr_dec_data[0];
      lrdimm_cmp_clr <= #TCQ mb_to_addr_dec_data[0];
    end else begin
      lrdimm_cmp_en <= #TCQ lrdimm_cmp_en;
      lrdimm_cmp_clr <= #TCQ 1'b0;
    end
  end

  generate
    genvar bt;
    for (bt = 0; bt < DBYTES*2; bt = bt + 1) begin
      assign mcal_DQ0In_lrdimm_or[bt]  = (| mcal_DQIn_r[bt*4*8+:8]) | mcal_DQ0In_lrdimm_or_r[bt];
      assign mcal_DQ0In_lrdimm_and[bt] = (& mcal_DQIn_r[bt*4*8+:8]) & mcal_DQ0In_lrdimm_and_r[bt];

      always @ (posedge clk) begin
        if(rst_r1 | lrdimm_cmp_clr) begin
          mcal_DQ0In_lrdimm_or_r[bt]  <= #TCQ 1'b0;
          mcal_DQ0In_lrdimm_and_r[bt] <= #TCQ 1'b1;
        end else if(lrdimm_cmp_en) begin
          mcal_DQ0In_lrdimm_or_r[bt]   <= #TCQ mcal_DQ0In_lrdimm_or[bt];
          mcal_DQ0In_lrdimm_and_r[bt]  <= #TCQ mcal_DQ0In_lrdimm_and[bt];
        end
      end
    end
  endgenerate

  // LRDIMM DQ0 check: Stable one, Stable zero
  assign mcal_DQ0In_lrdimm_st_one  = mcal_DQ0In_lrdimm_and_r;
  assign mcal_DQ0In_lrdimm_st_zero = ~mcal_DQ0In_lrdimm_or_r;

  assign mcal_dq_cmp_lrdimm = {{32-(DBYTES*2){1'b0}}, mcal_DQ0In_lrdimm_st_one, {32-(DBYTES*2){1'b0}}, mcal_DQ0In_lrdimm_st_zero};

  always @ (posedge clk)
  begin
    if ((dqin_valid_shift[1] ) | wrlvl_mode) begin
      mcal_DQIn_byte_r  <= #TCQ mcal_DQIn_r[cmp_byte*64 +:64];
	  mcal_DQIn_r_valid <= #TCQ mcal_DQIn_r;
	end
  end

  always @(posedge clk) begin
     mcal_DQIn_r <= #TCQ mcal_DQIn;
     mcal_DMIn_n_r <= #TCQ mcal_DMIn_n;
     mcal_DMIn_bit_r1 <= #TCQ mcal_DMIn_n_r[dm_index*8+:8];
     mcal_DQIn_byte_r1<= mcal_DQIn_r_valid[cmp_byte*64 +:64]; //mcal_DQIn_byte_r
  end 

  always @(posedge clk) begin
    traffic_error_r       <= #TCQ traffic_error;
	traffic_error_byte_r  <= #TCQ traffic_error_r[cmp_byte*64 +:64];
  end
  
  generate
    genvar bit_i;
    for (bit_i = 0; bit_i < 8; bit_i = bit_i + 1) begin: traffic_error_byte
	  assign traffic_error_byte_rise[bit_i] = traffic_error_byte_r[bit_i*8 + 6] | 
	                                          traffic_error_byte_r[bit_i*8 + 4] | 
	                                          traffic_error_byte_r[bit_i*8 + 2] | 
									          traffic_error_byte_r[bit_i*8 + 0];
	  assign traffic_error_byte_fall[bit_i] = traffic_error_byte_r[bit_i*8 + 7] | 
	                                          traffic_error_byte_r[bit_i*8 + 5] | 
	                                          traffic_error_byte_r[bit_i*8 + 3] | 
									          traffic_error_byte_r[bit_i*8 + 1];
	end
  endgenerate
  
  assign traffic_error_byte_rise_fall = (traffic_error_byte_rise | 
                                         traffic_error_byte_fall);
  
  always @(posedge clk) begin
    traffic_status_r1     <= #TCQ {traffic_status_watch_dog_hang,
	                               traffic_status_err_type, 
								   traffic_status_err_type_valid, 
								   traffic_status_err_bit_valid, 
								   traffic_wr_done, 
								   traffic_status_done};
	traffic_status_r2     <= #TCQ traffic_status_r1;
  end
  
  always @(posedge clk) begin
    traffic_start_r2 <= #TCQ traffic_start_r1;
    traffic_start    <= #TCQ traffic_start_r2;
	
    traffic_rst_r2   <= #TCQ traffic_rst_r1;
	traffic_rst      <= #TCQ traffic_rst_r2;
	
    traffic_err_chk_en_r2 <= #TCQ traffic_err_chk_en_r1;
	traffic_err_chk_en    <= #TCQ traffic_err_chk_en_r2;
	
    traffic_instr_addr_mode_r2 <= #TCQ traffic_instr_addr_mode_r1;
	traffic_instr_addr_mode    <= #TCQ traffic_instr_addr_mode_r2;

    traffic_instr_data_mode_r2 <= #TCQ traffic_instr_data_mode_r1;
	traffic_instr_data_mode    <= #TCQ traffic_instr_data_mode_r2;

    traffic_instr_rw_mode_r2 <= #TCQ traffic_instr_rw_mode_r1;
	traffic_instr_rw_mode    <= #TCQ traffic_instr_rw_mode_r2;

    traffic_instr_rw_submode_r2 <= #TCQ traffic_instr_rw_submode_r1;
	traffic_instr_rw_submode    <= #TCQ traffic_instr_rw_submode_r2;

    traffic_instr_num_of_iter_r2 <= #TCQ traffic_instr_num_of_iter_r1;
    traffic_instr_num_of_iter    <= #TCQ traffic_instr_num_of_iter_r2;
	
	traffic_instr_nxt_instr_r2 <= #TCQ traffic_instr_nxt_instr_r1;
    traffic_instr_nxt_instr    <= #TCQ traffic_instr_nxt_instr_r2;
  end
  
  // Generate read data valid signal from mc_pi fifo_rden logic.
  // Generate signal to clear the mc_pi fifo_rden logic on cnt_clr until calDone
  wire clear_fifo_rden_nxt = cnt_clr & ~calDone;
  wire [7:0] dqin_valid_shift_nxt = { 8 { ~cnt_clr } } & { dqin_valid_shift[6:0], mc_clb2phy_fifo_rden_nxt };
  always @ (posedge clk)
  begin
    dqin_valid_shift <= #TCQ dqin_valid_shift_nxt;
    clear_fifo_rden  <= #TCQ clear_fifo_rden_nxt;
  end

  // Generate fifo_rden override signal in wrlvl mode
  wire [DBYTES*13-1:0]  clb2phy_fifo_rden_nxt = { DBYTES*13 { (wrlvl_mode | lrdimm_cal_mode) & ~calDone } };
  always @ (posedge clk)
  begin
    clb2phy_fifo_rden    <= #TCQ clb2phy_fifo_rden_nxt;
  end
  
  
  //*************************************************************************//
  //******************CMD Processor *****************************************//
  //*************************************************************************//

  //cmd always start from A. It is used for toggling of cmd
  //a_b_cmd_sel_start is used for A/B command toggling
  always @ (posedge clk) begin
    if (rst_r1) begin
      a_b_cmd_sel_start <= #TCQ 'b0;
      a_b_cmd_sel <= #TCQ 'b0;
    end
    else begin
      a_b_cmd_sel_start <= #TCQ (seq_cnt_access_b & io_addr_strobe & io_write_strobe)? mb_to_addr_dec_data[0]:a_b_cmd_sel_start;
      a_b_cmd_sel <= a_b_cmd_sel_pre;
    end
  end

  //cmd_go : checking command is processing
  //sec_cnt_dec : 1 command is processed. can_sec_cnt decreased by 1
  //cmd_gen_dly : delay for next command
  //cal_seq[0] : 0 for A command only, 1 for A/B alternate command
  //wrCAS and wrRAS should be one clock earlier then cal_CS_n
  always @ (posedge clk)
  begin
    if (rst_r1) begin
      seq_cnt_dec <= #TCQ 'b0;
      cmd_gen_dly <= #TCQ 'b0;
    end else begin
      seq_cnt_access <= #TCQ  seq_cnt_access_b;
      //cmd generation process is started when cal_seq_cnt is set, and stopped when cal_seq_cnt is set to 0
       cmd_go <= #TCQ (cmd_go_ind & seq_cnt_access & (cal_seq_cnt_gt_0))?1:((cal_seq_cnt_gt_0 == 'b0 )?0:cmd_go);

      //seq_cnt_dec is generated when delay between 2 cmd is same as delay set by MB
        if(cmd_go & (cal_seq_cnt_gt_0)) begin
        if(~cal_seq[0]) begin    //A command only
	  seq_cnt_dec <= #TCQ (cmd_gen_dly == cal_seq_a_a_dly[7:0])?1:0;
          cmd_gen_dly <= #TCQ (cmd_gen_dly == cal_seq_a_a_dly[7:0])?0:cmd_gen_dly + 'b1;
        end else begin
          if (a_b_cmd_sel_gen) begin  //B command is selcted (A->B)
            seq_cnt_dec <= #TCQ  (cmd_gen_dly == cal_seq_a_b_dly[7:0])?1:0;
            cmd_gen_dly <= #TCQ (cmd_gen_dly == cal_seq_a_b_dly[7:0])? 0: cmd_gen_dly + 'b1;
          end else begin  //A command is selcted (B->A)
            seq_cnt_dec <= #TCQ  (cmd_gen_dly == cal_seq_b_a_dly[7:0]);
            cmd_gen_dly <= #TCQ  (cmd_gen_dly == cal_seq_b_a_dly[7:0])? 0: cmd_gen_dly + 'b1;
          end
        end
      end else begin
        seq_cnt_dec <= #TCQ 'b0;
        cmd_gen_dly <= #TCQ 'b0;
      end
    end
  end

  //Seq cnt decreasing whenever cmd is issued
  //rd cnt decreasing whenenver read is issued
  //clear seq cnt when cnt_clr is issued
  always @ (posedge clk)
  begin
    //whenever seq_cnt_dec, cal_seq_cnt is decreasing
    //if clr message is written, cal_seq_cnt is set to "0"
    if(seq_cnt_access_b) begin  //wnen seq_cnt is written
      if ((CLAMSHELL == "ON") && cal_mrs) begin
        cal_seq_cnt <= #TCQ 2*mb_to_addr_dec_data[31:0];
      end else begin
        cal_seq_cnt <= #TCQ mb_to_addr_dec_data[31:0];
      end
      cal_seq_rd_cnt <= #TCQ mb_to_addr_dec_data[7:0];
      cnt_clr        <= #TCQ 'b0;
    end else if (cnt_clr_access) begin //when cnt_clr is written
      cnt_clr <= #TCQ mb_to_addr_dec_data[0];
    end else if (cnt_clr) begin
      cal_seq_cnt <= #TCQ 'b0;
      cal_seq_rd_cnt <= #TCQ 'b0;
    end else begin
      cal_seq_cnt <= #TCQ (cal_seq_cnt_gt_0) & seq_cnt_dec? cal_seq_cnt - 'b1 : cal_seq_cnt;
      if (dqin_valid_shift[1] & cal_seq_rd_cnt != 0) 
	    cal_seq_rd_cnt <= #TCQ cal_seq_rd_cnt - 'b1;
	  else
	    cal_seq_rd_cnt <= #TCQ cal_seq_rd_cnt;
    end
  end

 // signal to have the status of the counters. Will be used in comparison

  always @ (posedge clk)
  begin
     if(seq_cnt_access_b)
       cal_seq_cnt_gt_0 <= #TCQ |mb_to_addr_dec_data[31:0];
     else if (cnt_clr)
       cal_seq_cnt_gt_0 <= #TCQ 0;
     else if (seq_cnt_dec)
       cal_seq_cnt_gt_0 <= #TCQ (cal_seq_cnt > 1);
     else 
       cal_seq_cnt_gt_0 <= #TCQ |cal_seq_cnt;
  end 

  assign cal_ADR_A_ext = LRDIMM_EN ? (extended_write_mode ? (extended_write_r[0] ? (cal_ADR_A ^ 8'h40) : (extended_write_r[2] ? (cal_ADR_A ^ 8'h80) : cal_ADR_A)) : cal_ADR_A) : cal_ADR_A;
 
  assign                  cal_ADR_int_nxt = cplx_cal ? { { 32-ABITS { 1'b0 }}, cplx_ADR }   : ( a_b_cmd_sel? cal_ADR_B:   cal_ADR_A_ext );
  //wire [7:0]              cal_ACT_n_nxt   = cplx_cal ? cplx_ACT_n : ( a_b_cmd_sel? cal_ACT_n_B: cal_ACT_n_A );

  //RESET, PAR, and CKE not currently adjusted by calibration. If that changes, 
  //need to update to handle the CS tied off case
  assign cal_RESET_n = cal_RST_CKE_ODT_PAR[7:0];
  assign cal_PAR     = cal_RST_CKE_ODT_PAR[15:8];
  generate
    genvar cke_i;
    for(cke_i = 0; cke_i < CKEBITS ; cke_i = cke_i + 1)
      assign cal_CKE[cke_i*8 +:8] = {8{cal_RST_CKE_ODT_PAR[16 + cke_i]}};
  endgenerate

  wire [ODTBITS-1:0]     cal_ODT_mux_nxt = cplx_cal ? cplx_ODT : cal_RST_CKE_ODT_PAR[ODTBITS+23:24];
  always @(posedge clk)
     cal_ODT_mux <= #TCQ cal_ODT_mux_nxt;

  generate
    genvar odt_i;
    for (odt_i = 0; odt_i < ODTBITS ; odt_i = odt_i + 1) begin
      assign cal_ODT_mux_8[odt_i*8 +:8] = {8{cal_ODT_mux[odt_i]}};
      // Set up signals to shift the ODT submodule output by one UI.
      assign mc_cal_ODT_msb_nxt[odt_i]  = mc_cal_ODT[odt_i*8 + 7];
      assign mc_cal_ODT_shifted[odt_i*8 +:8] = { mc_cal_ODT[odt_i*8 +:7], mc_cal_ODT_msb[odt_i] };
    end
  endgenerate

  // Delay msb by one fabric clock for one UI shift to align with other addr_decode cmd/add signals
  always @(posedge clk)
    mc_cal_ODT_msb <= #TCQ mc_cal_ODT_msb_nxt;

  // Final assignment of module's odt output. Using Traffic ODT style for both normal traffic and calibration.
  assign cal_ODT = 1'b1 ? mc_cal_ODT_shifted : cal_ODT_mux_8;


  always @(posedge clk)
     extended_write_mode <= #TCQ cal_seq[2];

   wire [7:0]               cal_RAS_nxt  = cplx_cal ? cplx_RAS  : cal_RAS_pre;
   wire [7:0]               cal_CAS_nxt  = cplx_cal ? cplx_CAS  : cal_CAS_pre;
   wire [7:0]               cal_WE_nxt   = cplx_cal ? cplx_WE   : cal_WE_pre;
   wire [7:0]               cal_ACT_n_nxt= cplx_cal ? cplx_ACT_n: cal_ACT_n_pre;
   wire [CSBITS*8-1:0]      cal_CS_n_nxt = cplx_cal ? cplx_CS_n : cal_CS_n_pre;

   assign cal_RAS  = cal_RAS_nxt;
   assign cal_CAS  = cal_CAS_nxt;
   assign cal_WE   = cal_WE_nxt;
   assign cal_ACT_n= cal_ACT_n_nxt;
   assign cal_CS_n = cal_CS_n_nxt;
  
   assign cal_CS_A_clm = ((CLAMSHELL=="ON") && cal_mrs)
                              ? ((cal_seq_cnt==1) ? (cal_CS_A | {CS_PAIR{16'h00FF}})
                                                  : (cal_CS_A | {CS_PAIR{16'hFF00}}))
                              : cal_CS_A ;
   assign cal_CS_B_clm = ((CLAMSHELL=="ON") && cal_mrs)
                              ? ((cal_seq_cnt==1) ? (cal_CS_B | {CS_PAIR{16'h00FF}})
                                                  : (cal_CS_B | {CS_PAIR{16'hFF00}}))
                              : cal_CS_B ;

   wire [7:0] cal_WE_noCS_A    = (USE_CS_PORT == 0 && 
                                  cal_WE_A == {8{1'b0}}) ? cal_CS_A_clm : {8{1'b1}};
   wire [7:0] cal_CAS_noCS_A   = (USE_CS_PORT == 0 && 
                                  cal_CAS_A == {8{1'b0}}) ? cal_CS_A_clm : {8{1'b1}};
   wire [7:0] cal_RAS_noCS_A   = (USE_CS_PORT == 0 && 
                                  cal_RAS_A == {8{1'b0}}) ? cal_CS_A_clm : {8{1'b1}};
   wire [7:0] cal_ACT_n_noCS_A = (USE_CS_PORT == 0 && 
                                  cal_ACT_n_A == {8{1'b0}}) ? cal_CS_A_clm : {8{1'b1}};
								  
   wire [7:0] cal_WE_noCS_B    = (USE_CS_PORT == 0 && 
                                  cal_WE_A == {8{1'b0}}) ? cal_CS_B_clm : {8{1'b1}};
   wire [7:0] cal_CAS_noCS_B   = (USE_CS_PORT == 0 && 
                                  cal_CAS_A == {8{1'b0}}) ? cal_CS_B_clm : {8{1'b1}};
   wire [7:0] cal_RAS_noCS_B   = (USE_CS_PORT == 0 && 
                                  cal_RAS_A == {8{1'b0}}) ? cal_CS_B_clm : {8{1'b1}};
   wire [7:0] cal_ACT_n_noCS_B = (USE_CS_PORT == 0 && 
                                  cal_ACT_n_A == {8{1'b0}}) ? cal_CS_B_clm : {8{1'b1}};
   
  //RAS/CAS/WE/CS will be reset to 1
  //CS will be retiming for CMD generation
  always @ (posedge clk)
  begin
    if (rst_r1) begin
      cal_CS_n_pre <= #TCQ {CSBITS*8{1'b1}};
      cal_WE_pre    <= #TCQ {8{1'b1}};
      cal_CAS_pre   <= #TCQ {8{1'b1}};
      cal_RAS_pre   <= #TCQ {8{1'b1}};
      cal_ACT_n_pre <= #TCQ {8{1'b1}};
      rdCAS <= #TCQ 'b0;
      wrCAS <= #TCQ 'b0;
      extended_write <= #TCQ 'b0;
      extended_write_r <= #TCQ 'b0;
      wren <= #TCQ 'b0;
    end else begin
      cal_WE_pre    <= #TCQ cal_WE_pre_nxt;
      cal_CAS_pre   <= #TCQ cal_CAS_pre_nxt;
      cal_RAS_pre   <= #TCQ cal_RAS_pre_nxt;
      cal_ACT_n_pre <= #TCQ cal_ACT_n_pre_nxt;
      extended_write[0]   <= #TCQ cal_seq_cnt_gt_0 & seq_cnt_dec; 
      extended_write[2:1] <= #TCQ extended_write [1:0];
      extended_write_r <= #TCQ extended_write;
      wren <= #TCQ wrDataEn;
      if ( cplx_issue_cas_wr | cplx_issue_cas_rd ) begin
        cal_CS_n_pre <= #TCQ {CSBITS*8{1'b1}};
        rdCAS <= #TCQ cplx_issue_cas_rd;
        wrCAS <= #TCQ cplx_issue_cas_wr;
      //Time adjustment and A/B selction for CS
      end else if( cal_seq_cnt_gt_0 & seq_cnt_dec & ~extended_write_mode ) begin
        //Don't generate CS for wrlvl_mode
        cal_CS_n_pre <= #TCQ wrlvl_mode? {CSBITS*8{1'b1}}:
		                     (a_b_cmd_sel_pre? cal_CS_B_clm: cal_CS_A_clm);   //select CS and load for one fablic clock
        rdCAS <= #TCQ it_is_read;
        wrCAS <= #TCQ it_is_write | wrlvl_mode | write_vref_mode | lrdimm_drive_dq ;   //write command or wrlvl mode generate tri-state
      end else if(~extended_write_mode) begin
        cal_CS_n_pre <= #TCQ  {CSBITS*8{1'b1}};
	rdCAS <= #TCQ 'b0;
        wrCAS <= #TCQ lrdimm_drive_dq ? 1'b1 : 1'b0;
      end else begin
        wrCAS <= #TCQ |extended_write;                                    //3 wrCAS issue for extended write
        cal_CS_n_pre <= #TCQ (LRDIMM_EN ? |extended_write : extended_write[1]) ? cal_CS_A_clm:{CSBITS*8{1'b1}} ;   //only one CS issue
        rdCAS <= #TCQ 'b0;
      end
    end
  end

generate
always @(*) begin
  if (USE_CS_PORT == 1) begin
    cal_WE_pre_nxt    =  ( a_b_cmd_sel ? cal_WE_B    : cal_WE_A );
    cal_CAS_pre_nxt   =  ( a_b_cmd_sel ? cal_CAS_B   : cal_CAS_A );
    cal_RAS_pre_nxt   =  ( a_b_cmd_sel ? cal_RAS_B   : cal_RAS_A );
    cal_ACT_n_pre_nxt =  ( a_b_cmd_sel ? cal_ACT_n_B : cal_ACT_n_A );
  end else begin
    if ( cplx_issue_cas_wr | cplx_issue_cas_rd ) begin
      cal_WE_pre_nxt    =  cal_WE_pre;
      cal_CAS_pre_nxt   =  cal_CAS_pre;
      cal_RAS_pre_nxt   =  cal_RAS_pre;
      cal_ACT_n_pre_nxt =  cal_ACT_n_pre;
    end else if( cal_seq_cnt_gt_0 & seq_cnt_dec & ~extended_write_mode ) begin
      cal_WE_pre_nxt    =  ( a_b_cmd_sel_pre?cal_WE_noCS_B:  cal_WE_noCS_A );
      cal_CAS_pre_nxt   =  ( a_b_cmd_sel_pre?cal_CAS_noCS_B: cal_CAS_noCS_A );
      cal_RAS_pre_nxt   =  ( a_b_cmd_sel_pre?cal_RAS_noCS_B: cal_RAS_noCS_A );
      cal_ACT_n_pre_nxt =  ( a_b_cmd_sel_pre?cal_ACT_n_noCS_B: cal_ACT_n_noCS_A );
    end else if(~extended_write_mode) begin
      cal_WE_pre_nxt    =  {8{1'b1}};
      cal_CAS_pre_nxt   =  {8{1'b1}};
      cal_RAS_pre_nxt   =  {8{1'b1}};
      cal_ACT_n_pre_nxt =  {8{1'b1}};
    end else begin
      cal_WE_pre_nxt    =  extended_write[1]? cal_WE_noCS_A : {8{1'b1}};
      cal_CAS_pre_nxt   =  extended_write[1]? cal_CAS_noCS_A : {8{1'b1}};
      cal_RAS_pre_nxt   =  extended_write[1]? cal_RAS_noCS_A : {8{1'b1}};
      cal_ACT_n_pre_nxt =  extended_write[1]? cal_ACT_n_noCS_A : {8{1'b1}};
    end
  end
end
endgenerate

  
  generate
    genvar dm_i;
    for(dm_i=0; dm_i<DBYTES; dm_i= dm_i+1) begin
	  always @ (posedge clk) begin
	     if (rst_r1)
	      cal_DMOut_n_A_r[dm_i*8+:8] <= #TCQ 8'h0;
	     else if (dm_index == (dm_i/4))
	      cal_DMOut_n_A_r[dm_i*8+:8] <= #TCQ cal_DMOut_n_A[(dm_i%4)*8+:8];
		else
		  cal_DMOut_n_A_r[dm_i*8+:8] <= #TCQ cal_DMOut_n_A_r[dm_i*8+:8];
	  end
	end
  endgenerate

  wire [DBYTES*8-1:0] cal_DMOut_n_nxt = cplx_cal ? cplx_DMOut_n : ( wrDataEn? cal_DMOut_n_A_r: {(DBYTES*8){1'b0}} );

  always @ (posedge clk) begin
    //cal_DMOut_n_A_r <= #TCQ cal_DMOut_n_A;
    cal_DMOut_n <= #TCQ cal_DMOut_n_nxt;
  end 

  //*************************************************************************//
  //******************Write related signal retiming**************************//
  //*************************************************************************//

  //after cwl (of fabrick clock) DQ,DM,DQS is sent to phy
/*  generate
    always @ (posedge clk)
    begin
      for(i = 0; i < DBYTES; i=i+1) begin
       if(extended_write_mode) begin
	 case({wren[1],wren[0],wrDataEn})
	   3'b001: cal_DQOut[64*i +:64] <= #TCQ cal_DQOut_pre[63:0];
	   3'b011: cal_DQOut[64*i +:64] <= #TCQ cal_DQOut_A[63:0];
	   3'b111: cal_DQOut[64*i +:64] <= #TCQ cal_DQOut_post[63:0];
	   default: cal_DQOut[64*i +:64] <= #TCQ cal_DQOut_A[63:0];
	 endcase
       end else begin
         cal_DQOut[64*i +:64] <= #TCQ cal_DQOut_A[63:0];
       end
      end  //for
    end  //always
  endgenerate */

  // symplified the above logic for timing 
  wire [DBYTES*8*8-1:0]    cal_DQOut_nxt = cplx_cal ? cplx_DQOut : cal_DQ;
  always @ (posedge clk)
    cal_DQOut <= #TCQ cal_DQOut_nxt;
  
generate
    always @ (posedge clk)
    begin
       if (lrdimm_drive_dq) begin 
         for(j = 0; j < DBYTES; j=j+1) begin
           cal_DQ[64*j +:64]    <= #TCQ {64{~cal_DQOut_A[j]}};
	 end
       end else if (!write_vref_mode) begin 
           for(i = 0; i < DBYTES; i=i+1) begin
             cal_DQ[64*i +:64]    <= #TCQ cal_DQOut_A[63:0];
               if(extended_write_mode) begin
                  if(wrDataEn && ~wren)
                     cal_DQ[64*i +:64] <= #TCQ cal_DQOut_A[63:0];
                  else if(wrDataEn && wren)
                     cal_DQ[64*i +:64] <= #TCQ cal_DQOut_post[63:0];
                  else if(~wrDataEn)
                     cal_DQ[64*i +:64] <= #TCQ cal_DQOut_pre[63:0];
                end
             end
       end else begin
            for(i = 0; i < DBYTES; i=i+1) begin
               if (devices_dsel)
		 cal_DQ[64*i +:64] <= #TCQ 64'b0;
	       else if ((DRAM_WIDTH == 4) && (i == dram_device_sel[7:1]))
		 cal_DQ[64*i +:64] <= #TCQ (dram_device_sel[0] ? 64'h00000000FFFFFFFF : 64'hFFFFFFFF00000000);
	       else if ((DRAM_WIDTH >= 8) && (i == dram_device_sel[7:0])) 
                 cal_DQ[64*i +:64] <= #TCQ 64'b0;
               else 
                 cal_DQ[64*i +:64] <= #TCQ 64'hFFFFFFFFFFFFFFFF;
            end
       end
    end
  endgenerate 

  //***************************************************************************
  // Delay counter for Margin Checking
  //***************************************************************************
  always @(posedge clk)
    if (traffic_clr_error_r2 || rst_r1)
      delay_cntr_rd_valid <= #TCQ 1'b0;
    else     
      //delay_cntr_rd_valid <= #TCQ dqin_valid_shift[4];
      delay_cntr_rd_valid <= #TCQ traffic_wr_done;

  assign delay_cntr_ce = ~delay_cntr_done & delay_cntr_rd_valid;

  always @(posedge clk)
    if (traffic_clr_error_r2 || rst_r1)
      //delay_cntr <= #TCQ {DLY_CNTR_WIDTH{1'b1}};
      delay_cntr <= #TCQ (traffic_instr_nxt_instr_r1 == 6'b0) ? 'h4 : 'h1;
    else if (delay_cntr_ce)
      delay_cntr <= #TCQ delay_cntr - 1;
	else
	  delay_cntr <= #TCQ delay_cntr;

  assign delay_cntr_done = (delay_cntr == {DLY_CNTR_WIDTH{1'b0}}) ? 1'b1 : 1'b0;
  
  always @(posedge clk)
  begin
    traffic_clr_error_r  <= #TCQ cnt_clr;
    traffic_clr_error_r1 <= #TCQ traffic_clr_error_r;
    traffic_clr_error_r2 <= #TCQ traffic_clr_error_r1;
    traffic_clr_error    <= #TCQ traffic_clr_error_r2;
  end

// Complex calibration module

   wire                     cplx_DQIn_valid = mc_clb2phy_fifo_rden_nxt;
   wire [DBYTES*8*8-1:0]    cplx_DQIn       = mcal_DQIn_r;

ddr4_v2_2_10_cal_cplx # (
    .DBYTES      (DBYTES),
    .ABITS      (ABITS),
    .BABITS     (BABITS),
    .BGBITS     (BGBITS),
    .CKEBITS    (CKEBITS),
    .CSBITS     (CSBITS_CS),
    .ODTBITS    (ODTBITS),
    .TCQ        (TCQ),
    .MEM        (MEM),
    .CPLX_PAT_LENGTH  (CPLX_PAT_LENGTH),
    .EXTRA_CMD_DELAY  (EXTRA_CMD_DELAY),
    .WL         (WL),
    .CLK_2TO1   (CLK_2TO1)
) u_ddr_cal_cplx (
    .clk                    (clk),
    .rst                    (rst_r1),
    // Inputs
    .cplx_config            (cplx_config),
    .cplx_DQIn              (cplx_DQIn),
    .cplx_DQIn_valid        (cplx_DQIn_valid),
    // Outputs
    .cplx_cal               (cplx_cal),
    .cplx_status            (cplx_status),
    .cplx_err_log30         (cplx_err_log30),
    .cplx_err_log74         (cplx_err_log74),
    .cplx_DQOut             (cplx_DQOut),
    .cplx_DMOut_n           (cplx_DMOut_n),
    .cplx_ADR               (cplx_ADR),
    .cplx_WE                (cplx_WE),
    .cplx_RAS               (cplx_RAS),
    .cplx_CAS               (cplx_CAS),
    .cplx_ACT_n             (cplx_ACT_n),
    .cplx_BA                (cplx_BA),
    .cplx_BG                (cplx_BG),
    .cplx_CKE               (cplx_CKE),
    .cplx_CS_n              (cplx_CS_n_cshell),
    .cplx_ODT               (cplx_ODT),
    .cplx_PAR               (cplx_PAR),
    .cplx_issue_cas_rd      (cplx_issue_cas_rd),
    .cplx_issue_cas_wr      (cplx_issue_cas_wr),
	.cplx_expected_data     (cplx_expected_data)
);
always @(*) begin
  for (rnk = 0; rnk < RANKS; rnk = rnk + 1) begin
    if (CLAMSHELL == "OFF") begin
      cplx_CS_n = cplx_CS_n_cshell;
    end else begin
      cplx_CS_n[rnk*16+:16] = {2{cplx_CS_n_cshell[rnk*8+:8]}};
    end
  end
end

// Parameter based odt generation for calibration.
// Uses same parameters and submodule as the MC.

wire casSlot2  = casSlot == 2'd2; // Only slot0 and slot2 are supported
wire tranSentC = rdCAS | wrCAS;

always @(*) begin
  lrdimm_cal_rank = {RNK_BITS{1'b0}};
  for (rnk = 0; rnk < RANKS; rnk = rnk + 1) begin
    if (CLAMSHELL == "OFF") begin
      if(&cal_CS_n[rnk*8+:8] == 1'b0)
        lrdimm_cal_rank = rnk;
    end else begin
      if(&cal_CS_n[rnk*16+:16] == 1'b0)
        lrdimm_cal_rank = rnk;
    end
  end
end

assign cal_mem_rank = LRDIMM_EN ? lrdimm_cal_rank : calRank;

ddr4_v2_2_10_cal_mc_odt #(
    .ODTWR     (ODTWR)
   ,.ODTWRDEL  (ODTWRDEL)
   ,.ODTWRDUR  (ODTWRDUR)
   ,.ODTWRODEL (ODTWRODEL)
   ,.ODTWRODUR (ODTWRODUR)

   ,.ODTRD     (ODTRD)
   ,.ODTRDDEL  (ODTRDDEL)
   ,.ODTRDDUR  (ODTRDDUR)
   ,.ODTRDODEL (ODTRDODEL)
   ,.ODTRDODUR (ODTRDODUR)

   ,.RANKS     (RANKS)
   ,.RNK_BITS  (RNK_BITS)
   ,.ODTNOP    (ODTNOP)
   ,.ODTBITS   (ODTBITS)
   ,.TCQ       (0.1)      // hardcode delay due to different timescale in this submodule
)u_ddr_cal_odt(
    .clk (clk)
   ,.rst (rst_r1)

   ,.mc_ODT    (mc_cal_ODT)

   ,.casSlot2  (casSlot2)
   ,.rank      (cal_mem_rank)
   ,.winRead   (rdCAS)
   ,.winWrite  (wrCAS)
   ,.tranSentC (tranSentC)
);





endmodule




